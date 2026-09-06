//! Cross-language SMT script parity ([VER-013] AC1).
//!
//! For every fixture in `spec/verification-fixtures/fixtures.json` the scripts the
//! verifier would send to z3 ([`SmtVerifier::encode_scripts`]) must equal the
//! committed goldens under `spec/verification-fixtures/scripts/<id>/`, byte for
//! byte. The goldens are written by THIS test with `LIBPETRI_SMT_SCRIPT_UPDATE=1`
//! (`scripts/smt-script-parity.py --update`) and diffed by the Java, TypeScript
//! and Python script-parity tests too, so the four implementations emit the same
//! text. A diff is a parity finding in whichever emitter drifted, never a reason
//! to edit a golden by hand.
//!
//! With a z3 on the machine the test also ties the API to the pipeline: what
//! `verify()` actually sends (captured through `LIBPETRI_SMT_DUMP`) is what
//! `encode_scripts()` reports. The environment is process-global, so this file
//! holds exactly ONE `#[test]`.

#![cfg(feature = "z3")]

#[path = "common/json.rs"]
mod json;
#[path = "common/nets.rs"]
mod nets;
use json::{Json, parse_json};

use std::fs;
use std::path::{Path, PathBuf};

use libpetri_verification::property::SmtProperty;
use libpetri_verification::smt_verifier::{EncodedScripts, SmtVerifier, z3_available};

fn property_of(prop: &Json) -> SmtProperty {
    match prop.str("type") {
        "deadlock-free" => SmtProperty::DeadlockFree,
        "terminates-at-sink" => SmtProperty::TerminatesAtSink,
        "mutual-exclusion" => SmtProperty::mutual_exclusion(
            prop.arr("places")
                .iter()
                .map(|p| match p {
                    Json::Str(s) => s.clone(),
                    other => panic!("expected place name string, got {other:?}"),
                })
                .collect(),
        ),
        "place-bound" => SmtProperty::place_bound(prop.str("place"), prop.usize("bound")),
        "unreachable" => SmtProperty::unreachable(vec![prop.str("place").to_string()]),
        other => panic!("unknown fixture property type '{other}'"),
    }
}

/// The verifier a fixture configures, with both validation layers on (the
/// defaults; the certificate script depends on nothing else).
fn verifier_for<'a>(fixture: &Json, built: &'a nets::FixtureNet) -> SmtVerifier<'a> {
    let property = property_of(fixture.get("property").expect("fixture without property"));
    let mut verifier = SmtVerifier::for_net(&built.net)
        .initial_marking(built.initial.clone())
        .property(property)
        .certificate_check(true)
        .counterexample_replay(true)
        .timeout(30_000);
    if !built.env_places.is_empty() {
        verifier = verifier
            .environment_places(built.env_places.iter().cloned())
            .environment_mode(built.env_mode.clone());
    }
    let sinks = fixture.str_arr_opt("sinkPlaces");
    if !sinks.is_empty() {
        verifier = verifier.sink_places(sinks.iter().cloned());
    }
    let budgets = fixture.str_arr_opt("budgetPlaces");
    if !budgets.is_empty() {
        verifier = verifier.budget_places(budgets.iter().cloned());
    }
    // Optional shared-schema field: [VER-007]'s semiflow union.
    verifier = verifier.semiflow_invariants(fixture.bool_opt("semiflowInvariants"));
    verifier
}

/// The first line on which two texts differ, for the finding.
fn first_difference(expected: &str, actual: &str) -> String {
    for (i, (e, a)) in expected.lines().zip(actual.lines()).enumerate() {
        if e != a {
            return format!("line {}:\n  golden: {e}\n  actual: {a}", i + 1);
        }
    }
    format!(
        "one text is a prefix of the other (golden {} lines, actual {} lines)",
        expected.lines().count(),
        actual.lines().count()
    )
}

fn compare(findings: &mut Vec<String>, id: &str, file: &Path, actual: Option<&str>) {
    let golden = fs::read_to_string(file).ok();
    match (golden, actual) {
        (Some(g), Some(a)) if g == a => {}
        (Some(g), Some(a)) => findings.push(format!(
            "SCRIPT PARITY FINDING [{id}]: {} differs from the golden at {}",
            file.display(),
            first_difference(&g, a)
        )),
        (None, Some(_)) => findings.push(format!(
            "SCRIPT PARITY FINDING [{id}]: no golden at {} (run scripts/smt-script-parity.py --update)",
            file.display()
        )),
        (Some(_), None) => findings.push(format!(
            "SCRIPT PARITY FINDING [{id}]: {} exists but this encoding emits no such script",
            file.display()
        )),
        (None, None) => {}
    }
}

#[test]
fn smt_scripts_match_the_committed_goldens() {
    let root = PathBuf::from(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../spec/verification-fixtures"
    ));
    let raw = fs::read_to_string(root.join("fixtures.json")).expect("read fixtures.json");
    let doc = parse_json(&raw);
    let fixtures = doc.arr("fixtures");
    assert!(!fixtures.is_empty(), "fixtures.json lists no fixtures");
    let update = std::env::var_os("LIBPETRI_SMT_SCRIPT_UPDATE").is_some();

    let mut findings: Vec<String> = Vec::new();
    let mut encoded: Vec<(String, EncodedScripts)> = Vec::new();
    for fixture in fixtures {
        let id = fixture.str("id");
        let built = nets::build(fixture.str("net"));
        let scripts = verifier_for(fixture, &built).encode_scripts();
        let dir = root.join("scripts").join(id);
        let horn = dir.join("horn.smt2");
        let certificate = dir.join("certificate.smt2");
        if update {
            fs::create_dir_all(&dir).expect("create golden dir");
            fs::write(&horn, &scripts.horn).expect("write horn golden");
            match &scripts.certificate {
                Some(text) => fs::write(&certificate, text).expect("write certificate golden"),
                None => {
                    let _ = fs::remove_file(&certificate);
                }
            }
            eprintln!("[script-parity] wrote {}", dir.display());
        } else {
            compare(&mut findings, id, &horn, Some(&scripts.horn));
            compare(&mut findings, id, &certificate, scripts.certificate.as_deref());
        }
        encoded.push((id.to_string(), scripts));
    }

    // API ↔ pipeline: the HORN script verify() sends is the one encode_scripts()
    // reports. Route B fixtures never reach the solver; a structural early proof
    // leaves no dump either, and both are skipped.
    if z3_available() {
        let scratch = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../target/smt-parity")
            .join(format!("{}", std::process::id()));
        for fixture in fixtures {
            if fixture.str_opt("route") == Some("B") {
                continue;
            }
            let id = fixture.str("id");
            let dump = scratch.join(id);
            // SAFETY: this binary runs one test; no other thread reads the environment.
            unsafe { std::env::set_var("LIBPETRI_SMT_DUMP", &dump) };
            let built = nets::build(fixture.str("net"));
            let _ = verifier_for(fixture, &built).verify();
            // SAFETY: as above.
            unsafe { std::env::remove_var("LIBPETRI_SMT_DUMP") };
            let sent = fs::read_dir(&dump)
                .ok()
                .into_iter()
                .flatten()
                .filter_map(|e| e.ok())
                .map(|e| e.path())
                .filter(|p| {
                    let name = p.file_name().unwrap_or_default().to_string_lossy().into_owned();
                    name.contains("-horn") && name.ends_with(".smt2")
                })
                .min();
            if let Some(path) = sent {
                let actual = fs::read_to_string(&path).expect("read dumped script");
                let reported = &encoded.iter().find(|(f, _)| f == id).expect("encoded").1.horn;
                if &actual != reported {
                    findings.push(format!(
                        "SCRIPT PARITY FINDING [{id}]: the HORN script verify() sent ({}) differs \
                         from encode_scripts() at {}",
                        path.display(),
                        first_difference(reported, &actual)
                    ));
                }
            }
        }
        let _ = fs::remove_dir_all(&scratch);
    } else {
        eprintln!("skipping the verify() dump cross-check: no usable z3");
    }

    assert!(
        findings.is_empty(),
        "\n{} script parity finding(s):\n\n{}",
        findings.len(),
        findings.join("\n\n")
    );
}
