//! Cross-language verdict-parity fixture runner (C4).
//!
//! Runs every fixture in `spec/verification-fixtures/fixtures.json` — the
//! shared expectations all four language implementations assert against —
//! through the real [`SmtVerifier`] with BOTH independent validation layers
//! on: certificate checking (a `Proven` re-verified as an inductive invariant
//! in a second z3 run) and counterexample replay (a `Violated` re-executed
//! against the abstract semantics). The nets are built with the public core
//! builder API in `tests/common/nets.rs` per each fixture's normative
//! `netDescription`.
//!
//! A verdict disagreeing with a fixture's `expected` is a parity FINDING to
//! investigate and report prominently — never a reason to adjust the fixture.
//! All fixtures run before failing, so one finding does not mask another.

#![cfg(feature = "z3")]

#[path = "common/json.rs"]
mod json;
#[path = "common/nets.rs"]
mod nets;
use json::{Json, parse_json};

use libpetri_verification::property::SmtProperty;
use libpetri_verification::result::Verdict;
use libpetri_verification::smt_verifier::{SmtVerifier, z3_available};

// === Fixture plumbing ===

/// Maps a fixture's `property` object onto [`SmtProperty`]. Note the shared
/// schema's `unreachable` carries a singular `place`.
fn property_of(prop: &Json) -> SmtProperty {
    match prop.str("type") {
        "deadlock-free" => SmtProperty::DeadlockFree,
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

/// The line every implementation prints when the ν name-aware state-class-graph
/// verifier ([NU-050] Route B) — not the SMT / Route A encoders — decided the
/// query. Fixtures marked `"route": "B"` assert it BEFORE their verdict, so a
/// silent fall-back to Route A fails loudly instead of passing vacuously.
const ROUTE_B_MARKER: &str = "ν-net Route B: name-aware state-class graph (NU-050)";

fn verdict_word(verdict: &Verdict) -> &'static str {
    match verdict {
        Verdict::Proven { .. } => "proven",
        Verdict::Violated => "violated",
        Verdict::Unknown { .. } => "unknown",
    }
}

/// Runs every shared fixture and reports ALL disagreements at once.
#[test]
fn verdict_parity_fixtures() {
    if !z3_available() {
        // A skip here used to be a silent green: the whole cross-language
        // fixture contract goes unchecked. `tests/z3_gate.rs` polices this
        // from outside the `z3` cfg; fail loudly here too so the runner that
        // lost its solver names the suite it dropped.
        assert!(
            std::env::var("CI").is_err(),
            "verdict_parity_fixtures cannot run on this CI runner: no `z3` binary on PATH, \
             so the shared cross-language fixture expectations were never checked"
        );
        eprintln!("skipping verdict_parity_fixtures: z3 binary not on PATH");
        return;
    }

    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../spec/verification-fixtures/fixtures.json"
    );
    let raw = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read shared fixtures at {path}: {e}"));
    let doc = parse_json(&raw);
    let fixtures = doc.arr("fixtures");
    assert!(!fixtures.is_empty(), "fixtures.json lists no fixtures");

    let mut findings: Vec<String> = Vec::new();
    for fixture in fixtures {
        let id = fixture.str("id");
        let expected = fixture.str("expected");
        let built = nets::build(fixture.str("net"));
        let property = property_of(fixture.get("property").expect("fixture without property"));

        let mut verifier = SmtVerifier::for_net(&built.net)
            .initial_marking(built.initial.clone())
            .property(property)
            // Both independent validation layers explicitly ON — the point of
            // the parity suite (they are also the defaults).
            .certificate_check(true)
            .counterexample_replay(true)
            .timeout(30_000);
        if !built.env_places.is_empty() {
            verifier = verifier
                .environment_places(built.env_places.iter().cloned())
                .environment_mode(built.env_mode.clone());
        }
        // Optional shared-schema field: expected terminal places, per [VER-002].
        let sinks = fixture.str_arr_opt("sinkPlaces");
        if !sinks.is_empty() {
            verifier = verifier.sink_places(sinks.iter().cloned());
        }
        // Optional shared-schema field: ν budget places ([NU-040]), which put a
        // reachability-safety query on Route A's name-coloured encoding.
        let budgets = fixture.str_arr_opt("budgetPlaces");
        if !budgets.is_empty() {
            verifier = verifier.budget_places(budgets.iter().cloned());
        }
        let result = verifier.verify();

        let got = verdict_word(&result.verdict);
        let route_b = fixture.str_opt("route") == Some("B");
        eprintln!(
            "[parity] {id}: expected={expected} got={got} route={} replay_confirmed={:?} elapsed={}ms",
            fixture.str_opt("route").unwrap_or("A"),
            result.counterexample_confirmed,
            result.elapsed_ms
        );
        // The route marker is checked FIRST: a `route: "B"` fixture that silently
        // fell back to Route A would pin nothing, so name that failure directly
        // rather than letting it surface as a confusing verdict mismatch.
        if route_b && !result.report.contains(ROUTE_B_MARKER) {
            findings.push(format!(
                "ROUTE FINDING [{id}]: fixture declares route \"B\" but the report does not \
                 name the ν name-aware state-class graph — the query fell back to Route A, so \
                 the Route B deadlock predicate was never exercised\n\
                 --- verifier report ---\n{}",
                result.report
            ));
            continue;
        }
        if got != expected {
            findings.push(format!(
                "PARITY FINDING [{id}]: expected '{expected}', got '{got}'\n\
                 --- verifier report ---\n{}",
                result.report
            ));
            continue;
        }
        if let Some(Json::Str(substring)) = fixture.get("expectReportContains") {
            if !result.report.contains(substring.as_str()) {
                findings.push(format!(
                    "PARITY FINDING [{id}]: verdict '{got}' matches but the report is missing \
                     the required substring {substring:?}\n--- verifier report ---\n{}",
                    result.report
                ));
                continue;
            }
        }
        // Rust-side strengthening beyond the shared contract: on every
        // violated fixture, z3 4.13's refutation proof yields ground
        // `Reachable` states and the abstract replay confirms the chain
        // (observed across all five violated shapes: deadlock, mutex, bound,
        // env injection, H1 consume-all). Losing this is a replay/decoder
        // regression, NOT a fixture mismatch — reported separately.
        // Route B is exempt: its counterexample is a path of the name-partition
        // graph, not of the flat abstract semantics, so it reports
        // `counterexample_confirmed = None` by construction.
        if expected == "violated" && !route_b && result.counterexample_confirmed != Some(true) {
            findings.push(format!(
                "REPLAY REGRESSION [{id}]: verdict is Violated as expected, but the \
                 counterexample no longer replays (confirmed=false)\n\
                 --- verifier report ---\n{}",
                result.report
            ));
        }
    }

    assert!(
        findings.is_empty(),
        "\n{} parity finding(s):\n\n{}",
        findings.len(),
        findings.join("\n\n")
    );
}
