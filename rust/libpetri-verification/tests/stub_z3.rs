//! End-to-end tests against a STUB `z3` (V5, V6, C4, and the [VER-013]
//! transport contract).
//!
//! The verifier shells out to a `z3` executable, so the only way to pin how it
//! reads a solver reply is to control the reply. Each scenario writes a tiny
//! shell script named `z3` into its own directory and points `LIBPETRI_Z3` at
//! it; the first scenario leaves the variable unset and reaches the same stub
//! through `PATH` instead. Every stub answers `--version` first, because the
//! transport probes the executable before it runs a script.
//!
//! The environment is process-global, so this file holds exactly ONE `#[test]`
//! and runs its scenarios in sequence: cargo gives every integration-test file
//! its own process, and nothing else runs in this one.

#![cfg(feature = "z3")]

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

use libpetri_core::action::fork;
use libpetri_core::arc::inhibitor;
use libpetri_core::input::one;
use libpetri_core::output::out_place;
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::transition::Transition;
use libpetri_verification::environment::EnvironmentAnalysisMode;
use libpetri_verification::marking_state::MarkingStateBuilder;
use libpetri_verification::property::SmtProperty;
use libpetri_verification::result::{VerificationResult, Verdict};
use libpetri_verification::smt_verifier::SmtVerifier;

/// The `--version` answer every stub gives before it looks at a script.
const VERSION_OK: &str = "Z3 version 4.16.0 - 64 bit";

/// Writes `<root>/<name>/z3`: a POSIX shell script that answers `--version`
/// with `version` and otherwise runs `body`. Returns the script's path.
fn install_stub(root: &Path, name: &str, version: &str, body: &str) -> PathBuf {
    let dir = root.join(name);
    fs::create_dir_all(&dir).expect("create stub dir");
    let path = dir.join("z3");
    let script = format!(
        "#!/bin/sh\nif [ \"$1\" = \"--version\" ]; then echo '{version}'; exit 0; fi\n{body}"
    );
    let mut file = fs::File::create(&path).expect("write stub z3");
    file.write_all(script.as_bytes()).expect("write stub z3");
    drop(file);
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).expect("chmod stub z3");
    }
    path
}

/// Points the transport at `path` for the scenarios that follow.
fn use_stub(path: &Path) {
    // SAFETY: this binary runs one test; no other thread reads the environment.
    unsafe { std::env::set_var("LIBPETRI_Z3", path) };
}

/// A scratch directory under `target/` — no external tempdir dependency.
fn scratch_dir() -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../target/stub-z3")
        .join(format!("{}", std::process::id()));
    fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

/// p0(1) -> p1: a plain chain the stub's answers are applied to.
fn chain_net() -> PetriNet {
    let p0 = Place::<i32>::new("p0");
    let p1 = Place::<i32>::new("p1");
    let t = Transition::builder("t")
        .input(one(&p0))
        .output(out_place(&p1))
        .action(fork())
        .build();
    PetriNet::builder("stub_chain").transition(t).build()
}

/// Nothing ever drains `blocker`, so `t` can never fire: `p1` is unreachable
/// under the abstract semantics no matter what the solver claims.
fn frozen_net() -> PetriNet {
    let p0 = Place::<i32>::new("p0");
    let blocker = Place::<i32>::new("blocker");
    let p1 = Place::<i32>::new("p1");
    let t = Transition::builder("t")
        .input(one(&p0))
        .inhibitor(inhibitor(&blocker))
        .output(out_place(&p1))
        .action(fork())
        .build();
    PetriNet::builder("stub_frozen").transition(t).build()
}

fn verify_with(
    net: &PetriNet,
    tokens: &[(&str, usize)],
    property: SmtProperty,
    timeout_ms: u64,
) -> VerificationResult {
    let mut marking = MarkingStateBuilder::new();
    for (place, count) in tokens {
        marking = marking.tokens(*place, *count);
    }
    SmtVerifier::for_net(net)
        .initial_marking(marking.build())
        .property(property)
        .environment_mode(EnvironmentAnalysisMode::Ignore)
        .timeout(timeout_ms)
        .verify()
}

fn verify(net: &PetriNet, tokens: &[(&str, usize)], property: SmtProperty) -> VerificationResult {
    verify_with(net, tokens, property, 5_000)
}

fn unknown_reason(result: &VerificationResult) -> &str {
    match &result.verdict {
        Verdict::Unknown { reason } => reason,
        other => panic!("expected Unknown, got {other:?}\n{}", result.report),
    }
}

/// The V5 reply: a banner, `unsat`, the benign model error, a two-state proof.
const V5_BODY: &str = r#"cat > /dev/null
echo 'WARNING: solver configured with a non-default strategy'
echo 'unsat'
echo '(error "model is not available")'
echo '(proof (asserted (Reachable 1 0)) (asserted (Reachable 0 1)))'
"#;

#[test]
fn stub_z3_scenarios() {
    if cfg!(not(unix)) {
        eprintln!("skipping stub_z3_scenarios: the stub is a POSIX shell script");
        return;
    }
    let root = scratch_dir();

    // === V5 via PATH: a warning line ahead of the verdict must not lose it ===
    //
    // The HORN script asks for both a proof and a model, so one of the two
    // always answers `(error …)`; a build that prints a banner first, or
    // orders those lines differently, used to turn every flat-path verdict
    // into Unknown because the classifier anchored on `starts_with`. This
    // first scenario also covers the default resolution: `LIBPETRI_Z3` unset,
    // `z3` found on `PATH`.
    let on_path = install_stub(&root, "path", VERSION_OK, V5_BODY);
    // SAFETY: single-threaded test binary, see the module docs.
    unsafe {
        std::env::remove_var("LIBPETRI_Z3");
        std::env::set_var(
            "PATH",
            format!(
                "{}:{}",
                on_path.parent().unwrap().display(),
                std::env::var("PATH").unwrap_or_default()
            ),
        );
    }
    let result = verify(&chain_net(), &[("p0", 1)], SmtProperty::place_bound("p1", 0));
    assert!(
        result.is_violated(),
        "a warning line before `unsat` must not lose the verdict (V5)\n{}",
        result.report
    );
    assert_eq!(
        result.counterexample_confirmed,
        Some(true),
        "the decoded chain replays\n{}",
        result.report
    );
    assert!(
        result.report.contains("  Solver: z3 4.16.0\n"),
        "the report names the probed solver version\n{}",
        result.report
    );

    // === C4: a genuine no-chain replay is the one downgrade ===
    //
    // Same stub answer on a net whose only transition is frozen by an
    // inhibitor: the abstract successor space is {M0} and holds no violating
    // state, so the counterexample is spurious and VIOLATED is withheld.
    use_stub(&install_stub(
        &root,
        "c4",
        VERSION_OK,
        r#"cat > /dev/null
echo 'unsat'
echo '(proof (asserted (Reachable 1 1 0)))'
"#,
    ));
    let result = verify(
        &frozen_net(),
        &[("p0", 1), ("blocker", 1)],
        SmtProperty::unreachable(vec!["p1".into()]),
    );
    assert_eq!(
        unknown_reason(&result),
        "counterexample replay found no firing chain to the violation under the abstract \
         semantics, so VIOLATED is withheld",
        "the C2 reason, verbatim"
    );
    assert_eq!(result.counterexample_confirmed, Some(false));

    // === V6: an (error …) on STDERR must never leave a Proven standing ===
    //
    // The stub answers `sat` with a plausible certificate on the HORN run,
    // then answers the certificate check with three clean `unsat` lines on
    // stdout while routing the error that dropped an assert to stderr. Taking
    // stdout at face value would retain PROVEN on a vacuous check.
    use_stub(&install_stub(
        &root,
        "v6-stderr",
        VERSION_OK,
        r#"script=$(cat)
case "$script" in
  *"set-logic HORN"*)
    echo 'sat'
    echo '(error "proof is not available")'
    echo '(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool (<= x!1 1))'
    ;;
  *)
    echo '(error "line 4: unknown constant Reachable")' >&2
    echo 'unsat'
    echo 'unsat'
    echo 'unsat'
    ;;
esac
"#,
    ));
    let result = verify(&chain_net(), &[("p0", 1)], SmtProperty::place_bound("p1", 1));
    let reason = unknown_reason(&result);
    assert!(
        reason.starts_with("certificate check could not run:")
            && reason.contains("stderr")
            && reason.ends_with("PROVEN is withheld without an independently validated certificate"),
        "the C2 could-not-run reason: {reason}"
    );
    assert!(
        result.report.contains("  Certificate check: FAILED"),
        "{}",
        result.report
    );

    // === V6 (exit status): a non-zero exit with unparseable answers ===
    use_stub(&install_stub(
        &root,
        "v6-exit",
        VERSION_OK,
        r#"script=$(cat)
case "$script" in
  *"set-logic HORN"*)
    echo 'sat'
    echo '(define-fun Reachable ((x!0 Int) (x!1 Int)) Bool (<= x!1 1))'
    ;;
  *)
    echo 'unsat'
    exit 1
    ;;
esac
"#,
    ));
    let result = verify(&chain_net(), &[("p0", 1)], SmtProperty::place_bound("p1", 1));
    assert!(
        matches!(result.verdict, Verdict::Unknown { .. }),
        "a truncated certificate run must not certify, got {:?}\n{}",
        result.verdict,
        result.report
    );

    // === V5 (no verdict at all): an (error …) reply is Unknown, not a panic ===
    use_stub(&install_stub(
        &root,
        "no-verdict",
        VERSION_OK,
        r#"cat > /dev/null
echo '(error "line 1: invalid command")'
"#,
    ));
    let result = verify(&chain_net(), &[("p0", 1)], SmtProperty::place_bound("p1", 1));
    assert_eq!(
        unknown_reason(&result),
        "Z3 error: (error \"line 1: invalid command\")"
    );

    // === VER-013 AC4: the `-T` backstop prints `timeout`, which is not a verdict ===
    //
    // With a 5 s budget the backstop is `-T:6`; the reason names it, and the
    // report's result line carries the same reason.
    use_stub(&install_stub(
        &root,
        "timeout",
        VERSION_OK,
        r#"cat > /dev/null
echo 'timeout'
"#,
    ));
    let result = verify(&chain_net(), &[("p0", 1)], SmtProperty::place_bound("p1", 1));
    assert_eq!(unknown_reason(&result), "z3 hard timeout after 6s");
    assert!(
        result.report.contains("Result: UNKNOWN (z3 hard timeout after 6s)\n"),
        "{}",
        result.report
    );

    // === VER-013 AC4: a solver that ignores both timeouts is killed ===
    //
    // The stub never reads its stdin and never exits; the watchdog at the
    // budget plus twice the grace kills it and the reason says so. No elapsed
    // time is asserted, only the outcome.
    use_stub(&install_stub(&root, "wedged", VERSION_OK, "exec sleep 30\n"));
    let result = verify_with(&chain_net(), &[("p0", 1)], SmtProperty::place_bound("p1", 1), 200);
    assert_eq!(
        unknown_reason(&result),
        "z3 did not exit within 2200 ms and was killed"
    );

    // === VER-013 AC5: a reply far larger than a pipe buffer is drained ===
    //
    // Two megabytes of banner on BOTH streams before the verdict. Without a
    // concurrent drain the solver blocks on a full pipe while the transport
    // waits for it to exit, and nothing ever completes.
    use_stub(&install_stub(
        &root,
        "banner",
        VERSION_OK,
        r#"cat > /dev/null
yes 'WARNING: a very long banner line' | head -c 2000000
yes 'WARNING: a very long banner line' | head -c 2000000 >&2
echo
echo 'unsat'
echo '(proof (asserted (Reachable 1 0)) (asserted (Reachable 0 1)))'
"#,
    ));
    let result = verify(&chain_net(), &[("p0", 1)], SmtProperty::place_bound("p1", 0));
    assert!(
        result.is_violated(),
        "a 2 MB banner on each stream must not stall or hide the verdict\n{}",
        result.report
    );
    assert_eq!(result.counterexample_confirmed, Some(true));

    // === VER-013 AC3: a solver below the version floor is refused ===
    use_stub(&install_stub(
        &root,
        "too-old",
        "Z3 version 4.7.1 - 64 bit",
        V5_BODY,
    ));
    let result = verify(&chain_net(), &[("p0", 1)], SmtProperty::place_bound("p1", 0));
    assert_eq!(
        unknown_reason(&result),
        "z3 4.7.1 is older than the minimum 4.8.0"
    );
    assert!(
        result
            .report
            .contains("  Solver: z3 unavailable (z3 4.7.1 is older than the minimum 4.8.0)\n"),
        "{}",
        result.report
    );

    // === VER-013 AC3: a probe that reports no version is refused ===
    use_stub(&install_stub(&root, "no-version", "not a solver", V5_BODY));
    let result = verify(&chain_net(), &[("p0", 1)], SmtProperty::place_bound("p1", 0));
    assert_eq!(
        unknown_reason(&result),
        "z3 --version did not report a version: not a solver"
    );

    // === VER-013 AC2: a missing executable names the command and the env var ===
    use_stub(Path::new("/nonexistent/libpetri-z3"));
    let result = verify(&chain_net(), &[("p0", 1)], SmtProperty::place_bound("p1", 0));
    assert_eq!(
        unknown_reason(&result),
        "z3 binary not found: /nonexistent/libpetri-z3; install z3 >= 4.8.0 or set LIBPETRI_Z3"
    );
    assert!(
        result.report.contains("  Solver: z3 unavailable (z3 binary not found:"),
        "{}",
        result.report
    );

    // === VER-013: LIBPETRI_SMT_DUMP records every script and reply ===
    let dump = root.join("dump");
    // SAFETY: single-threaded test binary, see the module docs.
    unsafe { std::env::set_var("LIBPETRI_SMT_DUMP", &dump) };
    use_stub(&on_path);
    let result = verify(&chain_net(), &[("p0", 1)], SmtProperty::place_bound("p1", 0));
    assert!(result.is_violated(), "{}", result.report);
    let script = fs::read_to_string(dump.join("001-horn.smt2")).expect("dumped HORN script");
    assert!(
        script.contains("(set-logic HORN)") && script.ends_with("(get-model)"),
        "the dump is the script as sent:\n{script}"
    );
    let reply = fs::read_to_string(dump.join("001-horn.out")).expect("dumped reply");
    assert!(reply.contains("\nunsat\n"), "the dump is the reply as received:\n{reply}");
    assert!(
        !dump.join("001-horn.err").exists(),
        "no .err file when stderr was empty"
    );
    // SAFETY: as above.
    unsafe { std::env::remove_var("LIBPETRI_SMT_DUMP") };

    let _ = fs::remove_dir_all(&root);
}
