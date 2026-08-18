//! End-to-end tests against a STUB `z3` on `PATH` (V5, V6, C4).
//!
//! The verifier shells out to the `z3` binary, so the only way to pin how it
//! reads a solver reply is to control the reply. Each scenario writes a tiny
//! shell script named `z3`, puts its directory first on `PATH`, and runs the
//! real pipeline against it.
//!
//! `PATH` is process-global, so this file holds exactly ONE `#[test]` and runs
//! its scenarios in sequence: cargo gives every integration-test file its own
//! process, and nothing else runs in this one.

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

/// Installs a `z3` shell script whose body is `script` and prepends its
/// directory to `PATH`. Returns the directory so later scenarios can replace
/// the script in place (the `PATH` entry stays valid).
fn install_stub(dir: &Path, script: &str) {
    let path = dir.join("z3");
    let mut file = fs::File::create(&path).expect("write stub z3");
    file.write_all(script.as_bytes()).expect("write stub z3");
    drop(file);
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).expect("chmod stub z3");
    }
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

fn verify(net: &PetriNet, tokens: &[(&str, usize)], property: SmtProperty) -> VerificationResult {
    let mut marking = MarkingStateBuilder::new();
    for (place, count) in tokens {
        marking = marking.tokens(*place, *count);
    }
    SmtVerifier::for_net(net)
        .initial_marking(marking.build())
        .property(property)
        .environment_mode(EnvironmentAnalysisMode::Ignore)
        .timeout(5_000)
        .verify()
}

#[test]
fn stub_z3_scenarios() {
    if cfg!(not(unix)) {
        eprintln!("skipping stub_z3_scenarios: the stub is a POSIX shell script");
        return;
    }
    let dir = scratch_dir();
    // SAFETY: this binary runs one test; no other thread reads the environment.
    unsafe {
        std::env::set_var(
            "PATH",
            format!("{}:{}", dir.display(), std::env::var("PATH").unwrap_or_default()),
        );
    }

    // === V5: a warning line ahead of the verdict must not lose the verdict ===
    //
    // The HORN script asks for both a proof and a model, so one of the two
    // always answers `(error …)`; a build that prints a banner first, or
    // orders those lines differently, used to turn every flat-path verdict
    // into Unknown because the classifier anchored on `starts_with`.
    install_stub(
        &dir,
        r#"#!/bin/sh
cat > /dev/null
echo 'WARNING: solver configured with a non-default strategy'
echo 'unsat'
echo '(error "model is not available")'
echo '(proof (asserted (Reachable 1 0)) (asserted (Reachable 0 1)))'
"#,
    );
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

    // === C4: a genuine no-chain replay is the one downgrade ===
    //
    // Same stub answer on a net whose only transition is frozen by an
    // inhibitor: the abstract successor space is {M0} and holds no violating
    // state, so the counterexample is spurious and VIOLATED is withheld.
    install_stub(
        &dir,
        r#"#!/bin/sh
cat > /dev/null
echo 'unsat'
echo '(proof (asserted (Reachable 1 1 0)))'
"#,
    );
    let result = verify(
        &frozen_net(),
        &[("p0", 1), ("blocker", 1)],
        SmtProperty::unreachable(vec!["p1".into()]),
    );
    match &result.verdict {
        Verdict::Unknown { reason } => assert_eq!(
            reason,
            "counterexample replay found no firing chain to the violation under the abstract \
             semantics, so VIOLATED is withheld",
            "the C2 reason, verbatim"
        ),
        other => panic!("expected the no-chain downgrade, got {other:?}\n{}", result.report),
    }
    assert_eq!(result.counterexample_confirmed, Some(false));

    // === V6: an (error …) on STDERR must never leave a Proven standing ===
    //
    // The stub answers `sat` with a plausible certificate on the HORN run,
    // then answers the certificate check with three clean `unsat` lines on
    // stdout while routing the error that dropped an assert to stderr. Taking
    // stdout at face value would retain PROVEN on a vacuous check.
    install_stub(
        &dir,
        r#"#!/bin/sh
script=$(cat)
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
    );
    let result = verify(&chain_net(), &[("p0", 1)], SmtProperty::place_bound("p1", 1));
    match &result.verdict {
        Verdict::Unknown { reason } => assert!(
            reason.starts_with("certificate check could not run:")
                && reason.contains("stderr")
                && reason.ends_with("PROVEN is withheld without an independently validated certificate"),
            "the C2 could-not-run reason: {reason}"
        ),
        other => panic!(
            "an errored certificate check must never retain Proven, got {other:?}\n{}",
            result.report
        ),
    }
    assert!(
        result.report.contains("  Certificate check: FAILED"),
        "{}",
        result.report
    );

    // === V6 (exit status): a non-zero exit with unparseable answers ===
    install_stub(
        &dir,
        r#"#!/bin/sh
script=$(cat)
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
    );
    let result = verify(&chain_net(), &[("p0", 1)], SmtProperty::place_bound("p1", 1));
    assert!(
        matches!(result.verdict, Verdict::Unknown { .. }),
        "a truncated certificate run must not certify, got {:?}\n{}",
        result.verdict,
        result.report
    );

    // === V5 (no verdict at all): an (error …) reply is Unknown, not a panic ===
    install_stub(
        &dir,
        r#"#!/bin/sh
cat > /dev/null
echo '(error "line 1: invalid command")'
"#,
    );
    let result = verify(&chain_net(), &[("p0", 1)], SmtProperty::place_bound("p1", 1));
    match &result.verdict {
        Verdict::Unknown { reason } => assert!(reason.contains("Z3 error"), "{reason}"),
        other => panic!("expected Unknown, got {other:?}\n{}", result.report),
    }

    let _ = fs::remove_dir_all(&dir);
}
