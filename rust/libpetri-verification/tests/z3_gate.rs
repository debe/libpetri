//! CI gate for the z3 back-end (the Rust analogue of Java's `Z3NativeGateTest`).
//!
//! Everything that exercises the SMT verifier can vanish without turning a
//! build red, in two independent ways:
//!
//! 1. **The feature.** `smt_verifier`, `smt_encoder`, `certificate_check` and
//!    `name_coloured_encoder` are `#[cfg(feature = "z3")]`, and the crate's
//!    default feature set is EMPTY, so `tests/verdict_parity.rs` and
//!    `tests/stub_z3.rs` — both `#![cfg(feature = "z3")]` over their whole file
//!    — compile to empty binaries under a plain `cargo test -p
//!    libpetri-verification` and report `0 passed` in green.
//! 2. **The binary.** With the feature on but no `z3` on `PATH`, the parity
//!    runner and every z3-gated unit test skip themselves and pass.
//!
//! Either way the verifier ships unverified *because* the checks did not run.
//! This file carries no `cfg` of its own — it cannot be compiled away — and
//! turns both silent skips into a red build wherever `CI` is set. Locally
//! (no `CI` in the environment) it only prints what was skipped, so a
//! developer without z3 can still run the suite.

/// True if the `z3` binary the verification crate shells out to answers on
/// `PATH`. Duplicated from `smt_verifier::z3_available` on purpose: that
/// function lives behind the very feature gate this test exists to police.
fn z3_binary_available() -> bool {
    std::process::Command::new("z3")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

#[test]
fn z3_backed_suites_must_actually_run_in_ci() {
    let feature_on = cfg!(feature = "z3");
    let binary_on = z3_binary_available();

    let mut skipped: Vec<&str> = Vec::new();
    if !feature_on {
        skipped.push(
            "the `z3` feature is OFF, so tests/verdict_parity.rs (shared cross-language \
             fixtures) and tests/stub_z3.rs (solver-reply handling) compiled to EMPTY test \
             binaries, and every #[cfg(feature = \"z3\")] unit test in smt_verifier / \
             certificate_check / name_coloured_encoder was compiled out — run with \
             --all-features",
        );
    }
    if !binary_on {
        skipped.push(
            "the `z3` binary is not on PATH, so the verdict-parity runner, the certificate \
             check and the counterexample replay skipped themselves — install z3",
        );
    }

    if skipped.is_empty() {
        return;
    }
    if std::env::var("CI").is_err() {
        eprintln!("z3-backed verification suites did not run:");
        for reason in &skipped {
            eprintln!("  - {reason}");
        }
        return; // developer machine: skipping is a legitimate local choice
    }
    panic!(
        "the z3-backed verification suites did not run on a CI runner, so the SMT verifier is \
         unverified in this build:\n{}\nFix the runner rather than relaxing this assertion.",
        skipped
            .iter()
            .map(|reason| format!("  - {reason}"))
            .collect::<Vec<_>>()
            .join("\n")
    );
}
