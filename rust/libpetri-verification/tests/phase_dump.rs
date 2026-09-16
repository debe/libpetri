//! `LIBPETRI_SMT_DUMP` under the pre-fixpoint phases ([VER-013], [VER-018] AC6).
//!
//! Every script the state-equation phase and the firing bound send is kept under its
//! own phase name: `state-equation` and `invariant` ([VER-018]), `ranking` and `bmc`
//! ([VER-019]). The environment variable is process-global and the dump counter
//! process-wide, so this file holds exactly ONE `#[test]`: the first verification here
//! is the first dump of the process, and its files are numbered from `001`.

#![cfg(feature = "z3")]

use std::fs;
use std::path::{Path, PathBuf};

use libpetri_core::action::fork;
use libpetri_core::arc::inhibitor;
use libpetri_core::input::{all, one};
use libpetri_core::output::{and, out_place, xor};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::transition::Transition;
use libpetri_verification::marking_state::MarkingStateBuilder;
use libpetri_verification::property::SmtProperty;
use libpetri_verification::result::VerificationResult;
use libpetri_verification::smt_verifier::{SmtVerifier, z3_available};

/// The join of [VER-018]'s test derivation: `mergeSkip` after the data arrived is the
/// one spurious candidate, and one inductive inequality excludes it.
fn join_with_skip() -> PetriNet {
    let p = |name: &str| Place::<i32>::new(name);
    let (start, a_data, a_empty, b_data, b_empty) = (p("start"), p("aData"), p("aEmpty"), p("bData"), p("bEmpty"));
    let (hasdata, ready0, ready1, done, skipped) = (p("hasdata"), p("ready0"), p("ready1"), p("done"), p("skipped"));
    let t = |name: &str| Transition::builder(name).action(fork());
    PetriNet::builder("joinWithSkip")
        .transitions([
            t("route")
                .input(one(&start))
                .output(xor(vec![
                    and(vec![out_place(&a_data), out_place(&b_empty)]),
                    and(vec![out_place(&a_empty), out_place(&b_data)]),
                ]))
                .build(),
            t("armAData")
                .input(one(&a_data))
                .output(and(vec![out_place(&hasdata), out_place(&ready0)]))
                .build(),
            t("armAEmpty").input(one(&a_empty)).output(out_place(&ready0)).build(),
            t("armBData")
                .input(one(&b_data))
                .output(and(vec![out_place(&hasdata), out_place(&ready1)]))
                .build(),
            t("armBEmpty").input(one(&b_empty)).output(out_place(&ready1)).build(),
            t("mergeStart")
                .input(one(&ready0))
                .input(one(&ready1))
                .input(all(&hasdata))
                .output(out_place(&done))
                .build(),
            t("mergeSkip")
                .input(one(&ready0))
                .input(one(&ready1))
                .inhibitor(inhibitor(&hasdata))
                .output(out_place(&skipped))
                .build(),
        ])
        .build()
}

/// The queue-and-bundle net of [VER-019]'s test derivation, `M0 = {budget: 3, src: 1}`:
/// the ranking `budget + s + 2*src` bounds every run by 5 firings.
fn queue_and_bundle() -> PetriNet {
    let p = |name: &str| Place::<i32>::new(name);
    let (budget, q, src, s, out) = (p("budget"), p("q"), p("src"), p("s"), p("out"));
    let t = |name: &str| Transition::builder(name).action(fork());
    PetriNet::builder("queue3")
        .transitions([
            t("produce")
                .input(one(&budget))
                .inhibitor(inhibitor(&s))
                .inhibitor(inhibitor(&out))
                .output(out_place(&q))
                .build(),
            t("signal").input(one(&src)).output(out_place(&s)).build(),
            t("bundle").input(all(&q)).input(one(&s)).output(out_place(&out)).build(),
            t("bundleEmpty")
                .input(one(&s))
                .inhibitor(inhibitor(&q))
                .output(out_place(&out))
                .build(),
        ])
        .build()
}

/// Runs `verify` with the dump directed at `dir` and returns the result and the
/// scripts kept there, in the order they were sent.
fn dumped(dir: &Path, verify: impl FnOnce() -> VerificationResult) -> (VerificationResult, Vec<String>) {
    // SAFETY: this binary runs one test; no other thread reads the environment.
    unsafe { std::env::set_var("LIBPETRI_SMT_DUMP", dir) };
    let result = verify();
    // SAFETY: as above.
    unsafe { std::env::remove_var("LIBPETRI_SMT_DUMP") };
    let mut scripts: Vec<String> = fs::read_dir(dir)
        .map(|entries| {
            entries
                .filter_map(|e| e.ok())
                .map(|e| e.file_name().to_string_lossy().into_owned())
                .filter(|name| name.ends_with(".smt2"))
                .collect()
        })
        .unwrap_or_default();
    scripts.sort();
    (result, scripts)
}

#[test]
fn the_phases_dump_each_query_under_its_own_phase_name() {
    if !z3_available() {
        eprintln!("skipping the_phases_dump_each_query_under_its_own_phase_name: z3 binary not on PATH");
        return;
    }
    let scratch = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../target/phase-dump")
        .join(format!("{}", std::process::id()));

    // The candidate, the inequality excluding it, the unsat, and the certificate check.
    let join = join_with_skip();
    let (result, scripts) = dumped(&scratch.join("join"), || {
        SmtVerifier::for_net(&join)
            .enumeration_max_classes(0)
            .initial_marking(MarkingStateBuilder::new().tokens("start", 1).build())
            .property(SmtProperty::DeadlockFree)
            .sink_places(["done".to_string(), "skipped".to_string()])
            .timeout(30_000)
            .verify()
    });
    assert!(result.is_proven(), "{}", result.report);
    assert_eq!(
        scripts,
        vec![
            "001-state-equation.smt2",
            "002-invariant.smt2",
            "003-state-equation.smt2",
            "004-certificate.smt2"
        ],
        "{}",
        result.report
    );

    // The ranking, then one bounded run at the bound itself (5 < 8).
    let queue = queue_and_bundle();
    let (result, scripts) = dumped(&scratch.join("queue"), || {
        SmtVerifier::for_net(&queue)
            .enumeration_max_classes(0)
            .initial_marking(MarkingStateBuilder::new().tokens("budget", 3).tokens("src", 1).build())
            .property(SmtProperty::DeadlockFree)
            .sink_places(["out".to_string(), "budget".to_string()])
            .state_equation_phase(false)
            .timeout(30_000)
            .verify()
    });
    assert!(result.is_proven(), "{}", result.report);
    assert_eq!(scripts, vec!["005-ranking.smt2", "006-bmc.smt2"], "{}", result.report);

    let _ = fs::remove_dir_all(&scratch);
}
