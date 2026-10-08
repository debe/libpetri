//! [VER-024]: stubborn-set reduction of the enumeration route.
//!
//! `fork: start → s0_0 … s(k-1)_0`, then per subnet `i` a cycle (or, with `chain`, a
//! chain ending in `s(i)_n`) `s(i)_j → s(i)_(j+1)`.

#![cfg(feature = "z3")]

use libpetri_core::action::fork;
use libpetri_core::arc::reset;
use libpetri_core::input::one;
use libpetri_core::output::{and_places, out_place};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::transition::Transition;
use libpetri_verification::marking_state::{MarkingState, MarkingStateBuilder};
use libpetri_verification::property::SmtProperty;
use libpetri_verification::result::{VerificationResult, VerificationRoute};
use libpetri_verification::smt_verifier::SmtVerifier;

fn s(i: usize, j: usize) -> Place<()> {
    Place::new(format!("s{i}_{j}"))
}

fn forked(k: usize, n: usize, chain: bool) -> (PetriNet, MarkingState, Vec<String>) {
    let firsts: Vec<Place<()>> = (0..k).map(|i| s(i, 0)).collect();
    let firsts: Vec<_> = firsts.iter().map(|p| p.as_ref()).collect();
    let firsts: Vec<_> = firsts.iter().collect();
    let mut builder = PetriNet::builder(format!("fork-{k}x{n}")).transition(
        Transition::builder("fork")
            .input(one(&Place::<()>::new("start")))
            .output(and_places(&firsts))
            .action(fork())
            .build(),
    );
    for i in 0..k {
        for j in 0..n {
            let to = if chain { s(i, j + 1) } else { s(i, (j + 1) % n) };
            builder = builder.transition(
                Transition::builder(format!("t{i}_{j}"))
                    .input(one(&s(i, j)))
                    .output(out_place(&to))
                    .action(fork())
                    .build(),
            );
        }
    }
    let ends = (0..k).map(|i| format!("s{i}_{n}")).collect();
    (builder.build(), MarkingStateBuilder::new().tokens("start", 1).build(), ends)
}

fn classes(result: &VerificationResult) -> usize {
    let line = result
        .report
        .lines()
        .find_map(|l| l.strip_prefix("State classes: "))
        .unwrap_or_else(|| panic!("no class count\n{}", result.report));
    line.trim().parse().unwrap()
}

/// AC2: k independent cycles close in `1 + n` classes instead of `1 + n^k`.
#[test]
fn closes_independent_cycles_in_one_plus_n_classes() {
    let (net, m0, _) = forked(3, 4, false);
    let verify = |reduce: bool| {
        SmtVerifier::for_net(&net)
            .initial_marking(m0.clone())
            .property(SmtProperty::DeadlockFree)
            .partial_order_reduction(reduce)
            .verify()
    };
    let reduced = verify(true);
    let full = verify(false);
    assert!(reduced.is_proven(), "{}", reduced.report);
    assert!(full.is_proven(), "{}", full.report);
    assert_eq!(reduced.route, VerificationRoute::Enumeration, "{}", reduced.report);
    assert_eq!(classes(&reduced), 1 + 4);
    assert_eq!(classes(&full), 1 + 4usize.pow(3));
    assert!(reduced.report.contains("Stubborn-set reduction (VER-024): on\n"), "{}", reduced.report);
    assert!(!full.report.contains("Stubborn-set reduction"), "{}", full.report);
}

/// AC1: every dead marking is kept: a chain end is a violation, proven once the
/// ends are sinks.
#[test]
fn keeps_every_dead_marking() {
    let (net, m0, ends) = forked(3, 3, true);
    let violated = SmtVerifier::for_net(&net)
        .initial_marking(m0.clone())
        .property(SmtProperty::DeadlockFree)
        .verify();
    assert!(violated.is_violated(), "{}", violated.report);
    assert_eq!(violated.counterexample_transitions.len(), 1 + 3 * 3, "{}", violated.report);
    assert_eq!(violated.counterexample_confirmed, Some(true));
    assert_eq!(classes(&violated), 2 + 3 * 3);
    let proven = SmtVerifier::for_net(&net)
        .initial_marking(m0)
        .property(SmtProperty::DeadlockFree)
        .sink_places(ends)
        .verify();
    assert!(proven.is_proven(), "{}", proven.report);
}

/// `a_produce` deposits into `r`, `b_reset` empties it. Firing `b_reset` last leaves
/// `r` empty, firing it first strands the token `a_produce` deposits later: only
/// that order violates, so the two must be dependent.
#[test]
fn a_reset_and_a_deposit_on_one_place_are_dependent() {
    let (x, y, r, done) = (
        Place::<()>::new("x"),
        Place::<()>::new("y"),
        Place::<()>::new("r"),
        Place::<()>::new("done"),
    );
    let net = PetriNet::builder("reset-vs-deposit")
        .transition(Transition::builder("a_produce").input(one(&x)).output(out_place(&r)).action(fork()).build())
        .transition(
            Transition::builder("b_reset")
                .input(one(&y))
                .reset(reset(&r))
                .output(out_place(&done))
                .action(fork())
                .build(),
        )
        .build();
    let m0 = MarkingStateBuilder::new().tokens("x", 1).tokens("y", 1).build();
    for reduce in [true, false] {
        // Atomic firing: the reset would otherwise split `a_produce` in flight ([VER-004]).
        let result = SmtVerifier::for_net(&net)
            .initial_marking(m0.clone())
            .property(SmtProperty::DeadlockFree)
            .sink_places(vec!["done".to_string()])
            .assume_atomic_firing(true)
            .partial_order_reduction(reduce)
            .verify();
        assert!(result.is_violated(), "{}", result.report);
        if reduce {
            assert_eq!(result.counterexample_transitions, ["b_reset", "a_produce"], "{}", result.report);
        }
    }
}

/// AC3: a safety property reads the full graph.
#[test]
fn a_safety_property_reads_the_full_graph() {
    let (net, m0, _) = forked(3, 4, false);
    let result = SmtVerifier::for_net(&net)
        .initial_marking(m0)
        .property(SmtProperty::place_bound("s0_0", 1))
        .linear_bound(false)
        .verify();
    assert!(result.is_proven(), "{}", result.report);
    assert_eq!(result.route, VerificationRoute::Enumeration, "{}", result.report);
    assert_eq!(classes(&result), 1 + 4usize.pow(3));
    assert!(!result.report.contains("Stubborn-set reduction"), "{}", result.report);
}
