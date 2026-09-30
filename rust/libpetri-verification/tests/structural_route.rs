//! The structural early `Proven` of `verify_net` ([VER-020]) on nets Commoner's theorem
//! does not cover.
//!
//! Lean: `Libpetri/Novel/SiphonSearch.lean`, `empty_net_structural_proven_dead`.

#![cfg(feature = "z3")]

use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_verification::marking_state::MarkingStateBuilder;
use libpetri_verification::property::SmtProperty;
use libpetri_verification::result::VerificationRoute;
use libpetri_verification::smt_verifier::{SmtVerifier, z3_available};

/// A net with no transition is quiescent from the start, so `{a:1}` strands a token:
/// a [VER-002] `DeadlockFree` violation. Commoner's condition holds vacuously on it
/// (the marked place is a siphon and its own marked trap), and before the guard in
/// `structural_check` the verifier returned `Proven { method: "structural" }` once the
/// [VER-017] enumeration was off.
#[test]
fn a_net_without_transitions_is_not_proven_structurally() {
    if !z3_available() {
        eprintln!("skipping a_net_without_transitions_is_not_proven_structurally: z3 binary not on PATH");
        return;
    }
    let a = Place::<i32>::new("a");
    let net = PetriNet::builder("empty").place(a.as_ref()).build();
    let result = SmtVerifier::for_net(&net)
        .enumeration_max_classes(0)
        .initial_marking(MarkingStateBuilder::new().tokens("a", 1).build())
        .property(SmtProperty::DeadlockFree)
        .timeout(30_000)
        .verify();
    assert_ne!(result.route, VerificationRoute::Structural, "{}", result.report);
    assert!(result.is_violated(), "{}", result.report);
}
