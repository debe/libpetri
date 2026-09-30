//! The ν mint declaration ([NU-010]) and the carrier declaration ([NU-051]) at every entry
//! point: a mint name that is not a transition of the net is rejected by `verify`,
//! `encode_scripts` and `verify_open_net` alike; a Route B decline caused by an undeclared
//! mint names the transition and the declaration; and the open-net route splits its closed
//! net with the carrier places a `configure_smt` hook declares, as `SmtVerifier` does.

#![cfg(feature = "z3")]

use libpetri_core::action::fork;
use libpetri_core::arc::inhibitor;
use libpetri_core::input::one;
use libpetri_core::match_spec::MatchSpec;
use libpetri_core::name::NameId;
use libpetri_core::output::{and, out_place};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::transition::Transition;
use libpetri_verification::marking_state::MarkingStateBuilder;
use libpetri_verification::open_net::{OpenNetContract, OpenNetOptions, verify_open_net};
use libpetri_verification::property::SmtProperty;
use libpetri_verification::result::Verdict;
use libpetri_verification::smt_verifier::{SmtVerifier, z3_available};

/// `fork: source → branchA, branchB` and `join` joining the two by name into `merged`.
fn fork_join() -> PetriNet {
    let source = Place::<()>::new("source");
    let (a, b, merged) = (Place::<String>::new("branchA"), Place::<String>::new("branchB"), Place::<String>::new("merged"));
    let fork_t = Transition::builder("fork")
        .input(one(&source))
        .output(and(vec![out_place(&a), out_place(&b)]))
        .action(fork())
        .build();
    let key = |s: &String| NameId::new(s.clone());
    let join = Transition::builder("join")
        .input(one(&a))
        .input(one(&b))
        .match_spec(MatchSpec::builder().key(&a, key).key(&b, key).build())
        .output(out_place(&merged))
        .action(fork())
        .build();
    PetriNet::builder("fork-join").transitions([fork_t, join]).build()
}

fn verifier(net: &PetriNet) -> SmtVerifier<'_> {
    SmtVerifier::for_net(net)
        .initial_marking(MarkingStateBuilder::new().tokens("source", 1).build())
        .property(SmtProperty::DeadlockFree)
        .sink_places(["merged".to_string()])
}

const TYPO: &str = "declared mint transition 'frok' not in the net (NU-010)";

#[test]
fn verify_answers_unknown_for_a_mint_name_not_in_the_net() {
    let net = fork_join();
    let result = verifier(&net).mint_transition("frok").verify();
    assert!(matches!(&result.verdict, Verdict::Unknown { reason } if reason == TYPO), "{}", result.report);
}

/// `encode_scripts` used to encode the net as if nothing were declared.
#[test]
#[should_panic(expected = "declared mint transition 'frok' not in the net (NU-010)")]
fn encode_scripts_panics_for_a_mint_name_not_in_the_net() {
    let net = fork_join();
    let _ = verifier(&net).mint_transition("frok").encode_scripts();
}

/// `verify_open_net` used to answer per route: the SMT route's queries said `Unknown`,
/// the graph route never looked. Now it answers `Unknown` with the same reason before
/// either route runs.
#[test]
fn verify_open_net_answers_unknown_for_a_mint_name_not_in_the_net() {
    let net = fork_join();
    let contract = OpenNetContract::builder().initial_tokens("source", 1).rest(["merged"]).build();
    let options = OpenNetOptions::default().with_configure_smt(Box::new(|v| v.mint_transition("frok")));
    let result = verify_open_net(&net, &contract, &options);
    assert!(matches!(&result.verdict, Verdict::Unknown { reason } if reason == TYPO), "{}", result.report);
    assert_eq!(result.class_count, 0, "{}", result.report);
}

/// Route B declines a net whose only obstacle is an undeclared mint, and says which
/// transition to declare with what. Before, the report and the reason were the generic
/// ones.
#[test]
fn a_route_b_decline_for_an_undeclared_mint_points_at_mint_transitions() {
    if !z3_available() {
        eprintln!("skipping: z3 binary not on PATH");
        return;
    }
    let net = fork_join();
    let pointer = "'fork' writes a coloured place without consuming one and is not declared to mint \
                   (NU-010); if the action writes a name minted with fresh_name, declare it with \
                   mint_transitions";
    let result = verifier(&net).verify();
    assert!(result.report.contains(&format!("ν-net Route B declined: {pointer}.")), "{}", result.report);
    let Verdict::Unknown { reason } = &result.verdict else {
        panic!("expected Unknown, got {:?}\n{}", result.verdict, result.report);
    };
    assert!(reason.ends_with(&format!("; {pointer}")), "{reason}");
    // Declared, Route B decides it.
    let declared = verifier(&net).mint_transition("fork").verify();
    assert!(declared.is_proven(), "{}", declared.report);
    assert!(!declared.report.contains("Route B declined"), "{}", declared.report);
}

/// `t: a → and(c, d)` writes the carrier `c`, and `u` tests `d` with an inhibitor, so the
/// split needs `t` and cannot express it ([VER-004]). The open-net route used to split it
/// anyway, blind to the carrier its hook declares; `SmtVerifier` refuses it.
#[test]
fn verify_open_net_splits_with_the_carriers_its_hook_declares() {
    let (a, c, d, q, r) =
        (Place::<()>::new("a"), Place::<String>::new("c"), Place::<()>::new("d"), Place::<()>::new("q"), Place::<()>::new("r"));
    let t = Transition::builder("t").input(one(&a)).output(and(vec![out_place(&c), out_place(&d)])).action(fork()).build();
    let u = Transition::builder("u").input(one(&q)).inhibitor(inhibitor(&d)).output(out_place(&r)).action(fork()).build();
    let net = PetriNet::builder("carrier-split").transitions([t, u]).build();
    let refusal = "it writes the coloured place 'c', whose tokens carry a ν name";

    let direct = SmtVerifier::for_net(&net)
        .initial_marking(MarkingStateBuilder::new().tokens("a", 1).tokens("q", 1).build())
        .property(SmtProperty::place_bound("r", 1))
        .carrier_place("c")
        .verify();
    assert!(matches!(&direct.verdict, Verdict::Unknown { reason } if reason.contains(refusal)), "{}", direct.report);

    let contract = OpenNetContract::builder().initial_tokens("a", 1).initial_tokens("q", 1).rest(["c", "d", "r"]).build();
    let options = OpenNetOptions::default().with_configure_smt(Box::new(|v| v.carrier_place("c")));
    let result = verify_open_net(&net, &contract, &options);
    assert!(matches!(&result.verdict, Verdict::Unknown { reason } if reason.contains(refusal)), "{}", result.report);
}
