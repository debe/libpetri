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

/// `build_plan` solves the colour-slot program only after every structural refusal, and
/// writes its report line right after the re-check. With `copy: extra → branchA` writing a
/// coloured place as an undeclared mint, the classification refuses the plan, so the
/// simplex never runs and the line never appears. Without `copy` the plan is built and the
/// line is there, which is what makes its absence mean something. Neither run enumerates a
/// semiflow: the slot bound is not a semiflow search.
#[test]
fn an_undeclared_mint_refuses_the_coloured_plan_before_the_slot_bound_is_solved() {
    if !z3_available() {
        eprintln!("skipping: z3 binary not on PATH");
        return;
    }
    const SLOT_BOUND: &str = "Colour-slot bound: ";
    let run = |net: &PetriNet| {
        SmtVerifier::for_net(net)
            .initial_marking(MarkingStateBuilder::new().tokens("source", 1).tokens("extra", 1).build())
            .property(SmtProperty::place_bound("merged", 5))
            .budget_place("source")
            .linear_bound(false)
            .enumeration_max_classes(0)
            .verify()
    };

    let declared = run(&fork_join());
    assert!(declared.report.contains("ν-encoding: name-coloured (colour-slot bound k=2;"), "{}", declared.report);
    // `source` weighs at least both keys: optimum 2 over source, branchA and branchB, and
    // the fork, the one row producing into them.
    assert!(
        declared.report.contains(
            "  Colour-slot bound: LP optimum 2 over 3 places and 1 transitions, so k=2 (re-checked in exact arithmetic)\n"
        ),
        "{}",
        declared.report
    );
    assert_eq!(declared.report.matches(SLOT_BOUND).count(), 1, "{}", declared.report);

    let (extra, a) = (Place::<()>::new("extra"), Place::<String>::new("branchA"));
    let copy = Transition::builder("copy").input(one(&extra)).output(out_place(&a)).action(fork()).build();
    let base = fork_join();
    let net = PetriNet::builder("fork-join-copy")
        .transitions(base.transitions().iter().cloned().chain([copy]))
        .build();
    let undeclared = run(&net);
    assert!(!undeclared.report.contains("ν-encoding: name-coloured"), "{}", undeclared.report);
    assert!(!undeclared.report.contains(SLOT_BOUND), "{}", undeclared.report);
    for report in [&declared.report, &undeclared.report] {
        assert!(!report.contains("semiflow"), "{report}");
    }
}

/// `t: p0 → p1` with `p0` an environment place under `ArrivalsBetween(1, 1)`, and `u: q → r`
/// inhibited by `p1`, so the closure adds `env:arrive[0]:p0` and the in-flight split
/// ([VER-004]) adds `complete:t`.
fn rewritten_by_verify() -> PetriNet {
    let (p0, p1, q, r) = (Place::<()>::new("p0"), Place::<()>::new("p1"), Place::<()>::new("q"), Place::<()>::new("r"));
    let t = Transition::builder("t").input(one(&p0)).output(out_place(&p1)).action(fork()).build();
    let u = Transition::builder("u").input(one(&q)).inhibitor(inhibitor(&p1)).output(out_place(&r)).action(fork()).build();
    PetriNet::builder("rewritten").transitions([t, u]).build()
}

/// NU-010 AC6: `verify` checks the declaration against the caller's net, as
/// `encode_scripts` does, not against the net its own rewrites built. A transition only
/// the `Arrivals` closure or the in-flight split adds is not in the net.
#[test]
fn nu_010_ac6_mint_naming_a_rewrite_added_transition_is_refused() {
    use libpetri_verification::environment::EnvironmentAnalysisMode;
    use libpetri_verification::result::VerificationRoute;
    let net = rewritten_by_verify();
    for name in ["env:arrive[0]:p0", "complete:t"] {
        let result = SmtVerifier::for_net(&net)
            .initial_marking(MarkingStateBuilder::new().tokens("q", 1).build())
            .property(SmtProperty::place_bound("r", 1))
            .environment_places(["p0".to_string()])
            .environment_mode(EnvironmentAnalysisMode::ArrivalsBetween { min_tokens: 1, max_tokens: 1 })
            .mint_transition(name)
            .verify();
        let expected = format!("declared mint transition '{name}' not in the net (NU-010)");
        assert!(matches!(&result.verdict, Verdict::Unknown { reason } if *reason == expected), "{}", result.report);
        assert_eq!(result.route, VerificationRoute::Unavailable, "{}", result.report);
    }
}

const CARRIER_TYPO: &str = "declared carrier place '7' not in the net (NU-051)";

/// NU-051: a declared carrier that is not a place of the net is refused in either fragment
/// mode and whatever the route, before any route runs. Under BASE nothing used to look; under
/// EXTENDED a bounded quiescence query deferred Route B's refusal to Route A, whose plan
/// skips a carrier it cannot resolve; and a reachability bound with a budget never reached
/// Route B at all.
#[test]
fn nu_051_an_unknown_carrier_is_refused_in_both_modes_on_every_route() {
    use libpetri_verification::name_fragment::FragmentMode;
    use libpetri_verification::result::VerificationRoute;
    let net = fork_join();
    let cases = [
        (FragmentMode::Base, SmtProperty::DeadlockFree),
        (FragmentMode::Extended, SmtProperty::DeadlockFree),
        (FragmentMode::Base, SmtProperty::place_bound("merged", 1)),
        (FragmentMode::Extended, SmtProperty::place_bound("merged", 1)),
    ];
    for (mode, property) in cases {
        let result = verifier(&net)
            .property(property.clone())
            .mint_transition("fork")
            .budget_place("source")
            .fragment_mode(mode)
            .carrier_place("7")
            .verify();
        assert!(
            matches!(&result.verdict, Verdict::Unknown { reason } if reason == CARRIER_TYPO),
            "{mode:?} {property:?}: {:?}\n{}",
            result.verdict,
            result.report
        );
        assert_eq!(result.route, VerificationRoute::Unavailable, "{}", result.report);
    }
}

/// NU-051: `encode_scripts` refuses an unknown carrier as it refuses an unknown mint, with
/// the reason `verify` answers `Unknown` with.
#[test]
#[should_panic(expected = "declared carrier place '7' not in the net (NU-051)")]
fn nu_051_encode_scripts_panics_for_a_carrier_not_in_the_net() {
    let net = fork_join();
    let _ = verifier(&net).mint_transition("fork").carrier_place("7").encode_scripts();
}

/// NU-051: a `configure_smt` hook's unknown carrier is refused before either open-net route
/// runs; the graph route never read the declaration.
#[test]
fn nu_051_verify_open_net_answers_unknown_for_a_carrier_not_in_the_net() {
    let net = fork_join();
    let contract = OpenNetContract::builder().initial_tokens("source", 1).rest(["merged"]).build();
    let options = OpenNetOptions::default()
        .with_configure_smt(Box::new(|v| v.mint_transition("fork").carrier_place("7")));
    let result = verify_open_net(&net, &contract, &options);
    assert!(matches!(&result.verdict, Verdict::Unknown { reason } if reason == CARRIER_TYPO), "{}", result.report);
    assert_eq!(result.class_count, 0, "{}", result.report);
}
