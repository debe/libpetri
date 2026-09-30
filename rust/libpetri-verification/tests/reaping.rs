//! Deadline reaping in the verifier's quiescence ([VER-002], [VER-004], [TIME-013]).
//!
//! A `deadline` / `window` transition a late executor reaps keeps its input tokens and is
//! not re-enabled until one of its input places changes, so the executor can rest at a
//! marking the untimed net still enables. Lean: `Libpetri/Novel/ReapingVsUntimed.lean`,
//! `reaping_refutes_ver004_ac3`, whose witness is the first net below.

#![cfg(feature = "z3")]

use libpetri_core::action::fork;
use libpetri_core::input::one;
use libpetri_core::output::out_place;
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::timing::{Timing, immediate, window};
use libpetri_core::transition::Transition;
use libpetri_verification::marking_state::{MarkingState, MarkingStateBuilder};
use libpetri_verification::property::SmtProperty;
use libpetri_verification::result::{CounterexampleTiming, VerificationResult, VerificationRoute};
use libpetri_verification::smt_verifier::{SmtVerifier, z3_available};

fn arc(name: &str, from: &Place<()>, to: &Place<()>, timing: Timing) -> Transition {
    Transition::builder(name)
        .input(one(from))
        .output(out_place(to))
        .timing(timing)
        .action(fork())
        .build()
}

/// `p0 —t→ p1`, `t = window(3, 5)`: the Lean witness.
fn witness() -> PetriNet {
    let p0 = Place::<()>::new("p0");
    let p1 = Place::<()>::new("p1");
    PetriNet::builder("reaping-witness").transition(arc("t", &p0, &p1, window(3, 5))).build()
}

fn p0() -> MarkingState {
    MarkingStateBuilder::new().tokens("p0", 1).build()
}

fn verify(net: &PetriNet, property: SmtProperty, no_reaping: bool) -> VerificationResult {
    SmtVerifier::for_net(net)
        .initial_marking(p0())
        .property(property)
        .sink_places(["p1".to_string()])
        .assume_no_reaping(no_reaping)
        .timeout(30_000)
        .verify()
}

macro_rules! require_z3 {
    ($name:literal) => {
        if !z3_available() {
            eprintln!(concat!("skipping ", $name, ": z3 binary not on PATH"));
            return;
        }
    };
}

/// The executor reaps `t` and rests at `{p0}`, stranding the token: `DeadlockFree` is
/// violated by the initial marking itself, a trace of no firings.
#[test]
fn the_witness_rests_at_its_initial_marking() {
    require_z3!("the_witness_rests_at_its_initial_marking");
    let result = verify(&witness(), SmtProperty::DeadlockFree, false);
    assert!(result.is_violated(), "{}", result.report);
    assert!(result.counterexample_transitions.is_empty(), "{:?}\n{}", result.counterexample_transitions, result.report);
    assert_eq!(result.counterexample_trace.first(), Some(&p0()), "{}", result.report);
    assert!(result.report.contains("Reaping (TIME-013): t can be reaped"), "{}", result.report);
}

/// The same on the fixpoint query alone, with the state-equation and firing-bound phases
/// off: the CHC `Bad` reads reap-quiescence too, and the initial-marking violation comes
/// back as the empty trace ([VER-003] AC8).
#[test]
fn the_fixpoint_query_alone_finds_the_reaped_rest() {
    require_z3!("the_fixpoint_query_alone_finds_the_reaped_rest");
    let run = |no_reaping: bool| {
        SmtVerifier::for_net(&witness())
            .initial_marking(p0())
            .property(SmtProperty::DeadlockFree)
            .sink_places(["p1".to_string()])
            .state_equation_phase(false)
            .firing_bound(false)
            .assume_no_reaping(no_reaping)
            .timeout(30_000)
            .verify()
    };
    let result = run(false);
    assert!(result.is_violated(), "{}", result.report);
    assert_eq!(result.route, VerificationRoute::Smt, "{}", result.report);
    assert!(result.counterexample_transitions.is_empty(), "{}", result.report);
    assert_eq!(result.counterexample_trace.first(), Some(&p0()), "{}", result.report);
    assert!(run(true).is_proven());
}

/// Under `assume_no_reaping` the strict reading returns: `t` always fires, so the run
/// rests at `{p1}`, a sink. The report names the assumption.
#[test]
fn assume_no_reaping_restores_the_strict_verdict() {
    require_z3!("assume_no_reaping_restores_the_strict_verdict");
    let result = verify(&witness(), SmtProperty::DeadlockFree, true);
    assert!(result.is_proven(), "{}", result.report);
    assert!(
        result.report.contains("ASSUMPTION: no transition is reaped (the assume-no-reaping option)"),
        "{}",
        result.report
    );
}

/// `TerminatesAtSink` reads the same resting marking: `{p0}` marks no sink.
#[test]
fn terminates_at_sink_sees_the_reaped_rest_too() {
    require_z3!("terminates_at_sink_sees_the_reaped_rest_too");
    let result = verify(&witness(), SmtProperty::TerminatesAtSink, false);
    assert!(result.is_violated(), "{}", result.report);
    assert!(result.counterexample_transitions.is_empty(), "{}", result.report);
    assert!(verify(&witness(), SmtProperty::TerminatesAtSink, true).is_proven());
}

/// A reapable transition shadowed by an immediate one on the same input: wherever `t` is
/// enabled, `u` is too, and `u` cannot be reaped, so the executor never rests at `{p0}`.
#[test]
fn a_shadowed_reapable_transition_changes_nothing() {
    require_z3!("a_shadowed_reapable_transition_changes_nothing");
    let p0 = Place::<()>::new("p0");
    let p1 = Place::<()>::new("p1");
    let net = PetriNet::builder("shadowed")
        .transition(arc("t", &p0, &p1, window(3, 5)))
        .transition(arc("u", &p0, &p1, immediate()))
        .build();
    let result = verify(&net, SmtProperty::DeadlockFree, false);
    assert!(result.is_proven(), "{}", result.report);
}

/// The structural route proves only that no marking is dead; `t: a → a` with a window is
/// never dead, but a late executor reaps it and rests on `{a}`. The route must not answer.
/// (`FOLLOWUPS.md` item 4, Lean `structural_proven_is_untimed_only`.)
#[test]
fn a_reapable_self_loop_is_not_proven_structurally() {
    require_z3!("a_reapable_self_loop_is_not_proven_structurally");
    let a = Place::<()>::new("a");
    let net = PetriNet::builder("self-loop").transition(arc("t", &a, &a, window(3, 5))).build();
    let run = |no_reaping: bool| {
        SmtVerifier::for_net(&net)
            .enumeration_max_classes(0)
            .initial_marking(MarkingStateBuilder::new().tokens("a", 1).build())
            .property(SmtProperty::DeadlockFree)
            .assume_no_reaping(no_reaping)
            .timeout(30_000)
            .verify()
    };
    let reaping = run(false);
    assert_ne!(reaping.route, VerificationRoute::Structural, "{}", reaping.report);
    assert!(reaping.is_violated(), "{}", reaping.report);
    assert!(reaping.counterexample_transitions.is_empty(), "{}", reaping.report);
    // Strictly, `t` is enabled in every reachable marking and nothing ever rests.
    assert!(run(true).is_proven());
}

/// The timed check of [VER-023] reads the timed graph reap-aware, so it confirms the
/// violation rather than calling it spurious under timing.
#[test]
fn the_timed_check_confirms_the_reaped_rest() {
    require_z3!("the_timed_check_confirms_the_reaped_rest");
    let result = SmtVerifier::for_net(&witness())
        .initial_marking(p0())
        .property(SmtProperty::DeadlockFree)
        .sink_places(["p1".to_string()])
        .timed_counterexample_check(true)
        .timeout(30_000)
        .verify();
    assert!(result.is_violated(), "{}", result.report);
    assert_eq!(result.counterexample_timing, Some(CounterexampleTiming::TimedConfirmed), "{}", result.report);
}

/// The marking properties do not read quiescence: their scripts are the same either way.
#[test]
fn marking_property_scripts_do_not_change() {
    let script = |no_reaping: bool| {
        SmtVerifier::for_net(&witness())
            .initial_marking(p0())
            .property(SmtProperty::place_bound("p1", 1))
            .assume_no_reaping(no_reaping)
            .encode_scripts()
            .horn
    };
    assert_eq!(script(false), script(true));
}

/// The quiescence clause of the HORN script leaves the reapable transition out: with
/// `t` the only transition it is empty, and `Bad` is the stranding clause alone.
#[test]
fn the_quiescence_clause_skips_the_reapable_transition() {
    let script = |no_reaping: bool| {
        SmtVerifier::for_net(&witness())
            .initial_marking(p0())
            .property(SmtProperty::DeadlockFree)
            .sink_places(["p1".to_string()])
            .assume_no_reaping(no_reaping)
            .encode_scripts()
            .horn
    };
    let (reaping, strict) = (script(false), script(true));
    assert_ne!(reaping, strict);
    assert!(strict.contains("(< m0 1)"), "{strict}");
    assert!(!reaping.contains("(< m0 1)"), "{reaping}");
}

// ==================== lateness on Route B ([TIME-006], [TIME-013]) ====================

/// `t1: p → a` at `early`, `t2: p → b` at `delayed(10)`, beside a same-mint ν-join
/// (`fork: source → branchA, branchB`, `join` keyed on the name → `merged`) so that the
/// query runs on Route B. On time `t1` always wins the race for `p`; a late executor
/// reaps a `deadline` / `window` `t1`, or fires an `exact` one after `t2`, and marks `b`.
/// Lean: `TimedScg/Retrodict.reaping_escapes_timed_graph`, `TimedScg/Late.late_run_sound`.
fn late_race(early: Timing) -> PetriNet {
    use libpetri_core::match_spec::MatchSpec;
    use libpetri_core::name::NameId;
    use libpetri_core::output::and;
    use libpetri_core::timing::delayed;

    let p = Place::<()>::new("p");
    let a = Place::<()>::new("a");
    let b = Place::<()>::new("b");
    let source = Place::<()>::new("source");
    let branch_a = Place::<String>::new("branchA");
    let branch_b = Place::<String>::new("branchB");
    let merged = Place::<String>::new("merged");
    let fork_t = Transition::builder("fork")
        .input(one(&source))
        .output(and(vec![out_place(&branch_a), out_place(&branch_b)]))
        .action(fork())
        .build();
    let join = Transition::builder("join")
        .input(one(&branch_a))
        .input(one(&branch_b))
        .match_spec(
            MatchSpec::builder()
                .key(&branch_a, |s: &String| NameId::new(s.clone()))
                .key(&branch_b, |s: &String| NameId::new(s.clone()))
                .build(),
        )
        .output(out_place(&merged))
        .action(fork())
        .build();
    PetriNet::builder("late-race")
        .transition(arc("t1", &p, &a, early))
        .transition(arc("t2", &p, &b, delayed(10)))
        .transition(fork_t)
        .transition(join)
        .build()
}

fn verify_late_race(early: Timing, property: SmtProperty, no_reaping: bool) -> VerificationResult {
    SmtVerifier::for_net(&late_race(early))
        .mint_transition("fork")
        .initial_marking(MarkingStateBuilder::new().tokens("p", 1).tokens("source", 1).build())
        .property(property)
        .assume_no_reaping(no_reaping)
        .timeout(30_000)
        .verify()
}

/// Item 1: a marking property on Route B reads the late executor too. The strong-semantics
/// graph proves `b` unreachable; a late executor reaps `t1` and fires `t2`.
#[test]
fn route_b_marking_properties_see_a_reaped_race() {
    use libpetri_core::timing::deadline;
    for early in [deadline(5), window(3, 5)] {
        let late = verify_late_race(early, SmtProperty::unreachable(vec!["b".into()]), false);
        assert_eq!(late.route, VerificationRoute::NuScg, "{}", late.report);
        assert!(late.is_violated(), "{early:?}: a reaped t1 lets t2 mark b\n{}", late.report);
        assert_eq!(late.counterexample_transitions.last().map(String::as_str), Some("t2"), "{}", late.report);
        let on_time = verify_late_race(early, SmtProperty::unreachable(vec!["b".into()]), true);
        assert_eq!(on_time.route, VerificationRoute::NuScg, "{}", on_time.report);
        assert!(on_time.is_proven(), "{early:?}: on time t1 always wins\n{}", on_time.report);
        assert!(on_time.report.contains("ASSUMPTION: no transition is reaped"), "{}", on_time.report);
        assert!(on_time.report.contains("on-time executor"), "{}", on_time.report);
    }
}

/// Item 2: `exact` is enforced softly ([TIME-006]): a late executor fires it late, so
/// Route B lifts its latest bound as well, for every property.
#[test]
fn route_b_lifts_the_latest_bound_of_exact() {
    use libpetri_core::timing::exact;
    let late = verify_late_race(exact(5), SmtProperty::unreachable(vec!["b".into()]), false);
    assert_eq!(late.route, VerificationRoute::NuScg, "{}", late.report);
    assert!(late.is_violated(), "a late exact t1 lets t2 fire first\n{}", late.report);
    assert!(late.report.contains("latest bound of t1 was lifted"), "{}", late.report);
    let on_time = verify_late_race(exact(5), SmtProperty::unreachable(vec!["b".into()]), true);
    assert!(on_time.is_proven(), "{}", on_time.report);
    assert!(on_time.report.contains("on-time executor"), "{}", on_time.report);
}

/// R6: `forkA` and `forkB` mint one name each by 1 ms, so the ν-join never has a binding
/// and the executor never enables it ([NU-020]); the watchdog marks `BAD` at 10 ms. The
/// join's `window(0, 5)` must not bound the watchdog, on time or late.
#[test]
fn route_b_gives_a_name_disabled_join_no_clock() {
    use libpetri_core::match_spec::MatchSpec;
    use libpetri_core::name::NameId;
    use libpetri_core::timing::{deadline, delayed};
    let place = |n: &str| Place::<String>::new(n);
    let key = |s: &String| NameId::new(s.clone());
    let step = |name: &str, from: &str, to: &str, timing: Timing| {
        Transition::builder(name)
            .input(one(&place(from)))
            .output(out_place(&place(to)))
            .timing(timing)
            .action(fork())
            .build()
    };
    let join = Transition::builder("join")
        .input(one(&place("branchA")))
        .input(one(&place("branchB")))
        .match_spec(MatchSpec::builder().key(&place("branchA"), key).key(&place("branchB"), key).build())
        .output(out_place(&place("merged")))
        .timing(window(0, 5))
        .action(fork())
        .build();
    let net = PetriNet::builder("name-disabled-join")
        .transition(step("forkA", "sourceA", "branchA", deadline(1)))
        .transition(step("forkB", "sourceB", "branchB", deadline(1)))
        .transition(join)
        .transition(step("watchdog", "W", "BAD", delayed(10)))
        .build();
    for no_reaping in [true, false] {
        let result = SmtVerifier::for_net(&net)
            .mint_transitions(["forkA".to_string(), "forkB".to_string()])
            .initial_marking(
                MarkingStateBuilder::new().tokens("sourceA", 1).tokens("sourceB", 1).tokens("W", 1).build(),
            )
            .property(SmtProperty::unreachable(vec!["BAD".into()]))
            .assume_no_reaping(no_reaping)
            .timeout(30_000)
            .verify();
        assert_eq!(result.route, VerificationRoute::NuScg, "{}", result.report);
        assert!(result.is_violated(), "no_reaping={no_reaping}: the watchdog fires\n{}", result.report);
    }
}

/// A net timed only with `immediate` and `delayed` has no latest bound to lift: Route B
/// reports and decides it exactly as before, with or without the option.
#[test]
fn route_b_leaves_a_net_without_latest_bounds_alone() {
    use libpetri_core::timing::delayed;
    let run = |no_reaping: bool| verify_late_race(delayed(5), SmtProperty::unreachable(vec!["b".into()]), no_reaping);
    let (late, on_time) = (run(false), run(true));
    assert_eq!(late.route, VerificationRoute::NuScg, "{}", late.report);
    // Neither bound is urgent, so `t2` can win the race on time too.
    assert!(late.is_violated(), "{}", late.report);
    assert!(!late.report.contains("lifted"), "{}", late.report);
    assert!(!late.report.contains("TIME-013"), "{}", late.report);
    let strip = |r: &str| r.lines().filter(|l| !l.starts_with("Elapsed")).collect::<Vec<_>>().join("\n");
    assert_eq!(strip(&late.report), strip(&on_time.report));
}

// ==================== reap-awareness on every quiescence route (item 5) ====================

/// The firing bound of [VER-019] alone: it bounds the witness's runs by one firing, and
/// it must still read the reaped rest at `{p0}`, not prove termination at the sink.
#[test]
fn the_firing_bound_reads_the_reaped_rest() {
    require_z3!("the_firing_bound_reads_the_reaped_rest");
    let run = |no_reaping: bool| {
        SmtVerifier::for_net(&witness())
            .initial_marking(p0())
            .property(SmtProperty::DeadlockFree)
            .sink_places(["p1".to_string()])
            .state_equation_phase(false)
            .assume_no_reaping(no_reaping)
            .timeout(30_000)
            .verify()
    };
    let reaping = run(false);
    assert!(reaping.is_violated(), "{}", reaping.report);
    assert!(reaping.report.contains("Firing bound (VER-019)"), "{}", reaping.report);
    assert!(reaping.counterexample_transitions.is_empty(), "{}", reaping.report);
    assert!(run(true).is_proven());
}

/// The state-equation phase of [VER-018] alone, the firing bound off.
#[test]
fn the_state_equation_phase_reads_the_reaped_rest() {
    require_z3!("the_state_equation_phase_reads_the_reaped_rest");
    let run = |no_reaping: bool| {
        SmtVerifier::for_net(&witness())
            .initial_marking(p0())
            .property(SmtProperty::DeadlockFree)
            .sink_places(["p1".to_string()])
            .firing_bound(false)
            .assume_no_reaping(no_reaping)
            .timeout(30_000)
            .verify()
    };
    let reaping = run(false);
    assert!(reaping.is_violated(), "{}", reaping.report);
    assert!(reaping.report.contains("State-equation phase (VER-018)"), "{}", reaping.report);
    assert!(run(true).is_proven());
}

/// Route A ([NU-053]): Route B is capped at one class so the budgeted quiescence query
/// falls through to the coloured encoder. `fork` mints a name from the budget; the
/// `window(50, 200)` join is reaped by a late executor, stranding both branches.
#[test]
fn route_a_reads_a_reaped_join_as_resting() {
    require_z3!("route_a_reads_a_reaped_join_as_resting");
    use libpetri_core::match_spec::MatchSpec;
    use libpetri_core::name::NameId;
    use libpetri_core::output::and;

    let source = Place::<()>::new("source");
    let budget = Place::<()>::new("budget");
    let branch_a = Place::<String>::new("branchA");
    let branch_b = Place::<String>::new("branchB");
    let merged = Place::<String>::new("merged");
    let fork_t = Transition::builder("fork")
        .input(one(&source))
        .input(one(&budget))
        .output(and(vec![out_place(&branch_a), out_place(&branch_b)]))
        .action(fork())
        .build();
    let join = Transition::builder("join")
        .input(one(&branch_a))
        .input(one(&branch_b))
        .match_spec(
            MatchSpec::builder()
                .key(&branch_a, |s: &String| NameId::new(s.clone()))
                .key(&branch_b, |s: &String| NameId::new(s.clone()))
                .build(),
        )
        .output(out_place(&merged))
        .timing(window(50, 200))
        .action(fork())
        .build();
    let net = PetriNet::builder("reaped-join-route-a").transition(fork_t).transition(join).build();
    let run = |no_reaping: bool| {
        SmtVerifier::for_net(&net)
            .enumeration_max_classes(0)
            .initial_marking(MarkingStateBuilder::new().tokens("source", 1).tokens("budget", 1).build())
            .property(SmtProperty::DeadlockFree)
            .sink_places(["merged".to_string()])
            .budget_places(["budget".to_string()])
            .nu_max_classes(1)
            .assume_no_reaping(no_reaping)
            .timeout(30_000)
            .verify()
    };
    let reaping = run(false);
    assert!(reaping.report.contains("ν-encoding: name-coloured"), "Route A must decide:\n{}", reaping.report);
    assert!(reaping.is_violated(), "a reaped join strands both branches:\n{}", reaping.report);
    // Strictly the join always fires; Spacer may not converge on the proof.
    let strict = run(true);
    assert!(!strict.is_violated(), "{}", strict.report);
}

// ==================== the timed check of [VER-023] (item 3) ====================

/// The timed check keeps the strong-semantics graph, so on the race without the ν-join it
/// calls the untimed counterexample spurious. That never turns the verdict, and the report
/// names what the timed claim assumes. Lean: `TimedScg/Retrodict.reaping_escapes_timed_graph`.
#[test]
fn the_timed_check_never_turns_a_violation_and_names_its_assumptions() {
    require_z3!("the_timed_check_never_turns_a_violation_and_names_its_assumptions");
    use libpetri_core::timing::delayed;
    let p = Place::<()>::new("p");
    let a = Place::<()>::new("a");
    let b = Place::<()>::new("b");
    let net = PetriNet::builder("race")
        .transition(arc("t1", &p, &a, window(3, 5)))
        .transition(arc("t2", &p, &b, delayed(10)))
        .build();
    let result = SmtVerifier::for_net(&net)
        .initial_marking(MarkingStateBuilder::new().tokens("p", 1).build())
        .property(SmtProperty::unreachable(vec!["b".into()]))
        .timed_counterexample_check(true)
        .timeout(30_000)
        .verify();
    assert!(result.is_violated(), "{}", result.report);
    assert_eq!(result.counterexample_timing, Some(CounterexampleTiming::SpuriousUnderTiming), "{}", result.report);
    assert!(result.report.contains("assumes an on-time executor"), "{}", result.report);
    assert!(result.report.contains("atomic"), "{}", result.report);
}
