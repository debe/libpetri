//! [VER-022] open-net verification against a contract: the port of
//! `typescript/tests/verification/open-net.test.ts`.
//!
//! The subnet under test is a node gadget in the shape n8n-libpetri compiles: one input edge
//! carrying data or empty, one output with two outgoing edges, a shared budget and a halt.
//!
//! ```text
//! X/start: one(X/in) one(_budget) one(X/idle) inhibitor(_halt) → X/running
//! X/run:   one(X/running) → and( xor( and( xor(and(e1/data, e2/data), and(e1/empty, e2/empty)), X/routed ),
//!                                     and(_halt, _budget) ),
//!                                X/idle )
//! X/done:  one(X/routed) → and(_budget, X/done)
//! X/skip:  one(X/in_empty) inhibitor(_halt) → and(e1/empty, e2/empty, X/skipped)
//! ```

use libpetri_core::action::fork;
use libpetri_core::arc::inhibitor;
use libpetri_core::input::one;
use libpetri_core::output::{Out, and, out_place, xor};
use libpetri_core::petri_net::PetriNet;
use libpetri_core::place::Place;
use libpetri_core::timing::{deadline, delayed};
use libpetri_core::transition::Transition;

use crate::marking_state::MarkingStateBuilder;
use crate::property::count_phrase;
use crate::result::Verdict;
use crate::smt_verifier::z3_available;
use crate::state_class_graph::{StateClassGraph, StateClassGraphOptions};
use crate::environment::EnvironmentAnalysisMode;

use super::*;

fn place(name: &str) -> Place<()> {
    Place::new(name)
}

fn ands(places: &[&Place<()>]) -> Out {
    and(places.iter().map(|p| out_place(*p)).collect())
}

struct Gadget {
    in_: Place<()>,
    in_empty: Place<()>,
    idle: Place<()>,
    budget: Place<()>,
    halt: Place<()>,
    running: Place<()>,
    routed: Place<()>,
    done: Place<()>,
    skipped: Place<()>,
    e1_data: Place<()>,
    e1_empty: Place<()>,
    e2_data: Place<()>,
    e2_empty: Place<()>,
    trace: Place<()>,
}

fn p() -> Gadget {
    Gadget {
        in_: place("X/in"),
        in_empty: place("X/in_empty"),
        idle: place("X/idle"),
        budget: place("_budget"),
        halt: place("_halt"),
        running: place("X/running"),
        routed: place("X/routed"),
        done: place("X/done"),
        skipped: place("X/skipped"),
        e1_data: place("e1/data"),
        e1_empty: place("e1/empty"),
        e2_data: place("e2/data"),
        e2_empty: place("e2/empty"),
        trace: place("X/trace"),
    }
}

#[derive(Default, Clone, Copy)]
struct Defects {
    /// The skip writes e1's empty but nothing for e2: an edge with neither data nor empty.
    skip_forgets_e2: bool,
    /// The run's data branch also writes e1's empty.
    run_writes_both: bool,
    /// Done keeps the budget unit.
    no_refund: bool,
    /// The run leaves a token on an internal place nothing consumes.
    leak: bool,
    /// A transition that can fire forever while the node runs.
    spin: bool,
    /// The start is delayed; the untimed claim must not care.
    timed_start: bool,
}

fn gadget(d: Defects) -> PetriNet {
    let p = p();
    let mut start = Transition::builder("X/start")
        .input(one(&p.in_))
        .input(one(&p.budget))
        .input(one(&p.idle))
        .inhibitor(inhibitor(&p.halt))
        .output(out_place(&p.running))
        .action(fork());
    if d.timed_start {
        start = start.timing(delayed(50));
    }
    let data = if d.run_writes_both {
        ands(&[&p.e1_data, &p.e1_empty, &p.e2_data])
    } else {
        ands(&[&p.e1_data, &p.e2_data])
    };
    let routes = xor(vec![data, ands(&[&p.e1_empty, &p.e2_empty])]);
    let success = if d.leak {
        and(vec![routes, out_place(&p.routed), out_place(&p.trace)])
    } else {
        and(vec![routes, out_place(&p.routed)])
    };
    let run = Transition::builder("X/run")
        .input(one(&p.running))
        .output(and(vec![xor(vec![success, ands(&[&p.halt, &p.budget])]), out_place(&p.idle)]))
        .action(fork())
        .build();
    let done = Transition::builder("X/done")
        .input(one(&p.routed))
        .output(if d.no_refund { out_place(&p.done) } else { ands(&[&p.budget, &p.done]) })
        .action(fork())
        .build();
    let skip = Transition::builder("X/skip")
        .input(one(&p.in_empty))
        .inhibitor(inhibitor(&p.halt))
        .output(if d.skip_forgets_e2 {
            ands(&[&p.e1_empty, &p.skipped])
        } else {
            ands(&[&p.e1_empty, &p.e2_empty, &p.skipped])
        })
        .action(fork())
        .build();
    let mut transitions = vec![start.build(), run, done, skip];
    if d.spin {
        transitions.push(
            Transition::builder("X/spin")
                .input(one(&p.running))
                .output(out_place(&p.running))
                .action(fork())
                .build(),
        );
    }
    PetriNet::builder("X").transitions(transitions).build()
}

#[derive(Clone, Copy)]
struct Terms {
    terminal: bool,
    budget: usize,
    termination: bool,
}

impl Default for Terms {
    fn default() -> Self {
        Self { terminal: true, budget: 1, termination: true }
    }
}

/// The node contract as n8n-libpetri states it, for a budget of `budget`.
fn contract(t: Terms) -> OpenNetContract {
    let k = t.budget;
    let mut builder = OpenNetContract::builder()
        .initial_tokens("X/idle", 1)
        .initial_tokens("_budget", k)
        .arrive(1, ["X/in", "X/in_empty"])
        .arrive_at_most(1, ["_halt"])
        .expect("e1", 1, ["e1/data", "e1/empty"])
        .expect("e2", 1, ["e2/data", "e2/empty"])
        .expect("idle", 1, ["X/idle"])
        .expect("budget", k, ["_budget"])
        .expect("history", 1, ["X/done", "X/skipped"]);
    if t.terminal {
        builder = builder.terminal("_halt", ["X/in", "X/in_empty"]);
    }
    if !t.termination {
        builder = builder.require_termination(false);
    }
    builder.build()
}

fn verify(net: &PetriNet, c: &OpenNetContract) -> OpenNetResult {
    verify_open_net(net, c, &OpenNetOptions::default())
}

fn subjects(r: &OpenNetResult) -> Vec<&str> {
    r.violations.iter().map(|v| v.subject.as_str()).collect()
}

fn smt_only() -> OpenNetOptions {
    OpenNetOptions { max_classes: 0, ..Default::default() }
}

fn skip_without_z3(test: &str) -> bool {
    if z3_available() {
        return false;
    }
    eprintln!("skipping {test}: z3 binary not on PATH");
    true
}

// ==================== graph route ====================

#[test]
fn graph_proves_a_well_formed_gadget_halts_included() {
    let r = verify(&gadget(Defects::default()), &contract(Terms::default()));
    assert!(r.verdict.is_proven(), "{}", r.report);
    assert_eq!(r.route, OpenNetRoute::Enumeration);
    assert!(r.graph_complete);
    assert!(r.violations.is_empty());
    assert!(r.report.contains("=== OPEN-NET CONTRACT VERIFICATION (VER-022) ==="));
    assert!(r.report.contains("e1 = exactly 1 across {e1/data, e1/empty}"));
    assert!(r.report.contains("Terminal: when _halt: X/in, X/in_empty"));
    // The enumeration route's proof is the exhausted graph, not a certificate.
    assert!(matches!(r.verdict, Verdict::Proven { inductive_invariant: None, .. }));
}

#[test]
fn graph_proves_it_for_a_budget_of_two_as_well() {
    let r = verify(&gadget(Defects::default()), &contract(Terms { budget: 2, ..Default::default() }));
    assert!(r.verdict.is_proven(), "{}", r.report);
}

#[test]
fn graph_names_the_edge_a_broken_skip_leaves_with_neither_data_nor_empty_with_its_port_trace() {
    let r = verify(&gadget(Defects { skip_forgets_e2: true, ..Default::default() }), &contract(Terms::default()));
    assert!(r.verdict.is_violated(), "{}", r.report);
    assert_eq!(subjects(&r), vec!["e2"]);
    let v = &r.violations[0];
    assert_eq!(v.kind, ContractViolationKind::Clause);
    assert_eq!(v.detail, "exactly 1 across {e2/data, e2/empty} at quiescence, found 0");
    assert!(v.confirmed);
    // Shortest witness: the empty arrives, the halt is declined, the skip fires.
    let mut sorted = v.transitions.clone();
    sorted.sort();
    assert_eq!(sorted, vec!["X/skip", "env:arrive[0]:X/in_empty", "env:decline[1]"]);
    assert_eq!(v.markings.len(), v.transitions.len() + 1);
    let skip = v.port_trace.iter().find(|s| s.transition == "X/skip").unwrap();
    assert_eq!(skip.environment, None);
    let change = |place: &str, delta: i64| PortChange { place: place.to_string(), delta };
    assert_eq!(skip.changes, vec![change("X/in_empty", -1), change("e1/empty", 1), change("X/skipped", 1)]);
    let arrival = v.port_trace.iter().find(|s| s.transition == "env:arrive[0]:X/in_empty").unwrap();
    assert_eq!(arrival.environment, Some(EnvironmentStepKind::Arrival));
    let last = v.markings.last().unwrap();
    assert_eq!(last.count("e2/empty") + last.count("e2/data"), 0);
    assert!(r.report.contains("[e2] clause: exactly 1 across {e2/data, e2/empty} at quiescence, found 0"));
    assert!(r.report.contains("Port trace:"));
}

/// The very net the case above calls broken. Whether writing no output edge is a defect or
/// a designed skip is the contract's to say, not the verifier's: a node that can
/// legitimately skip needs its edge clauses conditional on having run, which is what a
/// terminal on X/skipped states. The upper bounds are not waived, so a double write is still
/// caught.
#[test]
fn graph_a_declared_skip_waives_the_output_edge_a_skipping_node_never_writes_and_keeps_its_upper_bound() {
    let declared = OpenNetContract::builder()
        .initial_tokens("X/idle", 1)
        .initial_tokens("_budget", 1)
        .arrive(1, ["X/in", "X/in_empty"])
        .arrive_at_most(1, ["_halt"])
        .expect("e1", 1, ["e1/data", "e1/empty"])
        .expect("e2", 1, ["e2/data", "e2/empty"])
        .expect("idle", 1, ["X/idle"])
        .expect("budget", 1, ["_budget"])
        .expect("history", 1, ["X/done", "X/skipped"])
        .terminal("_halt", ["X/in", "X/in_empty"])
        .terminal("X/skipped", [] as [&str; 0])
        .build();
    let skip = verify(&gadget(Defects { skip_forgets_e2: true, ..Default::default() }), &declared);
    assert!(skip.verdict.is_proven(), "{}", skip.report);
    // Still a violation when the run writes an edge twice: that breaks an upper bound.
    let both = verify(&gadget(Defects { run_writes_both: true, ..Default::default() }), &declared);
    assert!(both.verdict.is_violated(), "{}", both.report);
    assert_eq!(subjects(&both), vec!["e1"]);
}

#[test]
fn graph_reports_an_edge_that_receives_both_data_and_empty_and_keeps_that_bound_under_a_halt() {
    let r = verify(&gadget(Defects { run_writes_both: true, ..Default::default() }), &contract(Terms::default()));
    assert!(r.verdict.is_violated(), "{}", r.report);
    assert_eq!(subjects(&r), vec!["e1"]);
    assert!(r.violations[0].detail.contains("found 2"));
}

#[test]
fn graph_reports_a_budget_unit_the_gadget_keeps() {
    let r = verify(&gadget(Defects { no_refund: true, ..Default::default() }), &contract(Terms::default()));
    assert_eq!(subjects(&r), vec!["budget"], "{}", r.report);
    assert_eq!(r.violations[0].detail, "exactly 1 across {_budget} at quiescence, found 0");
}

#[test]
fn graph_names_an_internal_place_a_run_leaves_a_token_on() {
    let r = verify(&gadget(Defects { leak: true, ..Default::default() }), &contract(Terms::default()));
    let found: Vec<(ContractViolationKind, &str)> =
        r.violations.iter().map(|v| (v.kind, v.subject.as_str())).collect();
    assert_eq!(found, vec![(ContractViolationKind::Stranded, "X/trace")], "{}", r.report);
}

#[test]
fn graph_reports_a_run_that_never_comes_to_rest_as_a_lasso() {
    let r = verify(&gadget(Defects { spin: true, ..Default::default() }), &contract(Terms::default()));
    let kinds: Vec<ContractViolationKind> = r.violations.iter().map(|v| v.kind).collect();
    assert_eq!(kinds, vec![ContractViolationKind::Termination], "{}", r.report);
    let v = &r.violations[0];
    let start = v.cycle_start.expect("a lasso marks where its cycle starts");
    assert_eq!(v.transitions[start..].to_vec(), vec!["X/spin"]);
    assert_eq!(v.markings[start], *v.markings.last().unwrap());
    assert!(r.report.contains("Firing sequence: env:arrive[0]:X/in, X/start, then repeating X/spin"));
}

#[test]
fn graph_with_termination_waived_the_same_spinning_gadget_meets_its_contract() {
    let r = verify(
        &gadget(Defects { spin: true, ..Default::default() }),
        &contract(Terms { termination: false, ..Default::default() }),
    );
    assert!(r.verdict.is_proven(), "{}", r.report);
}

#[test]
fn graph_makes_the_untimed_claim_a_delayed_start_changes_nothing() {
    let plain = verify(&gadget(Defects::default()), &contract(Terms::default()));
    let timed = verify(&gadget(Defects { timed_start: true, ..Default::default() }), &contract(Terms::default()));
    assert!(timed.verdict.is_proven(), "{}", timed.report);
    assert_eq!(timed.class_count, plain.class_count);
}

#[test]
fn graph_without_a_designed_terminal_a_halt_strands_the_arrival_and_waives_nothing() {
    let r = verify(&gadget(Defects::default()), &contract(Terms { terminal: false, ..Default::default() }));
    assert!(r.verdict.is_violated(), "{}", r.report);
    // Clauses in contract order, then stranded places in code-point order.
    assert_eq!(subjects(&r), vec!["e1", "e2", "history", "X/in", "X/in_empty", "_halt"]);
}

#[test]
fn graph_a_clause_over_places_the_net_never_writes_counts_zero_there_and_the_report_says_so() {
    let c = OpenNetContract::builder()
        .initial_tokens("X/idle", 1)
        .initial_tokens("_budget", 1)
        .arrive(1, ["X/in", "X/in_empty"])
        .expect("e1", 1, ["e1/data", "e1/empty"])
        .expect("e2", 1, ["e2/data", "e2/empty"])
        .expect("e3", 1, ["e3/data", "e3/empty"])
        .expect("idle", 1, ["X/idle"])
        .expect("budget", 1, ["_budget"])
        .expect("history", 1, ["X/done", "X/skipped"])
        .rest(["_halt"])
        .build();
    let r = verify(&gadget(Defects::default()), &c);
    assert!(subjects(&r).contains(&"e3"), "{}", r.report);
    assert!(r.report.contains("Not declared by the net: e3/data, e3/empty"));
}

#[test]
fn graph_delivers_exactly_n_arrivals_and_at_most_n_may_deliver_none() {
    let q = place("q");
    let out = place("out");
    let relay = PetriNet::builder("relay")
        .transition(Transition::builder("t").input(one(&q)).output(out_place(&out)).action(fork()).build())
        .build();
    let exactly = verify(&relay, &OpenNetContract::builder().arrive(2, ["q"]).expect("out", 2, ["out"]).build());
    assert!(exactly.verdict.is_proven(), "{}", exactly.report);

    let at_most = verify(&relay, &OpenNetContract::builder().arrive_at_most(2, ["q"]).expect("out", 2, ["out"]).build());
    assert!(at_most.verdict.is_violated(), "{}", at_most.report);
    assert_eq!(at_most.violations[0].detail, "exactly 2 across {out} at quiescence, found 0");

    let between = verify(
        &relay,
        &OpenNetContract::builder().arrive_at_most(2, ["q"]).expect_between("out", 0, Some(2), ["out"]).build(),
    );
    assert!(between.verdict.is_proven(), "{}", between.report);
}

#[test]
fn graph_a_graph_that_does_not_close_is_unknown_without_the_smt_route_and_says_why() {
    let options = OpenNetOptions { max_classes: 3, smt: false, ..Default::default() };
    let r = verify_open_net(&gadget(Defects::default()), &contract(Terms::default()), &options);
    assert!(!r.graph_complete);
    match &r.verdict {
        Verdict::Unknown { reason } => assert_eq!(
            reason,
            "the state-class graph did not close within 3 classes, and the SMT route is disabled"
        ),
        other => panic!("expected unknown, got {other:?}"),
    }
}

// ==================== the closure and the contract ====================

#[test]
fn closure_closes_the_net_with_ordinary_places_and_transitions() {
    let closed = close_open_net(&gadget(Defects::default()), &contract(Terms::default()));
    assert_eq!(closed.initial_marking.count("env:arrivals[0]"), 1);
    assert_eq!(closed.initial_marking.count("env:optional[1]"), 1);
    assert_eq!(closed.initial_marking.count("X/idle"), 1);
    let names: Vec<&str> = closed.environment.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names, vec!["env:arrive[0]:X/in", "env:arrive[0]:X/in_empty", "env:arrive?[1]:_halt", "env:decline[1]"]);
    assert_eq!(closed.environment_step("env:decline[1]"), Some(&EnvironmentStep::Decline { group: 1 }));
    assert!(closed.undeclared.is_empty());
    assert_eq!(closed.net.places().iter().filter(|p| p.name() == "X/in").count(), 1);
}

#[test]
#[should_panic(expected = "already declares")]
fn closure_refuses_a_net_whose_names_the_closure_would_reuse() {
    let clash = PetriNet::builder("clash")
        .transition(Transition::builder("t").input(one(&place("env:arrivals[0]"))).build())
        .build();
    close_open_net(&clash, &OpenNetContract::builder().arrive(1, ["q"]).build());
}

#[test]
#[should_panic(expected = "max >= 1")]
fn contract_refuses_an_arrival_group_that_delivers_nothing() {
    OpenNetContract::builder().arrive_at_most(0, ["X/in"]);
}

#[test]
#[should_panic(expected = "0 <= min <= max")]
fn contract_refuses_an_arrival_group_whose_max_is_below_its_min() {
    OpenNetContract::builder().arrive_between(2, 1, ["X/in"]);
}

// The reference also refuses `arrive(Infinity, …)`: a bound here is a `usize`, which the type
// already keeps finite.

#[test]
#[should_panic(expected = "names no place")]
fn contract_refuses_an_arrival_group_over_no_place() {
    OpenNetContract::builder().arrive(1, [] as [&str; 0]);
}

#[test]
#[should_panic(expected = "duplicate clause name 'a'")]
fn contract_refuses_a_duplicate_clause_name() {
    OpenNetContract::builder().expect("a", 1, ["X/idle"]).expect("a", 1, ["_budget"]);
}

#[test]
#[should_panic(expected = "0 <= min <= max")]
fn contract_refuses_a_clause_whose_max_is_below_its_min() {
    OpenNetContract::builder().expect_between("a", 2, Some(1), ["X/idle"]);
}

#[test]
#[should_panic(expected = "needs a name")]
fn contract_refuses_a_nameless_clause() {
    OpenNetContract::builder().expect("", 1, ["X/idle"]);
}

#[test]
fn contract_phrases_counts_the_way_the_report_prints_them() {
    assert_eq!(count_phrase(1, Some(1)), "exactly 1");
    assert_eq!(count_phrase(0, Some(1)), "at most 1");
    assert_eq!(count_phrase(2, None), "at least 2");
    assert_eq!(count_phrase(0, None), "any number");
    assert_eq!(count_phrase(1, Some(3)), "between 1 and 3");
}

#[test]
fn contract_lists_the_ports_in_first_mention_order_markers_included() {
    assert_eq!(
        contract(Terms::default()).places(),
        vec!["X/idle", "_budget", "X/in", "X/in_empty", "_halt", "e1/data", "e1/empty", "e2/data", "e2/empty", "X/done", "X/skipped"]
    );
}

// ==================== environment transitions ====================

/// A node that asks its environment and runs again on every answer: N/run either finishes
/// or sends a request; the environment answers at most twice, from a budget of its own, or
/// ends.
fn node() -> PetriNet {
    let inp = place("N/in");
    let running = place("N/running");
    let request = place("N/request");
    let reply = place("N/reply");
    let done = place("N/done");
    PetriNet::builder("N")
        .transition(Transition::builder("N/start").input(one(&inp)).output(out_place(&running)).action(fork()).build())
        .transition(Transition::builder("N/resume").input(one(&reply)).output(out_place(&running)).action(fork()).build())
        .transition(
            Transition::builder("N/run")
                .input(one(&running))
                .output(xor(vec![out_place(&request), out_place(&done)]))
                .action(fork())
                .build(),
        )
        .build()
}

/// No actions: an environment transition never runs, so `passthrough()` is fine even with
/// outputs.
fn node_contract(done_at_least: usize) -> OpenNetContract {
    let again = Transition::builder("env/again")
        .input(one(&place("N/request")))
        .input(one(&place("env/rounds")))
        .output(out_place(&place("N/reply")))
        .build();
    let end = Transition::builder("env/end")
        .input(one(&place("N/request")))
        .output(out_place(&place("env/ended")))
        .build();
    OpenNetContract::builder()
        .initial_tokens("env/rounds", 2)
        .arrive(1, ["N/in"])
        .expect_between("done", done_at_least, Some(1), ["N/done"])
        .environment([again, end])
        .build()
}

#[test]
fn environment_proves_a_node_against_an_environment_that_answers_what_it_sends_and_never_strands_the_environment() {
    let r = verify(&node(), &node_contract(0));
    // env/rounds keeps what the environment did not spend and env/ended keeps the ended
    // exchanges: both are the environment's own places, so neither is stranded.
    assert!(r.verdict.is_proven(), "{}", r.report);
    assert!(r.report.contains("Environment transitions: env/again, env/end"));
}

#[test]
fn environment_marks_the_environment_transitions_in_the_port_trace() {
    let r = verify(&node(), &node_contract(1));
    assert_eq!(subjects(&r), vec!["done"], "{}", r.report);
    let step = r.violations[0].port_trace.iter().find(|s| s.transition == "env/end").unwrap();
    assert_eq!(step.environment, Some(EnvironmentStepKind::Transition));
    let change = |place: &str, delta: i64| PortChange { place: place.to_string(), delta };
    assert_eq!(step.changes, vec![change("N/request", -1), change("env/ended", 1)]);
    assert!(
        r.report.lines().any(|l| {
            let l = l.trim_start();
            l.split_once(". ").is_some_and(|(n, rest)| {
                n.chars().all(|c| c.is_ascii_digit()) && rest == "env/end [environment]  N/request -1, env/ended +1"
            })
        }),
        "{}",
        r.report
    );
}

#[test]
fn environment_keeps_the_environments_own_places_apart_and_out_of_the_undeclared_list() {
    let closed = close_open_net(&node(), &node_contract(0));
    assert_eq!(closed.environment_step("env/again"), Some(&EnvironmentStep::Transition));
    let mut places = closed.environment_places.clone();
    places.sort();
    assert_eq!(places, vec!["env/ended", "env/rounds"]);
    assert!(closed.undeclared.is_empty());
}

#[test]
#[should_panic(expected = "already declares")]
fn environment_refuses_an_environment_transition_named_like_one_of_the_nets() {
    let clash = Transition::builder("N/run").input(one(&place("N/request"))).build();
    close_open_net(&node(), &OpenNetContract::builder().arrive(1, ["N/in"]).environment([clash]).build());
}

#[test]
#[should_panic(expected = "duplicate environment transition 'env/end'")]
fn environment_refuses_an_environment_transition_declared_twice() {
    let end = || Transition::builder("env/end").input(one(&place("N/request"))).build();
    OpenNetContract::builder().environment([end(), end()]);
}

// ==================== report text ====================

/// The report is pinned byte for byte to the TypeScript reference's `renderReport` for the
/// same net and contract: this is its text, markings in `localeCompare` order and the port
/// trace in the contract's first-mention order.
#[test]
fn report_matches_the_reference_for_an_environment_step_in_the_port_trace() {
    let r = verify(&node(), &node_contract(1));
    let expected = "\
=== OPEN-NET CONTRACT VERIFICATION (VER-022) ===

Net: N, closed by 3 environment transitions over 1 arrival groups
Contract:
  Initial marking: {env/rounds:2}
  Arrivals: exactly 1 onto {N/in}
  At quiescence: done = exactly 1 across {N/done}
  Environment transitions: env/again, env/end
  Termination: every run comes to rest

=== State-class graph (untimed, priority-blind) ===
  Classes: 16, closed

=== RESULT ===
VIOLATED: 1 part of the contract broken
  [done] clause: exactly 1 across {N/done} at quiescence, found 0
    Port trace:
      1. env:arrive[0]:N/in [environment arrival]  N/in +1
      2. N/start  N/in -1
      3. N/run  N/request +1
      4. env/end [environment]  N/request -1, env/ended +1
    Firing sequence: env:arrive[0]:N/in, N/start, N/run, env/end
    Quiescent marking: {env/ended:1, env/rounds:2}";
    assert_eq!(r.report, expected);
}

/// A lasso whose stem is an arrival: the port trace marks where the cycle starts, and the
/// firing sequence says what repeats.
#[test]
fn report_matches_the_reference_for_a_lasso() {
    let a = place("a");
    let b = place("b");
    let ping = PetriNet::builder("ping")
        .transition(Transition::builder("t1").input(one(&a)).output(out_place(&b)).action(fork()).build())
        .transition(Transition::builder("t2").input(one(&b)).output(out_place(&a)).action(fork()).build())
        .build();
    let c = OpenNetContract::builder().arrive(1, ["a"]).expect_between("ab", 0, None, ["a", "b"]).build();
    let r = verify(&ping, &c);
    let expected = "\
=== OPEN-NET CONTRACT VERIFICATION (VER-022) ===

Net: ping, closed by 1 environment transitions over 1 arrival groups
Contract:
  Initial marking: {}
  Arrivals: exactly 1 onto {a}
  At quiescence: ab = any number across {a, b}
  Termination: every run comes to rest

=== State-class graph (untimed, priority-blind) ===
  Classes: 3, closed

=== RESULT ===
VIOLATED: 1 part of the contract broken
  [termination] termination: a run can repeat t1 → t2 forever without coming to rest
    Port trace:
      1. env:arrive[0]:a [environment arrival]  a +1
      -- the cycle starts here --
      2. t1  a -1, b +1
      3. t2  a +1, b -1
    Firing sequence: env:arrive[0]:a, then repeating t1, t2
    Marking on the cycle: {a:1}";
    assert_eq!(r.report, expected);
}

/// An excused place no arc touches still joins the closed net, so the SMT encoder resolves
/// it and the stranding query excuses it exactly as the graph does.
#[test]
fn closure_registers_an_arc_less_excused_place_so_both_routes_resolve_it() {
    let c = OpenNetContract::builder()
        .initial_tokens("X/idle", 1)
        .initial_tokens("_budget", 1)
        .arrive(1, ["X/in", "X/in_empty"])
        .arrive_at_most(1, ["_halt"])
        .expect("history", 1, ["X/done", "X/skipped"])
        .terminal("_halt", ["X/in", "X/in_empty", "ghost"])
        .rest(["ghost2"])
        .build();
    let closed = close_open_net(&gadget(Defects::default()), &c);
    assert_eq!(closed.undeclared, vec!["ghost2", "ghost"]);
    assert!(closed.net.places().iter().any(|p| p.name() == "ghost"));
    let r = verify(&gadget(Defects::default()), &c);
    assert!(r.report.contains("Not declared by the net: ghost2, ghost (no arc touches them; a clause there counts zero)"));
}

// ==================== untimed exploration (VER-004, used by VER-022) ====================

#[test]
fn untimed_exploration_reaches_a_marking_the_timing_excludes() {
    let p = place("p");
    let a = place("a");
    let b = place("b");
    let t1 = Transition::builder("t1").input(one(&p)).output(out_place(&a)).timing(deadline(5)).action(fork()).build();
    let t2 = Transition::builder("t2").input(one(&p)).output(out_place(&b)).timing(delayed(10)).action(fork()).build();
    let net = PetriNet::builder("race").transitions([t1, t2]).build();
    let m0 = MarkingStateBuilder::new().tokens("p", 1).build();
    let timed = StateClassGraph::build(&net, &m0, 100);
    let untimed = StateClassGraph::build_with_options(
        &net,
        &m0,
        100,
        &[],
        &EnvironmentAnalysisMode::Ignore,
        StateClassGraphOptions { untimed: true },
    );
    assert!(!timed.classes().iter().any(|sc| sc.marking.count("b") > 0));
    assert!(untimed.classes().iter().any(|sc| sc.marking.count("b") > 0));
}

// ==================== SMT route ====================

#[test]
fn smt_with_termination_waived_proves_the_well_formed_gadget_through_existing_properties() {
    if skip_without_z3("smt_with_termination_waived_proves_the_well_formed_gadget_through_existing_properties") {
        return;
    }
    let r = verify_open_net(
        &gadget(Defects::default()),
        &contract(Terms { termination: false, ..Default::default() }),
        &smt_only(),
    );
    assert!(r.verdict.is_proven(), "{}", r.report);
    assert_eq!(r.route, OpenNetRoute::Smt);
    assert!(r.report.contains("=== SMT route ==="));
    assert!(r.report.contains("State-class graph: skipped"));
}

#[test]
fn smt_decides_termination_by_a_firing_bound_when_the_graph_is_not_built() {
    if skip_without_z3("smt_decides_termination_by_a_firing_bound_when_the_graph_is_not_built") {
        return;
    }
    let r = verify_open_net(&gadget(Defects::default()), &contract(Terms::default()), &smt_only());
    assert!(r.verdict.is_proven(), "{}", r.report);
    assert!(
        r.report.lines().any(|l| {
            l.strip_prefix("  [termination] Firing bound (VER-019): every run has at most ")
                .and_then(|rest| rest.split_once(" firings"))
                .is_some_and(|(n, _)| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()))
        }),
        "{}",
        r.report
    );
}

#[test]
fn smt_leaves_termination_undecided_when_no_firing_bound_exists_and_names_what_repeats() {
    if skip_without_z3("smt_leaves_termination_undecided_when_no_firing_bound_exists_and_names_what_repeats") {
        return;
    }
    let r = verify_open_net(&gadget(Defects { spin: true, ..Default::default() }), &contract(Terms::default()), &smt_only());
    match &r.verdict {
        Verdict::Unknown { reason } => assert!(
            reason.contains("termination: no firing bound: the marking equation lets X/spin repeat"),
            "{}",
            r.report
        ),
        other => panic!("expected unknown, got {other:?}\n{}", r.report),
    }
}

#[test]
fn smt_names_the_broken_edge_on_the_smt_route_too() {
    if skip_without_z3("smt_names_the_broken_edge_on_the_smt_route_too") {
        return;
    }
    let r = verify_open_net(
        &gadget(Defects { skip_forgets_e2: true, ..Default::default() }),
        &contract(Terms { termination: false, ..Default::default() }),
        &smt_only(),
    );
    assert!(r.verdict.is_violated(), "{}", r.report);
    assert_eq!(r.route, OpenNetRoute::Smt);
    assert!(subjects(&r).contains(&"e2"));
}

#[test]
fn smt_decides_a_lower_bound_above_1_through_the_quiescent_count() {
    if skip_without_z3("smt_decides_a_lower_bound_above_1_through_the_quiescent_count") {
        return;
    }
    let r = verify_open_net(&gadget(Defects::default()), &contract(Terms { budget: 2, ..Default::default() }), &smt_only());
    assert!(r.verdict.is_proven(), "{}", r.report);
    assert!(r.report.contains(
        "[budget] Quiescent count: exactly 2 across {_budget}; lower bound waived while {_halt} is marked: proven"
    ));
}

#[test]
fn smt_carries_the_certificates_its_proven_queries_returned_labelled_by_contract_part() {
    if skip_without_z3("smt_carries_the_certificates_its_proven_queries_returned_labelled_by_contract_part") {
        return;
    }
    let r = verify_open_net(
        &gadget(Defects::default()),
        &contract(Terms { termination: false, ..Default::default() }),
        &smt_only(),
    );
    // The proof evidence is the conjunction of the parts' invariants, not nothing.
    match &r.verdict {
        Verdict::Proven { inductive_invariant: Some(invariant), .. } => {
            assert!(invariant.contains("[stranding]"), "{invariant}")
        }
        other => panic!("expected a proof with a certificate, got {other:?}\n{}", r.report),
    }
}

#[test]
fn smt_skips_a_count_clause_no_marking_can_fail_and_says_so_rather_than_going_silent() {
    if skip_without_z3("smt_skips_a_count_clause_no_marking_can_fail_and_says_so_rather_than_going_silent") {
        return;
    }
    let anything = OpenNetContract::builder()
        .initial_tokens("X/idle", 1)
        .initial_tokens("_budget", 1)
        .arrive(1, ["X/in", "X/in_empty"])
        .arrive_at_most(1, ["_halt"])
        .expect("e1", 1, ["e1/data", "e1/empty"])
        .expect("e2", 1, ["e2/data", "e2/empty"])
        .expect("idle", 1, ["X/idle"])
        .expect("budget", 1, ["_budget"])
        // Between 0 and ∞ across the history places: every marking satisfies it.
        .expect_between("history", 0, None, ["X/done", "X/skipped"])
        .terminal("_halt", ["X/in", "X/in_empty"])
        .require_termination(false)
        .build();
    let r = verify_open_net(&gadget(Defects::default()), &anything, &smt_only());
    assert!(r.verdict.is_proven(), "{}", r.report);
    assert!(r.report.contains("[history] any number across {X/done, X/skipped} at quiescence: proven (no query needed)"));
}

/// The stranding attribution is the one predicate the two routes compute by different
/// means, and getting it wrong is how a per-place row reports a stranding the complete graph
/// proves cannot happen: it has to ask "marked AND unexcused", not "marked". The graph route
/// reaches the same verdict on this gadget above, so the two are diffable.
#[test]
fn smt_names_the_stranded_place_on_the_smt_route_too_with_the_same_widening_the_graph_applies() {
    if skip_without_z3("smt_names_the_stranded_place_on_the_smt_route_too_with_the_same_widening_the_graph_applies") {
        return;
    }
    let r = verify_open_net(
        &gadget(Defects { leak: true, ..Default::default() }),
        &contract(Terms { termination: false, ..Default::default() }),
        &smt_only(),
    );
    assert!(r.verdict.is_violated(), "{}", r.report);
    assert_eq!(r.route, OpenNetRoute::Smt);
    let found: Vec<(ContractViolationKind, &str)> =
        r.violations.iter().map(|v| (v.kind, v.subject.as_str())).collect();
    assert_eq!(found, vec![(ContractViolationKind::Stranded, "X/trace")], "{}", r.report);
    // Nothing excused by the terminal is named: _halt's excused arrivals may rest.
    assert!(r.violations[0].detail.contains("X/trace holds a token at quiescence"));
}

#[test]
fn smt_reports_the_count_a_broken_gadget_leaves_found_by_the_solver() {
    if skip_without_z3("smt_reports_the_count_a_broken_gadget_leaves_found_by_the_solver") {
        return;
    }
    let r = verify_open_net(
        &gadget(Defects { no_refund: true, ..Default::default() }),
        &contract(Terms { termination: false, ..Default::default() }),
        &smt_only(),
    );
    assert!(r.verdict.is_violated(), "{}", r.report);
    let budget = r.violations.iter().find(|v| v.subject == "budget").unwrap();
    assert!(budget.detail.starts_with("exactly 1 across {_budget} at quiescence"), "{}", budget.detail);
}
