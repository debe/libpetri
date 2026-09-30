//! Bounded state-space enumeration ([VER-017]): decide a property by building
//! the state-class graph and reading the verdict off it, when the graph closes
//! within a class budget.
//!
//! IC3/PDR is built for state spaces that are wide and shallow. A workflow net is
//! the opposite — narrow and deep: a forty-node pipeline has under two thousand
//! reachable classes, but its diameter is the length of the pipeline, so the
//! fixpoint engine needs a frame per stage and its cost climbs with the cube of
//! the length. Enumerating the same net is linear in the state space and finishes
//! in milliseconds. Measured on a forty-node chain (370 places): 410 s on the
//! fixpoint path, 0.11 s here.
//!
//! The route is exact when the graph closes — sound *and* complete, so a
//! `Violated` is a real firing sequence rather than a possibly-spurious
//! over-approximation, and a `Proven` is never the `Unknown` a fixpoint search
//! runs out of time for.
//!
//! It applies only to an **untimed** net — every transition `immediate` — and
//! that restriction is what makes the verdict interchangeable with the encoders'.
//! The state-class graph carries firing domains, so on a timed net it would
//! explore only the runs the timing admits and its `Proven` would be the weaker
//! timed claim; [VER-004] is explicit that the untimed proof is the stronger one,
//! and a route must not quietly hand back a weaker claim than the one it
//! replaced. On an untimed net no domain excludes anything, the graph explores
//! exactly the untimed reachable set, and the two routes decide the same
//! predicate over the same abstraction — enumeration simply decides it where the
//! search may not.
//!
//! When the graph does not close within the budget, a violation among the classes
//! it did explore still stands — every explored class is reachable, and the
//! worklist is breadth-first, so the witness is the shortest within the explored
//! graph ([VER-017] "Verdicts from a truncated graph"). Otherwise the route
//! declines and the caller runs the SMT pipeline unchanged: enumeration never
//! turns a verdict into `Unknown` that the solver could have decided, and a
//! truncated graph never proves anything.

use std::collections::{BTreeSet, VecDeque};

use libpetri_core::petri_net::PetriNet;
use libpetri_core::timing::Timing;

use crate::graph_decision::{ClassView, decide_over_classes};
use crate::marking_state::MarkingState;
use crate::property::SmtProperty;
use crate::rest_set::ConditionalSinks;
use crate::result::Verdict;
use crate::state_class_graph::StateClassGraph;

/// Whether every transition is `immediate`, so the state-class graph explores the
/// untimed reachable set exactly and its verdict is the encoders' claim rather
/// than the weaker timed one. See this module's header.
pub fn is_untimed(net: &PetriNet) -> bool {
    net.transitions()
        .iter()
        .all(|t| matches!(t.timing(), Timing::Immediate))
}

/// The note a decided verdict carries into the report.
pub const NOTE_ENUMERATED: &str =
    "Note: decided by bounded state-space enumeration — the state-class graph closed, so the \
verdict is sound AND complete: a `violated` is a real firing sequence, not a possibly-spurious \
over-approximation. The net is untimed, so this is the same claim the encoders make (VER-017).\n";

/// The report note of a violation found in the explored prefix of a graph that
/// did not close ([VER-012], [VER-017], [VER-023]). `graph` names the graph.
pub fn prefix_note(graph: &str, max_classes: usize) -> String {
    format!(
        "Note: the {graph} was truncated at {max_classes} classes; the violation was found in \
         the explored prefix. Every explored class is reachable, so the counterexample is a real \
         firing sequence, the shortest within the explored graph. A truncated graph never proves \
         a property.\n"
    )
}

/// Outcome of the enumeration route.
pub enum ScgOutcome {
    /// The graph decided the property. `truncated` is `true` for a violation found
    /// in the explored prefix of a graph that did not close ([VER-017]): every
    /// explored class is reachable, so the witness is a real firing sequence — the
    /// shortest within the explored graph. A truncated graph is never `Proven`.
    Decided {
        verdict: Verdict,
        trace: Vec<MarkingState>,
        transitions: Vec<String>,
        class_count: usize,
        truncated: bool,
    },
    /// The graph hit the class budget and its explored prefix violates nothing;
    /// the caller falls through to the SMT pipeline.
    Truncated { class_count: usize },
    /// The total verification budget or a cancellation stopped the build
    /// ([VER-013]) after `class_count` classes. Not a truncation: nothing is read
    /// off the graph, not even its prefix.
    Stopped { class_count: usize },
}

/// The graph's classes as the shared predicate reads them ([`decide_over_classes`]).
///
/// A class is quiescent only when it was **expanded** and has no successor: a
/// frontier class of a truncated graph has no successor recorded only because
/// nobody computed them ([VER-017]). On a closed graph every class is expanded.
///
/// With reapable transitions ([`crate::reaping`]) an expanded class also rests when
/// every transition it enables is reapable: a late executor reaps them and stops
/// there ([VER-002] reap-quiescence, [TIME-013]). With none, that is the plain rule.
struct GraphClasses<'g> {
    graph: &'g StateClassGraph,
    reapable: &'g BTreeSet<String>,
}

impl ClassView for GraphClasses<'_> {
    fn count(&self) -> usize {
        self.graph.class_count()
    }
    fn marking_of(&self, i: usize) -> &MarkingState {
        &self.graph.classes()[i].marking
    }
    fn is_quiescent(&self, i: usize) -> bool {
        i < self.graph.expanded_count()
            && (self.graph.successors(i).is_empty()
                || (!self.reapable.is_empty()
                    && self
                        .graph
                        .enabled_transitions(i)
                        .iter()
                        .all(|t| self.reapable.contains(t))))
    }
}

/// Decides `property` by enumeration, or reports truncation.
///
/// `max_classes` is the class budget; `0` disables the route (the caller then
/// never calls this). Builds the graph and hands it to
/// [`decide_over_state_space`].
///
/// This is the graph of `net` as given. It applies neither the in-flight split of
/// [VER-004] ([`crate::in_flight::split_in_flight`]) nor the reap-aware quiescence of
/// [TIME-013] ([`decide_over_state_space_reaping`]), and its note does not say so:
/// every firing is read as one atomic step and a marking rests only when nothing is
/// enabled. `SmtVerifier::verify` applies both before it reaches this route; a direct
/// caller that wants them splits the net first and decides with the reaping variant.
pub fn verify_via_state_class_graph(
    net: &PetriNet,
    initial: &MarkingState,
    property: &SmtProperty,
    sink_places: &[String],
    max_classes: usize,
    conditional_sinks: &[ConditionalSinks],
) -> ScgOutcome {
    let graph = StateClassGraph::build(net, initial, max_classes);
    decide_over_state_space(&graph, initial, property, sink_places, conditional_sinks)
}

/// Reads the verdict off a built graph. Only reads `graph`, so one graph answers
/// any number of properties ([`crate::state_space_cache`]).
///
/// A graph that did not close is decided over its explored prefix
/// ([VER-017] "Verdicts from a truncated graph"): every stored class counts for a
/// safety property, but only an expanded class with no successor counts as
/// quiescent. A hit is a `Violated` with `truncated: true`; no hit is
/// [`ScgOutcome::Truncated`]. A graph the total budget or a cancellation stopped
/// is [`ScgOutcome::Stopped`], and nothing is read off it.
///
/// `initial` is the marking the graph was built from, as the caller listed it: it
/// is the first state of a witness trace. The graph's own initial class holds the
/// same counts, but a cached graph may have been built from a marking listed in
/// another order.
pub fn decide_over_state_space(
    graph: &StateClassGraph,
    initial: &MarkingState,
    property: &SmtProperty,
    sink_places: &[String],
    conditional_sinks: &[ConditionalSinks],
) -> ScgOutcome {
    decide_over_state_space_reaping(
        graph,
        initial,
        property,
        sink_places,
        conditional_sinks,
        &BTreeSet::new(),
    )
}

/// [`decide_over_state_space`] reading quiescence reap-aware ([VER-002], [TIME-013]):
/// an expanded class whose enabled transitions are all in `reapable` rests too. The
/// graph decides only the runs it holds: a timed graph built on the net as written fires
/// every transition on time, and one built on [`crate::reaping::relax_late`]'s net also
/// holds the runs a late executor takes after a reap. An empty `reapable` is
/// [`decide_over_state_space`].
pub fn decide_over_state_space_reaping(
    graph: &StateClassGraph,
    initial: &MarkingState,
    property: &SmtProperty,
    sink_places: &[String],
    conditional_sinks: &[ConditionalSinks],
    reapable: &BTreeSet<String>,
) -> ScgOutcome {
    if graph.is_stopped() {
        return ScgOutcome::Stopped {
            class_count: graph.class_count(),
        };
    }
    let closed = graph.is_complete();

    let violating = decide_over_classes(
        &GraphClasses { graph, reapable },
        property,
        sink_places,
        conditional_sinks,
    );

    match violating {
        Some(idx) => {
            let (trace, transitions) = counterexample_path(graph, initial, idx);
            ScgOutcome::Decided {
                verdict: Verdict::Violated,
                trace,
                transitions,
                class_count: graph.class_count(),
                truncated: !closed,
            }
        }
        // Proven never comes from a prefix.
        None if !closed => ScgOutcome::Truncated {
            class_count: graph.class_count(),
        },
        None => ScgOutcome::Decided {
            verdict: Verdict::Proven {
                method: "state-space enumeration (VER-017)".into(),
                inductive_invariant: None,
            },
            trace: Vec::new(),
            transitions: Vec::new(),
            class_count: graph.class_count(),
            truncated: false,
        },
    }
}

/// [`decide_over_state_space`], read as an explored prefix even when the graph
/// closed: how the state-space cache answers a query whose class budget the cached
/// graph — a remembered truncation, or a closed graph too large for it — exceeds
/// ([VER-017]). A violation in it stands, marked `truncated`; nothing is proven
/// from it. On a closed graph every class is expanded, so the predicate reads it
/// exactly as [`decide_over_state_space`] does; only the verdict's standing changes.
#[cfg_attr(not(feature = "z3"), allow(dead_code))]
pub(crate) fn decide_over_prefix(
    graph: &StateClassGraph,
    initial: &MarkingState,
    property: &SmtProperty,
    sink_places: &[String],
    conditional_sinks: &[ConditionalSinks],
) -> ScgOutcome {
    match decide_over_state_space(graph, initial, property, sink_places, conditional_sinks) {
        ScgOutcome::Decided {
            verdict: Verdict::Violated,
            trace,
            transitions,
            class_count,
            ..
        } => ScgOutcome::Decided {
            verdict: Verdict::Violated,
            trace,
            transitions,
            class_count,
            truncated: true,
        },
        ScgOutcome::Decided { class_count, .. } => ScgOutcome::Truncated { class_count },
        other => other,
    }
}

/// Shortest firing sequence from the initial class (0) to `target`, as markings
/// and transition names. BFS over the recorded edges. Class 0 is reported as
/// `initial`, the caller's own listing of its marking.
///
/// The edge list is indexed by source in one pass first, so the walk is O(V + E)
/// like TypeScript's, which reads the graph's per-class adjacency directly.
/// Scanning the whole edge list per dequeued class instead would be O(V·E), and
/// this runs on exactly the graphs [VER-017] exists to make cheap: the default
/// budget is 50 000 classes. Grouping preserves edge-list order within a source,
/// so the tree the BFS builds — and hence the reported path — is unchanged.
fn counterexample_path(
    graph: &StateClassGraph,
    initial: &MarkingState,
    target: usize,
) -> (Vec<MarkingState>, Vec<String>) {
    let n = graph.class_count();
    let edges = graph.edges();
    let mut adjacency: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (idx, e) in edges.iter().enumerate() {
        if e.from < n {
            adjacency[e.from].push(idx);
        }
    }
    let mut parent: Vec<Option<usize>> = vec![None; n];
    let mut via: Vec<String> = vec![String::new(); n];
    let mut visited = vec![false; n];
    visited[0] = true;
    let mut queue = VecDeque::new();
    queue.push_back(0usize);
    while let Some(u) = queue.pop_front() {
        if u == target {
            break;
        }
        for &idx in &adjacency[u] {
            let e = &edges[idx];
            if !visited[e.to] {
                visited[e.to] = true;
                parent[e.to] = Some(u);
                via[e.to] = e.transition_name.clone();
                queue.push_back(e.to);
            }
        }
    }
    if target != 0 && parent[target].is_none() {
        return (Vec::new(), Vec::new());
    }
    let mut chain = vec![target];
    let mut cur = target;
    while let Some(p) = parent[cur] {
        chain.push(p);
        cur = p;
    }
    chain.reverse();
    let markings = chain
        .iter()
        .map(|&i| {
            if i == 0 {
                initial.clone()
            } else {
                graph.classes()[i].marking.clone()
            }
        })
        .collect();
    let transitions = chain.iter().skip(1).map(|&i| via[i].clone()).collect();
    (markings, transitions)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marking_state::MarkingStateBuilder;
    use libpetri_core::action::fork;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    /// A pipeline `p0 -> t0 -> p1 -> t1 -> … -> pn`: the reachable state space is
    /// one class per stage, but its *diameter* is the length, which is what makes
    /// the fixpoint search expensive and enumeration trivial.
    pub(crate) fn pipeline(n: usize, timed: bool) -> (PetriNet, MarkingState) {
        let mut builder = PetriNet::builder(format!("pipeline{n}"));
        for i in 0..n {
            let from = Place::<()>::new(format!("p{i}"));
            let to = Place::<()>::new(format!("p{}", i + 1));
            let t = Transition::builder(format!("t{i}"))
                .input(one(&from))
                .output(out_place(&to))
                .action(fork());
            let t = if timed {
                t.timing(libpetri_core::timing::delayed(10))
            } else {
                t
            };
            builder = builder.transition(t.build());
        }
        let net = builder.build();
        let m0 = MarkingStateBuilder::new().tokens("p0", 1).build();
        (net, m0)
    }

    #[test]
    fn is_untimed_separates_the_two_nets() {
        assert!(is_untimed(&pipeline(4, false).0));
        assert!(!is_untimed(&pipeline(4, true).0));
    }

    #[test]
    fn decides_deadlock_freedom_when_the_graph_closes() {
        let (net, m0) = pipeline(6, false);
        let outcome = verify_via_state_class_graph(
            &net,
            &m0,
            &SmtProperty::DeadlockFree,
            &["p6".to_string()],
            1000,
            &[],
        );
        match outcome {
            ScgOutcome::Decided {
                verdict,
                class_count,
                ..
            } => {
                assert!(verdict.is_proven(), "{verdict:?}");
                assert_eq!(class_count, 7);
            }
            ScgOutcome::Truncated { .. } | ScgOutcome::Stopped { .. } => {
                panic!("graph should close")
            }
        }
    }

    #[test]
    fn reports_a_violation_with_a_real_firing_sequence() {
        // The token comes to rest in p6, which is NOT declared a sink: stranded.
        let (net, m0) = pipeline(6, false);
        let outcome =
            verify_via_state_class_graph(&net, &m0, &SmtProperty::DeadlockFree, &[], 1000, &[]);
        match outcome {
            ScgOutcome::Decided {
                verdict,
                trace,
                transitions,
                ..
            } => {
                assert!(verdict.is_violated(), "{verdict:?}");
                assert_eq!(transitions, vec!["t0", "t1", "t2", "t3", "t4", "t5"]);
                assert_eq!(trace.last().expect("trace").count("p6"), 1);
            }
            ScgOutcome::Truncated { .. } | ScgOutcome::Stopped { .. } => {
                panic!("graph should close")
            }
        }
    }

    #[test]
    fn reports_truncation_rather_than_a_verdict_past_the_budget() {
        let (net, m0) = pipeline(6, false);
        // The graph has 7 classes.
        assert!(matches!(
            verify_via_state_class_graph(
                &net,
                &m0,
                &SmtProperty::DeadlockFree,
                &["p6".to_string()],
                3,
                &[]
            ),
            ScgOutcome::Truncated { .. }
        ));
        assert!(matches!(
            verify_via_state_class_graph(
                &net,
                &m0,
                &SmtProperty::DeadlockFree,
                &["p6".to_string()],
                1000,
                &[]
            ),
            ScgOutcome::Decided { .. }
        ));
    }

    #[test]
    fn decides_reachability_safety_over_the_same_graph() {
        let (net, m0) = pipeline(4, false);
        for property in [
            SmtProperty::place_bound("p4", 1),
            SmtProperty::unreachable(vec!["p0".into(), "p4".into()]),
        ] {
            match verify_via_state_class_graph(&net, &m0, &property, &[], 1000, &[]) {
                ScgOutcome::Decided { verdict, .. } => {
                    assert!(verdict.is_proven(), "{property:?} -> {verdict:?}")
                }
                ScgOutcome::Truncated { .. } | ScgOutcome::Stopped { .. } => {
                panic!("graph should close")
            }
            }
        }
    }

    // ---- The route as `SmtVerifier::verify` drives it ([VER-017] AC1-AC6) ----
    //
    // These need the `z3` feature only because that is where `SmtVerifier` lives;
    // the route itself returns before any solver is resolved, which is the point.

    #[cfg(feature = "z3")]
    use crate::result::VerificationRoute;
    #[cfg(feature = "z3")]
    use crate::smt_verifier::SmtVerifier;

    /// AC1: decided without a solver, the report naming the route and its class
    /// count and carrying no solver phase.
    #[cfg(feature = "z3")]
    #[test]
    fn decides_deadlock_freedom_with_no_solver_at_all() {
        let (net, m0) = pipeline(6, false);
        let result = SmtVerifier::for_net(&net)
            .initial_marking(m0)
            .property(SmtProperty::DeadlockFree)
            .sink_places(vec!["p6".to_string()])
            .verify();

        assert!(result.is_proven(), "{}", result.report);
        match &result.verdict {
            Verdict::Proven { method, .. } => {
                assert_eq!(method, "state-space enumeration (VER-017)")
            }
            other => panic!("{other:?}"),
        }
        assert!(
            result
                .report
                .contains("=== Bounded state-space enumeration (VER-017) ==="),
            "{}",
            result.report
        );
        assert!(result.report.contains("State classes: 7"), "{}", result.report);
        assert!(
            !result.report.contains("=== Phase 4: SMT Verification ==="),
            "{}",
            result.report
        );
        assert!(!result.report.contains("Solver: z3"), "{}", result.report);
    }

    /// AC2: a violation carries a real firing sequence, reported as confirmed —
    /// the graph path IS a firing sequence, so there is nothing to replay.
    #[cfg(feature = "z3")]
    #[test]
    fn a_violation_is_ordered_so_it_reports_as_confirmed() {
        // The token comes to rest in p4, which is NOT declared a sink: stranded.
        let (net, m0) = pipeline(4, false);
        let result = SmtVerifier::for_net(&net)
            .initial_marking(m0)
            .property(SmtProperty::DeadlockFree)
            .verify();
        assert!(result.is_violated(), "{}", result.report);
        assert_eq!(result.counterexample_confirmed, Some(true));
        assert_eq!(
            result.counterexample_transitions,
            vec!["t0", "t1", "t2", "t3"]
        );
        assert_eq!(
            result
                .counterexample_trace
                .last()
                .expect("trace")
                .count("p4"),
            1
        );
    }

    /// AC3, and [VER-003] AC4: the result names the deciding route and reports
    /// that P-invariants were not computed, so an empty invariant list off a graph
    /// route is not mistaken for "the net has none".
    #[cfg(feature = "z3")]
    #[test]
    fn names_the_route_and_says_invariants_were_not_computed() {
        let (net, m0) = pipeline(4, false);
        let enumerated = SmtVerifier::for_net(&net)
            .initial_marking(m0.clone())
            .property(SmtProperty::DeadlockFree)
            .sink_places(vec!["p4".to_string()])
            .verify();
        assert_eq!(enumerated.route, VerificationRoute::Enumeration);
        assert!(enumerated.invariants.is_empty());
        assert!(
            enumerated
                .report
                .contains("P-invariants: not computed (no encoding is built on this route)"),
            "{}",
            enumerated.report
        );

        let solved = SmtVerifier::for_net(&net)
            .enumeration_max_classes(0)
            .initial_marking(m0)
            .property(SmtProperty::DeadlockFree)
            .sink_places(vec!["p4".to_string()])
            .verify();
        assert_ne!(solved.route, VerificationRoute::Enumeration);
    }

    /// AC4: exceeding the budget names the budget and falls through unchanged.
    #[cfg(feature = "z3")]
    #[test]
    fn declines_past_its_class_budget_and_says_so() {
        let (net, m0) = pipeline(6, false);
        let result = SmtVerifier::for_net(&net)
            .initial_marking(m0)
            .property(SmtProperty::DeadlockFree)
            .sink_places(vec!["p6".to_string()])
            .enumeration_max_classes(3) // the graph has 7 classes
            .verify();
        assert!(
            result
                .report
                .contains("Bounded state-space enumeration truncated at 3 classes"),
            "{}",
            result.report
        );
        assert!(
            result.report.contains("=== Phase 1: Net Flattening ==="),
            "{}",
            result.report
        );
    }

    /// AC5: skipped for the budget `0`, for a timed net, and for a net with
    /// environment places; in each case the SMT pipeline runs.
    #[cfg(feature = "z3")]
    #[test]
    fn is_skipped_for_zero_budget_a_timed_net_and_environment_places() {
        let (net, m0) = pipeline(4, false);
        let off = SmtVerifier::for_net(&net)
            .initial_marking(m0)
            .property(SmtProperty::DeadlockFree)
            .sink_places(vec!["p4".to_string()])
            .enumeration_max_classes(0)
            .verify();
        assert!(
            !off.report.contains("Bounded state-space enumeration"),
            "{}",
            off.report
        );
        assert!(off.report.contains("=== Phase 1: Net Flattening ==="));

        let (timed, timed_m0) = pipeline(4, true);
        let t = SmtVerifier::for_net(&timed)
            .initial_marking(timed_m0)
            .property(SmtProperty::DeadlockFree)
            .sink_places(vec!["p4".to_string()])
            .verify();
        assert!(
            !t.report.contains("Bounded state-space enumeration"),
            "{}",
            t.report
        );

        // env IN -> T -> OUT: the graph does not model injection ([VER-006]).
        let in_p = Place::<i32>::new("IN");
        let out = Place::<i32>::new("OUT");
        let env_net = PetriNet::builder("env-source")
            .transition(
                Transition::builder("T")
                    .input(one(&in_p))
                    .output(out_place(&out))
                    .action(fork())
                    .build(),
            )
            .build();
        let e = SmtVerifier::for_net(&env_net)
            .initial_marking(MarkingStateBuilder::new().build())
            .property(SmtProperty::place_bound("OUT", 5))
            .environment_places(vec!["IN".to_string()])
            .verify();
        assert!(
            !e.report.contains("Bounded state-space enumeration"),
            "{}",
            e.report
        );
    }

    /// A reset arc on a place the same transition also consumes: both executors run
    /// this net, so the enumeration route must decide it rather than die on it.
    ///
    /// The fire step clears whatever the input loop left rather than removing the
    /// PRE-firing count — reading the original count overdraws, because the input
    /// already took its share. Rust states the reset (`set(place, 0)`) and so was
    /// never exposed to that; this pins it, and pins the marking the graph produces
    /// against what the executors do.
    // Feature-gated, not solver-gated: the route needs no z3 at run time, but
    // `SmtVerifier` itself only exists under the `z3` feature, so this cannot
    // compile without it. The same shape is covered in a default build by
    // `state_class_graph::tests::reset_on_a_place_the_transition_also_consumes`.
    #[cfg(feature = "z3")]
    #[test]
    fn decides_a_net_that_consumes_and_resets_the_same_place() {
        use libpetri_core::arc::reset;
        use libpetri_core::input::all;

        for spec in ["one", "all"] {
            let p = Place::<i32>::new("p");
            let q = Place::<i32>::new("q");
            let b = Transition::builder("t");
            let b = if spec == "one" { b.input(one(&p)) } else { b.input(all(&p)) };
            let net = PetriNet::builder("reset-input")
                .transition(
                    b.reset(reset(&p))
                        .output(out_place(&q))
                        .action(fork())
                        .build(),
                )
                .build();
            let result = SmtVerifier::for_net(&net)
                .initial_marking(MarkingStateBuilder::new().tokens("p", 3).build())
                .property(SmtProperty::place_bound("q", 5))
                .timeout(30_000)
                .verify();
            assert!(result.is_proven(), "{spec}: {}", result.report);
            assert_eq!(result.route, VerificationRoute::Enumeration, "{}", result.report);
        }
    }

    /// AC6: where both routes can answer, they answer the same.
    #[cfg(feature = "z3")]
    #[test]
    fn agrees_with_the_smt_pipeline_where_both_can_answer() {
        if !crate::smt_verifier::z3_available() {
            eprintln!("skipping agrees_with_the_smt_pipeline_*: z3 binary not on PATH");
            return;
        }
        let (net, m0) = pipeline(5, false);
        let cases: [(SmtProperty, Vec<String>); 2] = [
            (SmtProperty::DeadlockFree, vec!["p5".to_string()]),
            (SmtProperty::place_bound("p5", 1), Vec::new()),
        ];
        for (property, sinks) in cases {
            let build = |budget: usize| {
                SmtVerifier::for_net(&net)
                    .enumeration_max_classes(budget)
                    .initial_marking(m0.clone())
                    .property(property.clone())
                    .sink_places(sinks.clone())
                    .timeout(30_000)
                    .verify()
            };
            let enumerated = build(50_000);
            let solved = build(0);
            assert!(
                enumerated.report.contains("Bounded state-space enumeration"),
                "{}",
                enumerated.report
            );
            assert!(!solved.report.contains("Bounded state-space enumeration"));
            assert_eq!(
                std::mem::discriminant(&enumerated.verdict),
                std::mem::discriminant(&solved.verdict),
                "routes disagreed\n{}\n---\n{}",
                enumerated.report,
                solved.report
            );
        }
    }
}
