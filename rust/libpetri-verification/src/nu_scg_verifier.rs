//! ν-net exact verification via the name-aware state-class-graph name-partition
//! quotient ([NU-050], Route B).
//!
//! Builds the [`NameStateClassGraph`] (the symmetry-reduced, name-aware SCG) and
//! decides the requested [`SmtProperty`] directly over its reachable classes — no
//! Z3. Because the graph carries the DBM zone, the verdict is exact over *time*
//! too (name×time); because joins are name-aware, *quiescence* is exact. The
//! analysis is **sound**, and **complete (exact)** when the symbolic graph closes
//! within `max_classes`; otherwise it reports `Unknown` (ν-PN reachability is
//! undecidable — undecidability surfaces as truncation, never an unsound verdict;
//! this generalises [NU-050] #2).
//!
//! This route is invoked by [`crate::smt_verifier`] to *fill the gaps* the
//! SMT / Route A path cannot answer exactly: quiescence properties on a ν-net and
//! unbudgeted reachability-safety. It returns `None` when the net is not in the
//! supported mint→matched-join fragment, and the caller falls back.

use std::collections::{BTreeSet, HashSet, VecDeque};

use libpetri_core::petri_net::PetriNet;

use crate::environment::EnvironmentAnalysisMode;
use crate::marking_state::MarkingState;
use crate::name_fragment::{self, FragmentMode};
use crate::name_state_class_graph::NameStateClassGraph;
use crate::priority_semantics::PrioritySemantics;
use crate::property::SmtProperty;
use crate::result::Verdict;

/// Outcome of the name-aware ν-partition analysis.
pub struct NuScgOutcome {
    pub verdict: Verdict,
    pub trace: Vec<MarkingState>,
    pub transitions: Vec<String>,
    /// Report note (empty for the truncation `Unknown`, whose reason is on the
    /// verdict).
    pub note: String,
    pub class_count: usize,
}

const NOTE_EXACT: &str = "Note: ν-join correlation decided exactly via the state-class-graph \
name-partition quotient — the symbolic graph closed, so the verdict is sound AND complete \
(no spurious different-name counterexample; quiescence is name-aware), beyond the \
bounded-budget fragment (NU-050, Route B).\n";

/// Tries to decide `property` exactly via the name-aware SCG. Returns `None` when
/// `net` is not in the supported fragment (the caller falls back to the SMT /
/// Route A path).
#[allow(clippy::too_many_arguments)]
pub fn verify_via_name_scg(
    net: &PetriNet,
    initial: &MarkingState,
    property: &SmtProperty,
    sink_places: &[String],
    env_places: &[&str],
    env_mode: &EnvironmentAnalysisMode,
    max_classes: usize,
    fragment_mode: FragmentMode,
    carrier_places: &BTreeSet<String>,
    priority_semantics: PrioritySemantics,
) -> Option<NuScgOutcome> {
    // CORE-043: this is a public entry that reaches the ν-SCG without going through
    // `StateClassGraph::build_with_env`, where the check otherwise sits.
    libpetri_core::petri_net::require_output_producing_actions(net);

    // Carrier validation (EXTENDED, [NU-051]): a mistyped carrier name would make
    // two fork branches mint INDEPENDENT names, so the join never becomes
    // name-enabled and the verifier would report a confident false deadlock. Fail
    // loudly as `Unknown` naming the offending place — never silently proceed.
    if fragment_mode == FragmentMode::Extended {
        let known: HashSet<&str> = net.places().iter().map(|p| p.name()).collect();
        for c in carrier_places {
            if !known.contains(c.as_str()) {
                return Some(NuScgOutcome {
                    verdict: Verdict::Unknown {
                        reason: format!("declared carrier place '{c}' not in the net"),
                    },
                    trace: Vec::new(),
                    transitions: Vec::new(),
                    note: String::new(),
                    class_count: 0,
                });
            }
        }
    }

    let fragment = name_fragment::classify(net, fragment_mode, carrier_places)?;
    // We model no initial colour assignment, so coloured places must start empty.
    for p in &fragment.coloured_order {
        if initial.count(p) != 0 {
            return None;
        }
    }

    let scg = NameStateClassGraph::build(
        net,
        initial,
        &fragment,
        max_classes,
        env_places,
        env_mode,
        priority_semantics,
    );

    if !scg.is_complete() {
        return Some(NuScgOutcome {
            verdict: Verdict::Unknown {
                reason: format!(
                    "ν name-aware state-class graph truncated at {max_classes} classes — the \
                     live correlation pool is not structurally bounded; reachability over \
                     unbounded fresh names is undecidable (NU-050, Route B). Declare a budget \
                     place to bound the live pool, or raise nu_max_classes."
                ),
            },
            trace: Vec::new(),
            transitions: Vec::new(),
            note: String::new(),
            class_count: scg.class_count(),
        });
    }

    let (verdict, violating) = decide(&scg, property, sink_places);
    let (trace, transitions) = match violating {
        Some(idx) => counterexample_path(&scg, idx),
        None => (Vec::new(), Vec::new()),
    };
    Some(NuScgOutcome {
        verdict,
        trace,
        transitions,
        note: NOTE_EXACT.to_string(),
        class_count: scg.class_count(),
    })
}

/// Decides the property over the (complete) name-aware SCG. Returns the verdict
/// and, for a violation, the index of a witnessing class.
fn decide(
    scg: &NameStateClassGraph,
    property: &SmtProperty,
    sink_places: &[String],
) -> (Verdict, Option<usize>) {
    let proven = || Verdict::Proven {
        method: "ν name-partition SCG (NU-050, Route B)".into(),
        inductive_invariant: None,
    };

    match property {
        SmtProperty::PlaceBound { place, bound }
        | SmtProperty::BranchPlaceBound { place, bound } => {
            for (i, c) in scg.classes.iter().enumerate() {
                if c.base.marking.count(place) > *bound {
                    return (Verdict::Violated, Some(i));
                }
            }
            (proven(), None)
        }
        SmtProperty::Unreachable { places } => {
            for (i, c) in scg.classes.iter().enumerate() {
                if places.iter().all(|p| c.base.marking.count(p) >= 1) {
                    return (Verdict::Violated, Some(i));
                }
            }
            (proven(), None)
        }
        SmtProperty::MutualExclusion { places } => {
            for (i, c) in scg.classes.iter().enumerate() {
                let marked = places.iter().filter(|p| c.base.marking.count(p) >= 1).count();
                if marked >= 2 {
                    return (Verdict::Violated, Some(i));
                }
            }
            (proven(), None)
        }
        SmtProperty::DeadlockFree => {
            let sinks: HashSet<&str> = sink_places.iter().map(|s| s.as_str()).collect();
            for i in 0..scg.class_count() {
                // A quiescent (no successor) class is a deadlock, unless every
                // marked place is a declared sink (an intended final state).
                if scg.successors(i).is_empty() {
                    let marking = &scg.classes[i].base.marking;
                    let all_in_sinks = marking.places().all(|(p, _)| sinks.contains(p));
                    if !all_in_sinks {
                        return (Verdict::Violated, Some(i));
                    }
                }
            }
            (proven(), None)
        }
        SmtProperty::JoinedOrDeadLettered { pending } => {
            for i in 0..scg.class_count() {
                // A quiescent class still holding a pending token is a stranded
                // correlation group (name-aware: the join is genuinely disabled).
                if scg.successors(i).is_empty() && scg.classes[i].base.marking.count(pending) >= 1 {
                    return (Verdict::Violated, Some(i));
                }
            }
            (proven(), None)
        }
    }
}

/// Shortest firing sequence from the initial class (0) to `target` for the
/// counterexample trace. BFS over the recorded edges.
fn counterexample_path(scg: &NameStateClassGraph, target: usize) -> (Vec<MarkingState>, Vec<String>) {
    let n = scg.class_count();
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
        for e in &scg.edges {
            if e.from == u && !visited[e.to] {
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
        .map(|&i| scg.classes[i].base.marking.clone())
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
    use libpetri_core::match_spec::MatchSpec;
    use libpetri_core::name::NameId;
    use libpetri_core::output::{and, out_place};
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    const MAX: usize = 10_000;

    fn verify(net: &PetriNet, initial: &MarkingState, property: SmtProperty) -> NuScgOutcome {
        verify_via_name_scg(
            net,
            initial,
            &property,
            &[],
            &[],
            &EnvironmentAnalysisMode::Ignore,
            MAX,
            FragmentMode::Base,
            &BTreeSet::new(),
            PrioritySemantics::None,
        )
        .expect("net should be in the ν name-fragment")
    }

    /// Two independent mints feed one join: their fresh names can never be equal,
    /// so `merged` is unreachable — WITH NO BUDGET PLACE (the beyond-bounded win
    /// Route A cannot do; it would return Unknown without a declared budget).
    fn distinct_mints_no_budget() -> PetriNet {
        let source_a = Place::<()>::new("sourceA");
        let source_b = Place::<()>::new("sourceB");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let merged = Place::<String>::new("merged");

        let fork_a = Transition::builder("forkA")
            .input(one(&source_a))
            .output(out_place(&a))
            .action(fork())
            .build();
        let fork_b = Transition::builder("forkB")
            .input(one(&source_b))
            .output(out_place(&b))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .action(fork())
            .build();

        PetriNet::builder("distinct_mints_no_budget")
            .transitions([fork_a, fork_b, join])
            .build()
    }

    /// One mint stamps both branches with the same name, so the join can fire.
    fn same_mint() -> PetriNet {
        let source = Place::<()>::new("source");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let merged = Place::<String>::new("merged");

        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .output(and(vec![out_place(&a), out_place(&b)]))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .action(fork())
            .build();

        PetriNet::builder("same_mint")
            .transitions([t_fork, join])
            .build()
    }

    #[test]
    fn distinct_mints_merged_unreachable_proven_no_budget() {
        let net = distinct_mints_no_budget();
        let initial = MarkingStateBuilder::new()
            .tokens("sourceA", 1)
            .tokens("sourceB", 1)
            .build();
        let out = verify(&net, &initial, SmtProperty::unreachable(vec!["merged".into()]));
        assert!(
            out.verdict.is_proven(),
            "distinct-mint names can never correlate → merged unreachable (no budget needed): {:?}",
            out.verdict
        );
        assert!(out.note.contains("name-partition quotient"));
        assert!(out.note.contains("Route B"));
    }

    #[test]
    fn same_mint_merged_reachable_violated_with_trace() {
        let net = same_mint();
        let initial = MarkingStateBuilder::new().tokens("source", 1).build();
        let out = verify(&net, &initial, SmtProperty::unreachable(vec!["merged".into()]));
        assert!(out.verdict.is_violated(), "same-mint siblings join → merged reachable");
        assert!(
            out.transitions.iter().any(|t| t == "join"),
            "counterexample trace should fire the join: {:?}",
            out.transitions
        );
    }

    #[test]
    fn joined_or_dead_lettered_violated_when_distinct_strands_pending() {
        // forkA mints into branchA AND pending; forkB mints into branchB. Their
        // names differ, so the join is name-disabled and `pending` is stranded at
        // quiescence → JoinedOrDeadLettered VIOLATED (the SMT path returns Unknown).
        let source_a = Place::<()>::new("sourceA");
        let source_b = Place::<()>::new("sourceB");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let pending = Place::<()>::new("pending");
        let merged = Place::<String>::new("merged");

        let fork_a = Transition::builder("forkA")
            .input(one(&source_a))
            .output(and(vec![out_place(&a), out_place(&pending)]))
            .action(fork())
            .build();
        let fork_b = Transition::builder("forkB")
            .input(one(&source_b))
            .output(out_place(&b))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .input(one(&pending))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .action(fork())
            .build();
        let net = PetriNet::builder("strand")
            .transitions([fork_a, fork_b, join])
            .build();

        let initial = MarkingStateBuilder::new()
            .tokens("sourceA", 1)
            .tokens("sourceB", 1)
            .build();
        let out = verify(&net, &initial, SmtProperty::joined_or_dead_lettered("pending"));
        assert!(
            out.verdict.is_violated(),
            "distinct-name siblings cannot join → pending stranded at quiescence: {:?}",
            out.verdict
        );
    }

    #[test]
    fn joined_or_dead_lettered_proven_when_same_mint_always_joins() {
        // Same-mint scatter-gather: every group's pending is joinable, so no
        // quiescent state holds a pending token → PROVEN.
        let source = Place::<()>::new("source");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let pending = Place::<()>::new("pending");
        let merged = Place::<String>::new("merged");

        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .output(and(vec![out_place(&a), out_place(&b), out_place(&pending)]))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .input(one(&pending))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .action(fork())
            .build();
        let net = PetriNet::builder("joinable")
            .transitions([t_fork, join])
            .build();

        let initial = MarkingStateBuilder::new().tokens("source", 2).build();
        let out = verify(&net, &initial, SmtProperty::joined_or_dead_lettered("pending"));
        assert!(out.verdict.is_proven(), "every group joins → no stranded pending: {:?}", out.verdict);
    }

    #[test]
    fn name_times_time_same_mint_join_reachable_under_delay() {
        // A timed same-mint join: the name layer must compose with the reused DBM
        // step. With a delay the join still fires → merged reachable.
        use libpetri_core::timing;

        let source = Place::<()>::new("source");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let merged = Place::<String>::new("merged");

        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .output(and(vec![out_place(&a), out_place(&b)]))
            .timing(timing::delayed(100))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .timing(timing::window(50, 200))
            .action(fork())
            .build();
        let net = PetriNet::builder("timed_same_mint")
            .transitions([t_fork, join])
            .build();

        let initial = MarkingStateBuilder::new().tokens("source", 1).build();
        let out = verify(&net, &initial, SmtProperty::unreachable(vec!["merged".into()]));
        assert!(out.verdict.is_violated(), "timed same-mint join still reaches merged: {:?}", out.verdict);
    }

    #[test]
    fn unbounded_mint_truncates_to_unknown() {
        // A self-refilling fork mints a fresh name every firing with no join able
        // to consume it (branchB is never produced) → the symbolic graph grows
        // without bound → truncation → Unknown (NU-050 #2 generalised).
        let source = Place::<()>::new("source");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let merged = Place::<String>::new("merged");

        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .output(and(vec![out_place(&source), out_place(&a)]))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .action(fork())
            .build();
        let net = PetriNet::builder("unbounded_mint")
            .transitions([t_fork, join])
            .build();

        let initial = MarkingStateBuilder::new().tokens("source", 1).build();
        let out = verify_via_name_scg(
            &net,
            &initial,
            &SmtProperty::unreachable(vec!["merged".into()]),
            &[],
            &[],
            &EnvironmentAnalysisMode::Ignore,
            40,
            FragmentMode::Base,
            &BTreeSet::new(),
            PrioritySemantics::None,
        )
        .expect("in fragment");
        match &out.verdict {
            Verdict::Unknown { reason } => {
                assert!(reason.contains("truncated"), "reason: {reason}");
            }
            other => panic!("expected Unknown on truncation, got {other:?}"),
        }
    }

    #[test]
    fn non_nu_net_is_not_in_fragment() {
        // No match transition → not a ν-net → None (caller falls back).
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let net = PetriNet::builder("plain").transition(t).build();
        let initial = MarkingStateBuilder::new().tokens("p1", 1).build();
        assert!(verify_via_name_scg(
            &net,
            &initial,
            &SmtProperty::unreachable(vec!["p2".into()]),
            &[],
            &[],
            &EnvironmentAnalysisMode::Ignore,
            MAX,
            FragmentMode::Base,
            &BTreeSet::new(),
            PrioritySemantics::None,
        )
        .is_none());
    }

    // === EXTENDED coloured-consumer fragment ([NU-051]) ===

    /// A fork co-mints one fresh name into `branchA`, `branchB`, and the declared
    /// carrier `stray`; the join consumes `branchA`/`branchB` (leaving `stray`);
    /// a `drain` (when present) dead-letters the leftover `stray`. Without the
    /// drain, `stray` is stranded at quiescence.
    fn comint_carrier_drain_net(with_drain: bool) -> PetriNet {
        let source = Place::<()>::new("source");
        let a = Place::<String>::new("branchA");
        let b = Place::<String>::new("branchB");
        let stray = Place::<String>::new("stray");
        let merged = Place::<String>::new("merged");
        let dl = Place::<()>::new("deadletter");

        let t_fork = Transition::builder("fork")
            .input(one(&source))
            .output(and(vec![out_place(&a), out_place(&b), out_place(&stray)]))
            .action(fork())
            .build();
        let join = Transition::builder("join")
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&merged))
            .action(fork())
            .build();

        let mut builder = PetriNet::builder("comint_carrier_drain").transitions([t_fork, join]);
        if with_drain {
            let drain = Transition::builder("drain")
                .input(one(&stray))
                .output(out_place(&dl))
                .action(fork())
                .build();
            builder = builder.transition(drain);
        }
        builder.build()
    }

    /// EXTENDED admits the carrier-co-mint + drain net (`stray` is a declared
    /// carrier); the drain relays/dead-letters it via [`Role::Consume`].
    #[test]
    fn extended_carrier_comint_drain_in_fragment() {
        let net = comint_carrier_drain_net(true);
        let carriers: BTreeSet<String> = ["stray".to_string()].into_iter().collect();
        let out = verify_via_name_scg(
            &net,
            &MarkingStateBuilder::new().tokens("source", 2).build(),
            &SmtProperty::unreachable(vec!["merged".into()]),
            &[],
            &[],
            &EnvironmentAnalysisMode::Ignore,
            MAX,
            FragmentMode::Extended,
            &carriers,
            PrioritySemantics::None,
        );
        assert!(out.is_some(), "EXTENDED must admit the carrier-co-mint + drain net");
    }

    /// (f) An unknown carrier name surfaces as `Unknown` naming the offending
    /// place — never a silent fall-back, never a false verdict.
    #[test]
    fn unknown_carrier_place_is_unknown_with_reason() {
        let net = comint_carrier_drain_net(true);
        let carriers: BTreeSet<String> = ["typoStray".to_string()].into_iter().collect();
        let out = verify_via_name_scg(
            &net,
            &MarkingStateBuilder::new().tokens("source", 1).build(),
            &SmtProperty::DeadlockFree,
            &[],
            &[],
            &EnvironmentAnalysisMode::Ignore,
            MAX,
            FragmentMode::Extended,
            &carriers,
            PrioritySemantics::None,
        )
        .expect("carrier validation must surface an outcome, not fall back");
        match &out.verdict {
            Verdict::Unknown { reason } => assert!(
                reason.contains("typoStray"),
                "reason must name the offending carrier: {reason}"
            ),
            other => panic!("expected Unknown for an unknown carrier, got {other:?}"),
        }
    }

    // === NU-052: conflict-only priority ([PrioritySemantics::Conflict]) ===

    /// The Marvin guard-join vs. timed dead-letter-drain conflict, minimal.
    /// `MINT` co-mints one fresh name into `COL_A` (and `COL_B` when `co_mint_both`);
    /// an immediate, default-priority ν-`JOIN` matches them into `OUT`; a delayed,
    /// lower-priority `DRAIN_A` dead-letters `COL_A` into `DEADLETTER`. `DRAIN_A` and
    /// `JOIN` conflict on `COL_A`.
    fn priority_fixture(co_mint_both: bool, with_drain: bool) -> PetriNet {
        use libpetri_core::timing;

        let seed = Place::<()>::new("SEED");
        let a = Place::<String>::new("COL_A");
        let b = Place::<String>::new("COL_B");
        let out = Place::<String>::new("OUT");
        let dl = Place::<String>::new("DEADLETTER");

        let mint = Transition::builder("MINT")
            .input(one(&seed))
            .output(if co_mint_both {
                and(vec![out_place(&a), out_place(&b)])
            } else {
                out_place(&a)
            })
            .action(fork())
            .build();
        let join = Transition::builder("JOIN") // immediate, priority 0
            .input(one(&a))
            .input(one(&b))
            .match_spec(
                MatchSpec::builder()
                    .key(&a, |s: &String| NameId::new(s.clone()))
                    .key(&b, |s: &String| NameId::new(s.clone()))
                    .build(),
            )
            .output(out_place(&out))
            .action(fork())
            .build();

        let mut builder = PetriNet::builder("priorityFixture").transitions([mint, join]);
        if with_drain {
            let drain = Transition::builder("DRAIN_A") // delayed, lower priority, conflicts on COL_A
                .input(one(&a))
                .timing(timing::delayed(5_000))
                .priority(-10)
                .output(out_place(&dl))
                .action(fork())
                .build();
            builder = builder.transition(drain);
        }
        builder.build()
    }

    /// Runs Route B on the priority fixture as EXTENDED `DeadlockFree`, with `OUT`
    /// and `DEADLETTER` as sinks.
    fn verify_priority(net: &PetriNet, ps: PrioritySemantics) -> NuScgOutcome {
        let sinks = vec!["OUT".to_string(), "DEADLETTER".to_string()];
        verify_via_name_scg(
            net,
            &MarkingStateBuilder::new().tokens("SEED", 1).build(),
            &SmtProperty::DeadlockFree,
            &sinks,
            &[],
            &EnvironmentAnalysisMode::Ignore,
            MAX,
            FragmentMode::Extended,
            &BTreeSet::new(),
            ps,
        )
        .expect("EXTENDED must admit the priority fixture")
    }

    #[test]
    fn priority_blind_none_reports_spurious_stall() {
        // NONE (default, priority/timing-blind): the graph explores DRAIN_A stealing
        // the matched COL_A and stranding COL_B — a spurious stall.
        let out = verify_priority(&priority_fixture(true, true), PrioritySemantics::None);
        assert!(
            out.verdict.is_violated(),
            "priority-blind NONE must report the spurious stall: {:?}",
            out.verdict
        );
    }

    #[test]
    fn conflict_priority_proves_no_stall() {
        // CONFLICT: the immediate, higher-priority join pre-empts the delayed drain,
        // so COL_A is never stolen from a live join.
        let out = verify_priority(&priority_fixture(true, true), PrioritySemantics::Conflict);
        assert!(
            out.verdict.is_proven(),
            "CONFLICT must prove no-stall: {:?}",
            out.verdict
        );
    }

    #[test]
    fn conflict_priority_still_finds_genuine_stall() {
        // A real orphan (COL_A with no matching COL_B) and no drain: the join can
        // never fire and COL_A strands. CONFLICT must NOT hide this — the join is
        // not enabled, so nothing is pruned.
        let out = verify_priority(&priority_fixture(false, false), PrioritySemantics::Conflict);
        assert!(
            out.verdict.is_violated(),
            "CONFLICT must still find the genuine stall: {:?}",
            out.verdict
        );
    }

    #[test]
    fn conflict_priority_lets_drain_clear_a_real_orphan() {
        // A real orphan WITH the drain: CONFLICT does not prune the drain (the join
        // is not enabled), so the orphan is dead-lettered and the net is
        // deadlock-free.
        let out = verify_priority(&priority_fixture(false, true), PrioritySemantics::Conflict);
        assert!(
            out.verdict.is_proven(),
            "CONFLICT must let the drain clear a genuine orphan: {:?}",
            out.verdict
        );
    }
}
