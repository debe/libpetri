//! The witness search of the state-equation phase ([VER-018]): a breadth-first search
//! from `M0` under the exact abstract semantics ([`enabled_a`] / [`fire_a`] —
//! consume-all and reset clearing, inhibitor and read guards) that fires each flat
//! transition at most as often as a candidate's firing counts allow, and stops at the
//! first marking that violates the property. This is the cheap first level of directed
//! reachability (Blondin, Haase and Offtermatt, TACAS 2021): the counts bound the depth
//! by their sum, which on a workflow net is small.
//!
//! [`WitnessOutcome::Found`] is a real firing sequence of the untimed net, so the
//! violation it witnesses is confirmed by construction. [`WitnessOutcome::None`] is a
//! completed search: no run whose firing counts stay within the candidate's reaches a
//! violation. [`WitnessOutcome::Exhausted`] says nothing either way.
//!
//! Environment injection splits those three, because an injection is not a counted
//! firing and so is never searched. `Found` survives it: the search fires only counted
//! transitions, a run in which the environment injects nothing is still a run of the
//! net, and the quiescence half of `Bad(M)` is judged with relax-env enablement
//! ([`violation_predicate`](crate::abstract_replay::violation_predicate)) — a marking it
//! accepts is stuck even against an environment free to inject. `None` does not survive
//! it: its claim is that no run reaches a violation, and an injected token could enable
//! a run the search never considered. So under injection the completed search reports
//! `Exhausted`, which says nothing either way, rather than a negative it cannot support.
//! The guard sits on that terminal answer and nowhere else: on a net whose environment
//! injects, this search is the only leg of the phase that can produce a witness at all,
//! so it must still run there.
//!
//! Nothing here spawns or parses z3, and nothing is emitted: parity with the TypeScript
//! `parikh-search` is behavioural, pinned by the tests below.

use std::collections::HashSet;
use std::rc::Rc;

use crate::abstract_replay::{enabled_a, fire_a, within_env_bounds};
use crate::net_flattener::FlatNet;

/// The node budget of one witness search when the caller has no reason to pick another.
pub const DEFAULT_NODE_BUDGET: usize = 100_000;

/// Outcome of [`search_within_counts`]. `nodes` is the number of nodes the search
/// admitted, the root included.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WitnessOutcome {
    /// A run from `M0` within the counts that reaches a marking the predicate accepts.
    Found {
        /// The markings of the run, `M0 … M_bad` inclusive.
        states: Vec<Vec<i64>>,
        /// The flat transitions fired, one per consecutive pair of `states`.
        steps: Vec<String>,
        nodes: usize,
    },
    /// Every run within the counts was explored and none reaches a violation. Only ever
    /// reported on a net with no environment injection.
    None { nodes: usize },
    /// The search proves nothing: the node budget ran out, or it completed on a net the
    /// environment injects into. `reason` is report-ready.
    Exhausted { reason: String, nodes: usize },
}

/// A node's marking and the firing counts it has left. Two runs meeting at the same
/// pair have the same future, so the pair is the deduplication key. It is also what
/// the expansion and the reconstruction read, so the node and the seen-set share one
/// allocation: the budget admits 100 000 nodes of `P + T` entries each, and a second
/// copy of every one would double the search's footprint for nothing.
type Key = (Vec<i64>, Vec<i64>);

struct SearchNode {
    key: Rc<Key>,
    /// `(parent node, flat transition fired)`; `None` on the root.
    step: Option<(usize, usize)>,
}

/// Searches the runs from `initial` that fire each flat transition `t` at most
/// `counts[t]` times for one that reaches a marking `is_bad` accepts. A node is a
/// marking together with the counts still unspent, so two runs meeting there have the
/// same future and the second is dropped. The search is breadth-first, and transitions
/// are tried in flat order, so the run found is a shortest one and the same run the
/// TypeScript search finds.
///
/// `counts` is read against the flat transitions: an entry past its end reads as `0`,
/// so a short vector never lets a transition fire more often than the candidate says.
///
/// `env_inject` is the resolved injection list (`smt_encoder::resolve_env_injection`).
/// Its `Bounded(k)` entries are the post-cap every step of the encoded system carries
/// (`smt_encoder::env_bound_conditions`): a firing that leaves an env place above its
/// cap is not a step, so it is not searched. Injection itself is not searched, so a
/// completed search on a net with injected places reports
/// [`WitnessOutcome::Exhausted`] rather than [`WitnessOutcome::None`] — see the module
/// note for why a `Found` run is still reported there.
///
/// `node_budget` caps the nodes admitted, the root included; the budget trips on `>=`,
/// when a new node would be admitted. [`DEFAULT_NODE_BUDGET`] is the phase's default.
pub fn search_within_counts(
    flat: &FlatNet,
    initial: &[i64],
    counts: &[i64],
    env_inject: &[(usize, Option<usize>)],
    is_bad: impl Fn(&[i64]) -> bool,
    node_budget: usize,
) -> WitnessOutcome {
    let caps: Vec<(usize, usize)> = env_inject
        .iter()
        .filter_map(|&(pid, bound)| bound.map(|cap| (pid, cap)))
        .collect();
    let transition_count = flat.transitions.len();
    let remaining: Vec<i64> = (0..transition_count)
        .map(|t| counts.get(t).copied().unwrap_or(0))
        .collect();
    let root = Rc::new((initial.to_vec(), remaining));
    let mut nodes = vec![SearchNode {
        key: Rc::clone(&root),
        step: None,
    }];
    if is_bad(initial) {
        return WitnessOutcome::Found {
            states: vec![initial.to_vec()],
            steps: Vec::new(),
            nodes: 1,
        };
    }
    let mut seen: HashSet<Rc<Key>> = HashSet::new();
    seen.insert(root);

    let mut head = 0;
    while head < nodes.len() {
        let key = Rc::clone(&nodes[head].key);
        let (state, remaining) = &*key;
        for (t, ft) in flat.transitions.iter().enumerate() {
            if remaining[t] <= 0 || !enabled_a(flat, state, ft) {
                continue;
            }
            let next = fire_a(flat, state, ft);
            if !within_env_bounds(&next, &caps) {
                continue;
            }
            let mut rest = remaining.clone();
            rest[t] -= 1;
            let candidate: Key = (next, rest);
            if seen.contains(&candidate) {
                continue;
            }
            if nodes.len() >= node_budget {
                return WitnessOutcome::Exhausted {
                    reason: format!("search budget exhausted ({node_budget} nodes)"),
                    nodes: nodes.len(),
                };
            }
            let admitted = Rc::new(candidate);
            seen.insert(Rc::clone(&admitted));
            let bad = is_bad(&admitted.0);
            nodes.push(SearchNode {
                key: admitted,
                step: Some((head, t)),
            });
            if bad {
                let (states, steps) = reconstruct(flat, &nodes, nodes.len() - 1);
                return WitnessOutcome::Found {
                    states,
                    steps,
                    nodes: nodes.len(),
                };
            }
        }
        head += 1;
    }

    // The search ran out of counted runs, not out of budget. That settles `None` only
    // when nothing outside the counted firings can extend a run, so injection downgrades
    // it — here, at the terminal answer, and not at the entry, where it would also
    // discard the witnesses the search can still find.
    if env_inject.is_empty() {
        WitnessOutcome::None { nodes: nodes.len() }
    } else {
        WitnessOutcome::Exhausted {
            reason: "environment injection is not searched".to_string(),
            nodes: nodes.len(),
        }
    }
}

/// The run ending at node `last`: its markings from the root, and the transitions
/// between them.
fn reconstruct(flat: &FlatNet, nodes: &[SearchNode], last: usize) -> (Vec<Vec<i64>>, Vec<String>) {
    let mut states = Vec::new();
    let mut steps = Vec::new();
    let mut idx = last;
    loop {
        let node = &nodes[idx];
        states.push(node.key.0.clone());
        match node.step {
            Some((parent, t)) => {
                steps.push(flat.transitions[t].name.clone());
                idx = parent;
            }
            None => break,
        }
    }
    states.reverse();
    steps.reverse();
    (states, steps)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abstract_replay::violation_predicate;
    use crate::net_flattener::flatten;
    use crate::property::SmtProperty;
    use crate::smt_encoder::resolve_env_injection;
    use libpetri_core::action::fork;
    use libpetri_core::arc::inhibitor;
    use libpetri_core::input::{all, one};
    use libpetri_core::output::out_place;
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    fn marking_of(flat: &FlatNet, tokens: &[(&str, i64)]) -> Vec<i64> {
        let mut m = vec![0i64; flat.place_count];
        for (name, count) in tokens {
            m[flat.place_index[*name]] = *count;
        }
        m
    }

    fn names(places: &[&str]) -> Vec<String> {
        places.iter().map(|s| s.to_string()).collect()
    }

    /// The queue-and-bundle net of [VER-018]: a producer fires up to `n` times into `q`
    /// until the signal arrives, and the bundler takes `all(q)` with the signal
    /// (`bundleEmpty` takes the signal alone when the queue is empty). Cancellable: the
    /// signal may never come. Returns the flat net and `M0 = {budget: n, src: 1}`.
    fn queue_and_bundle(n: i64, cancellable: bool) -> (FlatNet, Vec<i64>) {
        let budget = Place::<i32>::new("budget");
        let q = Place::<i32>::new("q");
        let src = Place::<i32>::new("src");
        let s = Place::<i32>::new("s");
        let out = Place::<i32>::new("out");
        let cancelled = Place::<i32>::new("cancelled");
        let t = |name: &str| Transition::builder(name).action(fork());
        let mut transitions = vec![
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
        ];
        if cancellable {
            transitions.push(t("cancel").input(one(&src)).output(out_place(&cancelled)).build());
        }
        let net = PetriNet::builder(format!("queue{n}")).transitions(transitions).build();
        let flat = flatten(&net);
        let initial = marking_of(&flat, &[("budget", n), ("src", 1)]);
        (flat, initial)
    }

    /// `gatedStrand` strands `q` behind a gate that never opens. The net is the same
    /// either way; only whether `sig` is an injected environment place differs, so the
    /// two searches differ in injection and in nothing else.
    ///
    /// `Found` must survive injection: the run fires only counted transitions, and `gate`
    /// stays disabled under relax-env enablement because `gateOpen` is not injectable, so
    /// the marking really is stuck against any environment. `None` must not survive it.
    fn gated_strand(injectable: bool) -> (FlatNet, Vec<(usize, Option<usize>)>, Vec<i64>) {
        let start = Place::<i32>::new("start");
        let q = Place::<i32>::new("q");
        let gate_open = Place::<i32>::new("gateOpen");
        let done = Place::<i32>::new("done");
        let sig = Place::<i32>::new("sig");
        let t = |name: &str| Transition::builder(name).action(fork());
        let net = PetriNet::builder("gated")
            .transitions([
                t("fill").input(one(&start)).output(out_place(&q)).build(),
                t("gate")
                    .input(one(&sig))
                    .input(one(&gate_open))
                    .output(out_place(&done))
                    .build(),
            ])
            .build();
        let flat = flatten(&net);
        let env_inject = if injectable {
            resolve_env_injection(&flat, &[("sig".to_string(), None)])
        } else {
            Vec::new()
        };
        let initial = marking_of(&flat, &[("start", 1)]);
        (flat, env_inject, initial)
    }

    fn gated_counts(flat: &FlatNet, fill: i64) -> Vec<i64> {
        flat.transitions
            .iter()
            .map(|ft| if ft.name == "fill" { fill } else { 0 })
            .collect()
    }

    /// The same assertions the TypeScript port makes.
    #[test]
    fn searches_runs_within_the_firing_counts_and_finds_the_violation_they_reach() {
        let (flat, initial) = queue_and_bundle(2, true);
        let property = SmtProperty::DeadlockFree;
        let bad = violation_predicate(&flat, &property, &names(&["out", "budget", "cancelled"]), &[], &[]);
        let counts = |produce: i64| -> Vec<i64> {
            flat.transitions
                .iter()
                .map(|ft| match ft.name.as_str() {
                    "produce" => produce,
                    "cancel" => 1,
                    _ => 0,
                })
                .collect()
        };
        // Both units produced and the signal cancelled: nothing is enabled and q strands.
        let found = search_within_counts(&flat, &initial, &counts(2), &[], &bad, DEFAULT_NODE_BUDGET);
        match found {
            WitnessOutcome::Found { steps, states, .. } => {
                assert_eq!(steps, vec!["produce", "produce", "cancel"]);
                assert_eq!(states.len(), steps.len() + 1);
                assert_eq!(states[0], initial);
                assert_eq!(states[3], marking_of(&flat, &[("q", 2), ("cancelled", 1)]));
            }
            other => panic!("expected a witness, got {other:?}"),
        }
        // One unit leaves the producer enabled, so no run within these counts is quiescent.
        let none = search_within_counts(&flat, &initial, &counts(1), &[], &bad, DEFAULT_NODE_BUDGET);
        assert!(matches!(none, WitnessOutcome::None { .. }), "{none:?}");
    }

    #[test]
    fn searches_a_net_the_environment_can_inject_into_and_reports_a_witness_it_reaches() {
        let (flat, env_inject, initial) = gated_strand(true);
        assert_eq!(env_inject.len(), 1);
        let property = SmtProperty::DeadlockFree;
        let bad = violation_predicate(&flat, &property, &names(&["done"]), &[], &env_inject);
        // Before the guard split this was `Exhausted` at once, so the leg never ran at all.
        let found = search_within_counts(
            &flat,
            &initial,
            &gated_counts(&flat, 1),
            &env_inject,
            &bad,
            DEFAULT_NODE_BUDGET,
        );
        match found {
            WitnessOutcome::Found { steps, .. } => assert_eq!(steps, vec!["fill"]),
            other => panic!("expected a witness, got {other:?}"),
        }
    }

    #[test]
    fn downgrades_a_completed_search_to_exhausted_under_injection_where_it_would_answer_none() {
        let property = SmtProperty::DeadlockFree;
        // Counts that permit no firing: the initial marking is not quiescent, so nothing is
        // bad and the search completes having explored every run it is allowed.
        let (flat, env_inject, initial) = gated_strand(false);
        assert!(env_inject.is_empty());
        let bad = violation_predicate(&flat, &property, &names(&["done"]), &[], &env_inject);
        let plain = search_within_counts(
            &flat,
            &initial,
            &gated_counts(&flat, 0),
            &env_inject,
            &bad,
            DEFAULT_NODE_BUDGET,
        );
        assert_eq!(plain, WitnessOutcome::None { nodes: 1 });

        let (flat, env_inject, initial) = gated_strand(true);
        let bad = violation_predicate(&flat, &property, &names(&["done"]), &[], &env_inject);
        let outcome = search_within_counts(
            &flat,
            &initial,
            &gated_counts(&flat, 0),
            &env_inject,
            &bad,
            DEFAULT_NODE_BUDGET,
        );
        // The search ran before reporting, rather than refusing at the door.
        match outcome {
            WitnessOutcome::Exhausted { reason, nodes } => {
                assert!(reason.contains("environment injection"), "{reason}");
                assert!(nodes > 0);
            }
            other => panic!("expected exhausted, got {other:?}"),
        }
    }

    /// The budget counts admitted nodes, root included, and its reason is the text the
    /// TypeScript search reports. Five nodes cover `M0` and the distinct runs of up to two
    /// firings; the witness would be the sixth.
    #[test]
    fn stops_at_the_node_budget_with_the_reason_it_reports() {
        let (flat, initial) = queue_and_bundle(2, true);
        let property = SmtProperty::DeadlockFree;
        let bad = violation_predicate(&flat, &property, &names(&["out", "budget", "cancelled"]), &[], &[]);
        let counts: Vec<i64> = flat
            .transitions
            .iter()
            .map(|ft| if ft.name == "produce" { 2 } else if ft.name == "cancel" { 1 } else { 0 })
            .collect();
        let outcome = search_within_counts(&flat, &initial, &counts, &[], &bad, 5);
        assert_eq!(
            outcome,
            WitnessOutcome::Exhausted {
                reason: "search budget exhausted (5 nodes)".to_string(),
                nodes: 5,
            }
        );
        // A marking that is already bad needs no node beyond the root, whatever the budget.
        let stuck = marking_of(&flat, &[("q", 1)]);
        assert_eq!(
            search_within_counts(&flat, &stuck, &counts, &[], &bad, 0),
            WitnessOutcome::Found { states: vec![stuck.clone()], steps: Vec::new(), nodes: 1 }
        );
    }

    /// A `Bounded(k)` injection caps what a firing may leave in the env place: `emit`
    /// puts a second token into `sig` past the cap of one, so that run is not a step of
    /// the encoded system and the search does not take it.
    #[test]
    fn prunes_a_firing_that_breaks_the_environment_cap() {
        let start = Place::<i32>::new("start");
        let sig = Place::<i32>::new("sig");
        let over = Place::<i32>::new("over");
        let t = |name: &str| Transition::builder(name).action(fork());
        let net = PetriNet::builder("capped")
            .transitions([
                t("emit").input(one(&start)).output(out_place(&sig)).build(),
                t("overflow").input(one(&sig)).output(out_place(&over)).build(),
            ])
            .build();
        let flat = flatten(&net);
        let initial = marking_of(&flat, &[("start", 1), ("sig", 1)]);
        let counts = vec![1, 1];
        let property = SmtProperty::PlaceBound { place: "sig".to_string(), bound: 1 };
        let is_bad = |state: &[i64]| state[flat.place_index["sig"]] > 1;
        let capped = vec![(flat.place_index["sig"], Some(1))];
        // Uncapped, `emit` reaches `sig = 2` at once.
        let uncapped = search_within_counts(&flat, &initial, &counts, &[], is_bad, DEFAULT_NODE_BUDGET);
        assert!(matches!(uncapped, WitnessOutcome::Found { ref steps, .. } if steps == &["emit"]));
        let bad = violation_predicate(&flat, &property, &[], &[], &capped);
        let outcome = search_within_counts(&flat, &initial, &counts, &capped, &bad, DEFAULT_NODE_BUDGET);
        // `emit` first breaks the cap and is pruned; `overflow` then `emit` stays within it.
        // The search completes without a witness, and injection downgrades the answer.
        assert_eq!(
            outcome,
            WitnessOutcome::Exhausted {
                reason: "environment injection is not searched".to_string(),
                nodes: 3,
            }
        );
    }

    /// A short counts vector never lets a transition fire.
    #[test]
    fn reads_a_missing_count_as_zero() {
        let (flat, initial) = queue_and_bundle(1, true);
        let property = SmtProperty::DeadlockFree;
        let bad = violation_predicate(&flat, &property, &names(&["out", "budget", "cancelled"]), &[], &[]);
        assert_eq!(
            search_within_counts(&flat, &initial, &[], &[], &bad, DEFAULT_NODE_BUDGET),
            WitnessOutcome::None { nodes: 1 }
        );
    }
}
