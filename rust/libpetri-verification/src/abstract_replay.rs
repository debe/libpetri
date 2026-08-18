//! Abstract counterexample replay (C3): re-executes a decoded IC3/PDR
//! counterexample against the verifier's own abstraction.
//!
//! The verifier's abstraction is untimed and value-blind ([VER-004]): a state
//! is one token *count* per place, exactly the `m_i` integer variables of the
//! CHC encoding. This module is the executable form of that abstract
//! semantics, and it mirrors two other artifacts **by name**, so the fidelity
//! bridge can pin all three together:
//!
//! - `lean/Libpetri/Basic.lean` — [`enabled_a`] is Lean's `enabledA`,
//!   [`fire_a`] is Lean's `fireA` (reset arm first, then `consume_all`, then
//!   `M'[p] = M[p] − pre[p] + post[p]`);
//! - `crate::smt_encoder` — [`enabled_a`] evaluates the enablement conjuncts
//!   of `firing_conditions` (`m_i >= pre[i]`, inhibitor `m_i = 0`, read
//!   `m_i >= 1`), [`fire_a`] its update arms (reset → `post[i]`,
//!   consume-all(`All`/`AtLeast`) → `post[i]`, else `m_i − pre[i] + post[i]`),
//!   [`inject_a`] its `injection_conditions` (VER-006: `+1` on an env place
//!   under its bound), and [`violates`] its `encode_property_violation` /
//!   `encode_deadlock` (`Bad(M)`).
//!
//! [`within_env_bounds`] mirrors `env_bound_conditions`, which the encoders
//! conjoin into EVERY transition disjunct of the step relation: a firing whose
//! successor pushes an env place past its `Bounded(k)` cap is not a step of
//! the encoded system, so it must not be a step here either.
//!
//! The module is `pub` and deliberately NOT gated on the `z3` feature: it is
//! the abstract semantics itself, not a solver front-end. Nothing here spawns
//! or parses z3 (the decode that feeds it lives in
//! [`crate::counterexample`], which IS gated), so the correspondence above
//! stays testable — and citable from Lean — in a build with no solver at all.
//!
//! Because the abstraction over-approximates the concrete net, a decoded
//! counterexample can be *spurious for the concrete net* yet still replay
//! here. The converse is graded, and only one grade is evidence against the
//! verdict — see [`ReplayOutcome`]: a search that exhausted the whole abstract
//! successor space without reaching `Bad` ([`ReplayOutcome::NoChain`]) says the
//! counterexample is spurious or the decoder drifted, and the verifier
//! downgrades to `Unknown`; a search that merely ran out of budget
//! ([`ReplayOutcome::Exhausted`]) says nothing about the verdict and leaves it
//! `Violated`, unconfirmed. Neither ever crashes: every public entry point
//! here tolerates a malformed state vector rather than indexing out of bounds.

use std::collections::{BTreeSet, HashMap, VecDeque};

use crate::net_flattener::{FlatNet, FlatTransition};
use crate::property::SmtProperty;

/// Abstract enablement — Lean `enabledA` (`lean/Libpetri/Basic.lean`), the
/// enablement conjuncts of `smt_encoder::firing_conditions`:
/// `m_i >= pre[i]` for every input, `m_i = 0` for inhibitors, `m_i >= 1` for
/// reads. Reset arcs deliberately do not gate (CORE-034).
///
/// A state vector shorter than the net (or a transition with a short `pre`)
/// reads as zero there rather than panicking — the module contract.
pub fn enabled_a(flat: &FlatNet, state: &[i64], t: &FlatTransition) -> bool {
    for i in 0..flat.place_count {
        let pre = t.pre.get(i).copied().unwrap_or(0);
        if pre > 0 && at(state, i) < pre {
            return false;
        }
    }
    t.inhibitor_places.iter().all(|&p| at(state, p) == 0)
        && t.read_places.iter().all(|&p| at(state, p) >= 1)
}

/// Token count at place index `i`, reading past the end of a short state
/// vector as 0 (the bounds guard behind every public entry point here).
fn at(state: &[i64], i: usize) -> i64 {
    state.get(i).copied().unwrap_or(0)
}

/// Abstract successor — Lean `fireA` (`lean/Libpetri/Basic.lean`), the update
/// arms of `smt_encoder::firing_conditions`, in the same arm order:
///
/// * reset place → `M'[p] = post[p]`
/// * consume-all place (`All` / `AtLeast`) → `M'[p] = post[p]`
/// * otherwise → `M'[p] = M[p] − pre[p] + post[p]`
///
/// The caller is expected to have checked [`enabled_a`]; firing a disabled
/// transition would fabricate tokens on the `M − pre` arm.
pub fn fire_a(flat: &FlatNet, state: &[i64], t: &FlatTransition) -> Vec<i64> {
    (0..flat.place_count)
        .map(|i| {
            let post = t.post.get(i).copied().unwrap_or(0);
            if t.reset_places.contains(&i) || t.consume_all.contains(&i) {
                post
            } else {
                at(state, i) - t.pre.get(i).copied().unwrap_or(0) + post
            }
        })
        .collect()
}

/// Abstract environment-injection step — `smt_encoder::injection_conditions`
/// (VER-006): adds one token to env place `pid`; guarded by `M[pid] < k` when
/// the mode is `Bounded(k)` (`None` = AlwaysAvailable, unguarded). Returns
/// `None` when the guard blocks.
pub fn inject_a(state: &[i64], pid: usize, bound: Option<usize>) -> Option<Vec<i64>> {
    if pid >= state.len() {
        return None;
    }
    if let Some(k) = bound {
        if state[pid] >= k as i64 {
            return None;
        }
    }
    let mut next = state.to_vec();
    next[pid] += 1;
    Some(next)
}

/// Environment post-cap predicate — `smt_encoder::env_bound_conditions`, which
/// rides inside EVERY transition disjunct of the step relation: under
/// `EnvironmentAnalysisMode::Bounded(k)` a firing may not leave an env place
/// holding more than `k`. `env_bounds` is `(place index, cap)`; an empty slice
/// (AlwaysAvailable / Ignore) admits everything.
pub fn within_env_bounds(state: &[i64], env_bounds: &[(usize, usize)]) -> bool {
    env_bounds
        .iter()
        .all(|&(pid, cap)| at(state, pid) <= cap as i64)
}

/// The property-violation predicate `Bad(M)` — a concrete evaluation of
/// `smt_encoder::encode_property_violation` at `state`, arm for arm
/// (including the unresolved-place-name conventions: an unresolved place is
/// skipped from a conjunction, and an entirely unresolved property can never
/// be violated).
pub fn violates(
    flat: &FlatNet,
    state: &[i64],
    property: &SmtProperty,
    sink_places: &[String],
    env_inject: &[(usize, Option<usize>)],
) -> bool {
    match property {
        SmtProperty::DeadlockFree => deadlocked(flat, state, sink_places, env_inject),
        SmtProperty::MutualExclusion { places } | SmtProperty::Unreachable { places } => {
            let resolved: Vec<usize> = places
                .iter()
                .filter_map(|name| flat.place_index.get(name).copied())
                .collect();
            // The non-empty guard is load-bearing: with every name unresolved
            // the encoder emits `false`, so an all-unresolved property must
            // never be violated (otherwise EVERY marking would be `Bad`).
            !resolved.is_empty() && resolved.iter().all(|&pid| at(state, pid) >= 1)
        }
        SmtProperty::PlaceBound { place, bound }
        | SmtProperty::BranchPlaceBound { place, bound } => flat
            .place_index
            .get(place)
            .is_some_and(|&pid| at(state, pid) > *bound as i64),
        SmtProperty::JoinedOrDeadLettered { pending } => {
            flat.place_index.get(pending).is_some_and(|&pid| {
                deadlocked(flat, state, sink_places, env_inject) && at(state, pid) >= 1
            })
        }
    }
}

/// Concrete evaluation of `smt_encoder::encode_deadlock` at `state`: every
/// transition is disabled — with the VER-006 relaxation that an input/read on
/// an injectable env place is satisfiable by injection (AlwaysAvailable
/// always; Bounded(k) iff the demand is ≤ k) — and, when sinks are declared,
/// no declared sink place holds a token ([VER-002]).
fn deadlocked(
    flat: &FlatNet,
    state: &[i64],
    sink_places: &[String],
    env_inject: &[(usize, Option<usize>)],
) -> bool {
    let sink_indices: Vec<usize> = sink_places
        .iter()
        .filter_map(|name| flat.place_index.get(name).copied())
        .collect();
    let env_bound = |pid: usize| -> Option<Option<usize>> {
        env_inject.iter().find(|&&(p, _)| p == pid).map(|&(_, b)| b)
    };

    for ft in &flat.transitions {
        let mut permanently_disabled = false;
        // Mirrors the encoder's `disable_reasons`: `some_reason` = the list is
        // non-empty (the transition CAN be disabled by the marking),
        // `reason_holds` = one of them evaluates true at `state`.
        let mut some_reason = false;
        let mut reason_holds = false;

        for i in 0..flat.place_count {
            let pre = ft.pre.get(i).copied().unwrap_or(0);
            if pre > 0 {
                if let Some(bound) = env_bound(i) {
                    if matches!(bound, Some(k) if (pre as usize) > k) {
                        permanently_disabled = true;
                    }
                    continue;
                }
                some_reason = true;
                if at(state, i) < pre {
                    reason_holds = true;
                }
            }
        }
        for &inh_pid in &ft.inhibitor_places {
            some_reason = true;
            if at(state, inh_pid) > 0 {
                reason_holds = true;
            }
        }
        for &read_pid in &ft.read_places {
            if let Some(bound) = env_bound(read_pid) {
                if matches!(bound, Some(k) if k < 1) {
                    permanently_disabled = true;
                }
                continue;
            }
            some_reason = true;
            if at(state, read_pid) < 1 {
                reason_holds = true;
            }
        }

        if permanently_disabled {
            // Env can never supply the demand: disabled regardless of marking.
            continue;
        }
        if !some_reason {
            // Always enabled (possibly via injection) — the encoder emits a
            // global `false`: no marking is ever a deadlock.
            return false;
        }
        if !reason_holds {
            // Enabled at this state.
            return false;
        }
    }

    // Declared sinks ([VER-002]): a quiescent marking is a violation only when
    // NO declared sink holds a token — a token in any sink marks an expected
    // terminal state. Same predicate as the encoder.
    for &pid in &sink_indices {
        if at(state, pid) >= 1 {
            return false;
        }
    }
    true
}

/// A successful replay: the chain of abstract states from the initial marking
/// to a state satisfying `Bad`, plus the step labels between them.
#[derive(Debug, Clone)]
pub struct Replay {
    /// The abstract markings, `M₀` first and the violating state last.
    pub states: Vec<Vec<i64>>,
    /// One label per step between consecutive [`Replay::states`]: a flat
    /// transition name, or `inject(<place>)` for a VER-006 env-injection step.
    /// Always `states.len() - 1` long.
    pub transitions: Vec<String>,
}

/// What the bounded search in [`replay`] concluded. Only [`ReplayOutcome::NoChain`]
/// is evidence against the solver's verdict; the other two leave it alone. How
/// each outcome surfaces to callers is the tri-state documented on
/// [`VerificationResult::counterexample_confirmed`](crate::result::VerificationResult::counterexample_confirmed)
/// — note that `NoChain` downgrades the verdict AND reports `Some(false)`.
#[derive(Debug, Clone)]
pub enum ReplayOutcome {
    /// A chain `M₀ →* Bad` was found.
    Confirmed(Replay),
    /// The reachable abstract successor space was explored in full, within
    /// both budgets, and contains no violating state — the counterexample is
    /// spurious at the abstract level, or the decoder drifted from the
    /// encoder. The one outcome that downgrades `Violated` to `Unknown`.
    NoChain,
    /// A budget ran out before the space was covered, so the absence of a
    /// chain proves nothing. `reason` is report-ready.
    Exhausted { reason: String },
}

/// Bounded BFS search for a chain `M₀ →* Bad` through the decoded state set.
///
/// The decoded set is a SET — proof traversal order is deliberately not
/// trusted. One global breadth-first search runs over abstract steps
/// ([`fire_a`] on enabled transitions, kept [`within_env_bounds`], plus
/// [`inject_a`] env steps), carrying a per-segment depth counter that resets to
/// 0 each time the search lands on a decoded state: at most
/// `max_segment_steps` abstract steps are allowed between consecutive decoded
/// states (and after the last one), so the decoded states must genuinely carry
/// the chain. A state already reached at the same or a lower segment depth is
/// dominated and not re-expanded.
///
/// `node_budget` caps the nodes ADMITTED TO THE SEARCH — the reference
/// definition the sibling implementations conform to. A node is *admitted*
/// when it is pushed onto the search's node arena, i.e. only after it survived
/// both filters: the segment budget and domination (a state already reached at
/// the same or a lower segment depth is dropped, never admitted). The anchor
/// node counts as one, and the budget trips on `>=`: a search that has already
/// admitted `node_budget` nodes refuses the next one and returns
/// [`ReplayOutcome::Exhausted`], so at most `node_budget` nodes ever exist.
/// Successors that were generated and then dropped as dominated or over the
/// segment budget do NOT count against it.
///
/// The caller anchors the search: `initial` should be a member of `decoded`
/// (the verifier requires `M₀ ∈ set` before calling).
#[allow(clippy::too_many_arguments)]
pub fn replay(
    flat: &FlatNet,
    initial: &[i64],
    decoded: &BTreeSet<Vec<i64>>,
    property: &SmtProperty,
    sink_places: &[String],
    env_inject: &[(usize, Option<usize>)],
    env_bounds: &[(usize, usize)],
    max_segment_steps: usize,
    node_budget: usize,
) -> ReplayOutcome {
    struct Node {
        state: Vec<i64>,
        parent: Option<usize>,
        label: Option<String>,
        seg: usize,
    }

    let reconstruct = |nodes: &[Node], mut idx: usize| -> Replay {
        let mut states = Vec::new();
        let mut transitions = Vec::new();
        loop {
            states.push(nodes[idx].state.clone());
            match (nodes[idx].parent, &nodes[idx].label) {
                (Some(parent), Some(label)) => {
                    transitions.push(label.clone());
                    idx = parent;
                }
                _ => break,
            }
        }
        states.reverse();
        transitions.reverse();
        debug_assert_eq!(states.len(), transitions.len() + 1, "one label per step");
        Replay { states, transitions }
    };

    if initial.len() != flat.place_count {
        // A caller-side shape error, not a statement about the net: keep the
        // verdict rather than let a malformed anchor read as "no chain".
        return ReplayOutcome::Exhausted {
            reason: format!(
                "the anchor marking has {} entries for a {}-place net",
                initial.len(),
                flat.place_count
            ),
        };
    }

    let mut nodes = vec![Node {
        state: initial.to_vec(),
        parent: None,
        label: None,
        seg: 0,
    }];
    if violates(flat, initial, property, sink_places, env_inject) {
        return ReplayOutcome::Confirmed(reconstruct(&nodes, 0));
    }

    // Best (lowest) segment depth a state was reached with — a lower depth
    // strictly dominates (it permits more onward steps).
    let mut best_seg: HashMap<Vec<i64>, usize> = HashMap::new();
    best_seg.insert(initial.to_vec(), 0);
    let mut queue: VecDeque<usize> = VecDeque::from([0]);
    // Set when a successor was dropped for running past the segment budget:
    // the space was then NOT covered in full, so an empty queue afterwards is
    // exhaustion, not proof that no chain exists.
    let mut segment_pruned = false;

    while let Some(idx) = queue.pop_front() {
        let (cur_state, cur_seg) = (nodes[idx].state.clone(), nodes[idx].seg);

        let mut successors: Vec<(Vec<i64>, String)> = Vec::new();
        for ft in &flat.transitions {
            if enabled_a(flat, &cur_state, ft) {
                let next = fire_a(flat, &cur_state, ft);
                // The encoders conjoin the env post-cap into every transition
                // disjunct; a firing that breaks it is not a step of the
                // encoded system (V1).
                if within_env_bounds(&next, env_bounds) {
                    successors.push((next, ft.name.clone()));
                }
            }
        }
        for &(pid, bound) in env_inject {
            if let Some(next) = inject_a(&cur_state, pid, bound) {
                successors.push((next, format!("inject({})", flat.places[pid])));
            }
        }

        for (next, label) in successors {
            let seg = if decoded.contains(&next) { 0 } else { cur_seg + 1 };
            if seg > max_segment_steps {
                segment_pruned = true;
                continue;
            }
            if best_seg.get(&next).is_some_and(|&d| d <= seg) {
                continue;
            }
            best_seg.insert(next.clone(), seg);
            if nodes.len() >= node_budget {
                return ReplayOutcome::Exhausted {
                    reason: format!("search node budget of {node_budget} exhausted"),
                };
            }
            nodes.push(Node {
                state: next.clone(),
                parent: Some(idx),
                label: Some(label),
                seg,
            });
            let new_idx = nodes.len() - 1;
            if violates(flat, &next, property, sink_places, env_inject) {
                return ReplayOutcome::Confirmed(reconstruct(&nodes, new_idx));
            }
            queue.push_back(new_idx);
        }
    }

    if segment_pruned {
        ReplayOutcome::Exhausted {
            reason: format!(
                "segment budget of {max_segment_steps} step(s) between decoded states exhausted"
            ),
        }
    } else {
        ReplayOutcome::NoChain
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn flat_of(places: &[&str], transitions: Vec<FlatTransition>) -> FlatNet {
        let places: Vec<String> = places.iter().map(|s| s.to_string()).collect();
        let place_index: HashMap<String, usize> = places
            .iter()
            .enumerate()
            .map(|(i, n)| (n.clone(), i))
            .collect();
        FlatNet {
            place_count: places.len(),
            places,
            place_index,
            transitions,
        }
    }

    fn ft(name: &str, pre: Vec<i64>, post: Vec<i64>) -> FlatTransition {
        FlatTransition {
            name: name.into(),
            pre,
            post,
            inhibitor_places: Vec::new(),
            read_places: Vec::new(),
            reset_places: Vec::new(),
            consume_all: Vec::new(),
        }
    }

    /// Normal arc arm: `M'[p] = M[p] − pre[p] + post[p]` (Lean fireA's default).
    #[test]
    fn enabled_and_fire_normal_arc() {
        let flat = flat_of(&["p0", "p1"], vec![ft("t", vec![1, 0], vec![0, 1])]);
        let t = &flat.transitions[0];
        assert!(enabled_a(&flat, &[2, 0], t));
        assert!(!enabled_a(&flat, &[0, 5], t));
        assert_eq!(fire_a(&flat, &[2, 0], t), vec![1, 1]);
    }

    /// Consume-all arm (`All`): the place drains to `post[p]` regardless of
    /// how many tokens it held — the encoder's `m'_i = post[i]` arm.
    #[test]
    fn fire_consume_all_drains_place() {
        let mut t = ft("t", vec![1, 0], vec![0, 1]);
        t.consume_all = vec![0];
        let flat = flat_of(&["p0", "p1"], vec![t]);
        let t = &flat.transitions[0];
        assert!(enabled_a(&flat, &[3, 0], t));
        assert_eq!(fire_a(&flat, &[3, 0], t), vec![0, 1]);
    }

    /// Consume-all arm (`AtLeast(2)`): pre = 2 gates enablement; firing still
    /// drains the whole place.
    #[test]
    fn fire_at_least_gates_then_drains() {
        let mut t = ft("t", vec![2, 0], vec![0, 1]);
        t.consume_all = vec![0];
        let flat = flat_of(&["p0", "p1"], vec![t]);
        let t = &flat.transitions[0];
        assert!(!enabled_a(&flat, &[1, 0], t));
        assert!(enabled_a(&flat, &[5, 0], t));
        assert_eq!(fire_a(&flat, &[5, 0], t), vec![0, 1]);
    }

    /// Reset arm: `M'[p] = post[p]`, and reset does not gate enablement
    /// (CORE-034).
    #[test]
    fn fire_reset_clears_place_without_gating() {
        let mut t = ft("t", vec![1, 0, 0], vec![0, 1, 0]);
        t.reset_places = vec![2];
        let flat = flat_of(&["p0", "p1", "trash"], vec![t]);
        let t = &flat.transitions[0];
        assert!(enabled_a(&flat, &[1, 0, 7], t));
        assert_eq!(fire_a(&flat, &[1, 0, 7], t), vec![0, 1, 0]);
    }

    /// Inhibitor arm: blocked while the place is marked, enabled when empty.
    #[test]
    fn enabled_inhibitor_blocks_when_marked() {
        let mut t = ft("t", vec![1, 0, 0], vec![0, 1, 0]);
        t.inhibitor_places = vec![2];
        let flat = flat_of(&["p0", "p1", "blocker"], vec![t]);
        let t = &flat.transitions[0];
        assert!(!enabled_a(&flat, &[1, 0, 1], t));
        assert!(enabled_a(&flat, &[1, 0, 0], t));
    }

    /// Read arm: gates on `>= 1` and the read place is left unchanged.
    #[test]
    fn enabled_read_gates_and_fire_leaves_it() {
        let mut t = ft("t", vec![1, 0, 0], vec![0, 1, 0]);
        t.read_places = vec![2];
        let flat = flat_of(&["p0", "p1", "sensor"], vec![t]);
        let t = &flat.transitions[0];
        assert!(!enabled_a(&flat, &[1, 0, 0], t));
        assert!(enabled_a(&flat, &[1, 0, 2], t));
        assert_eq!(fire_a(&flat, &[1, 0, 2], t), vec![0, 1, 2]);
    }

    /// Injection step: unbounded always steps; Bounded(k) blocks at k.
    #[test]
    fn inject_respects_bound() {
        assert_eq!(inject_a(&[0, 0], 0, None), Some(vec![1, 0]));
        assert_eq!(inject_a(&[1, 0], 0, Some(2)), Some(vec![2, 0]));
        assert_eq!(inject_a(&[2, 0], 0, Some(2)), None);
    }

    /// Bad(M) mirrors the encoder's arms: bound exceeded, mutex/unreachable
    /// conjunction, unresolved names never violate.
    #[test]
    fn violates_bounds_and_conjunctions() {
        let flat = flat_of(&["p0", "p1"], vec![ft("t", vec![1, 0], vec![0, 1])]);
        let pb = SmtProperty::place_bound("p1", 1);
        assert!(!violates(&flat, &[0, 1], &pb, &[], &[]));
        assert!(violates(&flat, &[0, 2], &pb, &[], &[]));
        assert!(!violates(
            &flat,
            &[9, 9],
            &SmtProperty::place_bound("nope", 0),
            &[],
            &[]
        ));

        let mx = SmtProperty::mutual_exclusion(vec!["p0".into(), "p1".into()]);
        assert!(violates(&flat, &[1, 1], &mx, &[], &[]));
        assert!(!violates(&flat, &[1, 0], &mx, &[], &[]));
        // All names unresolved -> encoder emits `false`: never violated.
        let mx_unresolved = SmtProperty::mutual_exclusion(vec!["x".into(), "y".into()]);
        assert!(!violates(&flat, &[1, 1], &mx_unresolved, &[], &[]));
    }

    /// Deadlock Bad(M): the dead-end chain quiesces at p2; sinks and env
    /// injection relax it exactly as the encoder does.
    #[test]
    fn violates_deadlock_with_sinks_and_env() {
        let flat = flat_of(
            &["p0", "p1", "p2"],
            vec![
                ft("t01", vec![1, 0, 0], vec![0, 1, 0]),
                ft("t12", vec![0, 1, 0], vec![0, 0, 1]),
            ],
        );
        let dl = SmtProperty::DeadlockFree;
        assert!(!violates(&flat, &[1, 0, 0], &dl, &[], &[]));
        assert!(violates(&flat, &[0, 0, 1], &dl, &[], &[]));
        // Declaring p2 a sink excuses the quiescent {p2} marking.
        assert!(!violates(&flat, &[0, 0, 1], &dl, &["p2".to_string()], &[]));
        // An injectable p0 (AlwaysAvailable) makes t01 satisfiable by
        // injection: no marking is ever a deadlock.
        assert!(!violates(&flat, &[0, 0, 1], &dl, &[], &[(0, None)]));
        // Bounded(0) can never supply t01's demand: permanently disabled, so
        // the deadlock stands.
        assert!(violates(&flat, &[0, 0, 1], &dl, &[], &[(0, Some(0))]));
    }

    /// Unwraps a `Confirmed` outcome, reporting the other arms.
    fn confirmed(outcome: ReplayOutcome) -> Replay {
        match outcome {
            ReplayOutcome::Confirmed(replay) => replay,
            other => panic!("expected a confirmed chain, got {other:?}"),
        }
    }

    /// A chainable decoded set replays: M0 -> mid -> bad, labels in order.
    #[test]
    fn replay_finds_chain_through_decoded_states() {
        let flat = flat_of(
            &["p0", "p1", "p2"],
            vec![
                ft("t01", vec![1, 0, 0], vec![0, 1, 0]),
                ft("t12", vec![0, 1, 0], vec![0, 0, 1]),
            ],
        );
        let decoded: BTreeSet<Vec<i64>> =
            [vec![1, 0, 0], vec![0, 1, 0], vec![0, 0, 1]].into_iter().collect();
        let replay = confirmed(replay(
            &flat,
            &[1, 0, 0],
            &decoded,
            &SmtProperty::place_bound("p2", 0),
            &[],
            &[],
            &[],
            3,
            10_000,
        ));
        assert_eq!(
            replay.states,
            vec![vec![1, 0, 0], vec![0, 1, 0], vec![0, 0, 1]]
        );
        assert_eq!(replay.transitions, vec!["t01", "t12"]);
    }

    /// Segment bound: a Bad state more than `max_segment_steps` past the last
    /// decoded state is out of reach — the decoded set must carry the chain.
    /// Running out that way is EXHAUSTION, not evidence of no chain (C4).
    #[test]
    fn replay_unchainable_set_is_exhausted_not_no_chain() {
        // p0=6 -> six steps to p1=6 > 5, but only M0 was "decoded": the
        // 3-step segment budget runs out long before Bad.
        let flat = flat_of(&["p0", "p1"], vec![ft("t", vec![1, 0], vec![0, 1])]);
        let decoded: BTreeSet<Vec<i64>> = [vec![6, 0]].into_iter().collect();
        match replay(
            &flat,
            &[6, 0],
            &decoded,
            &SmtProperty::place_bound("p1", 5),
            &[],
            &[],
            &[],
            3,
            10_000,
        ) {
            ReplayOutcome::Exhausted { reason } => {
                assert!(reason.contains("segment budget"), "{reason}")
            }
            other => panic!("expected Exhausted(segment), got {other:?}"),
        }
    }

    /// A fully covered successor space with no violating state is the only
    /// genuine `NoChain` — the outcome that downgrades the verdict.
    #[test]
    fn replay_fully_explored_space_reports_no_chain() {
        // The inhibitor freezes t forever, so p1 is never marked; the whole
        // reachable space is {M0} and no segment budget is ever hit.
        let mut t = ft("t", vec![1, 0, 0], vec![0, 1, 0]);
        t.inhibitor_places = vec![2];
        let flat = flat_of(&["p0", "p1", "blocker"], vec![t]);
        let decoded: BTreeSet<Vec<i64>> = [vec![1, 0, 1]].into_iter().collect();
        assert!(matches!(
            replay(
                &flat,
                &[1, 0, 1],
                &decoded,
                &SmtProperty::unreachable(vec!["p1".into()]),
                &[],
                &[],
                &[],
                3,
                10_000,
            ),
            ReplayOutcome::NoChain
        ));
    }

    /// Env injection steps participate in the chain with `inject(...)` labels.
    #[test]
    fn replay_uses_injection_steps() {
        let flat = flat_of(&["e", "p1"], vec![ft("t", vec![1, 0], vec![0, 1])]);
        let decoded: BTreeSet<Vec<i64>> =
            [vec![0, 0], vec![1, 0], vec![0, 1]].into_iter().collect();
        let replay = confirmed(replay(
            &flat,
            &[0, 0],
            &decoded,
            &SmtProperty::place_bound("p1", 0),
            &[],
            &[(0, None)],
            &[],
            3,
            10_000,
        ));
        assert_eq!(replay.transitions, vec!["inject(e)", "t"]);
        assert_eq!(replay.states.last().unwrap(), &vec![0, 1]);
    }

    /// V1: under `Bounded(k)` the encoders cap every transition successor at
    /// `k` on an env place. A chain that only reaches Bad by pushing the env
    /// place past the cap is NOT a chain of the encoded system, so it must not
    /// confirm the counterexample.
    #[test]
    fn replay_rejects_chain_that_breaks_the_env_bound() {
        // e is a Bounded(1) env place. `feed` tops it up from p0, `drain`
        // needs TWO tokens in e — reachable only via e=2, which the post-cap
        // forbids. Two injections cannot get there either (the guard blocks
        // the second), so the only candidate chain is inject + feed.
        let flat = flat_of(
            &["e", "p0", "p1"],
            vec![
                ft("feed", vec![0, 1, 0], vec![1, 0, 0]),
                ft("drain", vec![2, 0, 0], vec![0, 0, 1]),
            ],
        );
        let m0 = vec![0, 1, 0];
        let decoded: BTreeSet<Vec<i64>> = [
            m0.clone(),
            vec![1, 1, 0],
            vec![1, 0, 0],
            vec![2, 0, 0],
            vec![0, 0, 1],
        ]
        .into_iter()
        .collect();
        let property = SmtProperty::place_bound("p1", 0);
        // Without the post-cap the chain inject(e) -> feed -> drain confirms.
        assert!(matches!(
            replay(&flat, &m0, &decoded, &property, &[], &[(0, Some(1))], &[], 3, 10_000),
            ReplayOutcome::Confirmed(_)
        ));
        // With it, e never reaches 2 and the space is covered in full.
        assert!(matches!(
            replay(&flat, &m0, &decoded, &property, &[], &[(0, Some(1))], &[(0, 1)], 3, 10_000),
            ReplayOutcome::NoChain
        ));
    }

    /// The node budget is a hard cap on nodes ADMITTED (root included, tripped
    /// on `>=`): an exhausted search says `Exhausted`, never spins and never
    /// claims `NoChain`.
    #[test]
    fn replay_respects_node_budget() {
        // Unbounded injection makes the abstract state space infinite; an
        // unsatisfiable Bad forces full exploration up to the budget.
        let flat = flat_of(&["e", "p1"], vec![ft("t", vec![1, 0], vec![0, 1])]);
        let decoded: BTreeSet<Vec<i64>> = (0..200).map(|n| vec![n, 0]).collect();
        match replay(
            &flat,
            &[0, 0],
            &decoded,
            &SmtProperty::place_bound("nope", 0),
            &[],
            &[(0, None)],
            &[],
            3,
            50,
        ) {
            ReplayOutcome::Exhausted { reason } => {
                assert!(reason.contains("node budget of 50"), "{reason}")
            }
            other => panic!("expected Exhausted(node budget), got {other:?}"),
        }
    }

    /// Pins the exact counting rule the sibling implementations conform to:
    /// the anchor node is admitted node #1, the budget trips on `>=`, and
    /// generated-then-dropped successors do not count.
    #[test]
    fn node_budget_counts_admitted_nodes_root_included() {
        // Two transitions with the SAME abstract effect: the second successor
        // is generated but dominated, so it must not consume budget.
        let flat = flat_of(
            &["a", "b"],
            vec![ft("t1", vec![1, 0], vec![0, 1]), ft("t2", vec![1, 0], vec![0, 1])],
        );
        let decoded: BTreeSet<Vec<i64>> = BTreeSet::from([vec![1, 0]]);
        let unreachable_bad = SmtProperty::place_bound("b", 9);
        let run = |budget: usize| {
            replay(&flat, &[1, 0], &decoded, &unreachable_bad, &[], &[], &[], 3, budget)
        };

        // Budget 1: the anchor alone fills it, so admitting the first
        // successor is refused.
        match run(1) {
            ReplayOutcome::Exhausted { reason } => {
                assert!(reason.contains("node budget of 1"), "{reason}")
            }
            other => panic!("budget 1 must trip on the anchor node, got {other:?}"),
        }
        // Budget 2: anchor + one admitted successor covers the whole space.
        // The dominated duplicate is generated but not admitted, so this is
        // NoChain and not exhaustion.
        assert!(
            matches!(run(2), ReplayOutcome::NoChain),
            "dominated successors must not count against the budget"
        );
    }

    /// A state vector that does not match the net is a caller error, not a
    /// verdict: every entry point tolerates it, and the search reports
    /// exhaustion rather than the downgrade-triggering `NoChain`.
    #[test]
    fn short_state_vectors_do_not_panic() {
        let flat = flat_of(&["p0", "p1"], vec![ft("t", vec![1, 0], vec![0, 1])]);
        let t = &flat.transitions[0];
        assert!(!enabled_a(&flat, &[], t));
        assert_eq!(fire_a(&flat, &[], t), vec![-1, 1]);
        assert_eq!(inject_a(&[], 3, None), None);
        assert!(!violates(&flat, &[], &SmtProperty::place_bound("p1", 0), &[], &[]));
        assert!(matches!(
            replay(
                &flat,
                &[0],
                &BTreeSet::new(),
                &SmtProperty::place_bound("p1", 0),
                &[],
                &[],
                &[],
                3,
                10_000,
            ),
            ReplayOutcome::Exhausted { .. }
        ));
    }
}
