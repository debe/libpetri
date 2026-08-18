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
//! Because the abstraction over-approximates the concrete net, a decoded
//! counterexample can be *spurious for the concrete net* yet still replay
//! here; conversely a decoded state set that does NOT replay indicates a
//! spurious CEX at the abstract level or a decoder mismatch — the verifier
//! downgrades to `Unknown` in that case, never crashes.

use std::collections::{BTreeSet, HashMap, VecDeque};

use crate::net_flattener::{FlatNet, FlatTransition};
use crate::property::SmtProperty;

/// Abstract enablement — Lean `enabledA` (`lean/Libpetri/Basic.lean`), the
/// enablement conjuncts of `smt_encoder::firing_conditions`:
/// `m_i >= pre[i]` for every input, `m_i = 0` for inhibitors, `m_i >= 1` for
/// reads. Reset arcs deliberately do not gate (CORE-034).
pub fn enabled_a(flat: &FlatNet, state: &[i64], t: &FlatTransition) -> bool {
    for i in 0..flat.place_count {
        if t.pre[i] > 0 && state[i] < t.pre[i] {
            return false;
        }
    }
    t.inhibitor_places.iter().all(|&p| state[p] == 0)
        && t.read_places.iter().all(|&p| state[p] >= 1)
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
            if t.reset_places.contains(&i) {
                t.post[i]
            } else if t.consume_all.contains(&i) {
                t.post[i]
            } else {
                state[i] - t.pre[i] + t.post[i]
            }
        })
        .collect()
}

/// Abstract environment-injection step — `smt_encoder::injection_conditions`
/// (VER-006): adds one token to env place `pid`; guarded by `M[pid] < k` when
/// the mode is `Bounded(k)` (`None` = AlwaysAvailable, unguarded). Returns
/// `None` when the guard blocks.
pub fn inject_a(state: &[i64], pid: usize, bound: Option<usize>) -> Option<Vec<i64>> {
    if let Some(k) = bound {
        if state[pid] >= k as i64 {
            return None;
        }
    }
    let mut next = state.to_vec();
    next[pid] += 1;
    Some(next)
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
            !resolved.is_empty() && resolved.iter().all(|&pid| state[pid] >= 1)
        }
        SmtProperty::PlaceBound { place, bound }
        | SmtProperty::BranchPlaceBound { place, bound } => flat
            .place_index
            .get(place)
            .is_some_and(|&pid| state[pid] > *bound as i64),
        SmtProperty::JoinedOrDeadLettered { pending } => {
            flat.place_index.get(pending).is_some_and(|&pid| {
                deadlocked(flat, state, sink_places, env_inject) && state[pid] >= 1
            })
        }
    }
}

/// Concrete evaluation of `smt_encoder::encode_deadlock` at `state`: every
/// transition is disabled — with the VER-006 relaxation that an input/read on
/// an injectable env place is satisfiable by injection (AlwaysAvailable
/// always; Bounded(k) iff the demand is ≤ k) — and, when sinks are declared,
/// some non-sink place still holds a token.
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
            if ft.pre[i] > 0 {
                if let Some(bound) = env_bound(i) {
                    if matches!(bound, Some(k) if (ft.pre[i] as usize) > k) {
                        permanently_disabled = true;
                    }
                    continue;
                }
                some_reason = true;
                if state[i] < ft.pre[i] {
                    reason_holds = true;
                }
            }
        }
        for &inh_pid in &ft.inhibitor_places {
            some_reason = true;
            if state[inh_pid] > 0 {
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
            if state[read_pid] < 1 {
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

    if !sink_indices.is_empty() {
        let non_sink: Vec<usize> = (0..flat.place_count)
            .filter(|pid| !sink_indices.contains(pid))
            .collect();
        if !non_sink.is_empty() && !non_sink.iter().any(|&pid| state[pid] >= 1) {
            // Only sinks are marked: not a deadlock.
            return false;
        }
    }
    true
}

/// A successful replay: the chain of abstract states from the initial marking
/// to a state satisfying `Bad`, plus the step labels between them (a flat
/// transition name, or `inject(<place>)` for a VER-006 env-injection step).
/// `states.len() == transitions.len() + 1`.
#[derive(Debug, Clone)]
pub struct Replay {
    pub states: Vec<Vec<i64>>,
    pub transitions: Vec<String>,
}

/// Bounded BFS search for a chain `M₀ →* Bad` through the decoded state set.
///
/// The decoded set is a SET — proof traversal order is deliberately not
/// trusted. The search runs over abstract steps ([`fire_a`] on enabled
/// transitions plus [`inject_a`] env steps), resetting a per-segment depth
/// counter each time it lands on a decoded state: at most `max_segment_steps`
/// abstract steps are allowed between consecutive decoded states (and after
/// the last one), so the decoded states must genuinely carry the chain. The
/// total number of explored nodes is capped at `node_budget`; exhaustion
/// returns `None` (the caller downgrades — never a crash).
///
/// The caller anchors the search: `initial` should be a member of `decoded`
/// (the verifier requires `M₀ ∈ set` before calling).
pub fn replay(
    flat: &FlatNet,
    initial: &[i64],
    decoded: &BTreeSet<Vec<i64>>,
    property: &SmtProperty,
    sink_places: &[String],
    env_inject: &[(usize, Option<usize>)],
    max_segment_steps: usize,
    node_budget: usize,
) -> Option<Replay> {
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
        Replay { states, transitions }
    };

    let mut nodes = vec![Node {
        state: initial.to_vec(),
        parent: None,
        label: None,
        seg: 0,
    }];
    if violates(flat, initial, property, sink_places, env_inject) {
        return Some(reconstruct(&nodes, 0));
    }

    // Best (lowest) segment depth a state was reached with — a lower depth
    // strictly dominates (it permits more onward steps).
    let mut best_seg: HashMap<Vec<i64>, usize> = HashMap::new();
    best_seg.insert(initial.to_vec(), 0);
    let mut queue: VecDeque<usize> = VecDeque::from([0]);

    while let Some(idx) = queue.pop_front() {
        let (cur_state, cur_seg) = (nodes[idx].state.clone(), nodes[idx].seg);

        let mut successors: Vec<(Vec<i64>, String)> = Vec::new();
        for ft in &flat.transitions {
            if enabled_a(flat, &cur_state, ft) {
                successors.push((fire_a(flat, &cur_state, ft), ft.name.clone()));
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
                continue;
            }
            if best_seg.get(&next).is_some_and(|&d| d <= seg) {
                continue;
            }
            best_seg.insert(next.clone(), seg);
            if nodes.len() >= node_budget {
                return None;
            }
            nodes.push(Node {
                state: next.clone(),
                parent: Some(idx),
                label: Some(label),
                seg,
            });
            let new_idx = nodes.len() - 1;
            if violates(flat, &next, property, sink_places, env_inject) {
                return Some(reconstruct(&nodes, new_idx));
            }
            queue.push_back(new_idx);
        }
    }

    None
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
        let replay = replay(
            &flat,
            &[1, 0, 0],
            &decoded,
            &SmtProperty::place_bound("p2", 0),
            &[],
            &[],
            3,
            10_000,
        )
        .expect("chain must be found");
        assert_eq!(
            replay.states,
            vec![vec![1, 0, 0], vec![0, 1, 0], vec![0, 0, 1]]
        );
        assert_eq!(replay.transitions, vec!["t01", "t12"]);
    }

    /// Segment bound: a Bad state more than `max_segment_steps` past the last
    /// decoded state is out of reach — the decoded set must carry the chain.
    #[test]
    fn replay_unchainable_set_returns_none() {
        // p0=6 -> six steps to p1=6 > 5, but only M0 was "decoded": the
        // 3-step segment budget runs out long before Bad.
        let flat = flat_of(&["p0", "p1"], vec![ft("t", vec![1, 0], vec![0, 1])]);
        let decoded: BTreeSet<Vec<i64>> = [vec![6, 0]].into_iter().collect();
        assert!(
            replay(
                &flat,
                &[6, 0],
                &decoded,
                &SmtProperty::place_bound("p1", 5),
                &[],
                &[],
                3,
                10_000,
            )
            .is_none()
        );
    }

    /// Env injection steps participate in the chain with `inject(...)` labels.
    #[test]
    fn replay_uses_injection_steps() {
        let flat = flat_of(&["e", "p1"], vec![ft("t", vec![1, 0], vec![0, 1])]);
        let decoded: BTreeSet<Vec<i64>> =
            [vec![0, 0], vec![1, 0], vec![0, 1]].into_iter().collect();
        let replay = replay(
            &flat,
            &[0, 0],
            &decoded,
            &SmtProperty::place_bound("p1", 0),
            &[],
            &[(0, None)],
            3,
            10_000,
        )
        .expect("injection chain must be found");
        assert_eq!(replay.transitions, vec!["inject(e)", "t"]);
        assert_eq!(replay.states.last().unwrap(), &vec![0, 1]);
    }

    /// The node budget is a hard cap: an exhausted search downgrades (None),
    /// never spins.
    #[test]
    fn replay_respects_node_budget() {
        // Unbounded injection makes the abstract state space infinite; an
        // unsatisfiable Bad forces full exploration up to the budget.
        let flat = flat_of(&["e", "p1"], vec![ft("t", vec![1, 0], vec![0, 1])]);
        let decoded: BTreeSet<Vec<i64>> = (0..200).map(|n| vec![n, 0]).collect();
        assert!(
            replay(
                &flat,
                &[0, 0],
                &decoded,
                &SmtProperty::place_bound("nope", 0),
                &[],
                &[(0, None)],
                3,
                50,
            )
            .is_none()
        );
    }
}
