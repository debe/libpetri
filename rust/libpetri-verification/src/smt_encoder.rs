use crate::marking_state::MarkingState;
use crate::net_flattener::{FlatNet, FlatTransition};
use crate::p_invariant::PInvariant;
use crate::property::SmtProperty;

/// Encoded SMT-LIB2 string for Z3 Spacer (CHC/Horn clauses).
///
/// The encoding uses Constrained Horn Clauses (CHC) for IC3/PDR verification:
/// - A `Reachable` predicate over integer marking variables
/// - Init rule: the initial marking is reachable
/// - Transition rules: each transition produces a successor marking
/// - Error rule: a marking violating the property is an error
///
/// Z3 Spacer then checks if `Error` is reachable from `Init` through transitions.
#[derive(Debug, Clone)]
pub struct SmtEncoding {
    pub smt2: String,
    pub place_count: usize,
}

/// Encodes a verification problem as CHC in SMT-LIB2 format for Z3 Spacer.
///
/// `env_injection` lists environment places the analysis MODELS as externally
/// injected (VER-006): `(name, None)` is unbounded (AlwaysAvailable), `(name,
/// Some(k))` caps injection at `k` (Bounded). Each entry emits one injection rule
/// and relaxes the deadlock check for that place's inputs.
///
/// `produce_proofs` (C3, counterexample replay) emits
/// `(set-option :produce-proofs true)` ahead of the script and `(get-proof)`
/// after `(check-sat)`: on unsat (property VIOLATED) z3 prints the refutation
/// proof, whose ground `Reachable` applications the replay decoder collects
/// ([`crate::counterexample::decode_state_set`]); on sat (PROVEN) z3 answers
/// `(error "proof is not available")` and the model still follows — both
/// verified empirically on z3 4.13, so the proven path ignores it gracefully.
pub fn encode(
    flat: &FlatNet,
    initial_marking: &MarkingState,
    property: &SmtProperty,
    invariants: &[PInvariant],
    sink_places: &[String],
    env_bounds: &[(String, usize)],
    env_injection: &[(String, Option<usize>)],
    produce_proofs: bool,
) -> SmtEncoding {
    let p = flat.place_count;
    let mut lines = Vec::new();

    // Resolve injectable env places to (index, bound) once.
    let env_inject = resolve_env_injection(flat, env_injection);

    if produce_proofs {
        lines.push("(set-option :produce-proofs true)".to_string());
    }
    lines.push("(set-logic HORN)".to_string());
    lines.push(String::new());

    // Declare Reachable predicate: (declare-fun Reachable (Int Int ... Int) Bool)
    let int_params = (0..p).map(|_| "Int").collect::<Vec<_>>().join(" ");
    lines.push(format!("(declare-fun Reachable ({int_params}) Bool)"));
    lines.push("(declare-fun Error () Bool)".to_string());
    lines.push(String::new());

    // Variable names: m0, m1, ..., mP-1 for current marking
    //                 m0p, m1p, ..., mP-1p for next marking
    let m_vars: Vec<String> = (0..p).map(|i| format!("m{i}")).collect();
    let mp_vars: Vec<String> = (0..p).map(|i| format!("m{i}p")).collect();

    // Init rule: (assert (forall () (Reachable M0)))
    let m0_values: Vec<String> = (0..p)
        .map(|i| {
            let count = initial_marking.count(&flat.places[i]);
            count.to_string()
        })
        .collect();
    lines.push(format!("(assert (Reachable {}))", m0_values.join(" ")));
    lines.push(String::new());

    // Transition rules
    for ft in &flat.transitions {
        let rule = encode_transition_rule(flat, ft, &m_vars, &mp_vars, invariants, env_bounds);
        lines.push(rule);
    }

    // Environment-injection rules (VER-006): per injected env place p,
    //   Reachable(M') :- Reachable(M) [AND m_p < bound] AND m'_p = m_p + 1
    //     AND (for q != p) m'_q = m_q.
    // AlwaysAvailable (None) omits the guard. These are NOT flat transitions, so the
    // deadlock encoding (which iterates flat.transitions) never sees them. No
    // P-invariant strengthening — injection deliberately breaks conservation.
    for &(pid, bound) in &env_inject {
        lines.push(encode_injection_rule(p, pid, bound, &m_vars, &mp_vars));
    }
    lines.push(String::new());

    // Error rule (deadlock check relaxes injectable env inputs).
    let error_rule = encode_error_rule(flat, property, &m_vars, sink_places, &env_inject);
    lines.push(error_rule);
    lines.push(String::new());

    // Query: assert the error state is unreachable. Under HORN/Spacer this is SAT
    // when an inductive invariant excludes every violating state (property PROVEN)
    // and UNSAT when no such invariant exists (property VIOLATED). (A bare
    // `(not Error)` — Error is 0-ary, so no quantifier; `(forall () ...)` is an
    // invalid empty binder that z3 rejects.)
    lines.push("(assert (not Error))".to_string());
    lines.push("(check-sat)".to_string());
    if produce_proofs {
        // Unsat (VIOLATED): the refutation proof carries the ground
        // `Reachable` facts the replay decoder needs. Sat (PROVEN): a benign
        // `(error "proof is not available")` line; the model still prints.
        lines.push("(get-proof)".to_string());
    }
    // On sat (property PROVEN) this prints the model — the interpretation of
    // `Reachable` is the inductive invariant, which the verifier extracts and
    // re-checks independently (see `certificate_check`). On unsat z3 prints
    // `(error "model is not available")` after the `unsat` line; the line-based
    // result parsing in `smt_verifier` keys on the first line and ignores it.
    lines.push("(get-model)".to_string());

    SmtEncoding {
        smt2: lines.join("\n"),
        place_count: p,
    }
}

/// Resolves the named `env_injection` list to `(place index, bound)` pairs,
/// silently dropping names that do not resolve in the flat net. Shared by the
/// CHC encoding and the certificate check so both see the same injection set.
pub(crate) fn resolve_env_injection(
    flat: &FlatNet,
    env_injection: &[(String, Option<usize>)],
) -> Vec<(usize, Option<usize>)> {
    env_injection
        .iter()
        .filter_map(|(name, bound)| flat.place_index.get(name).map(|&pid| (pid, *bound)))
        .collect()
}

// === Shared condition emitters ===
//
// The per-transition / per-injection conjuncts below are emitted by BOTH the
// CHC rule encoding (this module's `encode`) and the plain-SMT step relation
// `encode_step_relation_smt2` used by the independent certificate check
// (`crate::certificate_check`), so the two encodings cannot drift.

#[allow(clippy::needless_range_loop)]
/// Enablement + firing + non-negativity conjuncts for one flat transition:
/// `enabled(M, t)`, `fire(M, M', t)`, `M' >= 0`. Deliberately EXCLUDES the
/// `Reachable` body atom, the P-invariant strengthening, and the env bounds —
/// the callers add what their encoding needs.
fn firing_conditions(
    flat: &FlatNet,
    ft: &FlatTransition,
    m_vars: &[String],
    mp_vars: &[String],
) -> Vec<String> {
    let p = flat.place_count;
    let mut conditions = Vec::new();

    // Enablement: pre-conditions (m_i >= pre[i])
    for i in 0..p {
        if ft.pre[i] > 0 {
            conditions.push(format!("(>= {} {})", m_vars[i], ft.pre[i]));
        }
    }

    // Inhibitor arcs: m_i = 0
    for &inh_pid in &ft.inhibitor_places {
        conditions.push(format!("(= {} 0)", m_vars[inh_pid]));
    }

    // Read arcs: m_i >= 1
    for &read_pid in &ft.read_places {
        conditions.push(format!("(>= {} 1)", m_vars[read_pid]));
    }

    // Fire relation: m'_i = m_i - pre[i] + post[i]
    // For reset places: m'_i = post[i]
    // For consume-all places: m'_i = post[i] (token count drops to 0 then post added)
    for i in 0..p {
        if ft.reset_places.contains(&i) {
            // Reset: clear all tokens then add post
            conditions.push(format!("(= {} {})", mp_vars[i], ft.post[i]));
        } else if ft.consume_all.contains(&i) {
            // Consume all then add post
            conditions.push(format!("(= {} {})", mp_vars[i], ft.post[i]));
        } else {
            let delta = ft.post[i] - ft.pre[i];
            match delta.cmp(&0) {
                std::cmp::Ordering::Greater => {
                    conditions.push(format!("(= {} (+ {} {}))", mp_vars[i], m_vars[i], delta));
                }
                std::cmp::Ordering::Less => {
                    conditions.push(format!("(= {} (- {} {}))", mp_vars[i], m_vars[i], -delta));
                }
                std::cmp::Ordering::Equal => {
                    conditions.push(format!("(= {} {})", mp_vars[i], m_vars[i]));
                }
            }
        }
    }

    // Non-negativity: m'_i >= 0
    for i in 0..p {
        conditions.push(format!("(>= {} 0)", mp_vars[i]));
    }

    conditions
}

/// P-invariant conjuncts over the given marking variables (the CHC path
/// applies them to the next marking). The step relation
/// (`encode_step_relation_smt2`) never emits these — the certificate check
/// keeps its relation UNSTRENGTHENED and instead conjoins them into the
/// certificate candidate, where the VCs re-prove them ([`crate::certificate_check`]).
pub(crate) fn invariant_conditions(invariants: &[PInvariant], mp_vars: &[String]) -> Vec<String> {
    let mut conditions = Vec::new();
    for inv in invariants {
        let terms: Vec<String> = inv
            .support
            .iter()
            .map(|&i| format!("(* {} {})", inv.weights[i], mp_vars[i]))
            .collect();
        if !terms.is_empty() {
            let sum = if terms.len() == 1 {
                terms[0].clone()
            } else {
                format!("(+ {})", terms.join(" "))
            };
            conditions.push(format!("(= {} {})", sum, inv.constant));
        }
    }
    conditions
}

/// Environment post-cap conjuncts on the next marking (legacy Bounded mode).
fn env_bound_conditions(
    flat: &FlatNet,
    env_bounds: &[(String, usize)],
    mp_vars: &[String],
) -> Vec<String> {
    let mut conditions = Vec::new();
    for (place_name, max_tokens) in env_bounds {
        if let Some(&pid) = flat.place_index.get(place_name) {
            conditions.push(format!("(<= {} {})", mp_vars[pid], max_tokens));
        }
    }
    conditions
}

/// Guard + column-update conjuncts for one env-injection step (VER-006):
/// `[m_pid < bound]`, `m'_pid = m_pid + 1`, all other columns copied.
fn injection_conditions(
    p: usize,
    pid: usize,
    bound: Option<usize>,
    m_vars: &[String],
    mp_vars: &[String],
) -> Vec<String> {
    let mut conditions = Vec::new();
    if let Some(k) = bound {
        conditions.push(format!("(< {} {})", m_vars[pid], k));
    }
    for i in 0..p {
        if i == pid {
            conditions.push(format!("(= {} (+ {} 1))", mp_vars[i], m_vars[i]));
        } else {
            conditions.push(format!("(= {} {})", mp_vars[i], m_vars[i]));
        }
    }
    conditions
}

/// Encodes a single transition rule as a CHC.
///
/// ```text
/// (assert (forall ((m0 Int) ... (m0p Int) ...)
///   (=> (and (Reachable m0 ... mP-1)
///            enabled(M, t)
///            fire(M, M', t)
///            non-negativity(M')
///            invariants(M')
///            env-bounds(M'))
///       (Reachable m0p ... mP-1p))))
/// ```
fn encode_transition_rule(
    flat: &FlatNet,
    ft: &FlatTransition,
    m_vars: &[String],
    mp_vars: &[String],
    invariants: &[PInvariant],
    env_bounds: &[(String, usize)],
) -> String {
    // Quantified variables
    let all_vars: String = m_vars
        .iter()
        .chain(mp_vars.iter())
        .map(|v| format!("({v} Int)"))
        .collect::<Vec<_>>()
        .join(" ");

    let mut conditions = Vec::new();

    // Reachable(m0, ..., mP-1)
    conditions.push(format!("(Reachable {})", m_vars.join(" ")));
    conditions.extend(firing_conditions(flat, ft, m_vars, mp_vars));
    conditions.extend(invariant_conditions(invariants, mp_vars));
    conditions.extend(env_bound_conditions(flat, env_bounds, mp_vars));

    let body = format!("(and {})", conditions.join("\n            "));

    format!(
        "(assert (forall ({all_vars})\n  (=> {body}\n      (Reachable {}))))",
        mp_vars.join(" ")
    )
}

/// Encodes one environment-injection rule (VER-006). `bound` of `None` is
/// unbounded (AlwaysAvailable); `Some(k)` guards injection so the place never
/// exceeds `k` (Bounded). All columns other than `pid` are copied unchanged.
fn encode_injection_rule(
    p: usize,
    pid: usize,
    bound: Option<usize>,
    m_vars: &[String],
    mp_vars: &[String],
) -> String {
    let all_vars: String = m_vars
        .iter()
        .chain(mp_vars.iter())
        .map(|v| format!("({v} Int)"))
        .collect::<Vec<_>>()
        .join(" ");

    let mut conditions = Vec::new();
    conditions.push(format!("(Reachable {})", m_vars.join(" ")));
    conditions.extend(injection_conditions(p, pid, bound, m_vars, mp_vars));

    let body = format!("(and {})", conditions.join("\n            "));
    format!(
        "(assert (forall ({all_vars})\n  (=> {body}\n      (Reachable {}))))",
        mp_vars.join(" ")
    )
}

/// Joins conjuncts into a single formula (`true` when empty, the bare conjunct
/// when singleton — SMT-LIB `and` wants at least two arguments). Shared with
/// the certificate check's candidate builder.
pub(crate) fn conjoin(conditions: &[String]) -> String {
    match conditions {
        [] => "true".to_string(),
        [single] => single.clone(),
        _ => format!("(and {})", conditions.join(" ")),
    }
}

/// Encodes the net's one-step transition relation `T(M, M')` as a single plain
/// SMT-LIB2 formula over the free variables `m0..mN` / `m0p..mNp` (the same
/// naming the CHC encoding quantifies over): the disjunction of every
/// flat-transition firing and every env-injection step (VER-006).
///
/// This is the UNSTRENGTHENED relation used by the independent certificate
/// check ([`crate::certificate_check`]): it shares the per-transition /
/// per-injection condition emitters with the CHC path (`firing_conditions`,
/// `env_bound_conditions`, `injection_conditions`) but deliberately OMITS the
/// P-invariant conjuncts, so a certificate poisoned by a wrong invariant
/// cannot re-certify itself.
pub(crate) fn encode_step_relation_smt2(
    flat: &FlatNet,
    env_bounds: &[(String, usize)],
    env_injection: &[(String, Option<usize>)],
) -> String {
    let p = flat.place_count;
    let m_vars: Vec<String> = (0..p).map(|i| format!("m{i}")).collect();
    let mp_vars: Vec<String> = (0..p).map(|i| format!("m{i}p")).collect();
    let env_inject = resolve_env_injection(flat, env_injection);

    let mut disjuncts = Vec::new();
    for ft in &flat.transitions {
        let mut conditions = firing_conditions(flat, ft, &m_vars, &mp_vars);
        conditions.extend(env_bound_conditions(flat, env_bounds, &mp_vars));
        disjuncts.push(conjoin(&conditions));
    }
    for &(pid, bound) in &env_inject {
        disjuncts.push(conjoin(&injection_conditions(p, pid, bound, &m_vars, &mp_vars)));
    }

    match disjuncts.as_slice() {
        [] => "false".to_string(),
        [single] => single.clone(),
        _ => format!("(or {})", disjuncts.join("\n    ")),
    }
}

/// Encodes the error rule based on the property.
fn encode_error_rule(
    flat: &FlatNet,
    property: &SmtProperty,
    m_vars: &[String],
    sink_places: &[String],
    env_inject: &[(usize, Option<usize>)],
) -> String {
    let all_vars: String = m_vars
        .iter()
        .map(|v| format!("({v} Int)"))
        .collect::<Vec<_>>()
        .join(" ");

    let violation = encode_property_violation(flat, property, m_vars, sink_places, env_inject);

    format!(
        "(assert (forall ({all_vars})\n  (=> (and (Reachable {}) {violation})\n      Error)))",
        m_vars.join(" ")
    )
}

/// Encodes the property violation condition (`Bad(M)` over `m_vars`). Also
/// used by the certificate check's safety VC ([`crate::certificate_check`]),
/// which must test against exactly the violation the error rule encodes.
pub(crate) fn encode_property_violation(
    flat: &FlatNet,
    property: &SmtProperty,
    m_vars: &[String],
    sink_places: &[String],
    env_inject: &[(usize, Option<usize>)],
) -> String {
    match property {
        SmtProperty::DeadlockFree => encode_deadlock(flat, m_vars, sink_places, env_inject),
        SmtProperty::MutualExclusion { places } => {
            // Violation: all specified places simultaneously have tokens
            let conditions: Vec<String> = places
                .iter()
                .filter_map(|name| flat.place_index.get(name))
                .map(|&pid| format!("(>= {} 1)", m_vars[pid]))
                .collect();
            if conditions.is_empty() {
                "false".to_string()
            } else {
                format!("(and {})", conditions.join(" "))
            }
        }
        // BranchPlaceBound is the ν-net budget lever (NU-040): a count bound,
        // encoded identically to PlaceBound. Sound under the matched-transition
        // over-approximation — the real net fires fewer joins, so it cannot
        // exceed a bound the over-approximation respects.
        SmtProperty::PlaceBound { place, bound }
        | SmtProperty::BranchPlaceBound { place, bound } => {
            if let Some(&pid) = flat.place_index.get(place) {
                format!("(> {} {})", m_vars[pid], bound)
            } else {
                "false".to_string()
            }
        }
        SmtProperty::Unreachable { places } => {
            let conditions: Vec<String> = places
                .iter()
                .filter_map(|name| flat.place_index.get(name))
                .map(|&pid| format!("(>= {} 1)", m_vars[pid]))
                .collect();
            if conditions.is_empty() {
                "false".to_string()
            } else {
                format!("(and {})", conditions.join(" "))
            }
        }
        // JoinedOrDeadLettered (NU-040): a quiescent (deadlocked) state that
        // still holds a `pending` token is a stranded correlation group. Reuse
        // the deadlock predicate and conjoin pending non-emptiness.
        SmtProperty::JoinedOrDeadLettered { pending } => {
            let deadlock = encode_deadlock(flat, m_vars, sink_places, env_inject);
            match flat.place_index.get(pending) {
                Some(&pid) => format!("(and {deadlock} (>= {} 1))", m_vars[pid]),
                // Unknown pending place name: no state can violate.
                None => "false".to_string(),
            }
        }
    }
}

#[allow(clippy::needless_range_loop)]
/// Encodes deadlock: all transitions are disabled.
///
/// Environment inputs are treated as injectable (VER-006): an input/read on an
/// injectable env place is satisfiable by external injection, so it is NOT a
/// reason the transition is disabled — AlwaysAvailable always satisfies it,
/// Bounded(k) satisfies it iff the required cardinality is ≤ k. This mirrors the
/// state class graph's always-available enablement so a reactive net merely
/// waiting for input is not reported as a deadlock; only a genuinely stuck
/// marking is.
fn encode_deadlock(
    flat: &FlatNet,
    m_vars: &[String],
    sink_places: &[String],
    env_inject: &[(usize, Option<usize>)],
) -> String {
    let sink_indices: Vec<usize> = sink_places
        .iter()
        .filter_map(|name| flat.place_index.get(name).copied())
        .collect();
    // Injectable env place index -> bound (None = unbounded).
    let env_bound = |pid: usize| -> Option<Option<usize>> {
        env_inject.iter().find(|&&(p, _)| p == pid).map(|&(_, b)| b)
    };

    let mut disabled_conditions = Vec::new();

    for ft in &flat.transitions {
        // A transition is disabled if any pre-condition is not met,
        // or any inhibitor arc is active, or any read arc is not met.
        let mut disable_reasons = Vec::new();
        // True if env injection can never satisfy a required input -> the
        // transition is permanently disabled regardless of the marking.
        let mut permanently_disabled = false;

        for i in 0..flat.place_count {
            if ft.pre[i] > 0 {
                if let Some(bound) = env_bound(i) {
                    // Injectable: satisfiable unless a finite cap is below the demand.
                    if matches!(bound, Some(k) if (ft.pre[i] as usize) > k) {
                        permanently_disabled = true;
                    }
                    continue;
                }
                disable_reasons.push(format!("(< {} {})", m_vars[i], ft.pre[i]));
            }
        }
        for &inh_pid in &ft.inhibitor_places {
            disable_reasons.push(format!("(> {} 0)", m_vars[inh_pid]));
        }
        for &read_pid in &ft.read_places {
            if let Some(bound) = env_bound(read_pid) {
                if matches!(bound, Some(k) if k < 1) {
                    permanently_disabled = true;
                }
                continue;
            }
            disable_reasons.push(format!("(< {} 1)", m_vars[read_pid]));
        }

        if permanently_disabled {
            // Always disabled (env cannot supply the demand): contributes "true".
            disabled_conditions.push("true".to_string());
            continue;
        }

        if disable_reasons.is_empty() {
            // Transition is always enabled (possibly via injection) — no deadlock.
            return "false".to_string();
        }

        disabled_conditions.push(format!("(or {})", disable_reasons.join(" ")));
    }

    // Declared sinks ([VER-002]): the error condition is
    // `(all transitions disabled) AND (no sink place has a token)`, so each
    // declared sink contributes `M[sink] = 0`. A quiescent marking holding a
    // token in ANY declared sink is an expected terminal state, not a deadlock.
    // Mirrors Java `SmtEncoder.encodePropertyViolation` and TypeScript
    // `encodePropertyViolation`.
    for &pid in &sink_indices {
        disabled_conditions.push(format!("(= {} 0)", m_vars[pid]));
    }

    if disabled_conditions.is_empty() {
        "true".to_string()
    } else {
        format!("(and {})", disabled_conditions.join("\n         "))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marking_state::MarkingStateBuilder;
    use crate::net_flattener::flatten;
    use libpetri_core::action::fork;
    use libpetri_core::input::one;
    use libpetri_core::output::out_place;
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    fn simple_chain_net() -> (PetriNet, MarkingState) {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = Transition::builder("t1")
            .input(one(&p1))
            .output(out_place(&p2))
            .action(fork())
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let marking = MarkingStateBuilder::new().tokens("p1", 1).build();
        (net, marking)
    }

    #[test]
    fn encode_deadlock_free_produces_valid_smt2() {
        let (net, marking) = simple_chain_net();
        let flat = flatten(&net);
        let encoding = encode(&flat, &marking, &SmtProperty::DeadlockFree, &[], &[], &[], &[], false);

        assert!(encoding.smt2.contains("(set-logic HORN)"));
        assert!(encoding.smt2.contains("(declare-fun Reachable"));
        assert!(encoding.smt2.contains("(declare-fun Error () Bool)"));
        assert!(encoding.smt2.contains("(check-sat)"));
        assert_eq!(encoding.place_count, 2);
    }

    #[test]
    fn encode_contains_init_rule() {
        let (net, marking) = simple_chain_net();
        let flat = flatten(&net);
        let encoding = encode(&flat, &marking, &SmtProperty::DeadlockFree, &[], &[], &[], &[], false);

        // Should contain (assert (Reachable ...)) for initial marking
        assert!(encoding.smt2.contains("(assert (Reachable"));
    }

    #[test]
    fn encode_contains_transition_rules() {
        let (net, marking) = simple_chain_net();
        let flat = flatten(&net);
        let encoding = encode(&flat, &marking, &SmtProperty::DeadlockFree, &[], &[], &[], &[], false);

        // Should contain forall with quantified variables
        assert!(encoding.smt2.contains("(forall"));
        // Should contain enablement check
        assert!(encoding.smt2.contains("(>= m"));
    }

    #[test]
    fn encode_mutual_exclusion() {
        let (net, marking) = simple_chain_net();
        let flat = flatten(&net);
        let encoding = encode(
            &flat,
            &marking,
            &SmtProperty::mutual_exclusion(vec!["p1".into(), "p2".into()]),
            &[],
            &[],
            &[],
            &[],
            false,
        );

        // Error rule should check both places have tokens
        assert!(encoding.smt2.contains("Error"));
    }

    #[test]
    fn encode_place_bound() {
        let (net, marking) = simple_chain_net();
        let flat = flatten(&net);
        let encoding = encode(
            &flat,
            &marking,
            &SmtProperty::place_bound("p2", 5),
            &[],
            &[],
            &[],
            &[],
            false,
        );

        // Error rule should check bound violation
        assert!(encoding.smt2.contains("(> "));
    }

    #[test]
    fn encode_with_invariants() {
        let (net, marking) = simple_chain_net();
        let flat = flatten(&net);

        let inv = PInvariant {
            weights: vec![1, 1],
            constant: 1,
            support: vec![0, 1],
        };

        let encoding = encode(
            &flat,
            &marking,
            &SmtProperty::DeadlockFree,
            &[inv],
            &[],
            &[],
            &[],
            false,
        );

        // Should contain invariant constraint
        assert!(encoding.smt2.contains("(= "));
    }

    #[test]
    fn encode_with_env_bounds() {
        let (net, marking) = simple_chain_net();
        let flat = flatten(&net);

        let encoding = encode(
            &flat,
            &marking,
            &SmtProperty::DeadlockFree,
            &[],
            &[],
            &[("p1".into(), 3)],
            &[],
            false,
        );

        // Should contain bound constraint on environment place
        assert!(encoding.smt2.contains("(<= "));
    }

    /// C3 proof emission: `:produce-proofs` leads the script, `(get-proof)`
    /// sits between `(check-sat)` and `(get-model)`; off by default.
    #[test]
    fn encode_produce_proofs_ordering() {
        let (net, marking) = simple_chain_net();
        let flat = flatten(&net);
        let with = encode(&flat, &marking, &SmtProperty::DeadlockFree, &[], &[], &[], &[], true);
        assert!(with.smt2.starts_with("(set-option :produce-proofs true)\n(set-logic HORN)"));
        let cs = with.smt2.find("(check-sat)").unwrap();
        let gp = with.smt2.find("(get-proof)").unwrap();
        let gm = with.smt2.find("(get-model)").unwrap();
        assert!(cs < gp && gp < gm, "check-sat < get-proof < get-model");

        let without = encode(&flat, &marking, &SmtProperty::DeadlockFree, &[], &[], &[], &[], false);
        assert!(!without.smt2.contains("produce-proofs"));
        assert!(!without.smt2.contains("(get-proof)"));
    }
}
