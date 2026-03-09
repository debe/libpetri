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
pub fn encode(
    flat: &FlatNet,
    initial_marking: &MarkingState,
    property: &SmtProperty,
    invariants: &[PInvariant],
    sink_places: &[String],
    env_bounds: &[(String, usize)],
) -> SmtEncoding {
    let p = flat.place_count;
    let mut lines = Vec::new();

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
    lines.push(String::new());

    // Error rule
    let error_rule = encode_error_rule(flat, property, &m_vars, sink_places);
    lines.push(error_rule);
    lines.push(String::new());

    // Query
    lines.push("(assert (forall () (not Error)))".to_string());
    lines.push("(check-sat)".to_string());

    SmtEncoding {
        smt2: lines.join("\n"),
        place_count: p,
    }
}

#[allow(clippy::needless_range_loop)]
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
    let p = flat.place_count;

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

    // P-invariant constraints on next marking
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

    // Environment bounds
    for (place_name, max_tokens) in env_bounds {
        if let Some(&pid) = flat.place_index.get(place_name) {
            conditions.push(format!("(<= {} {})", mp_vars[pid], max_tokens));
        }
    }

    let body = format!("(and {})", conditions.join("\n            "));

    format!(
        "(assert (forall ({all_vars})\n  (=> {body}\n      (Reachable {}))))",
        mp_vars.join(" ")
    )
}

/// Encodes the error rule based on the property.
fn encode_error_rule(
    flat: &FlatNet,
    property: &SmtProperty,
    m_vars: &[String],
    sink_places: &[String],
) -> String {
    let all_vars: String = m_vars
        .iter()
        .map(|v| format!("({v} Int)"))
        .collect::<Vec<_>>()
        .join(" ");

    let violation = encode_property_violation(flat, property, m_vars, sink_places);

    format!(
        "(assert (forall ({all_vars})\n  (=> (and (Reachable {}) {violation})\n      Error)))",
        m_vars.join(" ")
    )
}

/// Encodes the property violation condition.
fn encode_property_violation(
    flat: &FlatNet,
    property: &SmtProperty,
    m_vars: &[String],
    sink_places: &[String],
) -> String {
    match property {
        SmtProperty::DeadlockFree => encode_deadlock(flat, m_vars, sink_places),
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
        SmtProperty::PlaceBound { place, bound } => {
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
    }
}

#[allow(clippy::needless_range_loop)]
/// Encodes deadlock: all transitions are disabled.
fn encode_deadlock(flat: &FlatNet, m_vars: &[String], sink_places: &[String]) -> String {
    let sink_indices: Vec<usize> = sink_places
        .iter()
        .filter_map(|name| flat.place_index.get(name).copied())
        .collect();

    let mut disabled_conditions = Vec::new();

    for ft in &flat.transitions {
        // A transition is disabled if any pre-condition is not met,
        // or any inhibitor arc is active, or any read arc is not met.
        let mut disable_reasons = Vec::new();

        for i in 0..flat.place_count {
            if ft.pre[i] > 0 {
                disable_reasons.push(format!("(< {} {})", m_vars[i], ft.pre[i]));
            }
        }
        for &inh_pid in &ft.inhibitor_places {
            disable_reasons.push(format!("(> {} 0)", m_vars[inh_pid]));
        }
        for &read_pid in &ft.read_places {
            disable_reasons.push(format!("(< {} 1)", m_vars[read_pid]));
        }

        if disable_reasons.is_empty() {
            // Transition is always enabled — deadlock impossible for this transition
            return "false".to_string();
        }

        disabled_conditions.push(format!("(or {})", disable_reasons.join(" ")));
    }

    // Also check that we're not in a sink state (if sink places specified)
    // Sink places: states where only sink places have tokens are not deadlocks
    if !sink_indices.is_empty() {
        let non_sink_has_tokens: Vec<String> = (0..flat.place_count)
            .filter(|pid| !sink_indices.contains(pid))
            .map(|pid| format!("(>= {} 1)", m_vars[pid]))
            .collect();
        if !non_sink_has_tokens.is_empty() {
            disabled_conditions.push(format!("(or {})", non_sink_has_tokens.join(" ")));
        }
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
            .build();
        let net = PetriNet::builder("test").transition(t).build();
        let marking = MarkingStateBuilder::new().tokens("p1", 1).build();
        (net, marking)
    }

    #[test]
    fn encode_deadlock_free_produces_valid_smt2() {
        let (net, marking) = simple_chain_net();
        let flat = flatten(&net);
        let encoding = encode(&flat, &marking, &SmtProperty::DeadlockFree, &[], &[], &[]);

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
        let encoding = encode(&flat, &marking, &SmtProperty::DeadlockFree, &[], &[], &[]);

        // Should contain (assert (Reachable ...)) for initial marking
        assert!(encoding.smt2.contains("(assert (Reachable"));
    }

    #[test]
    fn encode_contains_transition_rules() {
        let (net, marking) = simple_chain_net();
        let flat = flatten(&net);
        let encoding = encode(&flat, &marking, &SmtProperty::DeadlockFree, &[], &[], &[]);

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
        );

        // Should contain bound constraint on environment place
        assert!(encoding.smt2.contains("(<= "));
    }
}
