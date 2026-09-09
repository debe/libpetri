//! The linear state-equation bound ([VER-015]): a structural proof of a
//! reachability-safety property that needs no fixpoint search.
//!
//! Every reachable marking of the abstract net satisfies `M = M0 + C·σ` for some
//! firing count vector `σ ≥ 0`, so for any weighting `y ≥ 0` with `y·C ≤ 0` on
//! every transition, `y·M ≤ y·M0` holds along every run — a **decreasing**
//! conservation law, where the P-invariants of [VER-005] are the *equalities*
//! `y·C = 0`. The violation of a reachability-safety property is a lower demand
//! on some places (`m_p ≥ 1` for each place of an `Unreachable`, `m_p ≥ k+1` for
//! a `PlaceBound`); if some `y` makes that demand exceed `y·M0`, no reachable
//! marking meets it and the property is proven.
//!
//! Finding `y` is one linear query in `QF_LIA`, answered by the same `z3`
//! transport as everything else ([VER-013]); the answer is then re-checked in
//! exact integer arithmetic (`y ≥ 0`, `y·C ≤ 0` per transition,
//! `y·d ≥ y·M0 + 1`, all in checked `i128` — an overflow is a failed check), so
//! the proof rests on the check, not on the solver. It closes exactly the class
//! of proofs IC3 misses on pipeline-shaped nets: an ordering argument ("both
//! join slots armed means every upstream stage has run, so no halt is still
//! possible") is a weighted count bound, which Spacer's lemma generalisation
//! does not invent over fifty variables but a linear solver finds in
//! milliseconds.
//!
//! Soundness needs the same guards as the equality laws: zero weight on every
//! consume-all / reset place (H1 — the fire relation is not linear there) and
//! on every injected environment place (H3' — injection breaks conservation).
//!
//! The emitted script is byte-identical to the TypeScript and Java ports for
//! the same input (`scripts/<id>/bound.smt2` under
//! `spec/verification-fixtures`): places in flat index order, one row per flat
//! transition in net order, `(- k)` for a negative literal, a lone term
//! unwrapped.

use std::collections::{BTreeMap, BTreeSet};

use crate::marking_state::MarkingState;
use crate::net_flattener::FlatNet;
use crate::p_invariant::nonlinear_places;
use crate::property::SmtProperty;
use crate::smt_verifier::extract_define_funs;

/// One linear bound `Σ weights[p]·m_p ≤ constant`, with the demand it separates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearBound {
    /// `y`, one entry per flat place, all non-negative.
    pub weights: Vec<i128>,
    /// `y·M0`.
    pub constant: i128,
    /// `y·d`, what the violating markings need at least; strictly above `constant`.
    pub demand_value: i128,
}

/// The violation's demand: flat place index → the least count a violating
/// marking holds there. `None` when the property is not a reachability-safety
/// property, or names no place the net resolves (the verifier refuses those
/// before this runs).
pub fn violation_demand(flat: &FlatNet, property: &SmtProperty) -> Option<BTreeMap<usize, usize>> {
    let mut demand = BTreeMap::new();
    match property {
        SmtProperty::Unreachable { places } | SmtProperty::MutualExclusion { places } => {
            for name in places {
                if let Some(&pid) = flat.place_index.get(name) {
                    demand.insert(pid, 1);
                }
            }
        }
        SmtProperty::PlaceBound { place, bound } | SmtProperty::BranchPlaceBound { place, bound } => {
            if let Some(&pid) = flat.place_index.get(place) {
                demand.insert(pid, bound + 1);
            }
        }
        SmtProperty::DeadlockFree
        | SmtProperty::TerminatesAtSink
        | SmtProperty::JoinedOrDeadLettered { .. } => return None,
    }
    if demand.is_empty() { None } else { Some(demand) }
}

/// The places whose weight is pinned to zero: H1 (consume-all / reset) and H3'
/// (injected). `env_inject` is the resolved injection list
/// ([`crate::smt_encoder::resolve_env_injection`]).
pub fn zero_weight_places(flat: &FlatNet, env_inject: &[(usize, Option<usize>)]) -> BTreeSet<usize> {
    let mut zero: BTreeSet<usize> = nonlinear_places(flat)
        .iter()
        .enumerate()
        .filter(|&(_, &nonlinear)| nonlinear)
        .map(|(p, _)| p)
        .collect();
    zero.extend(env_inject.iter().map(|&(pid, _)| pid));
    zero
}

/// The `QF_LIA` script asking for a separating `y`, or `None` when the property
/// has no linear demand.
pub fn encode_linear_bound(
    flat: &FlatNet,
    initial_marking: &MarkingState,
    property: &SmtProperty,
    env_inject: &[(usize, Option<usize>)],
) -> Option<String> {
    let demand = violation_demand(flat, property)?;
    let p = flat.place_count;
    let zero = zero_weight_places(flat, env_inject);
    let mut lines: Vec<String> = Vec::new();
    lines.push("; Linear state-equation bound (VER-015): y >= 0 with y.C <= 0 on every".to_string());
    lines.push("; transition gives y.M <= y.M0 for every reachable M; sat = the violating".to_string());
    lines.push("; markings' demand exceeds that bound, so none is reachable.".to_string());
    lines.push("(set-logic QF_LIA)".to_string());
    for i in 0..p {
        lines.push(format!("(declare-const y{i} Int)"));
    }
    for i in 0..p {
        lines.push(format!("(assert (>= y{i} 0))"));
    }
    for i in &zero {
        lines.push(format!("(assert (= y{i} 0))"));
    }
    for ft in &flat.transitions {
        let terms: Vec<String> = (0..p)
            .filter_map(|i| {
                let c = ft.post[i] - ft.pre[i];
                (c != 0).then(|| term(c, &format!("y{i}")))
            })
            .collect();
        if !terms.is_empty() {
            lines.push(format!("(assert (<= {} 0))", sum(&terms)));
        }
    }
    let demand_terms: Vec<String> = demand
        .iter()
        .map(|(&i, &d)| term(d as i64, &format!("y{i}")))
        .collect();
    let mut init_terms = vec!["1".to_string()];
    for i in 0..p {
        let m0 = initial_marking.count(&flat.places[i]);
        if m0 > 0 {
            init_terms.push(term(m0 as i64, &format!("y{i}")));
        }
    }
    lines.push(format!("(assert (>= {} {}))", sum(&demand_terms), sum(&init_terms)));
    lines.push("(check-sat)".to_string());
    lines.push("(get-model)".to_string());
    Some(lines.join("\n"))
}

/// `c·v` as SMT-LIB text: a unit coefficient is the bare variable, `-1` is
/// `(- v)`, and a negative literal is written `(- k)`.
fn term(c: i64, v: &str) -> String {
    if c == 1 {
        v.to_string()
    } else if c == -1 {
        format!("(- {v})")
    } else if c > 0 {
        format!("(* {c} {v})")
    } else {
        format!("(* (- {}) {v})", -c)
    }
}

/// A lone term unwrapped, otherwise `(+ t1 t2 …)`.
fn sum(terms: &[String]) -> String {
    if terms.len() == 1 {
        terms[0].clone()
    } else {
        format!("(+ {})", terms.join(" "))
    }
}

/// The weighting in a `sat` reply's model: `y_p` per flat place, zero where the
/// model is silent. `None` when the reply defines no `y`, or a literal does not
/// fit `i128`.
pub fn decode_linear_bound(stdout: &str, place_count: usize) -> Option<Vec<i128>> {
    let mut y = vec![0i128; place_count];
    let mut seen = false;
    for def in extract_define_funs(stdout) {
        let Some((pid, value)) = parse_weight_definition(def.trim()) else {
            continue;
        };
        if pid >= place_count {
            continue;
        }
        y[pid] = value?;
        seen = true;
    }
    if seen { Some(y) } else { None }
}

/// Reads `(define-fun y<p> () Int <lit>)` with `<lit>` a natural literal `k` or
/// the negation form `(- k)` (z3 may break the line before the literal).
/// `None` when the definition is not a weight; `Some((p, None))` when it is one
/// whose literal overflows `i128`.
fn parse_weight_definition(def: &str) -> Option<(usize, Option<i128>)> {
    let body = def.strip_prefix("(define-fun")?.strip_suffix(')')?;
    let body = body.trim_start();
    let name_end = body.find(char::is_whitespace)?;
    let (name, rest) = body.split_at(name_end);
    let pid: usize = name.strip_prefix('y')?.parse().ok()?;
    let rest = rest.trim_start().strip_prefix("()")?;
    let rest = rest.trim_start().strip_prefix("Int")?;
    let lit = rest.trim();
    if lit.is_empty() {
        return None;
    }
    let (negative, digits) = match lit.strip_prefix('(') {
        Some(inner) => {
            let inner = inner.strip_suffix(')')?.trim();
            (true, inner.strip_prefix('-')?.trim())
        }
        None => (false, lit),
    };
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let magnitude: Option<i128> = digits.parse().ok();
    Some((pid, magnitude.map(|k| if negative { -k } else { k })))
}

/// Re-proves the bound in exact integer arithmetic: `y ≥ 0`, zero on every
/// H1/H3' place, `y·C ≤ 0` on every flat transition, and `y·d ≥ y·M0 + 1`.
/// Returns the bound when every check passes and `None` otherwise — an
/// arithmetic overflow included — so the verifier then continues to the
/// fixpoint query rather than trust the solver's model.
pub fn check_linear_bound_exact(
    flat: &FlatNet,
    initial_marking: &MarkingState,
    property: &SmtProperty,
    env_inject: &[(usize, Option<usize>)],
    y: &[i128],
) -> Option<LinearBound> {
    let demand = violation_demand(flat, property)?;
    let p = flat.place_count;
    if y.len() != p {
        return None;
    }
    let zero = zero_weight_places(flat, env_inject);
    for i in 0..p {
        if y[i] < 0 || (zero.contains(&i) && y[i] != 0) {
            return None;
        }
    }
    for ft in &flat.transitions {
        let mut delta: i128 = 0;
        for i in 0..p {
            if y[i] == 0 {
                continue;
            }
            let c = i128::from(ft.post[i] - ft.pre[i]);
            delta = delta.checked_add(y[i].checked_mul(c)?)?;
        }
        if delta > 0 {
            return None;
        }
    }
    let mut constant: i128 = 0;
    for i in 0..p {
        if y[i] != 0 {
            let m0 = initial_marking.count(&flat.places[i]) as i128;
            constant = constant.checked_add(y[i].checked_mul(m0)?)?;
        }
    }
    let mut demand_value: i128 = 0;
    for (&i, &d) in &demand {
        demand_value = demand_value.checked_add(y[i].checked_mul(d as i128)?)?;
    }
    if demand_value < constant.checked_add(1)? {
        return None;
    }
    Some(LinearBound {
        weights: y.to_vec(),
        constant,
        demand_value,
    })
}

/// `2*a + b <= 2` — the bound as the report prints it: weighted places in
/// place-index order, a unit weight unwritten, `0` when nothing is weighted.
pub fn format_linear_bound(flat: &FlatNet, bound: &LinearBound) -> String {
    let parts: Vec<String> = bound
        .weights
        .iter()
        .enumerate()
        .filter(|&(_, &w)| w != 0)
        .map(|(i, &w)| weighted(w, &flat.places[i]))
        .collect();
    format!("{} <= {}", join_or_zero(&parts), bound.constant)
}

/// `halt + ra + rb >= 3` — the violation's weighted demand as the report prints
/// it: `y_p·d_p` per demanded place in place-index order, zero weights skipped.
pub fn format_linear_demand(flat: &FlatNet, property: &SmtProperty, bound: &LinearBound) -> String {
    let demand = violation_demand(flat, property).unwrap_or_default();
    let parts: Vec<String> = demand
        .iter()
        .filter_map(|(&i, &d)| {
            let w = bound.weights[i].checked_mul(d as i128)?;
            (w != 0).then(|| weighted(w, &flat.places[i]))
        })
        .collect();
    format!("{} >= {}", join_or_zero(&parts), bound.demand_value)
}

fn weighted(w: i128, name: &str) -> String {
    if w == 1 { name.to_string() } else { format!("{w}*{name}") }
}

fn join_or_zero(parts: &[String]) -> String {
    if parts.is_empty() { "0".to_string() } else { parts.join(" + ") }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marking_state::MarkingStateBuilder;
    use crate::net_flattener::flatten;
    use libpetri_core::action::fork;
    use libpetri_core::input::{all, one};
    use libpetri_core::output::{and, out_place, xor};
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    /// A fork that may halt instead: p0(1) → f → AND(a, b) | halt; a → ga → ra;
    /// b → gb → rb; join: ra + rb → done. `{ra, rb, halt}` is unreachable — a halt
    /// consumes the token that would have fed both arms — and no EQUALITY law says
    /// so (the halt branch turns 2 units into 1), so the null-space basis cannot
    /// exclude it. The decreasing law 2·p0 + a + b + ra + rb + halt + 2·done ≤ 2
    /// does: the target needs 3. Places in flat order: a, b, done, halt, p0, ra, rb.
    fn fork_or_halt() -> (FlatNet, MarkingState) {
        let p0 = Place::<i32>::new("p0");
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let ra = Place::<i32>::new("ra");
        let rb = Place::<i32>::new("rb");
        let halt = Place::<i32>::new("halt");
        let done = Place::<i32>::new("done");
        let f = Transition::builder("f")
            .input(one(&p0))
            .output(xor(vec![and(vec![out_place(&a), out_place(&b)]), out_place(&halt)]))
            .action(fork())
            .build();
        let ga = Transition::builder("ga").input(one(&a)).output(out_place(&ra)).action(fork()).build();
        let gb = Transition::builder("gb").input(one(&b)).output(out_place(&rb)).action(fork()).build();
        let join = Transition::builder("join")
            .input(one(&ra))
            .input(one(&rb))
            .output(out_place(&done))
            .action(fork())
            .build();
        let net = PetriNet::builder("forkOrHalt").transitions([f, ga, gb, join]).build();
        (flatten(&net), MarkingStateBuilder::new().tokens("p0", 1).build())
    }

    fn targets() -> SmtProperty {
        SmtProperty::unreachable(vec!["halt".into(), "ra".into(), "rb".into()])
    }

    #[test]
    fn no_demand_for_the_quiescence_properties() {
        let (flat, m0) = fork_or_halt();
        for prop in [
            SmtProperty::DeadlockFree,
            SmtProperty::TerminatesAtSink,
            SmtProperty::joined_or_dead_lettered("a"),
        ] {
            assert_eq!(violation_demand(&flat, &prop), None);
            assert_eq!(encode_linear_bound(&flat, &m0, &prop, &[]), None);
        }
        // A property naming only unresolved places has no demand either.
        assert_eq!(
            violation_demand(&flat, &SmtProperty::unreachable(vec!["ghost".into()])),
            None
        );
    }

    #[test]
    fn encodes_y_non_negative_one_row_per_flat_transition_and_the_demand() {
        let (flat, m0) = fork_or_halt();
        let idx = |n: &str| flat.place_index[n];
        let script = encode_linear_bound(&flat, &m0, &targets(), &[]).unwrap();
        assert!(script.contains("(set-logic QF_LIA)"));
        for i in 0..flat.place_count {
            assert!(script.contains(&format!("(declare-const y{i} Int)")));
            assert!(script.contains(&format!("(assert (>= y{i} 0))")));
        }
        // f's halt branch: -p0 + halt, places in flat-index order.
        assert_eq!((idx("halt"), idx("p0")), (3, 4));
        assert!(script.contains("(assert (<= (+ y3 (- y4)) 0))"), "{script}");
        // Demand: halt + ra + rb >= 1 + p0.
        assert!(script.contains("(assert (>= (+ y3 y5 y6) (+ 1 y4)))"), "{script}");
        assert!(script.ends_with("(check-sat)\n(get-model)"));
        assert!(script.starts_with("; Linear state-equation bound (VER-015): y >= 0 with y.C <= 0 on every\n"));
    }

    #[test]
    fn pins_consume_all_and_injected_places_to_zero_weight() {
        let q = Place::<i32>::new("q");
        let r = Place::<i32>::new("r");
        let t = Transition::builder("t").input(all(&q)).output(out_place(&r)).action(fork()).build();
        let flat = flatten(&PetriNet::builder("drain").transition(t).build());
        let m0 = MarkingStateBuilder::new().tokens("q", 2).build();
        let prop = SmtProperty::place_bound("r", 1);
        let script = encode_linear_bound(&flat, &m0, &prop, &[]).unwrap();
        assert!(script.contains(&format!("(assert (= y{} 0))", flat.place_index["q"])));
        // A weighting that leans on the drained place is rejected by the exact check.
        let mut y = vec![0i128; flat.place_count];
        y[flat.place_index["q"]] = 1;
        y[flat.place_index["r"]] = 1;
        assert_eq!(check_linear_bound_exact(&flat, &m0, &prop, &[], &y), None);
        // An injected place is pinned the same way (H3').
        let injected = encode_linear_bound(&flat, &m0, &prop, &[(flat.place_index["r"], None)]).unwrap();
        assert!(injected.contains(&format!("(assert (= y{} 0))", flat.place_index["r"])));
    }

    #[test]
    fn decodes_a_model_and_re_checks_it_exactly() {
        let (flat, m0) = fork_or_halt();
        let idx = |n: &str| flat.place_index[n];
        let model = format!(
            "sat\n(\n  (define-fun y{} () Int\n    2)\n  (define-fun y{} () Int 1)\n  (define-fun y{} () Int 1)\n  \
             (define-fun y{} () Int 1)\n  (define-fun y{} () Int 1)\n  (define-fun y{} () Int 1)\n  \
             (define-fun y{} () Int 2)\n)",
            idx("p0"),
            idx("a"),
            idx("b"),
            idx("ra"),
            idx("rb"),
            idx("halt"),
            idx("done")
        );
        let y = decode_linear_bound(&model, flat.place_count).unwrap();
        assert_eq!(y[idx("p0")], 2);
        let bound = check_linear_bound_exact(&flat, &m0, &targets(), &[], &y).expect("a genuine bound");
        assert_eq!(bound.constant, 2);
        assert_eq!(bound.demand_value, 3);
        assert_eq!(format_linear_bound(&flat, &bound), "a + b + 2*done + halt + 2*p0 + ra + rb <= 2");
        assert_eq!(format_linear_demand(&flat, &targets(), &bound), "halt + ra + rb >= 3");
        // A weighting that is not decreasing under the fork is rejected.
        let mut bad = y.clone();
        bad[idx("p0")] = 1;
        assert_eq!(check_linear_bound_exact(&flat, &m0, &targets(), &[], &bad), None);
        // A weighting whose demand does not exceed the constant is rejected.
        let short = SmtProperty::unreachable(vec!["halt".into(), "ra".into()]);
        assert_eq!(check_linear_bound_exact(&flat, &m0, &short, &[], &y), None);
        // A negative weight is rejected; so is a vector of the wrong length.
        let mut negative = y.clone();
        negative[idx("a")] = -1;
        assert_eq!(check_linear_bound_exact(&flat, &m0, &targets(), &[], &negative), None);
        assert_eq!(check_linear_bound_exact(&flat, &m0, &targets(), &[], &y[1..]), None);
        // Negative literals decode; a silent model decodes to nothing.
        assert_eq!(decode_linear_bound("sat\n(\n  (define-fun y0 () Int\n    (- 3))\n)", 1), Some(vec![-3]));
        assert_eq!(decode_linear_bound("sat\n(\n)", 1), None);
        // Other definitions and out-of-range indices are ignored.
        assert_eq!(
            decode_linear_bound("sat\n(\n  (define-fun z0 () Int 4)\n  (define-fun y9 () Int 4)\n  (define-fun y0 () Int 7)\n)", 2),
            Some(vec![7, 0])
        );
    }

    #[test]
    fn exact_re_check_treats_overflow_as_failure() {
        // p0 → t → p1: the row is -y0 + y1 and the constant is y0·M0.
        let p0 = Place::<i32>::new("p0");
        let p1 = Place::<i32>::new("p1");
        let t = Transition::builder("t").input(one(&p0)).output(out_place(&p1)).action(fork()).build();
        let flat = flatten(&PetriNet::builder("chain").transition(t).build());
        let m0 = MarkingStateBuilder::new().tokens("p0", 2).build();
        let prop = SmtProperty::place_bound("p1", 2);
        // A genuine bound with small weights passes.
        assert!(check_linear_bound_exact(&flat, &m0, &prop, &[], &[1, 1]).is_some());
        // y0·M0 = i128::MAX · 2 overflows: no bound, never a wrapped constant.
        assert_eq!(check_linear_bound_exact(&flat, &m0, &prop, &[], &[i128::MAX, i128::MAX]), None);
        // A literal the model prints past i128 fails to decode.
        assert_eq!(
            decode_linear_bound("sat\n(\n  (define-fun y0 () Int 170141183460469231731687303715884105728)\n)", 1),
            None
        );
    }
}
