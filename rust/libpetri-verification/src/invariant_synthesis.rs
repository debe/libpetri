//! Inductive-inequality refinement for the state-equation phase ([VER-018]).
//!
//! The marking equation knows how often each transition fired, never in what order,
//! and it ignores the guards that impose the order. The typical spurious candidate on
//! a workflow net is a join that *skipped* — a transition inhibited by `hasdata` —
//! after the data token arrived: every count balances, and only the inhibitor rules
//! the run out. A trap cannot say that either. This refinement looks for one linear
//! inequality `a·M ≤ b` that
//!
//! 1. holds at `M0`,
//! 2. is kept by every step of the **exact** step relation — input weights, read and
//!    inhibitor guards, consume-all and reset clearing included, which is where it
//!    gets its power over the equation — and
//! 3. excludes the candidate: `a·M* ≥ b + 1`.
//!
//! For the join above that is `hasdata ≤ ready_0 + ready_1`: arrivals raise both
//! sides together, `skip` fires only when `hasdata` is empty, and `start` clears it.
//!
//! Condition 2 is the Farkas form of consecution (Colón, Sankaranarayanan and Sipma,
//! "Linear invariant generation using non-linear constraint solving", CAV 2003) with
//! the invariant's own multiplier restricted to `λ_t ∈ {0, 1}` per transition, which
//! keeps the query linear. Write `l_p = max(pre_p, 1 if p is read)` for the guard's
//! lower bound; an inhibited place is exactly `0` before the step.
//!
//! - `λ_t = 1`, the step keeps the bound: `a·M' − a·M ≤ 0` for every enabled `M`. A
//!   place `t` does not clear contributes its column `C_p`; a place it clears
//!   contributes `post_p − M_p ≤ post_p − l_p`, provided `a_p ≥ 0` (on an inhibited
//!   cleared place `M_p = 0`, so `post_p` and no sign condition).
//! - `λ_t = 0`, the guard restores the bound on its own: `a_p ≤ 0` on every place `t`
//!   neither clears nor inhibits, so `a·M'` is largest at `M = l`, and that value is
//!   `≤ b`.
//!
//! An environment injection must keep the bound (`a_p ≤ 0` on an injected place). The
//! query is one `QF_LIA` script with integer weights in `[−bound, bound]`.
//!
//! The weights [`encode_inductive_inequality`] returns are re-checked in exact integer
//! arithmetic ([`check_inductive_exact`]) before they are used. Those of
//! [`encode_relative_inequality`] are not, and cannot be: that bound holds only relative
//! to the marking equation, so the exact re-check would reject it. It rests on the
//! certificate check, which re-proves the whole refinement against the raw step relation
//! before any verdict rests on it.
//!
//! Environment injection is passed in resolved (`env_inject`, as
//! [`crate::smt_encoder::resolve_env_injection`] returns it) rather than read off the
//! flat net, as in [`crate::state_equation_query`]. The injected places are emitted in
//! place-index order whatever order that list has, so the scripts stay byte-identical
//! to the TypeScript, Java and Python ports ([VER-013] AC1).

use std::collections::BTreeSet;

use crate::net_flattener::{FlatNet, FlatTransition};
use crate::p_invariant::nonlinear_places;
use crate::smt_encoder::conjoin;
use crate::smt_verifier::extract_define_funs;
use crate::state_equation_query::{InequalityOrigin, MarkingInequality};

/// The default magnitude bound on the weights the query may choose.
pub const DEFAULT_WEIGHT_BOUND: i64 = 8;

/// The arcs of one flat transition per place, widened to `i128` so every difference the
/// encoders and the exact re-check take of them is exact.
struct StepParts {
    /// A consume-all input or a reset arc empties the place.
    cleared: Vec<bool>,
    inhibited: Vec<bool>,
    /// `l_p = max(pre_p, 1 if p is read)`: the least the guard lets the place hold.
    lower: Vec<i128>,
    pre: Vec<i128>,
    post: Vec<i128>,
}

/// The parts of `ft`, or `None` when it can never fire (it inhibits a place it needs).
fn step_parts(ft: &FlatTransition, place_count: usize) -> Option<StepParts> {
    let inhibited = mask(&ft.inhibitor_places, place_count);
    let read = mask(&ft.read_places, place_count);
    let mut cleared = mask(&ft.reset_places, place_count);
    // Rust's flat transition lists the consume-all places; TypeScript's flags them per place.
    for &p in &ft.consume_all {
        if p < place_count {
            cleared[p] = true;
        }
    }
    let pre: Vec<i128> = (0..place_count).map(|p| arc(&ft.pre, p)).collect();
    let post: Vec<i128> = (0..place_count).map(|p| arc(&ft.post, p)).collect();
    if (0..place_count).any(|p| inhibited[p] && (pre[p] > 0 || read[p])) {
        return None;
    }
    let lower = (0..place_count)
        .map(|p| pre[p].max(if read[p] { 1 } else { 0 }))
        .collect();
    Some(StepParts { cleared, inhibited, lower, pre, post })
}

/// The two ways a transition can keep `a·M ≤ b`, as coefficient rows over the places.
struct StepShape {
    /// `λ = 1`: `a_p ≥ 0` on these places, and `Σ keep[p]·a_p ≤ 0`.
    keep_non_negative: Vec<usize>,
    keep: Vec<i128>,
    /// `λ = 0`: `a_p ≤ 0` on every place outside `restore_free`, and `Σ restore[p]·a_p ≤ b`.
    restore_free: Vec<usize>,
    restore: Vec<i128>,
}

fn step_shape(parts: &StepParts) -> StepShape {
    let place_count = parts.pre.len();
    let mut keep = vec![0i128; place_count];
    let mut restore = vec![0i128; place_count];
    let mut keep_non_negative = Vec::new();
    let mut restore_free = Vec::new();
    for p in 0..place_count {
        let (pre, post, lower) = (parts.pre[p], parts.post[p], parts.lower[p]);
        if parts.cleared[p] {
            if parts.inhibited[p] {
                keep[p] = post;
            } else {
                keep[p] = post - lower;
                keep_non_negative.push(p);
            }
            restore[p] = post;
            restore_free.push(p);
        } else if parts.inhibited[p] {
            keep[p] = post - pre;
            restore[p] = post - pre;
            restore_free.push(p);
        } else {
            keep[p] = post - pre;
            restore[p] = post - pre + lower;
        }
    }
    StepShape { keep_non_negative, keep, restore_free, restore }
}

/// The `QF_LIA` script asking for weights `a` and a bound `b` that satisfy conditions
/// 1–3 of the module description for the given candidate marking. `u_p ≥ max(a_p, 0)`
/// carries each weight's positive part, so the `λ = 0` sign condition of a transition
/// is one equation (`Σ_p u_p = Σ_{p free} u_p`) rather than one atom per place.
pub fn encode_inductive_inequality(
    flat: &FlatNet,
    initial: &[i64],
    candidate: &[i64],
    env_inject: &[(usize, Option<usize>)],
    weight_bound: i64,
) -> String {
    let place_count = flat.place_count;
    let a = |p: usize| format!("a{p}");
    let u = |p: usize| format!("u{p}");
    let mut lines = vec![
        "; Inductive-inequality refinement (VER-018): a.M <= b holding at M0, kept by every"
            .to_string(),
        "; step of the exact step relation (guards and clearing included), and excluding"
            .to_string(),
        "; the candidate marking.".to_string(),
        "(set-logic QF_LIA)".to_string(),
    ];
    declare_weights(&mut lines, place_count, weight_bound, |lines| {
        lines.push("(declare-const upos Int)".to_string());
    });
    let positive: Vec<String> = (0..place_count).map(u).collect();
    lines.push(format!("(assert (= upos {}))", sum(&positive, "0")));
    lines.push(format!("(assert (<= {} b))", linear(initial, a)));
    lines.push(format!("(assert (>= {} (+ b 1)))", linear(candidate, a)));
    for ft in &flat.transitions {
        let Some(parts) = step_parts(ft, place_count) else {
            continue;
        };
        let shape = step_shape(&parts);
        let mut keeps: Vec<String> = shape
            .keep_non_negative
            .iter()
            .map(|&p| format!("(>= {} 0)", a(p)))
            .collect();
        keeps.push(format!("(<= {} 0)", linear(&shape.keep, a)));
        let free: Vec<String> = shape.restore_free.iter().map(|&p| u(p)).collect();
        let restores = [
            format!("(= upos {})", sum(&free, "0")),
            format!("(<= {} b)", linear(&shape.restore, a)),
        ];
        lines.push(format!("(assert (or {} {}))", conjoin(&keeps), conjoin(&restores)));
    }
    for p in injected_places(env_inject) {
        lines.push(format!("(assert (<= {} 0))", a(p)));
    }
    // The sparsest inequality: it prints as the structural fact (`hasdata <= ready_0 +
    // ready_1`) rather than an arbitrary combination, and it excludes more candidates.
    lines.push(format!("(minimize {})", magnitude_objective(place_count)));
    lines.push("(check-sat)".to_string());
    lines.push("(get-model)".to_string());
    lines.join("\n")
}

/// The query of [`encode_inductive_inequality`] with the marking equation as a
/// premise of every step: the inequality need only be kept by steps from markings the
/// equation admits. A bound like `q + 3·out ≤ 3` on a queue that is bundled once a
/// signal arrives needs it — `produce` keeps the bound only because `q ≤ 2` whenever
/// `budget ≥ 1`, and that is the equation's `q + budget ≤ 3`.
///
/// By Farkas, the premise contributes to transition `t`'s consecution one linear
/// consequence of the equation: a weighting `η^t` with `η^t·C_j ≤ 0` on every column
/// `j`, non-negative on a place whose row is an upper bound and absent on an injected
/// place, so that `η^t·M ≤ η^t·M0` holds wherever the equation does. With
/// `κ_t = Σ_{p not cleared} a_p·C_p + Σ_{p cleared} a_p·post_p` the two cases read:
///
/// - `λ_t = 1`: `η^t_p ≥ 0` on a place `t` neither clears nor inhibits, `a_p + η^t_p ≥ 0`
///   on a place it clears, and `κ_t ≤ −η^t·M0 + Σ_{p not inhibited} ν_p·l_p`, with
///   `ν_p = η^t_p` (`a_p + η^t_p` on a cleared place).
/// - `λ_t = 0`: `a_p ≤ η^t_p` on a place `t` neither clears nor inhibits, `η^t_p ≥ 0` on
///   a place it clears, and `κ_t − b ≤ −η^t·M0 + Σ ν_p·l_p`, with `ν_p = η^t_p − a_p`
///   (`η^t_p` on a cleared place).
///
/// With `η^t = 0` these are the conditions of [`encode_inductive_inequality`]. The
/// query carries one weighting per transition, so the phase asks it only when that
/// one found nothing. The weightings are real; the inequality's weights stay integers.
/// The certificate check re-proves the result as part of `SE ∧ refinements`.
pub fn encode_relative_inequality(
    flat: &FlatNet,
    initial: &[i64],
    candidate: &[i64],
    env_inject: &[(usize, Option<usize>)],
    weight_bound: i64,
) -> String {
    let place_count = flat.place_count;
    let upper = nonlinear_places(flat);
    let injected = injected_places(env_inject);
    let rows: Vec<usize> = (0..place_count).filter(|p| !injected.contains(p)).collect();
    let a = |p: usize| format!("a{p}");
    let ra = |p: usize| format!("(to_real a{p})");
    let mut lines = vec![
        "; Inductive-inequality refinement relative to the marking equation (VER-018):"
            .to_string(),
        "; a.M <= b holding at M0, kept by every step from a marking the equation admits"
            .to_string(),
        "; (one Farkas weighting e<t>_<p> of the equation per transition), and excluding"
            .to_string(),
        "; the candidate marking.".to_string(),
        "(set-logic QF_LIRA)".to_string(),
    ];
    declare_weights(&mut lines, place_count, weight_bound, |_| {});
    lines.push(format!("(assert (<= {} b))", linear(initial, a)));
    lines.push(format!("(assert (>= {} (+ b 1)))", linear(candidate, a)));
    for &p in &injected {
        lines.push(format!("(assert (<= {} 0))", a(p)));
    }
    // Each column of the equation over its rows, sparse: the same for every weighting, and
    // only the variable names change from one transition's weighting to the next.
    let columns: Vec<Vec<(usize, i128)>> = flat
        .transitions
        .iter()
        .map(|col| {
            rows.iter()
                .map(|&p| (p, arc(&col.post, p) - arc(&col.pre, p)))
                .filter(|&(_, c)| c != 0)
                .collect()
        })
        .collect();
    for (t, ft) in flat.transitions.iter().enumerate() {
        let Some(parts) = step_parts(ft, place_count) else {
            continue;
        };
        let e = |p: usize| format!("e{t}_{p}");
        for &p in &rows {
            lines.push(format!("(declare-const {} Real)", e(p)));
        }
        for &p in &rows {
            if upper[p] {
                lines.push(format!("(assert (>= {} 0))", e(p)));
            }
        }
        for column in &columns {
            if column.is_empty() {
                continue;
            }
            let terms: Vec<String> = column.iter().map(|&(p, c)| scaled(c, &e(p))).collect();
            lines.push(format!("(assert (<= {} 0.0))", sum(&terms, "0")));
        }
        // κ_t over the weights, and −η·M0.
        let mut kappa: Vec<String> = Vec::new();
        for p in 0..place_count {
            let c = if parts.cleared[p] { parts.post[p] } else { parts.post[p] - parts.pre[p] };
            if c != 0 {
                kappa.push(scaled(c, &ra(p)));
            }
        }
        let mut eta_m0: Vec<String> = Vec::new();
        for &p in &rows {
            let m0 = i128::from(initial.get(p).copied().unwrap_or(0));
            if m0 != 0 {
                eta_m0.push(scaled(-m0, &e(p)));
            }
        }
        let mut keep: Vec<String> = Vec::new();
        let mut keep_rhs = eta_m0.clone();
        let mut restore: Vec<String> = Vec::new();
        let mut restore_rhs = eta_m0;
        for p in 0..place_count {
            if parts.inhibited[p] {
                continue;
            }
            let l = parts.lower[p];
            let eta = if injected.contains(&p) { "0.0".to_string() } else { e(p) };
            if parts.cleared[p] {
                keep.push(format!("(>= (+ {} {eta}) 0.0)", ra(p)));
                restore.push(format!("(>= {eta} 0.0)"));
                if l != 0 {
                    keep_rhs.push(scaled(l, &format!("(+ {} {eta})", ra(p))));
                    restore_rhs.push(scaled(l, &eta));
                }
            } else {
                keep.push(format!("(>= {eta} 0.0)"));
                restore.push(format!("(<= {} {eta})", ra(p)));
                if l != 0 {
                    keep_rhs.push(scaled(l, &eta));
                    restore_rhs.push(scaled(l, &format!("(- {eta} {})", ra(p))));
                }
            }
        }
        let kappa = sum(&kappa, "0.0");
        keep.push(format!("(<= {kappa} {})", sum(&keep_rhs, "0.0")));
        restore.push(format!("(<= (- {kappa} (to_real b)) {})", sum(&restore_rhs, "0.0")));
        lines.push(format!("(assert (or {} {}))", conjoin(&keep), conjoin(&restore)));
    }
    lines.push(format!("(minimize {})", magnitude_objective(place_count)));
    lines.push("(check-sat)".to_string());
    lines.push("(get-model)".to_string());
    lines.join("\n")
}

/// The declarations both queries open with: `a`, `u`, `w` per place, `b`, whatever
/// `extra` adds, then the weight bound and the positive and negative parts per place.
fn declare_weights(
    lines: &mut Vec<String>,
    place_count: usize,
    weight_bound: i64,
    extra: impl FnOnce(&mut Vec<String>),
) {
    for v in ['a', 'u', 'w'] {
        for p in 0..place_count {
            lines.push(format!("(declare-const {v}{p} Int)"));
        }
    }
    lines.push("(declare-const b Int)".to_string());
    extra(lines);
    for p in 0..place_count {
        lines.push(format!(
            "(assert (and (>= a{p} (- {weight_bound})) (<= a{p} {weight_bound})))"
        ));
        lines.push(format!("(assert (and (>= u{p} 0) (>= u{p} a{p})))"));
        lines.push(format!("(assert (and (>= w{p} 0) (>= w{p} (- a{p}))))"));
    }
}

/// `Σ_p u_p + w_p`, interleaved per place: the total magnitude of the weights.
fn magnitude_objective(place_count: usize) -> String {
    let terms: Vec<String> = (0..place_count)
        .flat_map(|p| [format!("u{p}"), format!("w{p}")])
        .collect();
    sum(&terms, "0")
}

/// The injected places in place-index order, once each. TypeScript sorts its resolved
/// injection list by index; a `BTreeSet` gives the same order whatever order the caller's
/// list has.
fn injected_places(env_inject: &[(usize, Option<usize>)]) -> BTreeSet<usize> {
    env_inject.iter().map(|&(pid, _)| pid).collect()
}

/// `c·x` for a real-valued `x`, `c` an integer.
fn scaled(c: i128, x: &str) -> String {
    if c == 1 {
        return x.to_string();
    }
    if c == -1 {
        return format!("(- {x})");
    }
    if c > 0 {
        format!("(* {c}.0 {x})")
    } else {
        format!("(* (- {}.0) {x})", -c)
    }
}

/// The inequality in a `sat` reply's model; `None` when the model defines no bound `b`,
/// or when a literal does not fit `i128` (the phase then reports the model undecodable
/// rather than refine against a truncated inequality). A place the model is silent on
/// weighs `0`. The origin is always [`InequalityOrigin::Inductive`]: both queries share
/// this decoder, and the phase relabels the relative one.
pub fn decode_inductive_inequality(stdout: &str, place_count: usize) -> Option<MarkingInequality> {
    let mut weights = vec![0i128; place_count];
    let mut constant: Option<i128> = None;
    for def in extract_define_funs(stdout) {
        let Some((name, value)) = parse_inequality_definition(def.trim()) else {
            continue;
        };
        match name {
            InequalityVar::Bound => constant = Some(value?),
            InequalityVar::Weight(p) if p < place_count => weights[p] = value?,
            InequalityVar::Weight(_) => continue,
        }
    }
    constant.map(|constant| MarkingInequality {
        weights,
        constant,
        origin: InequalityOrigin::Inductive,
    })
}

/// Which variable of the query a model definition assigns.
enum InequalityVar {
    Weight(usize),
    Bound,
}

/// Reads `(define-fun a<p> () Int <lit>)` or `(define-fun b () Int <lit>)` with `<lit>`
/// a natural literal `k` or the negation form `(- k)` (z3 may break the line before the
/// literal). `None` when the definition is neither — `u<p>`, `w<p>`, `upos` and the real
/// weightings `e<t>_<p>` included; `Some((_, None))` when the literal overflows `i128`.
fn parse_inequality_definition(def: &str) -> Option<(InequalityVar, Option<i128>)> {
    let body = def.strip_prefix("(define-fun")?.strip_suffix(')')?;
    let body = body.trim_start();
    let name_end = body.find(char::is_whitespace)?;
    let (name, rest) = body.split_at(name_end);
    let var = if name == "b" {
        InequalityVar::Bound
    } else {
        let digits = name.strip_prefix('a')?;
        // `parse` would take `a+3`; the index is digits only, as z3 prints it.
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        InequalityVar::Weight(digits.parse().ok()?)
    };
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
    Some((var, magnitude.map(|k| if negative { -k } else { k })))
}

/// Re-proves conditions 1 and 2 of the module description in exact integer
/// arithmetic: the inequality holds at `M0`, every injected place has a weight `≤ 0`,
/// and every transition that can fire either keeps the bound (`λ = 1`) or restores it
/// from its guard (`λ = 0`). Condition 3 is not needed for soundness.
///
/// An overflow is a failed check, never a pass: a `λ = 1` sum that overflows is simply
/// not taken as keeping the bound, and a `λ = 0` sum that overflows rejects the
/// inequality, since neither case was then shown to hold.
pub fn check_inductive_exact(
    flat: &FlatNet,
    initial: &[i64],
    env_inject: &[(usize, Option<usize>)],
    inequality: &MarkingInequality,
) -> bool {
    let place_count = flat.place_count;
    let weights = &inequality.weights;
    if weights.len() != place_count {
        return false;
    }
    let m0: Vec<i128> = (0..place_count)
        .map(|p| i128::from(initial.get(p).copied().unwrap_or(0)))
        .collect();
    if !dot(weights, &m0).is_some_and(|v| v <= inequality.constant) {
        return false;
    }
    for &(pid, _) in env_inject {
        if weights.get(pid).is_some_and(|&w| w > 0) {
            return false;
        }
    }
    for ft in &flat.transitions {
        let Some(parts) = step_parts(ft, place_count) else {
            continue;
        };
        let shape = step_shape(&parts);
        let keeps = shape.keep_non_negative.iter().all(|&p| weights[p] >= 0)
            && dot(weights, &shape.keep).is_some_and(|v| v <= 0);
        if keeps {
            continue;
        }
        let free = mask(&shape.restore_free, place_count);
        let signs = weights.iter().enumerate().all(|(p, &w)| w <= 0 || free[p]);
        if !signs || !dot(weights, &shape.restore).is_some_and(|v| v <= inequality.constant) {
            return false;
        }
    }
    true
}

/// `Σ_p weights[p]·values[p]` in checked arithmetic; `None` on overflow.
fn dot(weights: &[i128], values: &[i128]) -> Option<i128> {
    let mut s: i128 = 0;
    for (p, &w) in weights.iter().enumerate() {
        let v = values.get(p).copied().unwrap_or(0);
        if w != 0 && v != 0 {
            s = s.checked_add(w.checked_mul(v)?)?;
        }
    }
    Some(s)
}

/// `Σ coeffs[p]·var(p)` over the non-zero coefficients, `0` when there are none.
fn linear<C: Copy + Into<i128>>(coeffs: &[C], var: impl Fn(usize) -> String) -> String {
    let mut terms: Vec<String> = Vec::new();
    for (p, &c) in coeffs.iter().enumerate() {
        let c: i128 = c.into();
        if c == 0 {
            continue;
        }
        let v = var(p);
        terms.push(if c == 1 {
            v
        } else if c == -1 {
            format!("(- {v})")
        } else if c > 0 {
            format!("(* {c} {v})")
        } else {
            format!("(* (- {}) {v})", -c)
        });
    }
    sum(&terms, "0")
}

/// A lone term unwrapped, otherwise `(+ t1 t2 …)`; `zero` when there are none.
fn sum(terms: &[String], zero: &str) -> String {
    match terms {
        [] => zero.to_string(),
        [single] => single.clone(),
        _ => format!("(+ {})", terms.join(" ")),
    }
}

fn mask(places: &[usize], place_count: usize) -> Vec<bool> {
    let mut out = vec![false; place_count];
    for &p in places {
        if p < place_count {
            out[p] = true;
        }
    }
    out
}

fn arc(vector: &[i64], p: usize) -> i128 {
    i128::from(vector.get(p).copied().unwrap_or(0))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::net_flattener::flatten;
    use crate::smt_verifier::z3_available;
    use crate::state_equation_query::format_inequality;
    use crate::z3_process::{classify_first_line, Z3Solver};
    use libpetri_core::action::fork;
    use libpetri_core::arc::{inhibitor, read, reset};
    use libpetri_core::input::{all, at_least, exactly, one};
    use libpetri_core::output::{and, out_place, xor};
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    /// The join of a compiled workflow ([VER-018] test derivation): `route` sends data
    /// down one arm and an empty marker down the other; a data arm writes `hasdata` with
    /// its `ready`, an empty arm `ready` alone; `mergeStart` takes both readies with
    /// `all(hasdata)`, `mergeSkip` both readies under `inhibitor(hasdata)`. Places in flat
    /// order: aData, aEmpty, bData, bEmpty, done, hasdata, ready0, ready1, skipped, start.
    fn join_with_skip() -> FlatNet {
        let start = Place::<i32>::new("start");
        let a_data = Place::<i32>::new("aData");
        let a_empty = Place::<i32>::new("aEmpty");
        let b_data = Place::<i32>::new("bData");
        let b_empty = Place::<i32>::new("bEmpty");
        let hasdata = Place::<i32>::new("hasdata");
        let ready0 = Place::<i32>::new("ready0");
        let ready1 = Place::<i32>::new("ready1");
        let done = Place::<i32>::new("done");
        let skipped = Place::<i32>::new("skipped");
        let t = |name: &str| Transition::builder(name).action(fork());
        let net = PetriNet::builder("joinWithSkip")
            .transitions([
                t("route")
                    .input(one(&start))
                    .output(xor(vec![
                        and(vec![out_place(&a_data), out_place(&b_empty)]),
                        and(vec![out_place(&a_empty), out_place(&b_data)]),
                    ]))
                    .build(),
                t("armAData")
                    .input(one(&a_data))
                    .output(and(vec![out_place(&hasdata), out_place(&ready0)]))
                    .build(),
                t("armAEmpty").input(one(&a_empty)).output(out_place(&ready0)).build(),
                t("armBData")
                    .input(one(&b_data))
                    .output(and(vec![out_place(&hasdata), out_place(&ready1)]))
                    .build(),
                t("armBEmpty").input(one(&b_empty)).output(out_place(&ready1)).build(),
                t("mergeStart")
                    .input(one(&ready0))
                    .input(one(&ready1))
                    .input(all(&hasdata))
                    .output(out_place(&done))
                    .build(),
                t("mergeSkip")
                    .input(one(&ready0))
                    .input(one(&ready1))
                    .inhibitor(inhibitor(&hasdata))
                    .output(out_place(&skipped))
                    .build(),
            ])
            .build();
        flatten(&net)
    }

    /// The queue-and-bundle net: `produce: budget → q` inhibited by `s` and `out`,
    /// `signal: src → s`, `bundle: all(q) + s → out`, `bundleEmpty: s, inhibitor(q) → out`.
    /// `M0 = {budget: 3, src: 1}`. Places in flat order: budget, out, q, s, src.
    fn queue_and_bundle() -> FlatNet {
        let budget = Place::<i32>::new("budget");
        let q = Place::<i32>::new("q");
        let src = Place::<i32>::new("src");
        let s = Place::<i32>::new("s");
        let out = Place::<i32>::new("out");
        let t = |name: &str| Transition::builder(name).action(fork());
        let net = PetriNet::builder("queue3")
            .transitions([
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
            ])
            .build();
        flatten(&net)
    }

    /// `fill: start → q`, `gate: sig + gateOpen → done`, with `sig` the place the
    /// environment injects into. Places in flat order: done, gateOpen, q, sig, start.
    fn gated() -> (FlatNet, Vec<(usize, Option<usize>)>) {
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
        let env_inject = vec![(flat.place_index["sig"], None)];
        (flat, env_inject)
    }

    /// Every clearing and guard shape at once: `t1` resets the place it inhibits and
    /// reads `gate`, `t2` takes two of `x` and reads `gate`, `t3` takes `at_least(2, z)`
    /// and resets `x`, and `t4` reads the place it inhibits, so it can never fire.
    /// Places in flat order: gate, p, r, x, y, z.
    fn clearing() -> FlatNet {
        let p = Place::<i32>::new("p");
        let gate = Place::<i32>::new("gate");
        let r = Place::<i32>::new("r");
        let x = Place::<i32>::new("x");
        let y = Place::<i32>::new("y");
        let z = Place::<i32>::new("z");
        let t = |name: &str| Transition::builder(name).action(fork());
        let net = PetriNet::builder("clearing")
            .transitions([
                t("t1")
                    .input(one(&p))
                    .read(read(&gate))
                    .reset(reset(&r))
                    .inhibitor(inhibitor(&r))
                    .output(out_place(&z))
                    .build(),
                t("t2").input(exactly(2, &x)).read(read(&gate)).output(out_place(&y)).build(),
                t("t3")
                    .input(one(&y))
                    .input(at_least(2, &z))
                    .reset(reset(&x))
                    .output(and(vec![out_place(&r), out_place(&x)]))
                    .build(),
                t("t4")
                    .input(one(&z))
                    .read(read(&p))
                    .inhibitor(inhibitor(&p))
                    .output(out_place(&p))
                    .build(),
            ])
            .build();
        flatten(&net)
    }

    fn marking_of(flat: &FlatNet, tokens: &[(&str, i64)]) -> Vec<i64> {
        let mut m = vec![0i64; flat.place_count];
        for (name, count) in tokens {
            m[flat.place_index[*name]] = *count;
        }
        m
    }

    fn inequality(flat: &FlatNet, terms: &[(&str, i128)], constant: i128) -> MarkingInequality {
        let mut weights = vec![0i128; flat.place_count];
        for (name, w) in terms {
            weights[flat.place_index[*name]] = *w;
        }
        MarkingInequality { weights, constant, origin: InequalityOrigin::Inductive }
    }

    /// The same assertions the TypeScript port makes.
    #[test]
    fn accepts_the_join_inequality_as_inductive_and_rejects_a_weaker_cousin() {
        let flat = join_with_skip();
        let initial = marking_of(&flat, &[("start", 1)]);
        let join = inequality(&flat, &[("hasdata", 1), ("ready0", -1), ("ready1", -1)], 0);
        assert!(check_inductive_exact(&flat, &initial, &[], &join));
        // Arm B raises hasdata without ready0.
        let cousin = inequality(&flat, &[("hasdata", 1), ("ready0", -1)], 0);
        assert!(!check_inductive_exact(&flat, &initial, &[], &cousin));
    }

    /// Why the relative inequality is never re-checked here: `3*out + q <= 3` holds only
    /// where the marking equation does, and `produce` raises `q` from a marking the exact
    /// step relation alone does not bound.
    #[test]
    fn rejects_the_relative_queue_bound_it_does_not_re_check() {
        let flat = queue_and_bundle();
        let initial = marking_of(&flat, &[("budget", 3), ("src", 1)]);
        let relative = inequality(&flat, &[("out", 3), ("q", 1)], 3);
        assert_eq!(format_inequality(&flat, &relative), "3*out + q <= 3");
        assert!(!check_inductive_exact(&flat, &initial, &[], &relative));
    }

    /// `sig + done <= 1` is kept by both firings, and broken by the environment the moment
    /// it may inject into `sig`.
    #[test]
    fn a_positive_weight_on_an_injected_place_fails_the_check() {
        let (flat, env_inject) = gated();
        let initial = marking_of(&flat, &[("start", 1)]);
        let bound = inequality(&flat, &[("sig", 1), ("done", 1)], 1);
        assert!(check_inductive_exact(&flat, &initial, &[], &bound));
        assert!(!check_inductive_exact(&flat, &initial, &env_inject, &bound));
    }

    #[test]
    fn an_overflow_is_a_failed_check_and_a_mis_sized_inequality_is_rejected() {
        let flat = join_with_skip();
        let initial = marking_of(&flat, &[("start", 2)]);
        let huge = inequality(&flat, &[("start", i128::MAX)], i128::MAX);
        assert!(!check_inductive_exact(&flat, &initial, &[], &huge));
        let short = MarkingInequality {
            weights: vec![0; flat.place_count - 1],
            constant: 0,
            origin: InequalityOrigin::Inductive,
        };
        assert!(!check_inductive_exact(&flat, &initial, &[], &short));
    }

    /// Rows the TypeScript port emits for the same net, candidate and bound (the whole
    /// scripts were diffed byte-identical when the port landed).
    #[test]
    fn encodes_one_consecution_row_per_transition_that_can_fire() {
        let flat = join_with_skip();
        let initial = marking_of(&flat, &[("start", 1)]);
        let candidate = marking_of(&flat, &[("hasdata", 1), ("skipped", 1)]);
        let script =
            encode_inductive_inequality(&flat, &initial, &candidate, &[], DEFAULT_WEIGHT_BOUND);
        assert!(script.starts_with(
            "; Inductive-inequality refinement (VER-018): a.M <= b holding at M0, kept by every\n"
        ));
        assert!(script.contains("(set-logic QF_LIA)\n(declare-const a0 Int)\n"));
        assert!(script.contains("(declare-const b Int)\n(declare-const upos Int)\n"));
        assert!(script.contains("(assert (and (>= a0 (- 8)) (<= a0 8)))"));
        assert!(script.contains("(assert (= upos (+ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9)))"));
        assert!(script.contains("(assert (<= a9 b))"));
        assert!(script.contains("(assert (>= (+ a5 a8) (+ b 1)))"));
        // mergeStart clears hasdata (a5 >= 0); mergeSkip is guarded by its inhibitor (u5 free).
        assert!(script.contains(
            "(assert (or (and (>= a5 0) (<= (+ a4 (- a5) (- a6) (- a7)) 0)) (and (= upos u5) (<= a4 b))))"
        ));
        assert!(script.contains(
            "(assert (or (<= (+ (- a6) (- a7) a8) 0) (and (= upos u5) (<= a8 b))))"
        ));
        assert_eq!(script.matches("(assert (or ").count(), flat.transitions.len());
        assert!(script.ends_with(
            "(minimize (+ u0 w0 u1 w1 u2 w2 u3 w3 u4 w4 u5 w5 u6 w6 u7 w7 u8 w8 u9 w9))\n(check-sat)\n(get-model)"
        ));

        // A transition that can never fire contributes nothing, and the weight bound is honoured.
        let flat = clearing();
        let initial = marking_of(&flat, &[("p", 1), ("gate", 1), ("x", 3)]);
        let candidate = marking_of(&flat, &[("r", 1), ("y", 2), ("z", 1)]);
        let script = encode_inductive_inequality(&flat, &initial, &candidate, &[], 3);
        assert_eq!(script.matches("(assert (or ").count(), 3);
        assert!(script.contains("(assert (and (>= a0 (- 3)) (<= a0 3)))"));
        // t1 clears r while inhibiting it: post only, no sign condition, and u2 free.
        assert!(script.contains(
            "(assert (or (<= (+ (- a1) a5) 0) (and (= upos u2) (<= (+ a0 a5) b))))"
        ));

        // An injected place may not carry a positive weight.
        let (flat, env_inject) = gated();
        let initial = marking_of(&flat, &[("start", 1)]);
        let candidate = marking_of(&flat, &[("q", 1), ("done", 1)]);
        let script = encode_inductive_inequality(
            &flat,
            &initial,
            &candidate,
            &env_inject,
            DEFAULT_WEIGHT_BOUND,
        );
        assert!(script.contains("(assert (<= a3 0))\n(minimize "));
    }

    #[test]
    fn encodes_one_farkas_weighting_of_the_equation_per_transition_that_can_fire() {
        let flat = join_with_skip();
        let initial = marking_of(&flat, &[("start", 1)]);
        let candidate = marking_of(&flat, &[("hasdata", 1), ("skipped", 1)]);
        let script =
            encode_relative_inequality(&flat, &initial, &candidate, &[], DEFAULT_WEIGHT_BOUND);
        assert!(script.contains("(set-logic QF_LIRA)"));
        assert!(!script.contains("upos"));
        // hasdata's row is an upper bound (mergeStart clears it), so its weighting is signed.
        assert!(script.contains("(declare-const e6_9 Real)\n(assert (>= e6_5 0))\n"));
        assert!(script.contains("(assert (<= (+ e6_0 e6_3 (- e6_9)) 0.0))"));
        assert!(script.contains(
            "(assert (or (and (>= e0_0 0.0) (>= e0_1 0.0) (>= e0_2 0.0) (>= e0_3 0.0) (>= e0_4 0.0) \
             (>= e0_5 0.0) (>= e0_6 0.0) (>= e0_7 0.0) (>= e0_8 0.0) (>= e0_9 0.0) \
             (<= (+ (to_real a0) (to_real a3) (- (to_real a9))) (+ (- e0_9) e0_9))) \
             (and (<= (to_real a0) e0_0) (<= (to_real a1) e0_1) (<= (to_real a2) e0_2) \
             (<= (to_real a3) e0_3) (<= (to_real a4) e0_4) (<= (to_real a5) e0_5) \
             (<= (to_real a6) e0_6) (<= (to_real a7) e0_7) (<= (to_real a8) e0_8) \
             (<= (to_real a9) e0_9) (<= (- (+ (to_real a0) (to_real a3) (- (to_real a9))) (to_real b)) \
             (+ (- e0_9) (- e0_9 (to_real a9)))))))"
        ));

        // A transition that can never fire gets no weighting.
        let flat = clearing();
        let initial = marking_of(&flat, &[("p", 1), ("gate", 1), ("x", 3)]);
        let candidate = marking_of(&flat, &[("r", 1), ("y", 2), ("z", 1)]);
        let script = encode_relative_inequality(&flat, &initial, &candidate, &[], 3);
        assert_eq!(script.matches("(assert (or ").count(), 3);
        assert!(!script.contains("e3_"));

        // An injected place has no row: no weighting variable, and `0.0` in its place.
        let (flat, env_inject) = gated();
        let initial = marking_of(&flat, &[("start", 1)]);
        let candidate = marking_of(&flat, &[("q", 1), ("done", 1)]);
        let script = encode_relative_inequality(
            &flat,
            &initial,
            &candidate,
            &env_inject,
            DEFAULT_WEIGHT_BOUND,
        );
        assert!(script.contains(
            "(assert (>= (+ a0 a2) (+ b 1)))\n(assert (<= a3 0))\n(declare-const e0_0 Real)"
        ));
        assert!(!script.contains("_3 Real"));
        assert!(script.contains("(>= 0.0 0.0)"));
        assert!(script.contains("(<= (to_real a3) 0.0)"));
    }

    /// z3's own reply to the join query, trimmed: line breaks before a literal, the
    /// negation form, and the auxiliary `u`/`w`/`upos` it defines alongside.
    #[test]
    fn decodes_the_weights_and_bound_of_a_model() {
        let flat = join_with_skip();
        let reply = "sat\n(\n  (define-fun w6 () Int\n    1)\n  (define-fun a7 () Int\n    (- 1))\n  \
                     (define-fun a6 () Int\n    (- 1))\n  (define-fun a5 () Int\n    1)\n  \
                     (define-fun b () Int\n    0)\n  (define-fun upos () Int\n    1)\n  \
                     (define-fun u5 () Int\n    1)\n  (define-fun a0 () Int\n    0)\n)";
        let decoded = decode_inductive_inequality(reply, flat.place_count).expect("a bound");
        assert_eq!(decoded.origin, InequalityOrigin::Inductive);
        assert_eq!(decoded.constant, 0);
        assert_eq!(format_inequality(&flat, &decoded), "hasdata <= ready0 + ready1");
    }

    #[test]
    fn decodes_nothing_without_a_bound_or_with_a_literal_too_large() {
        assert_eq!(
            decode_inductive_inequality("unsat\n(error \"model is not available\")", 2),
            None
        );
        assert_eq!(decode_inductive_inequality("sat\n((define-fun a0 () Int 1))", 2), None);
        // A weight index past the net, a real weighting and a malformed name are skipped
        // (`a+1` after `a1`, so reading it as `a1` would show).
        let decoded = decode_inductive_inequality(
            "sat\n((define-fun a9 () Int 4) (define-fun e0_1 () Real 3.0) \
             (define-fun a1 () Int (- 2)) (define-fun a+1 () Int 5) (define-fun b () Int 7))",
            2,
        )
        .expect("a bound");
        assert_eq!(decoded.weights, vec![0, -2]);
        assert_eq!(decoded.constant, 7);
        // A literal too large for `i128` is the whole decode's failure, bound or weight…
        let huge = "1".repeat(40);
        let reply = format!("sat\n((define-fun a0 () Int {huge}) (define-fun b () Int 0))");
        assert_eq!(decode_inductive_inequality(&reply, 2), None);
        let reply = format!("sat\n((define-fun a0 () Int 1) (define-fun b () Int (- {huge})))");
        assert_eq!(decode_inductive_inequality(&reply, 2), None);
        // …but not one on a place the net does not have.
        let reply = format!("sat\n((define-fun a5 () Int {huge}) (define-fun b () Int 0))");
        assert!(decode_inductive_inequality(&reply, 2).is_some());
    }

    fn solve(script: &str) -> String {
        let solver = Z3Solver::resolve().expect("z3 resolves");
        solver.run(script, "invariant", 30_000, &[]).expect("z3 runs").stdout
    }

    /// [VER-018] AC2's refinement, found by z3 from the Rust script and re-checked exactly.
    #[test]
    fn synthesizes_the_join_inequality_through_z3() {
        if !z3_available() {
            eprintln!("skipping synthesizes_the_join_inequality_through_z3: z3 binary not on PATH");
            return;
        }
        let flat = join_with_skip();
        let initial = marking_of(&flat, &[("start", 1)]);
        let candidate = marking_of(&flat, &[("hasdata", 1), ("skipped", 1)]);
        let reply = solve(&encode_inductive_inequality(
            &flat,
            &initial,
            &candidate,
            &[],
            DEFAULT_WEIGHT_BOUND,
        ));
        assert_eq!(classify_first_line(&reply), Some("sat"), "{reply}");
        let found = decode_inductive_inequality(&reply, flat.place_count).expect("a model");
        assert_eq!(format_inequality(&flat, &found), "hasdata <= ready0 + ready1");
        assert!(check_inductive_exact(&flat, &initial, &[], &found));
    }

    /// The queue's bound exists only relative to the equation: the exact query has no
    /// answer, the relative one finds `3*out + q <= 3`.
    #[test]
    fn the_queue_bound_needs_the_equation_as_a_premise() {
        if !z3_available() {
            eprintln!("skipping the_queue_bound_needs_the_equation_as_a_premise: z3 binary not on PATH");
            return;
        }
        let flat = queue_and_bundle();
        let initial = marking_of(&flat, &[("budget", 3), ("src", 1)]);
        let candidate = marking_of(&flat, &[("q", 1), ("out", 1)]);
        let exact =
            encode_inductive_inequality(&flat, &initial, &candidate, &[], DEFAULT_WEIGHT_BOUND);
        let reply = solve(&exact);
        assert_eq!(classify_first_line(&reply), Some("unsat"), "{reply}");
        let relative =
            encode_relative_inequality(&flat, &initial, &candidate, &[], DEFAULT_WEIGHT_BOUND);
        let reply = solve(&relative);
        assert_eq!(classify_first_line(&reply), Some("sat"), "{reply}");
        let found = decode_inductive_inequality(&reply, flat.place_count).expect("a model");
        assert_eq!(format_inequality(&flat, &found), "3*out + q <= 3");
    }
}
