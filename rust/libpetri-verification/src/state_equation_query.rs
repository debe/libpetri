//! The query of the state-equation phase ([VER-018]): one `QF_LIA` script asking
//! whether a marking the **marking equation** admits can violate the property.
//!
//! Every marking the untimed net reaches satisfies the rows of
//! [`state_equation_conditions`] for the firing counts `n ≥ 0` of the run that
//! reached it ([VER-016]): `m_p = M0_p + C_p·n` on a place whose column is exact,
//! and `m_p ≤ M0_p + C_p·n` on a place a consume-all or reset arc clears, since
//! every clearing firing removes at least its arc weight. `unsat` therefore proves
//! the property. A `sat` model is a *candidate*: a marking the equation admits,
//! which the net need not reach. The phase refines it away with inequalities every
//! reachable marking satisfies ([`MarkingInequality`]) and asks again.
//!
//! What the phase proves is `SE(M, n) ∧ ⋀ refinements(M)`, an inductive invariant
//! over the places and the firing counters. [`refinement_certificate`] renders it as
//! the `Reachable` interpretation the [VER-016] certificate check takes, which
//! re-proves initiation, consecution and safety against the raw step relation.
//!
//! The emitted script is byte-identical to the TypeScript, Java and Python ports
//! for the same input ([VER-013] AC1): places in flat index order, then the firing
//! counters, `(- k)` for a negative literal, a lone term unwrapped.

use crate::marking_state::MarkingState;
use crate::net_flattener::FlatNet;
use crate::property::SmtProperty;
use crate::rest_set::ConditionalSinks;
use crate::smt_encoder::{encode_property_violation, state_equation_conditions};
use crate::smt_verifier::extract_define_funs;

/// Which of the phase's three legs produced a refinement. The report names it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InequalityOrigin {
    /// An initially marked trap the candidate leaves empty.
    Trap,
    /// An inequality kept by every step of the exact step relation.
    Inductive,
    /// One kept only by steps from markings the marking equation admits.
    Relative,
}

impl InequalityOrigin {
    /// The word the report prints, e.g. `Refinement (inductive): …`.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Trap => "trap",
            Self::Inductive => "inductive",
            Self::Relative => "relative",
        }
    }
}

/// A linear inequality `Σ_p weights[p]·m_p ≤ constant` that every reachable marking
/// satisfies: an initially marked trap (`Σ_{q∈Q} m_q ≥ 1`, stored as weights `-1` and
/// constant `-1`), an inductive inequality, or one inductive relative to the marking
/// equation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MarkingInequality {
    pub weights: Vec<i128>,
    pub constant: i128,
    pub origin: InequalityOrigin,
}

/// A `sat` model of the query: a marking the equation admits and the firing counts it takes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Candidate {
    pub marking: Vec<i64>,
    pub counts: Vec<i64>,
}

/// The query: `m, n ≥ 0`, the marking equation, the refinements, and the property's
/// violation exactly as the HORN error rule encodes it.
pub fn encode_state_equation_query(
    flat: &FlatNet,
    initial_marking: &MarkingState,
    property: &SmtProperty,
    sink_places: &[String],
    env_inject: &[(usize, Option<usize>)],
    conditional_sinks: &[ConditionalSinks],
    refinements: &[MarkingInequality],
) -> String {
    let m_vars: Vec<String> = (0..flat.place_count).map(|i| format!("m{i}")).collect();
    let n_vars: Vec<String> = (0..flat.transitions.len()).map(|k| format!("n{k}")).collect();
    let mut lines = vec![
        "; State-equation phase (VER-018): every reachable marking satisfies the marking"
            .to_string(),
        "; equation for the firing counts of its run (an upper bound on a place a".to_string(),
        "; consume-all or reset arc clears); unsat = no such marking violates the property."
            .to_string(),
        "(set-logic QF_LIA)".to_string(),
    ];
    for v in m_vars.iter().chain(n_vars.iter()) {
        lines.push(format!("(declare-const {v} Int)"));
    }
    for v in m_vars.iter().chain(n_vars.iter()) {
        lines.push(format!("(assert (>= {v} 0))"));
    }
    for c in state_equation_conditions(flat, initial_marking, env_inject, &n_vars, &m_vars) {
        lines.push(format!("(assert {c})"));
    }
    for r in refinements {
        lines.push(format!("(assert {})", inequality_term(r, &m_vars)));
    }
    let bad = encode_property_violation(
        flat,
        property,
        &m_vars,
        sink_places,
        env_inject,
        conditional_sinks,
    );
    lines.push(format!("(assert {bad})"));
    lines.push("(check-sat)".to_string());
    lines.push("(get-model)".to_string());
    lines.join("\n")
}

/// The candidate in a `sat` reply's model; `None` when the model defines no marking or
/// counter, or when a literal does not fit (the phase then reports the model
/// undecodable rather than proceeding on a truncated one).
pub fn decode_candidate(
    stdout: &str,
    place_count: usize,
    transition_count: usize,
) -> Option<Candidate> {
    let mut marking = vec![0i64; place_count];
    let mut counts = vec![0i64; transition_count];
    let mut seen = false;
    for def in extract_define_funs(stdout) {
        let Some((kind, index, value)) = parse_candidate_definition(def.trim()) else {
            continue;
        };
        // A literal too large to hold is the whole decode's failure, as in the other
        // ports: half a candidate would be refined against as though it were whole.
        let value = value?;
        match kind {
            'm' if index < place_count => marking[index] = value,
            'n' if index < transition_count => counts[index] = value,
            _ => continue,
        }
        seen = true;
    }
    if seen {
        Some(Candidate { marking, counts })
    } else {
        None
    }
}

/// Reads `(define-fun m<p> () Int <lit>)` or `(define-fun n<t> () Int <lit>)` with
/// `<lit>` a natural literal `k` or the negation form `(- k)` (z3 may break the line
/// before the literal). `None` when the definition is neither; `Some((_, _, None))`
/// when the literal overflows `i64`.
fn parse_candidate_definition(def: &str) -> Option<(char, usize, Option<i64>)> {
    let body = def.strip_prefix("(define-fun")?.strip_suffix(')')?;
    let body = body.trim_start();
    let name_end = body.find(char::is_whitespace)?;
    let (name, rest) = body.split_at(name_end);
    let mut chars = name.chars();
    let kind = chars.next()?;
    if kind != 'm' && kind != 'n' {
        return None;
    }
    let index: usize = chars.as_str().parse().ok()?;
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
    let magnitude: Option<i64> = digits.parse().ok();
    Some((
        kind,
        index,
        magnitude.map(|k| if negative { -k } else { k }),
    ))
}

/// Whether the inequality holds at a marking, in exact integer arithmetic.
///
/// An overflow answers `true`. That is the conservative direction: the caller reads
/// `true` as "this refinement does not exclude the candidate" and reports the phase
/// inconclusive, where `false` would credit a refinement that was never evaluated.
pub fn holds_at(inequality: &MarkingInequality, marking: &[i64]) -> bool {
    let mut sum: i128 = 0;
    for (p, &w) in inequality.weights.iter().enumerate() {
        if w == 0 {
            continue;
        }
        let m = i128::from(marking.get(p).copied().unwrap_or(0));
        let Some(product) = w.checked_mul(m) else {
            return true;
        };
        let Some(next) = sum.checked_add(product) else {
            return true;
        };
        sum = next;
    }
    sum <= inequality.constant
}

/// The inequality as an SMT-LIB term over `vars`: `(<= Σ w·v c)`, or, when no weight
/// is positive, the same bound read the other way round — a trap is `(>= (+ v3 v5) 1)`.
fn inequality_term(inequality: &MarkingInequality, vars: &[String]) -> String {
    let flip = inequality.weights.iter().all(|&w| w <= 0);
    let mut terms: Vec<String> = Vec::new();
    for (p, &raw) in inequality.weights.iter().enumerate() {
        let w = if flip { -raw } else { raw };
        if w != 0 {
            terms.push(term(w, &vars[p]));
        }
    }
    let lhs = match terms.len() {
        0 => "0".to_string(),
        1 => terms[0].clone(),
        _ => format!("(+ {})", terms.join(" ")),
    };
    if flip {
        format!("(>= {lhs} {})", literal(-inequality.constant))
    } else {
        format!("(<= {lhs} {})", literal(inequality.constant))
    }
}

/// The phase's proof as the `Reachable` interpretation the [VER-016] certificate check
/// takes: `(define-fun Reachable ((x!0 Int) …) Bool …)` over the places and one firing
/// counter per flat transition. The check conjoins the marking equation itself, so the
/// body carries only the refinements, and is `true` when none was needed.
pub fn refinement_certificate(
    place_count: usize,
    transition_count: usize,
    refinements: &[MarkingInequality],
) -> String {
    let params: Vec<String> = (0..place_count + transition_count)
        .map(|i| format!("(x!{i} Int)"))
        .collect();
    let vars: Vec<String> = (0..place_count).map(|i| format!("x!{i}")).collect();
    let terms: Vec<String> = refinements
        .iter()
        .map(|r| inequality_term(r, &vars))
        .collect();
    let body = match terms.len() {
        0 => "true".to_string(),
        1 => terms[0].clone(),
        _ => format!("(and {})", terms.join("\n         ")),
    };
    format!(
        "(define-fun Reachable ({}) Bool\n    {body})",
        params.join(" ")
    )
}

/// `Merge/hasdata <= Merge/ready_0 + Merge/ready_1`; a trap reads `a + b >= 1`.
pub fn format_inequality(flat: &FlatNet, inequality: &MarkingInequality) -> String {
    let named = |p: usize, w: i128| -> String {
        if w == 1 {
            flat.places[p].clone()
        } else {
            format!("{w}*{}", flat.places[p])
        }
    };
    let mut left: Vec<String> = Vec::new();
    let mut right: Vec<String> = Vec::new();
    for (p, &w) in inequality.weights.iter().enumerate() {
        if w > 0 {
            left.push(named(p, w));
        } else if w < 0 {
            right.push(named(p, -w));
        }
    }
    if left.is_empty() {
        let lhs = if right.is_empty() {
            "0".to_string()
        } else {
            right.join(" + ")
        };
        return format!("{lhs} >= {}", -inequality.constant);
    }
    // `a <= b` reads better than `a <= 0 + b`, so a zero constant is dropped once the
    // right-hand side has a term of its own.
    let drop_zero = inequality.constant == 0 && !right.is_empty();
    let rhs = if drop_zero {
        right.join(" + ")
    } else {
        let mut parts = vec![inequality.constant.to_string()];
        parts.extend(right);
        parts.join(" + ")
    };
    format!("{} <= {rhs}", left.join(" + "))
}

fn term(c: i128, v: &str) -> String {
    if c == 1 {
        return v.to_string();
    }
    if c == -1 {
        return format!("(- {v})");
    }
    if c > 0 {
        format!("(* {c} {v})")
    } else {
        format!("(* (- {}) {v})", -c)
    }
}

fn literal(c: i128) -> String {
    if c < 0 {
        format!("(- {})", -c)
    } else {
        c.to_string()
    }
}
