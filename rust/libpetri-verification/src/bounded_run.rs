//! The firing-bound phase ([VER-019]). When every firing strictly lowers a weighted
//! token count, every run is short, and a bounded model check to that length decides
//! the property exactly — consume-all and reset clearing, inhibitor and read guards
//! included. A net whose runs are not bounded this way is reported as such and left to
//! the fixpoint query: a bound is both the runtime cap and the width of the claim.
//!
//! **Ranking.** Weights `r ≥ 0` with `r·C_t ≤ −1` for every flat transition `t` that
//! can fire. A clearing arc removes at least its weight, so the column `C_t = post −
//! pre` bounds its effect from above. `r·M` then drops by at least one per firing and
//! never goes below zero, so a run from `M0` has at most `K = r·M0` firings. One
//! `QF_LIA` query minimising `r·M0` ([`encode_ranking_query`]), re-checked in exact
//! integer arithmetic ([`check_ranking_exact`]). When none exists, Farkas gives
//! `y ≥ 0, y ≠ 0` with `C·y ≥ 0`: firing counts the marking equation lets repeat
//! forever ([`encode_repeatable_vector_query`]), whose support the report names.
//!
//! **Bounded model check.** One `QF_LIA` script unrolls `d` steps of the exact step
//! relation from `M0` — step `i` fires the transition its selector `s_i` names, or
//! idles, and once idle stays idle — and asks for a violation at the last marking
//! ([`encode_bounded_run`]). Idling makes "at most `d` firings" one query. `sat` is a
//! run, decoded and replayed firing by firing before it is believed ([`replay_run`]);
//! `unsat` at `d = K` covers every run of the net.
//!
//! **Injection.** `env_inject` is the resolved injection list
//! (`smt_encoder::resolve_env_injection`). Each entry is a step of the bounded run
//! beside the transitions ([VER-006]): injection `j` takes the selector `T + j`, adds
//! one token to its place, and under the bounded mode is taken only below the bound.
//! The bounded mode's post-caps are the entries with a bound. The firing-bound phase
//! never unrolls one — an injection is not a firing, so it refuses such a net — and
//! with none the selectors are the transitions' alone and `T` idles.
//!
//! **Witness phase ([VER-025]).** [`run_witness_phase`] asks the bounded model check
//! once, at a fixed depth, with no ranking: a search limit, not a bound. `sat` is a run,
//! replayed, trimmed of every step it can lose, and reported; `unsat` proves nothing.
//!
//! Every emitted script is byte-identical to the TypeScript port's ([VER-013] AC1).

use std::collections::BTreeMap;

use crate::abstract_replay::{enabled_a, fire_a, inject_a, violation_predicate, within_env_bounds};
use crate::marking_state::MarkingState;
use crate::net_flattener::{FlatNet, FlatTransition};
use crate::property::SmtProperty;
use crate::rest_set::ConditionalSinks;
use crate::smt_encoder::{conjoin, encode_property_violation};
use crate::smt_text::{MAX_SAFE_INTEGER, indexed, int_definition, sum, term};
use crate::smt_verifier::extract_define_funs;
use crate::z3_process::{QueryBudget, classify_first_line};

/// A ranking and the firing bound it gives: `weights·C_t ≤ −1` on every transition
/// that can fire.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FiringBound {
    /// `r`, one entry per flat place, all non-negative.
    pub weights: Vec<i128>,
    /// `K = r·M0`: no run from `M0` has more firings.
    pub bound: i128,
}

/// The largest firing bound the phase model-checks to: the largest the TypeScript port
/// counts depths in exactly, so the ports refuse the same bounds with the same reason. No
/// depth limit comes near it.
const LARGEST_BOUND: i128 = MAX_SAFE_INTEGER as i128;

/// Whether `ft` can ever fire: it does not inhibit a place it needs.
fn can_fire(ft: &FlatTransition) -> bool {
    ft.inhibitor_places
        .iter()
        .all(|&p| arc(&ft.pre, p) <= 0 && !ft.read_places.contains(&p))
}

/// The `QF_LIA` script asking for the ranking with the least `r·M0`.
pub fn encode_ranking_query(flat: &FlatNet, initial: &[i64]) -> String {
    let place_count = flat.place_count;
    let mut lines = vec![
        "; Firing bound (VER-019): weights r >= 0 that every firing lowers by at least one"
            .to_string(),
        "; (r.C_t <= -1, a clearing arc counted at its weight); every run from M0 then has"
            .to_string(),
        "; at most r.M0 firings. sat with the least r.M0.".to_string(),
        "(set-logic QF_LIA)".to_string(),
    ];
    for p in 0..place_count {
        lines.push(format!("(declare-const r{p} Int)"));
    }
    for p in 0..place_count {
        lines.push(format!("(assert (>= r{p} 0))"));
    }
    for ft in &flat.transitions {
        if !can_fire(ft) {
            continue;
        }
        let terms: Vec<String> = (0..place_count)
            .filter_map(|p| {
                let c = column(ft, p);
                (c != 0).then(|| term(c, &format!("r{p}")))
            })
            .collect();
        lines.push(format!("(assert (<= {} (- 1)))", sum(&terms, "0")));
    }
    let objective: Vec<String> = (0..place_count)
        .filter_map(|p| {
            let m0 = i128::from(initial.get(p).copied().unwrap_or(0));
            (m0 != 0).then(|| term(m0, &format!("r{p}")))
        })
        .collect();
    lines.push(format!("(minimize {})", sum(&objective, "0")));
    lines.push("(check-sat)".to_string());
    lines.push("(get-model)".to_string());
    lines.join("\n")
}

/// The ranking in a `sat` reply's model; `None` when it defines no weight, or when a
/// weight does not fit `i128` (the phase then reports the ranking failed its re-check
/// rather than bound runs by a truncated one).
pub fn decode_ranking(stdout: &str, place_count: usize) -> Option<Vec<i128>> {
    let mut weights = vec![0i128; place_count];
    let mut seen = false;
    for def in extract_define_funs(stdout) {
        let Some((name, literal)) = int_definition(def.trim()) else {
            continue;
        };
        let Some(p) = indexed(name, 'r').filter(|&p| p < place_count) else {
            continue;
        };
        weights[p] = literal.value()?;
        seen = true;
    }
    seen.then_some(weights)
}

/// Re-checks a ranking in exact integer arithmetic: `r ≥ 0` and `r·C_t ≤ −1` on every
/// flat transition that can fire. Returns the firing bound, or `None` when a check
/// fails.
///
/// An overflow is a failed check, never a pass: a column sum that overflows was not
/// shown to be `≤ −1`, and a bound that overflows bounds nothing.
pub fn check_ranking_exact(
    flat: &FlatNet,
    initial: &[i64],
    weights: &[i128],
) -> Option<FiringBound> {
    let place_count = flat.place_count;
    if weights.len() != place_count || weights.iter().any(|&w| w < 0) {
        return None;
    }
    for ft in &flat.transitions {
        if !can_fire(ft) {
            continue;
        }
        let mut delta: i128 = 0;
        for (p, &w) in weights.iter().enumerate() {
            delta = delta.checked_add(w.checked_mul(column(ft, p))?)?;
        }
        if delta > -1 {
            return None;
        }
    }
    let mut bound: i128 = 0;
    for (p, &w) in weights.iter().enumerate() {
        let m0 = i128::from(initial.get(p).copied().unwrap_or(0));
        bound = bound.checked_add(w.checked_mul(m0)?)?;
    }
    Some(FiringBound {
        weights: weights.to_vec(),
        bound,
    })
}

/// The `QF_LIA` script asking for the Farkas alternative of a ranking: firing counts
/// `y ≥ 0`, not all zero, with `C·y ≥ 0` on every place — counts the marking equation
/// lets repeat forever. The fewest firings.
pub fn encode_repeatable_vector_query(flat: &FlatNet) -> String {
    let live: Vec<usize> = flat
        .transitions
        .iter()
        .enumerate()
        .filter(|(_, ft)| can_fire(ft))
        .map(|(t, _)| t)
        .collect();
    let counts: Vec<String> = live.iter().map(|t| format!("y{t}")).collect();
    let mut lines = vec![
        "; No firing bound (VER-019): firing counts y >= 0, not all zero, with C.y >= 0 on"
            .to_string(),
        "; every place, so the marking equation lets them repeat forever.".to_string(),
        "(set-logic QF_LIA)".to_string(),
    ];
    for y in &counts {
        lines.push(format!("(declare-const {y} Int)"));
    }
    for y in &counts {
        lines.push(format!("(assert (>= {y} 0))"));
    }
    lines.push(format!("(assert (>= {} 1))", sum(&counts, "0")));
    for p in 0..flat.place_count {
        let terms: Vec<String> = live
            .iter()
            .filter_map(|&t| {
                let c = column(&flat.transitions[t], p);
                (c != 0).then(|| term(c, &format!("y{t}")))
            })
            .collect();
        if !terms.is_empty() {
            lines.push(format!("(assert (>= {} 0))", sum(&terms, "0")));
        }
    }
    lines.push(format!("(minimize {})", sum(&counts, "0")));
    lines.push("(check-sat)".to_string());
    lines.push("(get-model)".to_string());
    lines.join("\n")
}

/// The transitions a repeatable vector fires, in net order; `None` when the model
/// fires none.
pub fn decode_repeatable_vector(stdout: &str, transition_count: usize) -> Option<Vec<usize>> {
    let mut support: Vec<usize> = Vec::new();
    for def in extract_define_funs(stdout) {
        let Some((name, literal)) = int_definition(def.trim()) else {
            continue;
        };
        // Only the sign matters, so a count too large for any integer type still counts.
        if let Some(t) = indexed(name, 'y').filter(|&t| t < transition_count) {
            if literal.is_positive() {
                support.push(t);
            }
        }
    }
    support.sort_unstable();
    if support.is_empty() { None } else { Some(support) }
}

/// The bounded model check: `depth` steps from `initial`, selector `s_i ∈ [0, T + J]`
/// per step — a transition, then injection `j` of `env_inject` at `T + j`, and `T + J`
/// idles — the exact guard and update of the selected step, the environment post-caps,
/// and the property's violation at the last marking.
pub fn encode_bounded_run(
    flat: &FlatNet,
    initial: &[i64],
    property: &SmtProperty,
    sink_places: &[String],
    conditional_sinks: &[ConditionalSinks],
    env_inject: &[(usize, Option<usize>)],
    depth: usize,
) -> String {
    let place_count = flat.place_count;
    let transition_count = flat.transitions.len();
    let m = |i: usize, p: usize| -> String {
        if i == 0 {
            initial.get(p).copied().unwrap_or(0).to_string()
        } else {
            format!("m{i}_{p}")
        }
    };
    // The encoder's `envBounds(M')` conjunct. Empty for the firing-bound phase, which
    // refuses a net with injection; live for the witness phase ([VER-025]).
    let caps = environment_caps(env_inject, place_count);
    // The injection steps ([VER-006]) take the selectors after the transitions'; idling
    // moves past them.
    let injections = injection_steps(env_inject, place_count);
    let idle = transition_count + injections.len();
    // Each place's touchers, reversed: the `ite` chain nests from the last one inward.
    let nesting: Vec<Vec<usize>> = (0..place_count)
        .map(|p| {
            let mut touching: Vec<usize> = flat
                .transitions
                .iter()
                .enumerate()
                .filter(|(_, ft)| clears(ft, p) || column(ft, p) != 0)
                .map(|(t, _)| t)
                .collect();
            touching.extend(
                injections
                    .iter()
                    .enumerate()
                    .filter(|&(_, &(pid, _))| pid == p)
                    .map(|(j, _)| transition_count + j),
            );
            touching.reverse();
            touching
        })
        .collect();
    let mut lines = vec![
        format!("; Bounded run (VER-019): {depth} steps of the exact step relation from M0, idle"),
        "; only at the end; sat = a run to a violating marking.".to_string(),
        "(set-logic QF_LIA)".to_string(),
    ];
    for i in 0..depth {
        lines.push(format!("(declare-const s{i} Int)"));
    }
    for i in 1..=depth {
        for p in 0..place_count {
            lines.push(format!("(declare-const {} Int)", m(i, p)));
        }
    }
    for i in 0..depth {
        lines.push(format!("(assert (and (>= s{i} 0) (<= s{i} {idle})))"));
        if i + 1 < depth {
            lines.push(format!("(assert (=> (= s{i} {idle}) (= s{} {idle})))", i + 1));
        }
        for (t, ft) in flat.transitions.iter().enumerate() {
            let guard = guard_conditions(ft, place_count, |p| m(i, p));
            lines.push(format!("(assert (=> (= s{i} {t}) {}))", conjoin(&guard)));
        }
        for (j, &(pid, bound)) in injections.iter().enumerate() {
            if let Some(bound) = bound {
                lines.push(format!(
                    "(assert (=> (= s{i} {}) (< {} {bound})))",
                    transition_count + j,
                    m(i, pid)
                ));
            }
        }
        for p in 0..place_count {
            let mut value = m(i, p);
            for &t in &nesting[p] {
                let next = match flat.transitions.get(t) {
                    Some(ft) if clears(ft, p) => arc(&ft.post, p).to_string(),
                    Some(ft) => shifted(&m(i, p), column(ft, p)),
                    // An injection step: one more token.
                    None => shifted(&m(i, p), 1),
                };
                value = format!("(ite (= s{i} {t}) {next} {value})");
            }
            lines.push(format!("(assert (= {} {value}))", m(i + 1, p)));
        }
        for (&p, &cap) in &caps {
            lines.push(format!("(assert (<= {} {cap}))", m(i + 1, p)));
        }
    }
    let last: Vec<String> = (0..place_count).map(|p| m(depth, p)).collect();
    let bad = encode_property_violation(
        flat,
        property,
        &last,
        sink_places,
        env_inject,
        conditional_sinks,
    );
    lines.push(format!("(assert {bad})"));
    lines.push("(check-sat)".to_string());
    lines.push("(get-model)".to_string());
    lines.join("\n")
}

/// The steps a `sat` bounded run takes, in order, up to the first idle step; `None`
/// when the model defines no selector (at a positive depth).
///
/// `step_count` is `T + J`, the transitions and the injection steps the script was
/// encoded with: a selector in `[T, T + J)` is injection `selector − T`. A selector
/// outside `[0, T + J)` is an idle step, however far outside: one too large for any
/// integer type is read as idle too, which is what it is.
pub fn decode_bounded_run(
    stdout: &str,
    step_count: usize,
    depth: usize,
) -> Option<Vec<usize>> {
    // `None` is an idle step, the default of a selector the model is silent on.
    let mut selectors: Vec<Option<usize>> = vec![None; depth];
    let mut seen = depth == 0;
    for def in extract_define_funs(stdout) {
        let Some((name, literal)) = int_definition(def.trim()) else {
            continue;
        };
        let Some(i) = indexed(name, 's').filter(|&i| i < depth) else {
            continue;
        };
        selectors[i] = literal.index_below(step_count);
        seen = true;
    }
    if !seen {
        return None;
    }
    Some(selectors.iter().map_while(|s| *s).collect())
}

/// A firing sequence replayed under the exact abstract semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplayedRun {
    /// The markings, `M0` first and the violating one last.
    pub states: Vec<Vec<i64>>,
    /// The steps taken between consecutive states: a flat transition's name, or
    /// `inject(<place>)` for an injection step.
    pub steps: Vec<String>,
}

/// Replays a run from `initial` under the exact abstract semantics and returns its
/// markings and step names when every step is enabled and the last marking violates
/// the property (`is_bad`, as `abstract_replay::violation_predicate` builds it); `None`
/// otherwise, including for a step index past `T + J`.
///
/// An index below `T` fires that transition, which must also respect the environment
/// post-caps. `T + j` is injection `j` of `env_inject` ([VER-006]): refused at its
/// bound, else one more token, with no post-cap check — the injection rule of the
/// fixpoint encoding has none, and `abstract_replay::replay` takes the step the same
/// way.
pub fn replay_run(
    flat: &FlatNet,
    initial: &[i64],
    firings: &[usize],
    env_inject: &[(usize, Option<usize>)],
    is_bad: impl Fn(&[i64]) -> bool,
) -> Option<ReplayedRun> {
    let relation = StepRelation::of(flat, env_inject);
    let mut states = vec![initial.to_vec()];
    let mut steps = Vec::with_capacity(firings.len());
    let mut state = initial.to_vec();
    for &t in firings {
        let (next, label) = relation.step(&state, t)?;
        state = next;
        states.push(state.clone());
        steps.push(label);
    }
    if is_bad(&state) {
        Some(ReplayedRun { states, steps })
    } else {
        None
    }
}

/// The steps a run is replayed with: the flat net's transitions, then the injection
/// steps, with the environment post-caps a firing has to respect. Resolved once per
/// replay, and the one place a step is taken, so [`replay_run`] and the trim of the
/// witness phase ([`violating_prefix`]) cannot disagree about a step.
struct StepRelation<'a> {
    flat: &'a FlatNet,
    caps: Vec<(usize, usize)>,
    injections: Vec<(usize, Option<usize>)>,
}

impl<'a> StepRelation<'a> {
    fn of(flat: &'a FlatNet, env_inject: &[(usize, Option<usize>)]) -> Self {
        Self {
            flat,
            caps: environment_caps(env_inject, flat.place_count).into_iter().collect(),
            injections: injection_steps(env_inject, flat.place_count),
        }
    }

    /// The marking after step `t` from `state` and the step's name; `None` when the
    /// step is not enabled there, a firing leaves a post-cap, or `t` is past `T + J`.
    fn step(&self, state: &[i64], t: usize) -> Option<(Vec<i64>, String)> {
        let Some(ft) = self.flat.transitions.get(t) else {
            let &(pid, bound) = self.injections.get(t - self.flat.transitions.len())?;
            let next = inject_a(state, pid, bound)?;
            return Some((next, format!("inject({})", self.flat.places[pid])));
        };
        if !enabled_a(self.flat, state, ft) {
            return None;
        }
        let next = fire_a(self.flat, state, ft);
        within_env_bounds(&next, &self.caps).then(|| (next, ft.name.clone()))
    }
}

/// The shortest prefix of `run` that replays to a violating marking, as the markings
/// and step names it passes: the violation is tested before each step and after the
/// last, and the replay stops at the first hit. The empty prefix counts, so a
/// violating `initial` is the run of no steps. `None` when a step is not enabled
/// before any marking violates, or none does. Steps after the first violating marking
/// are not looked at, so they need not be enabled.
fn violating_prefix(
    relation: &StepRelation<'_>,
    initial: &[i64],
    run: &[usize],
    is_bad: impl Fn(&[i64]) -> bool,
) -> Option<ReplayedRun> {
    let mut replayed = ReplayedRun {
        states: vec![initial.to_vec()],
        steps: Vec::new(),
    };
    let mut state = initial.to_vec();
    for &t in run {
        if is_bad(&state) {
            return Some(replayed);
        }
        let (next, label) = relation.step(&state, t)?;
        state = next;
        replayed.states.push(state.clone());
        replayed.steps.push(label);
    }
    is_bad(&state).then_some(replayed)
}

/// `budget + s + 2*src` — the ranking as the report prints it.
pub fn format_ranking(flat: &FlatNet, bound: &FiringBound) -> String {
    let parts: Vec<String> = bound
        .weights
        .iter()
        .enumerate()
        .filter(|&(_, &w)| w != 0)
        .map(|(p, &w)| {
            if w == 1 {
                flat.places[p].clone()
            } else {
                format!("{w}*{}", flat.places[p])
            }
        })
        .collect();
    if parts.is_empty() {
        "0".to_string()
    } else {
        parts.join(" + ")
    }
}

/// What the bounded model check answered at one depth.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DepthAnswer {
    /// A run of at most that many firings reaches a violation.
    Sat,
    /// None does.
    Unsat,
}

impl DepthAnswer {
    /// The solver's word: `sat` or `unsat`.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
        }
    }
}

/// One depth of the bounded model check and what it answered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DepthStep {
    pub depth: usize,
    pub answer: DepthAnswer,
}

/// Outcome of [`run_firing_bound_phase`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FiringBoundOutcome {
    /// `unsat` at the firing bound: no run reaches a violation.
    Proven {
        bound: FiringBound,
        depths: Vec<DepthStep>,
    },
    /// A bounded run reaches a violation, replayed under the exact semantics.
    Violated {
        bound: FiringBound,
        depths: Vec<DepthStep>,
        states: Vec<Vec<i64>>,
        steps: Vec<String>,
    },
    /// No ranking exists; `repeatable` names the flat transitions a repeatable firing
    /// vector uses, when the second query found one.
    Unbounded { repeatable: Option<Vec<usize>> },
    /// The phase stepped aside, and why. Every depth answered before it did is kept.
    Inconclusive {
        reason: String,
        bound: Option<FiringBound>,
        depths: Vec<DepthStep>,
    },
}

/// Why the phase steps aside on a net the environment injects into. Shared with the
/// verifier, which also refuses a net whose declared environment places are not all
/// resolved: see `SmtVerifier::firing_bound_decision`.
pub(crate) const ENVIRONMENT_INJECTION_REASON: &str = "environment injection has no firing bound";

/// Options of [`run_firing_bound_phase`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FiringBoundOptions {
    /// Wall-clock budget for the whole phase in milliseconds; each query gets what is
    /// left (default 60 000).
    pub budget_ms: u64,
    /// The deepest bounded run the phase asks for (default 512).
    pub max_depth: usize,
}

impl Default for FiringBoundOptions {
    fn default() -> Self {
        Self {
            budget_ms: 60_000,
            max_depth: 512,
        }
    }
}

/// Runs the phase: the ranking query (or, when there is none, the repeatable-vector
/// query), then the bounded model check at depths 8, 16, 32, … up to the firing bound.
/// A violating run is replayed before it is reported; `unsat` at the bound is a proof.
///
/// Builds the violation predicate itself, as the state-equation phase ([VER-018]) does,
/// so the two phases cannot be handed inconsistent ones.
///
/// `solver(script, phase, timeout_ms)` runs one script — `phase` is `ranking` or `bmc`,
/// the dump name of [VER-013] — within `timeout_ms` and returns its stdout, or the
/// reason when the transport failed or the reply carries no verdict line.
#[allow(clippy::too_many_arguments)]
pub fn run_firing_bound_phase(
    flat: &FlatNet,
    initial_marking: &MarkingState,
    property: &SmtProperty,
    sink_places: &[String],
    conditional_sinks: &[ConditionalSinks],
    env_inject: &[(usize, Option<usize>)],
    solver: impl Fn(&str, &str, u64) -> Result<String, String>,
    options: FiringBoundOptions,
) -> FiringBoundOutcome {
    // [NU-055]: a run of counts carries no names.
    if property.is_name_alignment() {
        return FiringBoundOutcome::Inconclusive {
            reason: property.route_b_only_reason(),
            bound: None,
            depths: Vec::new(),
        };
    }
    let budget = QueryBudget::start(options.budget_ms);
    let max_depth = options.max_depth;
    let initial: Vec<i64> = flat
        .places
        .iter()
        .map(|name| i64::try_from(initial_marking.count(name)).unwrap_or(i64::MAX))
        .collect();
    let is_bad = violation_predicate(flat, property, sink_places, conditional_sinks, env_inject);
    let mut depths: Vec<DepthStep> = Vec::new();
    // An injection is not a firing, so no weighting bounds the runs it extends.
    if !env_inject.is_empty() {
        return FiringBoundOutcome::Inconclusive {
            reason: ENVIRONMENT_INJECTION_REASON.to_string(),
            bound: None,
            depths,
        };
    }
    let ask = |script: &str, phase: &str| -> Result<String, String> {
        solver(script, phase, budget.left()?)
    };

    let ranking = match ask(&encode_ranking_query(flat, &initial), "ranking") {
        Ok(reply) => reply,
        Err(reason) => return FiringBoundOutcome::Inconclusive { reason, bound: None, depths },
    };
    match classify_first_line(&ranking) {
        Some("unsat") => {
            let repeatable = match ask(&encode_repeatable_vector_query(flat), "ranking") {
                Ok(reply) if classify_first_line(&reply) == Some("sat") => {
                    decode_repeatable_vector(&reply, flat.transitions.len())
                }
                _ => None,
            };
            return FiringBoundOutcome::Unbounded { repeatable };
        }
        Some("sat") => {}
        _ => {
            return FiringBoundOutcome::Inconclusive {
                reason: "the ranking query answered unknown".to_string(),
                bound: None,
                depths,
            };
        }
    }
    let bound = decode_ranking(&ranking, flat.place_count)
        .and_then(|weights| check_ranking_exact(flat, &initial, &weights));
    let Some(bound) = bound else {
        return FiringBoundOutcome::Inconclusive {
            reason: "the ranking failed the exact re-check".to_string(),
            bound: None,
            depths,
        };
    };
    let k = match u64::try_from(bound.bound) {
        Ok(k) if bound.bound <= LARGEST_BOUND => k,
        _ => {
            return FiringBoundOutcome::Inconclusive {
                reason: format!("firing bound {} is too large", bound.bound),
                bound: Some(bound),
                depths,
            };
        }
    };
    // Every depth below is at most `max_depth`, so the conversions back to `usize` hold.
    let mut depth = (k.min(8) as usize).min(max_depth);
    loop {
        let script = encode_bounded_run(
            flat,
            &initial,
            property,
            sink_places,
            conditional_sinks,
            env_inject,
            depth,
        );
        let reply = match ask(&script, "bmc") {
            Ok(reply) => reply,
            Err(reason) => {
                return FiringBoundOutcome::Inconclusive { reason, bound: Some(bound), depths };
            }
        };
        // An answered depth is a depth we searched, whichever way it went; only a
        // verdict-less reply is not one.
        let answer = match classify_first_line(&reply) {
            Some("sat") => DepthAnswer::Sat,
            Some("unsat") => DepthAnswer::Unsat,
            _ => {
                return FiringBoundOutcome::Inconclusive {
                    reason: format!("the bounded run at depth {depth} answered unknown"),
                    bound: Some(bound),
                    depths,
                };
            }
        };
        depths.push(DepthStep { depth, answer });
        if answer == DepthAnswer::Sat {
            let replayed = decode_bounded_run(&reply, flat.transitions.len(), depth)
                .and_then(|firings| replay_run(flat, &initial, &firings, env_inject, &is_bad));
            return match replayed {
                Some(run) => FiringBoundOutcome::Violated {
                    bound,
                    depths,
                    states: run.states,
                    steps: run.steps,
                },
                None => FiringBoundOutcome::Inconclusive {
                    reason: "the bounded run did not replay under the exact semantics".to_string(),
                    bound: Some(bound),
                    depths,
                },
            };
        }
        if depth as u64 >= k {
            return FiringBoundOutcome::Proven { bound, depths };
        }
        if depth >= max_depth {
            return FiringBoundOutcome::Inconclusive {
                reason: format!("the firing bound {k} exceeds the depth limit {max_depth}"),
                bound: Some(bound),
                depths,
            };
        }
        depth = (depth as u64).saturating_mul(2).min(k).min(max_depth as u64) as usize;
    }
}

/// Outcome of [`run_witness_phase`]. Never a proof: the depth is a search limit, not a
/// bound on the runs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WitnessOutcome {
    /// A run reaches a violation: replayed under the exact semantics, then trimmed to
    /// end at the first violating marking it reaches and of every step it can lose.
    /// `steps` names the flat transitions and the `inject(<place>)` steps between
    /// consecutive `states`, the last of which is the only violating one.
    Violated {
        states: Vec<Vec<i64>>,
        steps: Vec<String>,
    },
    /// `unsat`: no run of at most the depth reaches a violation.
    NoRun,
    /// The phase stepped aside, and why.
    Inconclusive { reason: String },
    /// The verification was stopped during the trim ([VER-013]): its total budget ran
    /// out, or it was cancelled. Not a reason of the phase's own: the stop is sticky,
    /// and the pipeline's next step ends the query with the reason that names this one.
    Stopped,
}

/// Options of [`run_witness_phase`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WitnessOptions {
    /// Wall-clock budget for the phase in milliseconds, started before the script is
    /// encoded; the query gets what is left (default 7 500, an eighth of the verifier's
    /// default timeout).
    pub budget_ms: u64,
    /// The length of the bounded run the phase asks for (default 8).
    pub depth: usize,
}

impl Default for WitnessOptions {
    fn default() -> Self {
        Self {
            budget_ms: 7_500,
            depth: 8,
        }
    }
}

/// The script [`run_witness_phase`] sends at `depth`: [`encode_bounded_run`] from the
/// initial marking. What `SmtVerifier::encode_scripts` reports as `witness`.
pub fn encode_witness_query(
    flat: &FlatNet,
    initial_marking: &MarkingState,
    property: &SmtProperty,
    sink_places: &[String],
    conditional_sinks: &[ConditionalSinks],
    env_inject: &[(usize, Option<usize>)],
    depth: usize,
) -> String {
    encode_bounded_run(
        flat,
        &initial_vector(flat, initial_marking),
        property,
        sink_places,
        conditional_sinks,
        env_inject,
        depth,
    )
}

/// The initial marking as the bounded run counts it, one entry per flat place.
fn initial_vector(flat: &FlatNet, initial_marking: &MarkingState) -> Vec<i64> {
    flat.places
        .iter()
        .map(|name| i64::try_from(initial_marking.count(name)).unwrap_or(i64::MAX))
        .collect()
}

/// Runs the bounded witness phase ([VER-025]): one bounded model check of `depth` steps,
/// the injection steps of `env_inject` among them, with no firing bound behind it. A
/// violating run is replayed before it is believed, then trimmed, since the solver pads
/// a run to the full depth.
///
/// The trim keeps the shortest prefix that replays to a violating marking
/// ([`violating_prefix`]). Then one step at a time is dropped, last to first, wherever
/// what is left still has such a prefix, which becomes the run; the passes repeat until
/// one drops nothing. What is left after a drop only has to replay up to its first
/// violating marking: the steps past it are cut, so they need not be enabled. The run
/// reported therefore ends at the first violating marking it reaches, and no single
/// step of it can go; it is not claimed to be the shortest. A violating initial marking
/// is always the run of no steps, whatever model the solver returned.
///
/// The trim is cubic in the run's length and runs no solver, so it polls the
/// verification's stop ([VER-013]: total budget and cancellation alike) before every
/// candidate and answers [`WitnessOutcome::Stopped`]. Without a stop scope — a direct
/// caller, outside `SmtVerifier::verify` — the poll does nothing.
///
/// `solver(script, phase, timeout_ms)` is the transport of [`run_firing_bound_phase`];
/// `phase` is `witness`, the dump name of [VER-013].
#[allow(clippy::too_many_arguments)]
pub fn run_witness_phase(
    flat: &FlatNet,
    initial_marking: &MarkingState,
    property: &SmtProperty,
    sink_places: &[String],
    conditional_sinks: &[ConditionalSinks],
    env_inject: &[(usize, Option<usize>)],
    solver: impl Fn(&str, &str, u64) -> Result<String, String>,
    options: WitnessOptions,
) -> WitnessOutcome {
    witness_phase(
        flat,
        initial_marking,
        property,
        sink_places,
        conditional_sinks,
        env_inject,
        solver,
        options,
        crate::total_budget::cut,
    )
}

/// [`run_witness_phase`] with the stop its trim polls: `stop()` answers whether the
/// verification must end now.
#[allow(clippy::too_many_arguments)]
fn witness_phase(
    flat: &FlatNet,
    initial_marking: &MarkingState,
    property: &SmtProperty,
    sink_places: &[String],
    conditional_sinks: &[ConditionalSinks],
    env_inject: &[(usize, Option<usize>)],
    solver: impl Fn(&str, &str, u64) -> Result<String, String>,
    options: WitnessOptions,
    stop: impl Fn() -> bool,
) -> WitnessOutcome {
    // [NU-055]: a run of counts carries no names.
    if property.is_name_alignment() {
        return WitnessOutcome::Inconclusive {
            reason: property.route_b_only_reason(),
        };
    }
    let budget = QueryBudget::start(options.budget_ms);
    let depth = options.depth;
    let initial = initial_vector(flat, initial_marking);
    let is_bad = violation_predicate(flat, property, sink_places, conditional_sinks, env_inject);
    let script = encode_witness_query(
        flat,
        initial_marking,
        property,
        sink_places,
        conditional_sinks,
        env_inject,
        depth,
    );
    let reply = match budget.left().and_then(|left| solver(&script, "witness", left)) {
        Ok(reply) => reply,
        Err(reason) => return WitnessOutcome::Inconclusive { reason },
    };
    match classify_first_line(&reply) {
        Some("sat") => {}
        Some("unsat") => return WitnessOutcome::NoRun,
        _ => {
            return WitnessOutcome::Inconclusive {
                reason: format!("the bounded run at depth {depth} answered unknown"),
            };
        }
    }
    let relation = StepRelation::of(flat, env_inject);
    let step_count = flat.transitions.len() + relation.injections.len();
    // The whole run has to replay before any of it is believed.
    let run = decode_bounded_run(&reply, step_count, depth)
        .filter(|run| replay_run(flat, &initial, run, env_inject, &is_bad).is_some());
    let Some(run) = run else {
        return WitnessOutcome::Inconclusive {
            reason: "the bounded run did not replay under the exact semantics".to_string(),
        };
    };
    match trim_run(&relation, &initial, run, &is_bad, stop) {
        Some(trimmed) => WitnessOutcome::Violated {
            states: trimmed.states,
            steps: trimmed.steps,
        },
        None => WitnessOutcome::Stopped,
    }
}

/// The trim of the witness phase ([VER-025]) on `run`, which replays to a violating
/// marking: its shortest violating prefix ([`violating_prefix`]), then, pass after pass
/// until one drops nothing, each step from the last to the first is dropped where what
/// is left still has a violating prefix, which becomes the run. Returns the trimmed
/// run, replayed, or `None` when `stop`, asked before every candidate, answered `true`.
fn trim_run(
    relation: &StepRelation<'_>,
    initial: &[i64],
    mut run: Vec<usize>,
    is_bad: impl Fn(&[i64]) -> bool,
    stop: impl Fn() -> bool,
) -> Option<ReplayedRun> {
    let prefix = |run: &[usize]| violating_prefix(relation, initial, run, &is_bad);
    let mut replayed = prefix(&run)?;
    run.truncate(replayed.steps.len());
    loop {
        let before = run.len();
        // Only the last marking of `run` violates, so what is left after dropping step
        // `k` passes the same `k` markings first: its prefix keeps more than `k` steps,
        // and every smaller index is still one of the run.
        for k in (0..run.len()).rev() {
            if stop() {
                return None;
            }
            let mut candidate = run.clone();
            candidate.remove(k);
            if let Some(shorter) = prefix(&candidate) {
                candidate.truncate(shorter.steps.len());
                run = candidate;
                replayed = shorter;
            }
        }
        if run.len() == before {
            return Some(replayed);
        }
    }
}

/// The bounded injections' post-caps, `place index → cap`, in place-index order (the
/// verifier's own environment-bound order). An index past the net is dropped rather
/// than emitted as an undeclared variable.
fn environment_caps(
    env_inject: &[(usize, Option<usize>)],
    place_count: usize,
) -> BTreeMap<usize, usize> {
    env_inject
        .iter()
        .filter(|&&(pid, _)| pid < place_count)
        .filter_map(|&(pid, bound)| bound.map(|cap| (pid, cap)))
        .collect()
}

/// The injection steps of a bounded run ([VER-006]), in the list's order — place-index
/// order as the verifier resolves it — so injection `j` takes the selector `T + j` in
/// the script, the decode and the replay alike. An index past the net is dropped, as
/// its cap is.
fn injection_steps(
    env_inject: &[(usize, Option<usize>)],
    place_count: usize,
) -> Vec<(usize, Option<usize>)> {
    env_inject
        .iter()
        .copied()
        .filter(|&(pid, _)| pid < place_count)
        .collect()
}

/// A consume-all input or a reset arc empties the place.
fn clears(ft: &FlatTransition, p: usize) -> bool {
    ft.consume_all.contains(&p) || ft.reset_places.contains(&p)
}

/// The exact guard of `ft` over the marking `m`: inputs, then inhibitors, then reads.
fn guard_conditions(
    ft: &FlatTransition,
    place_count: usize,
    m: impl Fn(usize) -> String,
) -> Vec<String> {
    let mut out = Vec::new();
    for p in 0..place_count {
        let pre = arc(&ft.pre, p);
        if pre > 0 {
            out.push(format!("(>= {} {pre})", m(p)));
        }
    }
    for &p in &ft.inhibitor_places {
        out.push(format!("(= {} 0)", m(p)));
    }
    for &p in &ft.read_places {
        out.push(format!("(>= {} 1)", m(p)));
    }
    out
}

/// `v + delta` with the literal's sign spelled as the operator.
fn shifted(v: &str, delta: i128) -> String {
    if delta == 0 {
        v.to_string()
    } else if delta > 0 {
        format!("(+ {v} {delta})")
    } else {
        format!("(- {v} {})", -delta)
    }
}

/// `C_t` at place `p`: `post − pre`, widened so the difference is exact.
fn column(ft: &FlatTransition, p: usize) -> i128 {
    arc(&ft.post, p) - arc(&ft.pre, p)
}

fn arc(vector: &[i64], p: usize) -> i128 {
    i128::from(vector.get(p).copied().unwrap_or(0))
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use super::*;
    use crate::marking_state::MarkingStateBuilder;
    use crate::net_flattener::flatten;
    use crate::smt_verifier::z3_available;
    use crate::z3_process::{Z3Solver, failure_reason};
    use libpetri_core::action::fork;
    use libpetri_core::arc::{inhibitor, read, reset};
    use libpetri_core::input::{all, at_least, exactly, one};
    use libpetri_core::output::{and, out_place};
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    /// The queue-and-bundle net of [VER-018]/[VER-019]: `produce: budget → q` inhibited
    /// by `s` and `out`, `signal: src → s`, `bundle: all(q) + s → out`, `bundleEmpty: s,
    /// inhibitor(q) → out`, and with `cancellable` the alternative `cancel: src →
    /// cancelled`. `M0 = {budget: n, src: 1}`; the sinks are `out`, `budget` and, when
    /// cancellable, `cancelled`. Places in flat order: budget, (cancelled,) out, q, s, src.
    fn queue_and_bundle(n: usize, cancellable: bool) -> (FlatNet, MarkingState, Vec<String>) {
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
        let mut sinks = vec!["out".to_string(), "budget".to_string()];
        if cancellable {
            transitions.push(t("cancel").input(one(&src)).output(out_place(&cancelled)).build());
            sinks.push("cancelled".to_string());
        }
        let net = PetriNet::builder(format!("queue{n}")).transitions(transitions).build();
        let m0 = MarkingStateBuilder::new().tokens("budget", n).tokens("src", 1).build();
        (flatten(&net), m0, sinks)
    }

    /// `p0 → t0 → p1 → t1 → p2 → t2 → p0`: no ranking exists.
    fn ring() -> FlatNet {
        let p0 = Place::<i32>::new("p0");
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = |name: &str| Transition::builder(name).action(fork());
        let net = PetriNet::builder("ring")
            .transitions([
                t("t0").input(one(&p0)).output(out_place(&p1)).build(),
                t("t1").input(one(&p1)).output(out_place(&p2)).build(),
                t("t2").input(one(&p2)).output(out_place(&p0)).build(),
            ])
            .build();
        flatten(&net)
    }

    /// `fill: start → q`, `gate: sig + gateOpen → done`, with `sig` the place the
    /// environment injects into. Places in flat order: done, gateOpen, q, sig, start.
    fn gated() -> FlatNet {
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
        flatten(&net)
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

    fn vector(flat: &FlatNet, marking: &MarkingState) -> Vec<i64> {
        flat.places.iter().map(|name| marking.count(name) as i64).collect()
    }

    fn weights(flat: &FlatNet, terms: &[(&str, i128)]) -> Vec<i128> {
        let mut w = vec![0i128; flat.place_count];
        for (name, v) in terms {
            w[flat.place_index[*name]] = *v;
        }
        w
    }

    fn index_of(flat: &FlatNet, name: &str) -> usize {
        flat.transitions.iter().position(|ft| ft.name == name).expect("a transition")
    }

    /// The same assertions the TypeScript port makes.
    #[test]
    fn re_checks_a_ranking_exactly_and_rejects_one_some_firing_does_not_lower() {
        let (flat, m0, _) = queue_and_bundle(3, false);
        let initial = vector(&flat, &m0);
        let bound = check_ranking_exact(&flat, &initial, &weights(&flat, &[("budget", 1), ("src", 2), ("s", 1)]))
            .expect("a ranking");
        assert_eq!(bound.bound, 5);
        assert_eq!(format_ranking(&flat, &bound), "budget + s + 2*src");
        // Without a weight on s, bundleEmpty (s -> out) lowers nothing.
        assert_eq!(check_ranking_exact(&flat, &initial, &weights(&flat, &[("budget", 1), ("src", 2)])), None);
    }

    #[test]
    fn a_ranking_that_overflows_is_negative_or_mis_sized_fails_the_check() {
        let (flat, m0, _) = queue_and_bundle(3, false);
        let initial = vector(&flat, &m0);
        // Every column sum fits; r·M0 = 3·(i128::MAX / 2) does not.
        let huge = i128::MAX / 2;
        let overflowing = weights(&flat, &[("budget", huge), ("q", huge - 1), ("src", 2), ("s", 1)]);
        assert_eq!(check_ranking_exact(&flat, &initial, &overflowing), None);
        let negative = weights(&flat, &[("budget", 1), ("src", 2), ("s", 1), ("q", -1)]);
        assert_eq!(check_ranking_exact(&flat, &initial, &negative), None);
        assert_eq!(check_ranking_exact(&flat, &initial, &[1, 0, 0, 1]), None);

        // A transition that can never fire needs no decrease: `t4` of `clearing` raises
        // `2*p + z` by one, and the ranking still holds. A clearing arc counts at its
        // weight: `t3` resets `x` and puts one back, a column entry of +1.
        let flat = clearing();
        let initial = [1, 1, 0, 3, 0, 0];
        let w = weights(&flat, &[("p", 2), ("x", 1), ("y", 1), ("z", 1)]);
        let bound = check_ranking_exact(&flat, &initial, &w).expect("t1..t3 lower it");
        assert_eq!(bound.bound, 5);
        assert_eq!(format_ranking(&flat, &bound), "2*p + x + y + z");
        assert_eq!(format_ranking(&flat, &FiringBound { weights: vec![0; 6], bound: 0 }), "0");
        // A column sum that overflows is not shown to be <= -1: `t2` takes two of `x`.
        let column = weights(&flat, &[("p", 2), ("x", i128::MAX), ("y", 1), ("z", 1)]);
        assert_eq!(check_ranking_exact(&flat, &initial, &column), None);
    }

    /// The same assertions the TypeScript port makes, and the whole script, diffed
    /// byte-identical against it when the port landed.
    #[test]
    fn encodes_a_bounded_run_with_one_selector_per_step_and_replays_only_a_real_firing_sequence() {
        let (flat, m0, sinks) = queue_and_bundle(1, true);
        let initial = vector(&flat, &m0);
        let property = SmtProperty::deadlock_free();
        let script = encode_bounded_run(&flat, &initial, &property, &sinks, &[], &[], 2);
        let transitions = flat.transitions.len();
        assert!(script.contains("(declare-const s1 Int)"));
        assert!(script.contains(&format!("(assert (=> (= s0 {transitions}) (= s1 {transitions})))")));
        assert_eq!(
            script,
            "; Bounded run (VER-019): 2 steps of the exact step relation from M0, idle\n\
             ; only at the end; sat = a run to a violating marking.\n\
             (set-logic QF_LIA)\n\
             (declare-const s0 Int)\n(declare-const s1 Int)\n\
             (declare-const m1_0 Int)\n(declare-const m1_1 Int)\n(declare-const m1_2 Int)\n\
             (declare-const m1_3 Int)\n(declare-const m1_4 Int)\n(declare-const m1_5 Int)\n\
             (declare-const m2_0 Int)\n(declare-const m2_1 Int)\n(declare-const m2_2 Int)\n\
             (declare-const m2_3 Int)\n(declare-const m2_4 Int)\n(declare-const m2_5 Int)\n\
             (assert (and (>= s0 0) (<= s0 5)))\n\
             (assert (=> (= s0 5) (= s1 5)))\n\
             (assert (=> (= s0 0) (and (>= 1 1) (= 0 0) (= 0 0))))\n\
             (assert (=> (= s0 1) (>= 1 1)))\n\
             (assert (=> (= s0 2) (and (>= 0 1) (>= 0 1))))\n\
             (assert (=> (= s0 3) (and (>= 0 1) (= 0 0))))\n\
             (assert (=> (= s0 4) (>= 1 1)))\n\
             (assert (= m1_0 (ite (= s0 0) (- 1 1) 1)))\n\
             (assert (= m1_1 (ite (= s0 4) (+ 0 1) 0)))\n\
             (assert (= m1_2 (ite (= s0 2) (+ 0 1) (ite (= s0 3) (+ 0 1) 0))))\n\
             (assert (= m1_3 (ite (= s0 0) (+ 0 1) (ite (= s0 2) 0 0))))\n\
             (assert (= m1_4 (ite (= s0 1) (+ 0 1) (ite (= s0 2) (- 0 1) (ite (= s0 3) (- 0 1) 0)))))\n\
             (assert (= m1_5 (ite (= s0 1) (- 1 1) (ite (= s0 4) (- 1 1) 1))))\n\
             (assert (and (>= s1 0) (<= s1 5)))\n\
             (assert (=> (= s1 0) (and (>= m1_0 1) (= m1_4 0) (= m1_2 0))))\n\
             (assert (=> (= s1 1) (>= m1_5 1)))\n\
             (assert (=> (= s1 2) (and (>= m1_3 1) (>= m1_4 1))))\n\
             (assert (=> (= s1 3) (and (>= m1_4 1) (= m1_3 0))))\n\
             (assert (=> (= s1 4) (>= m1_5 1)))\n\
             (assert (= m2_0 (ite (= s1 0) (- m1_0 1) m1_0)))\n\
             (assert (= m2_1 (ite (= s1 4) (+ m1_1 1) m1_1)))\n\
             (assert (= m2_2 (ite (= s1 2) (+ m1_2 1) (ite (= s1 3) (+ m1_2 1) m1_2))))\n\
             (assert (= m2_3 (ite (= s1 0) (+ m1_3 1) (ite (= s1 2) 0 m1_3))))\n\
             (assert (= m2_4 (ite (= s1 1) (+ m1_4 1) (ite (= s1 2) (- m1_4 1) (ite (= s1 3) (- m1_4 1) m1_4)))))\n\
             (assert (= m2_5 (ite (= s1 1) (- m1_5 1) (ite (= s1 4) (- m1_5 1) m1_5))))\n\
             (assert (and (or (< m2_0 1) (> m2_4 0) (> m2_2 0))\n         \
             (or (< m2_5 1))\n         \
             (or (< m2_3 1) (< m2_4 1))\n         \
             (or (< m2_4 1) (> m2_3 0))\n         \
             (or (< m2_5 1))\n         \
             (or (>= m2_3 1) (>= m2_4 1) (>= m2_5 1))))\n\
             (check-sat)\n(get-model)"
        );

        let bad = violation_predicate(&flat, &property, &sinks, &[], &[]);
        let (produce, cancel, bundle) = (index_of(&flat, "produce"), index_of(&flat, "cancel"), index_of(&flat, "bundle"));
        let run = replay_run(&flat, &initial, &[produce, cancel], &[], &bad).expect("a real run");
        assert_eq!(run.steps, vec!["produce", "cancel"]);
        assert_eq!(run.states.len(), 3);
        assert_eq!(run.states[0], initial);
        assert_eq!(replay_run(&flat, &initial, &[bundle], &[], &bad), None);
        // A run that ends anywhere but a violation is not one.
        assert_eq!(replay_run(&flat, &initial, &[produce], &[], &bad), None);
        // An index past the net is not a firing.
        assert_eq!(replay_run(&flat, &initial, &[transitions], &[], &bad), None);
        let reply = format!(
            "sat\n(\n  (define-fun s0 () Int\n    {produce})\n  (define-fun s1 () Int\n    {transitions})\n)"
        );
        assert_eq!(decode_bounded_run(&reply, transitions, 2), Some(vec![produce]));
    }

    /// Emitted as the TypeScript port emits them (diffed byte-identical when the port
    /// landed): a transition that can never fire contributes no row, clearing arcs count
    /// at their weight, and an idle-free depth 0 asks the property of `M0` itself.
    #[test]
    fn encodes_the_ranking_and_repeatable_vector_queries() {
        let (flat, m0, sinks) = queue_and_bundle(2, true);
        let initial = vector(&flat, &m0);
        assert_eq!(
            encode_ranking_query(&flat, &initial),
            "; Firing bound (VER-019): weights r >= 0 that every firing lowers by at least one\n\
             ; (r.C_t <= -1, a clearing arc counted at its weight); every run from M0 then has\n\
             ; at most r.M0 firings. sat with the least r.M0.\n\
             (set-logic QF_LIA)\n\
             (declare-const r0 Int)\n(declare-const r1 Int)\n(declare-const r2 Int)\n\
             (declare-const r3 Int)\n(declare-const r4 Int)\n(declare-const r5 Int)\n\
             (assert (>= r0 0))\n(assert (>= r1 0))\n(assert (>= r2 0))\n\
             (assert (>= r3 0))\n(assert (>= r4 0))\n(assert (>= r5 0))\n\
             (assert (<= (+ (- r0) r3) (- 1)))\n\
             (assert (<= (+ r4 (- r5)) (- 1)))\n\
             (assert (<= (+ r2 (- r3) (- r4)) (- 1)))\n\
             (assert (<= (+ r2 (- r4)) (- 1)))\n\
             (assert (<= (+ r1 (- r5)) (- 1)))\n\
             (minimize (+ (* 2 r0) r5))\n(check-sat)\n(get-model)"
        );
        assert_eq!(
            encode_repeatable_vector_query(&flat),
            "; No firing bound (VER-019): firing counts y >= 0, not all zero, with C.y >= 0 on\n\
             ; every place, so the marking equation lets them repeat forever.\n\
             (set-logic QF_LIA)\n\
             (declare-const y0 Int)\n(declare-const y1 Int)\n(declare-const y2 Int)\n\
             (declare-const y3 Int)\n(declare-const y4 Int)\n\
             (assert (>= y0 0))\n(assert (>= y1 0))\n(assert (>= y2 0))\n\
             (assert (>= y3 0))\n(assert (>= y4 0))\n\
             (assert (>= (+ y0 y1 y2 y3 y4) 1))\n\
             (assert (>= (- y0) 0))\n(assert (>= y4 0))\n(assert (>= (+ y2 y3) 0))\n\
             (assert (>= (+ y0 (- y2)) 0))\n(assert (>= (+ y1 (- y2) (- y3)) 0))\n\
             (assert (>= (+ (- y1) (- y4)) 0))\n\
             (minimize (+ y0 y1 y2 y3 y4))\n(check-sat)\n(get-model)"
        );
        let script = encode_bounded_run(&flat, &initial, &SmtProperty::deadlock_free(), &sinks, &[], &[], 0);
        assert_eq!(
            script,
            "; Bounded run (VER-019): 0 steps of the exact step relation from M0, idle\n\
             ; only at the end; sat = a run to a violating marking.\n\
             (set-logic QF_LIA)\n\
             (assert (and (or (< 2 1) (> 0 0) (> 0 0))\n         \
             (or (< 1 1))\n         \
             (or (< 0 1) (< 0 1))\n         \
             (or (< 0 1) (> 0 0))\n         \
             (or (< 1 1))\n         \
             (or (>= 0 1) (>= 0 1) (>= 1 1))))\n\
             (check-sat)\n(get-model)"
        );

        let flat = clearing();
        let script = encode_ranking_query(&flat, &[1, 1, 0, 3, 0, 0]);
        assert!(script.contains(
            "(assert (<= (+ (- r1) r5) (- 1)))\n\
             (assert (<= (+ (* (- 2) r3) r4) (- 1)))\n\
             (assert (<= (+ r2 r3 (- r4) (* (- 2) r5)) (- 1)))\n\
             (minimize (+ r0 r1 (* 3 r3)))"
        ));
        // Three nested `ite`s in the order the TypeScript port nests them.
        let script = encode_bounded_run(&flat, &[1, 1, 0, 3, 0, 0], &SmtProperty::deadlock_free(), &[], &[], &[], 1);
        assert!(script.contains(
            "(assert (= m1_5 (ite (= s0 0) (+ 0 1) (ite (= s0 2) 0 (ite (= s0 3) (- 0 1) 0)))))"
        ));
        assert!(script.contains("(assert (=> (= s0 0) (and (>= 1 1) (= 0 0) (>= 1 1))))"));

        let flat = ring();
        assert!(encode_repeatable_vector_query(&flat).contains(
            "(assert (>= (+ (- y0) y2) 0))\n(assert (>= (+ y0 (- y1)) 0))\n(assert (>= (+ y1 (- y2)) 0))\n"
        ));
    }

    /// A bounded injection's cap follows every step, as `envBounds(M')` does in the
    /// encoder; an unbounded injection carries none.
    #[test]
    fn caps_a_bounded_injection_after_every_step_and_replays_against_the_cap() {
        let flat = gated();
        let initial = vec![0, 0, 0, 0, 1];
        let sig = flat.place_index["sig"];
        let done = vec!["done".to_string()];
        let property = SmtProperty::deadlock_free();
        let script = encode_bounded_run(&flat, &initial, &property, &done, &[], &[(sig, Some(2))], 2);
        assert!(script.contains("(assert (= m1_4 (ite (= s0 0) (- 1 1) 1)))\n(assert (<= m1_3 2))\n"));
        assert!(script.contains("(assert (<= m2_3 2))\n(assert (and "));
        let unbounded = encode_bounded_run(&flat, &initial, &property, &done, &[], &[(sig, None)], 2);
        assert!(!unbounded.contains("(assert (<= m"));

        // `gate` needs a signal: a state already over the cap cannot reach a replayed step.
        let over = vec![0, 1, 0, 3, 1];
        let fill = index_of(&flat, "fill");
        let accept = |_: &[i64]| true;
        assert_eq!(replay_run(&flat, &over, &[fill], &[(sig, Some(2))], accept), None);
        assert!(replay_run(&flat, &over, &[fill], &[(sig, None)], accept).is_some());
    }

    #[test]
    fn decodes_models_as_the_typescript_port_does() {
        // z3's line break before a literal, the negation form, and an index past the net.
        let reply = "sat\n(\n  (define-fun r0 () Int\n    1)\n  (define-fun r3 () Int\n    (- 2))\n  (define-fun r9 () Int 4)\n)";
        assert_eq!(decode_ranking(reply, 5), Some(vec![1, 0, 0, -2, 0]));
        // A malformed name, a `Real`, and a missing space are no definition of a weight.
        let reply = "sat\n((define-fun r+2 () Int 5) (define-fun r0 () Real 1.0) (define-fun r1 ()Int 1) (define-fun r002 () Int 6))";
        assert_eq!(decode_ranking(reply, 5), Some(vec![0, 0, 6, 0, 0]));
        assert_eq!(decode_ranking("unsat\n(error \"model is not available\")", 5), None);
        // A weight too large to hold is the whole decode's failure.
        let huge = "9".repeat(44);
        assert_eq!(decode_ranking(&format!("sat\n((define-fun r0 () Int {huge}) (define-fun r1 () Int 1))"), 5), None);

        // Only the sign of a count matters, whatever its size; `(- 0)` is zero.
        let reply = format!(
            "sat\n((define-fun y0 () Int 0) (define-fun y2 () Int (- 0)) (define-fun y1 () Int {huge}) \
             (define-fun y3 () Int (- 5)) (define-fun y4 () Int 1 ) (define-fun y5 () Int 1))"
        );
        assert_eq!(decode_repeatable_vector(&reply, 5), Some(vec![1, 4]));
        assert_eq!(decode_repeatable_vector("sat\n((define-fun y0 () Int 0))", 5), None);

        // The run stops at the first idle step; `(- 0)` selects transition 0.
        let reply = "sat\n((define-fun s0 () Int 2) (define-fun s1 () Int (- 0)) (define-fun s2 () Int 3) (define-fun s3 () Int 0))";
        assert_eq!(decode_bounded_run(reply, 3, 2), Some(vec![2, 0]));
        assert_eq!(decode_bounded_run(reply, 3, 4), Some(vec![2, 0]));
        // A selector too large for any integer type, or negative, is idle.
        let reply = format!("sat\n((define-fun s0 () Int 1) (define-fun s1 () Int {huge}) (define-fun s2 () Int 0))");
        assert_eq!(decode_bounded_run(&reply, 3, 4), Some(vec![1]));
        assert_eq!(decode_bounded_run("sat\n((define-fun s1 () Int 1) (define-fun s0 () Int (- 1)))", 3, 2), Some(vec![]));
        // No selector at a positive depth is no run; depth 0 needs none.
        assert_eq!(decode_bounded_run("sat\n((define-fun s5 () Int 1))", 3, 4), None);
        assert_eq!(decode_bounded_run("sat\n((define-fun m0 () Int 1))", 3, 0), Some(vec![]));
    }

    /// A scripted solver: answers by the script's first line, records every call.
    struct Stub {
        ranking: Result<String, String>,
        vector: Result<String, String>,
        bmc: Box<dyn Fn(usize) -> Result<String, String>>,
        calls: RefCell<Vec<(String, String, u64)>>,
    }

    impl Stub {
        fn new(ranking: &str, bmc: impl Fn(usize) -> Result<String, String> + 'static) -> Self {
            Stub {
                ranking: Ok(ranking.to_string()),
                vector: Ok("unknown".to_string()),
                bmc: Box::new(bmc),
                calls: RefCell::new(Vec::new()),
            }
        }

        fn solve(&self, script: &str, phase: &str, timeout_ms: u64) -> Result<String, String> {
            let header = script.lines().next().unwrap_or("");
            let label = if header.starts_with("; Firing bound") {
                "ranking".to_string()
            } else if header.starts_with("; No firing bound") {
                "vector".to_string()
            } else {
                let depth = header
                    .strip_prefix("; Bounded run (VER-019): ")
                    .and_then(|rest| rest.split(' ').next())
                    .and_then(|d| d.parse::<usize>().ok())
                    .expect("a bounded run");
                format!("bmc {depth}")
            };
            self.calls.borrow_mut().push((label.clone(), phase.to_string(), timeout_ms));
            match label.as_str() {
                "ranking" => self.ranking.clone(),
                "vector" => self.vector.clone(),
                _ => (self.bmc)(label[4..].parse().unwrap()),
            }
        }

        fn labels(&self) -> Vec<String> {
            self.calls.borrow().iter().map(|(label, _, _)| label.clone()).collect()
        }
    }

    /// `budget + s + 2*src` on the queue without cancel: places budget, out, q, s, src.
    const QUEUE_RANKING: &str = "sat\n((define-fun r0 () Int 1) (define-fun r3 () Int 1) (define-fun r4 () Int 2))";
    /// The same ranking on the cancellable queue: places budget, cancelled, out, q, s, src.
    const CANCEL_RANKING: &str = "sat\n((define-fun r0 () Int 1) (define-fun r4 () Int 1) (define-fun r5 () Int 2))";

    fn phase(
        flat: &FlatNet,
        m0: &MarkingState,
        sinks: &[String],
        env_inject: &[(usize, Option<usize>)],
        stub: &Stub,
        options: FiringBoundOptions,
    ) -> FiringBoundOutcome {
        run_firing_bound_phase(
            flat,
            m0,
            &SmtProperty::deadlock_free(),
            sinks,
            &[],
            env_inject,
            |script: &str, phase: &str, timeout_ms: u64| stub.solve(script, phase, timeout_ms),
            options,
        )
    }

    fn step(depth: usize, answer: DepthAnswer) -> DepthStep {
        DepthStep { depth, answer }
    }

    #[test]
    fn proves_at_the_bound_after_doubling_and_stops_at_the_depth_limit() {
        let (flat, m0, sinks) = queue_and_bundle(12, false);
        let stub = Stub::new(QUEUE_RANKING, |_| Ok("unsat".to_string()));
        let outcome = phase(&flat, &m0, &sinks, &[], &stub, FiringBoundOptions::default());
        let bound = FiringBound { weights: vec![1, 0, 0, 1, 2], bound: 14 };
        assert_eq!(
            outcome,
            FiringBoundOutcome::Proven {
                bound: bound.clone(),
                depths: vec![step(8, DepthAnswer::Unsat), step(14, DepthAnswer::Unsat)],
            }
        );
        assert_eq!(stub.labels(), vec!["ranking", "bmc 8", "bmc 14"]);
        let calls = stub.calls.borrow();
        assert_eq!((calls[0].1.as_str(), calls[1].1.as_str()), ("ranking", "bmc"));
        assert!(calls.iter().all(|&(_, _, timeout)| timeout > 0 && timeout <= 60_000));
        drop(calls);

        let stub = Stub::new(QUEUE_RANKING, |_| Ok("unsat".to_string()));
        let options = FiringBoundOptions { max_depth: 8, ..Default::default() };
        assert_eq!(
            phase(&flat, &m0, &sinks, &[], &stub, options),
            FiringBoundOutcome::Inconclusive {
                reason: "the firing bound 14 exceeds the depth limit 8".to_string(),
                bound: Some(bound),
                depths: vec![step(8, DepthAnswer::Unsat)],
            }
        );

        // A bound below the first depth is model-checked at the bound itself.
        let (flat, m0, sinks) = queue_and_bundle(0, false);
        let stub = Stub::new(QUEUE_RANKING, |_| Ok("unsat".to_string()));
        let outcome = phase(&flat, &m0, &sinks, &[], &stub, FiringBoundOptions::default());
        assert!(matches!(outcome, FiringBoundOutcome::Proven { ref depths, .. } if *depths == vec![step(2, DepthAnswer::Unsat)]));
    }

    #[test]
    fn reports_a_run_only_once_it_replays() {
        let (flat, m0, sinks) = queue_and_bundle(1, true);
        let (produce, cancel, bundle) = (index_of(&flat, "produce"), index_of(&flat, "cancel"), index_of(&flat, "bundle"));
        let stub = Stub::new(CANCEL_RANKING, move |_| {
            Ok(format!("sat\n((define-fun s0 () Int {produce}) (define-fun s1 () Int {cancel}) (define-fun s2 () Int 5))"))
        });
        match phase(&flat, &m0, &sinks, &[], &stub, FiringBoundOptions::default()) {
            FiringBoundOutcome::Violated { bound, depths, states, steps } => {
                assert_eq!(bound.bound, 3);
                assert_eq!(depths, vec![step(3, DepthAnswer::Sat)]);
                assert_eq!(steps, vec!["produce", "cancel"]);
                assert_eq!(states.last().unwrap()[flat.place_index["q"]], 1);
            }
            other => panic!("expected a violation, got {other:?}"),
        }

        let stub = Stub::new(CANCEL_RANKING, move |_| Ok(format!("sat\n((define-fun s0 () Int {bundle}))")));
        assert_eq!(
            phase(&flat, &m0, &sinks, &[], &stub, FiringBoundOptions::default()),
            FiringBoundOutcome::Inconclusive {
                reason: "the bounded run did not replay under the exact semantics".to_string(),
                bound: Some(FiringBound { weights: vec![1, 0, 0, 0, 1, 2], bound: 3 }),
                depths: vec![step(3, DepthAnswer::Sat)],
            }
        );
    }

    #[test]
    fn keeps_every_answered_depth_when_a_later_one_answers_unknown() {
        let (flat, m0, sinks) = queue_and_bundle(12, false);
        let stub = Stub::new(QUEUE_RANKING, |depth| {
            Ok(if depth == 8 { "unsat" } else { "unknown" }.to_string())
        });
        match phase(&flat, &m0, &sinks, &[], &stub, FiringBoundOptions::default()) {
            FiringBoundOutcome::Inconclusive { reason, bound, depths } => {
                assert_eq!(reason, "the bounded run at depth 14 answered unknown");
                assert_eq!(bound.map(|b| b.bound), Some(14));
                assert_eq!(depths, vec![step(8, DepthAnswer::Unsat)]);
            }
            other => panic!("expected inconclusive, got {other:?}"),
        }
        let stub = Stub::new(QUEUE_RANKING, |_| Err("z3 hard timeout after 3s".to_string()));
        match phase(&flat, &m0, &sinks, &[], &stub, FiringBoundOptions::default()) {
            FiringBoundOutcome::Inconclusive { reason, depths, .. } => {
                assert_eq!(reason, "z3 hard timeout after 3s");
                assert!(depths.is_empty());
            }
            other => panic!("expected inconclusive, got {other:?}"),
        }
    }

    #[test]
    fn names_the_repeatable_vector_when_no_ranking_exists() {
        let flat = ring();
        let m0 = MarkingStateBuilder::new().tokens("p0", 1).build();
        let mut stub = Stub::new("unsat", |_| panic!("no bounded run without a bound"));
        stub.vector = Ok("sat\n((define-fun y0 () Int 1) (define-fun y2 () Int 1) (define-fun y1 () Int 1))".to_string());
        let outcome = phase(&flat, &m0, &[], &[], &stub, FiringBoundOptions::default());
        assert_eq!(outcome, FiringBoundOutcome::Unbounded { repeatable: Some(vec![0, 1, 2]) });
        assert_eq!(stub.labels(), vec!["ranking", "vector"]);
        assert!(stub.calls.borrow().iter().all(|(_, phase, _)| phase == "ranking"));

        // Without an answer from the second query the net is still unbounded, unnamed.
        stub.vector = Err("Z3 error: (error \"boom\")".to_string());
        assert_eq!(
            phase(&flat, &m0, &[], &[], &stub, FiringBoundOptions::default()),
            FiringBoundOutcome::Unbounded { repeatable: None }
        );
        stub.vector = Ok("unsat".to_string());
        assert_eq!(
            phase(&flat, &m0, &[], &[], &stub, FiringBoundOptions::default()),
            FiringBoundOutcome::Unbounded { repeatable: None }
        );
    }

    #[test]
    fn steps_aside_on_injection_an_unknown_ranking_a_failed_re_check_or_a_spent_budget() {
        let (flat, m0, sinks) = queue_and_bundle(3, false);
        let inconclusive = |outcome: FiringBoundOutcome| match outcome {
            FiringBoundOutcome::Inconclusive { reason, bound, depths } => {
                assert!(depths.is_empty());
                (reason, bound.map(|b| b.bound))
            }
            other => panic!("expected inconclusive, got {other:?}"),
        };

        let stub = Stub::new(QUEUE_RANKING, |_| panic!("not asked"));
        let reason = inconclusive(phase(&flat, &m0, &sinks, &[(4, None)], &stub, FiringBoundOptions::default()));
        assert_eq!(reason, ("environment injection has no firing bound".to_string(), None));
        assert!(stub.labels().is_empty());

        let stub = Stub::new("unknown", |_| panic!("not asked"));
        let reason = inconclusive(phase(&flat, &m0, &sinks, &[], &stub, FiringBoundOptions::default()));
        assert_eq!(reason, ("the ranking query answered unknown".to_string(), None));

        // No weight on s: bundleEmpty lowers nothing, so the model is not a ranking.
        let stub = Stub::new("sat\n((define-fun r0 () Int 1) (define-fun r4 () Int 2))", |_| panic!("not asked"));
        let reason = inconclusive(phase(&flat, &m0, &sinks, &[], &stub, FiringBoundOptions::default()));
        assert_eq!(reason, ("the ranking failed the exact re-check".to_string(), None));
        let stub = Stub::new("sat\n((define-fun y0 () Int 1))", |_| panic!("not asked"));
        let reason = inconclusive(phase(&flat, &m0, &sinks, &[], &stub, FiringBoundOptions::default()));
        assert_eq!(reason, ("the ranking failed the exact re-check".to_string(), None));

        let stub = Stub::new(
            "sat\n((define-fun r0 () Int 9007199254740992) (define-fun r3 () Int 1) (define-fun r4 () Int 2))",
            |_| panic!("not asked"),
        );
        let reason = inconclusive(phase(&flat, &m0, &sinks, &[], &stub, FiringBoundOptions::default()));
        assert_eq!(reason, ("firing bound 27021597764222978 is too large".to_string(), Some(27021597764222978)));

        let stub = Stub::new(QUEUE_RANKING, |_| panic!("not asked"));
        let options = FiringBoundOptions { budget_ms: 0, ..Default::default() };
        let reason = inconclusive(phase(&flat, &m0, &sinks, &[], &stub, options));
        assert_eq!(reason, ("time budget of 0 ms exhausted".to_string(), None));
        assert!(stub.labels().is_empty());
    }

    /// The transport `linear_bound` uses: one z3 process per script, and a reply without
    /// a verdict line is the failure `failure_reason` names.
    fn z3() -> impl Fn(&str, &str, u64) -> Result<String, String> {
        let solver = Z3Solver::resolve().expect("z3 resolves");
        move |script: &str, phase: &str, timeout_ms: u64| {
            let reply = solver.run(script, phase, timeout_ms, &[])?;
            if classify_first_line(&reply.stdout).is_none() {
                return Err(failure_reason(&reply, timeout_ms));
            }
            Ok(reply.stdout)
        }
    }

    /// [VER-019]'s test derivation, at the phase: the queue's ranking gives the bound 5
    /// and the bounded run at depth 5 proves it; with the cancel alternative a replayed
    /// run violates it; the ring has no ranking, and its three transitions repeat.
    #[test]
    fn decides_the_queue_and_names_the_ring_through_z3() {
        if !z3_available() {
            eprintln!("skipping decides_the_queue_and_names_the_ring_through_z3: z3 binary not on PATH");
            return;
        }
        let property = SmtProperty::deadlock_free();
        let options = FiringBoundOptions { budget_ms: 30_000, ..Default::default() };
        let (flat, m0, sinks) = queue_and_bundle(3, false);
        match run_firing_bound_phase(&flat, &m0, &property, &sinks, &[], &[], z3(), options) {
            FiringBoundOutcome::Proven { bound, depths } => {
                assert_eq!(bound.bound, 5);
                assert_eq!(format_ranking(&flat, &bound), "budget + s + 2*src");
                assert_eq!(depths, vec![step(5, DepthAnswer::Unsat)]);
            }
            other => panic!("expected a proof, got {other:?}"),
        }

        let (flat, m0, sinks) = queue_and_bundle(3, true);
        match run_firing_bound_phase(&flat, &m0, &property, &sinks, &[], &[], z3(), options) {
            FiringBoundOutcome::Violated { bound, depths, states, steps } => {
                assert_eq!(bound.bound, 5);
                assert_eq!(depths, vec![step(5, DepthAnswer::Sat)]);
                assert!(steps.iter().any(|s| s == "cancel"), "{steps:?}");
                assert!(states.last().unwrap()[flat.place_index["q"]] > 0);
                let bad = violation_predicate(&flat, &property, &sinks, &[], &[]);
                assert!(bad(states.last().unwrap()));
            }
            other => panic!("expected a violation, got {other:?}"),
        }

        let flat = ring();
        let m0 = MarkingStateBuilder::new().tokens("p0", 1).build();
        let outcome = run_firing_bound_phase(
            &flat,
            &m0,
            &SmtProperty::place_bound("p0", 1),
            &[],
            &[],
            &[],
            z3(),
            options,
        );
        assert_eq!(outcome, FiringBoundOutcome::Unbounded { repeatable: Some(vec![0, 1, 2]) });
    }

    /// [NU-055] AC4: a run of counts carries no names, so the firing-bound phase steps
    /// aside before any query.
    #[test]
    fn nu055_the_firing_bound_phase_is_inconclusive_for_name_alignment() {
        let (flat, m0, sinks) = queue_and_bundle(2, false);
        for property in [SmtProperty::name_aligned(["q", "s"]), SmtProperty::quiescent_name_aligned(["q", "s"])] {
            let outcome = run_firing_bound_phase(
                &flat,
                &m0,
                &property,
                &sinks,
                &[],
                &[],
                |_: &str, _: &str, _: u64| -> Result<String, String> { panic!("no solver call expected") },
                FiringBoundOptions::default(),
            );
            match outcome {
                FiringBoundOutcome::Inconclusive { reason, bound: None, depths } => {
                    assert!(reason.contains("decided only by the name-partition state-class graph (NU-055, Route B)"), "{reason}");
                    assert!(depths.is_empty());
                }
                other => panic!("expected inconclusive, got {other:?}"),
            }
        }
    }

    // === Injection steps and the bounded witness phase ([VER-025]) ===

    /// `t: e → p1`, with `e` the place the environment injects into. Places in flat
    /// order: e, p1. One transition, so injection 0 takes the selector 1 and idling 2.
    fn env_pair() -> FlatNet {
        let e = Place::<i32>::new("e");
        let p1 = Place::<i32>::new("p1");
        let t = Transition::builder("t").input(one(&e)).output(out_place(&p1)).action(fork()).build();
        flatten(&PetriNet::builder("envPair").transition(t).build())
    }

    /// A `sat` reply whose step `i` selects `selectors[i]`.
    fn model(selectors: &[usize]) -> String {
        let defs: Vec<String> =
            selectors.iter().enumerate().map(|(i, s)| format!("(define-fun s{i} () Int {s})")).collect();
        format!("sat\n({})", defs.join(" "))
    }

    /// `t1: p1 → p2` and `t2: p2 → p1`: a cycle of two steps. Places in flat order: p1,
    /// p2; idling is selector 2.
    fn two_cycle() -> FlatNet {
        let p1 = Place::<i32>::new("p1");
        let p2 = Place::<i32>::new("p2");
        let t = |name: &str| Transition::builder(name).action(fork());
        let net = PetriNet::builder("twoCycle")
            .transitions([
                t("t1").input(one(&p1)).output(out_place(&p2)).build(),
                t("t2").input(one(&p2)).output(out_place(&p1)).build(),
            ])
            .build();
        flatten(&net)
    }

    /// `arm: a → blocker`, `clear: c → d` resetting `blocker`, and `fire: s → bad`
    /// inhibited by `blocker`. Places in flat order: a, bad, blocker, c, d, s; idling is
    /// selector 3.
    fn blocked() -> FlatNet {
        let p = |name: &str| Place::<i32>::new(name);
        let (a, bad, blocker, c, d, s) = (p("a"), p("bad"), p("blocker"), p("c"), p("d"), p("s"));
        let t = |name: &str| Transition::builder(name).action(fork());
        let net = PetriNet::builder("blocked")
            .transitions([
                t("arm").input(one(&a)).output(out_place(&blocker)).build(),
                t("clear").input(one(&c)).reset(reset(&blocker)).output(out_place(&d)).build(),
                t("fire").input(one(&s)).inhibitor(inhibitor(&blocker)).output(out_place(&bad)).build(),
            ])
            .build();
        flatten(&net)
    }

    /// The witness phase on `flat` from `tokens`, answered `reply`, the solver's calls
    /// recorded as `(first script line, phase, timeout)`.
    fn witness_on(
        flat: &FlatNet,
        tokens: &[(&str, usize)],
        property: &SmtProperty,
        env_inject: &[(usize, Option<usize>)],
        options: WitnessOptions,
        reply: Result<String, String>,
    ) -> (WitnessOutcome, Vec<(String, String, u64)>) {
        let mut m0 = MarkingStateBuilder::new();
        for (place, count) in tokens {
            m0 = m0.tokens(*place, *count);
        }
        let calls: RefCell<Vec<(String, String, u64)>> = RefCell::new(Vec::new());
        let outcome = run_witness_phase(
            flat,
            &m0.build(),
            property,
            &[],
            &[],
            env_inject,
            |script: &str, phase: &str, timeout_ms: u64| {
                let header = script.lines().next().unwrap_or("").to_string();
                calls.borrow_mut().push((header, phase.to_string(), timeout_ms));
                reply.clone()
            },
            options,
        );
        (outcome, calls.into_inner())
    }

    /// [`witness_on`] the net [`env_pair`], `e` injected under `bound`.
    fn witness(
        tokens: &[(&str, usize)],
        property: &SmtProperty,
        bound: Option<usize>,
        options: WitnessOptions,
        reply: Result<String, String>,
    ) -> (WitnessOutcome, Vec<(String, String, u64)>) {
        let flat = env_pair();
        witness_on(&flat, tokens, property, &[(flat.place_index["e"], bound)], options, reply)
    }

    /// The whole script, as [VER-025] lays it out: the selector range and the idle
    /// selector move past the injection, a bounded injection is guarded below its bound,
    /// and its arm is the last toucher of its place, so the innermost `ite`.
    #[test]
    fn encodes_an_injection_step_after_the_transitions() {
        let flat = env_pair();
        let e = flat.place_index["e"];
        let property = SmtProperty::place_bound("p1", 1);
        let script = encode_bounded_run(&flat, &[0, 0], &property, &[], &[], &[(e, Some(2))], 2);
        assert_eq!(
            script,
            "; Bounded run (VER-019): 2 steps of the exact step relation from M0, idle\n\
             ; only at the end; sat = a run to a violating marking.\n\
             (set-logic QF_LIA)\n\
             (declare-const s0 Int)\n(declare-const s1 Int)\n\
             (declare-const m1_0 Int)\n(declare-const m1_1 Int)\n\
             (declare-const m2_0 Int)\n(declare-const m2_1 Int)\n\
             (assert (and (>= s0 0) (<= s0 2)))\n\
             (assert (=> (= s0 2) (= s1 2)))\n\
             (assert (=> (= s0 0) (>= 0 1)))\n\
             (assert (=> (= s0 1) (< 0 2)))\n\
             (assert (= m1_0 (ite (= s0 0) (- 0 1) (ite (= s0 1) (+ 0 1) 0))))\n\
             (assert (= m1_1 (ite (= s0 0) (+ 0 1) 0)))\n\
             (assert (<= m1_0 2))\n\
             (assert (and (>= s1 0) (<= s1 2)))\n\
             (assert (=> (= s1 0) (>= m1_0 1)))\n\
             (assert (=> (= s1 1) (< m1_0 2)))\n\
             (assert (= m2_0 (ite (= s1 0) (- m1_0 1) (ite (= s1 1) (+ m1_0 1) m1_0))))\n\
             (assert (= m2_1 (ite (= s1 0) (+ m1_1 1) m1_1)))\n\
             (assert (<= m2_0 2))\n\
             (assert (> m2_1 1))\n\
             (check-sat)\n(get-model)"
        );
        // An unbounded injection is a step with no guard line and no cap.
        let unbounded = encode_bounded_run(&flat, &[0, 0], &property, &[], &[], &[(e, None)], 1);
        assert_eq!(
            unbounded,
            "; Bounded run (VER-019): 1 steps of the exact step relation from M0, idle\n\
             ; only at the end; sat = a run to a violating marking.\n\
             (set-logic QF_LIA)\n\
             (declare-const s0 Int)\n\
             (declare-const m1_0 Int)\n(declare-const m1_1 Int)\n\
             (assert (and (>= s0 0) (<= s0 2)))\n\
             (assert (=> (= s0 0) (>= 0 1)))\n\
             (assert (= m1_0 (ite (= s0 0) (- 0 1) (ite (= s0 1) (+ 0 1) 0))))\n\
             (assert (= m1_1 (ite (= s0 0) (+ 0 1) 0)))\n\
             (assert (> m1_1 1))\n\
             (check-sat)\n(get-model)"
        );
        // Two injections take consecutive selectors in the list's order; an index past
        // the net is no step.
        let both = encode_bounded_run(&flat, &[0, 0], &property, &[], &[], &[(e, None), (1, Some(3)), (7, None)], 1);
        assert!(both.contains("(assert (and (>= s0 0) (<= s0 3)))\n"), "{both}");
        assert!(both.contains("(assert (=> (= s0 2) (< 0 3)))\n"), "{both}");
        assert!(both.contains("(assert (= m1_1 (ite (= s0 0) (+ 0 1) (ite (= s0 2) (+ 0 1) 0))))\n"), "{both}");
        // Without injection the selectors are the transitions' and idling, as before.
        let closed = encode_bounded_run(&flat, &[0, 0], &property, &[], &[], &[], 1);
        assert!(closed.contains("(assert (and (>= s0 0) (<= s0 1)))\n"), "{closed}");
        assert!(closed.contains("(assert (= m1_0 (ite (= s0 0) (- 0 1) 0)))\n"), "{closed}");
    }

    /// Decoded with `T + J`, an injection selector is a step; decoded with `T` it would
    /// end the run, as idling does.
    #[test]
    fn an_injection_selector_decodes_as_a_step_not_as_idle() {
        let reply = model(&[1, 0, 1, 0, 2, 2]);
        assert_eq!(decode_bounded_run(&reply, 2, 6), Some(vec![1, 0, 1, 0]));
        assert_eq!(decode_bounded_run(&reply, 1, 6), Some(vec![]));

        // The phase decodes with `T + J`: read as idle, the run would be empty, and the
        // empty run does not violate the bound.
        let (outcome, _) = witness(
            &[],
            &SmtProperty::place_bound("p1", 1),
            Some(2),
            WitnessOptions::default(),
            Ok(model(&[1, 0, 1, 0, 2, 2, 2, 2])),
        );
        assert_eq!(
            outcome,
            WitnessOutcome::Violated {
                states: vec![vec![0, 0], vec![1, 0], vec![0, 1], vec![1, 1], vec![0, 2]],
                steps: vec!["inject(e)".into(), "t".into(), "inject(e)".into(), "t".into()],
            }
        );
    }

    /// An injection step is taken only below its bound, adds one token, and is named
    /// `inject(<place>)`. It carries no post-cap check, as the injection rule of the
    /// fixpoint encoding carries none; a firing does.
    #[test]
    fn replays_an_injection_below_its_bound_and_without_a_post_cap() {
        let flat = env_pair();
        let e = flat.place_index["e"];
        let accept = |_: &[i64]| true;
        let run = replay_run(&flat, &[0, 0], &[1, 1, 0], &[(e, Some(2))], accept).expect("two injections fit");
        assert_eq!(run.steps, vec!["inject(e)", "inject(e)", "t"]);
        assert_eq!(run.states, vec![vec![0, 0], vec![1, 0], vec![2, 0], vec![1, 1]]);
        // The third injection meets the bound; unbounded, it is a step like the others.
        assert_eq!(replay_run(&flat, &[0, 0], &[1, 1, 1], &[(e, Some(2))], accept), None);
        let run = replay_run(&flat, &[0, 0], &[1, 1, 1], &[(e, None)], accept).expect("no bound");
        assert_eq!(run.steps, vec!["inject(e)", "inject(e)", "inject(e)"]);
        assert_eq!(run.states.last(), Some(&vec![3, 0]));
        // The step after the injections is idling, which is no step of a run.
        assert_eq!(replay_run(&flat, &[0, 0], &[2], &[(e, None)], accept), None);
        // An injection still has to end in a violation.
        assert_eq!(replay_run(&flat, &[0, 0], &[1], &[(e, None)], |m: &[i64]| m[1] > 0), None);

        // `sig` sits over its cap: a firing is refused there, an injection into another
        // place is not.
        let flat = gated();
        let (sig, q) = (flat.place_index["sig"], flat.place_index["q"]);
        let over = vec![0, 1, 0, 3, 1];
        let inject = [(sig, Some(2)), (q, Some(5))];
        let transitions = flat.transitions.len();
        assert_eq!(replay_run(&flat, &over, &[index_of(&flat, "fill")], &inject, accept), None);
        let run = replay_run(&flat, &over, &[transitions + 1], &inject, accept).expect("no post-cap check");
        assert_eq!(run.steps, vec!["inject(q)"]);
        assert_eq!(replay_run(&flat, &over, &[transitions], &inject, accept), None);
    }

    /// The solver pads a run to the depth. Steps are dropped one at a time, last to
    /// first, while what is left still reaches a violation, and the passes repeat until
    /// one drops nothing.
    #[test]
    fn the_witness_phase_trims_a_replayed_run_until_no_step_can_go() {
        // Two injections after the violation are padding; the four before are needed.
        let (outcome, calls) = witness(
            &[],
            &SmtProperty::place_bound("p1", 1),
            Some(2),
            WitnessOptions::default(),
            Ok(model(&[1, 1, 0, 0, 1, 1, 2, 2])),
        );
        assert_eq!(
            outcome,
            WitnessOutcome::Violated {
                states: vec![vec![0, 0], vec![1, 0], vec![2, 0], vec![1, 1], vec![0, 2]],
                steps: vec!["inject(e)".into(), "inject(e)".into(), "t".into(), "t".into()],
            }
        );
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].0, "; Bounded run (VER-019): 8 steps of the exact step relation from M0, idle");
        assert_eq!(calls[0].1, "witness");
        assert!(calls[0].2 > 0 && calls[0].2 <= 7_500, "{calls:?}");

        // `arm, clear, fire`: `fire` alone violates, but `clear` cannot go while `arm`
        // is there, and `arm` is the last step a pass tries. The first pass drops `arm`
        // only; the second then drops `clear`.
        let (outcome, _) = witness_on(
            &blocked(),
            &[("a", 1), ("c", 1), ("s", 1)],
            &SmtProperty::place_bound("bad", 0),
            &[],
            WitnessOptions::default(),
            Ok(model(&[0, 1, 2, 3, 3, 3, 3, 3])),
        );
        assert_eq!(
            outcome,
            WitnessOutcome::Violated {
                states: vec![vec![1, 0, 0, 1, 0, 1], vec![1, 1, 0, 1, 0, 0]],
                steps: vec!["fire".into()],
            }
        );
    }

    /// [VER-013]: the trim asks the verification's stop before every candidate, and a
    /// stop ends the phase as a stop, not as a reason of its own. A run with no step to
    /// drop has no candidate and asks nothing.
    #[test]
    fn the_trim_polls_the_stop_before_every_candidate() {
        let flat = env_pair();
        let inject = [(flat.place_index["e"], Some(2))];
        let phase = |tokens: usize, property: SmtProperty, selectors: &[usize], stop_at: usize| {
            let polls = std::cell::Cell::new(0usize);
            let outcome = witness_phase(
                &flat,
                &MarkingStateBuilder::new().tokens("p1", tokens).build(),
                &property,
                &[],
                &[],
                &inject,
                |_: &str, _: &str, _: u64| Ok(model(selectors)),
                WitnessOptions::default(),
                || {
                    polls.set(polls.get() + 1);
                    polls.get() >= stop_at
                },
            );
            (outcome, polls.get())
        };
        // Four steps are needed: the one pass has four candidates and drops none, so
        // the stop is asked four times, and here it never answers.
        let needed = [1, 1, 0, 0, 1, 1, 2, 2];
        let (outcome, polls) = phase(0, SmtProperty::place_bound("p1", 1), &needed, usize::MAX);
        assert!(matches!(outcome, WitnessOutcome::Violated { ref steps, .. } if steps.len() == 4), "{outcome:?}");
        assert_eq!(polls, 4);
        // A stop on the first poll ends the trim there.
        assert_eq!(phase(0, SmtProperty::place_bound("p1", 1), &needed, 1), (WitnessOutcome::Stopped, 1));
        // And one that comes later, before the third candidate.
        assert_eq!(phase(0, SmtProperty::place_bound("p1", 1), &needed, 3), (WitnessOutcome::Stopped, 3));
        // `M0` violates: the run is empty, there is no candidate, and nothing is asked,
        // although the stop would answer at once.
        let (outcome, polls) = phase(2, SmtProperty::place_bound("p1", 1), &needed, 1);
        assert_eq!(outcome, WitnessOutcome::Violated { states: vec![vec![0, 2]], steps: vec![] });
        assert_eq!(polls, 0);
    }

    /// [VER-013]: the poll of [`run_witness_phase`] is the verification's own. The
    /// solver cancels the call as it answers, so the stop arrives between the reply and
    /// the trim: the phase ends stopped, and the reason names the step it ran in.
    /// Outside a stop scope the same call trims to the end.
    #[test]
    fn the_trim_ends_on_the_verifications_stop_and_polls_nothing_outside_one() {
        let flat = env_pair();
        let inject = [(flat.place_index["e"], Some(2))];
        let token = crate::cancel::CancelToken::new();
        let run = || {
            run_witness_phase(
                &flat,
                &MarkingStateBuilder::new().build(),
                &SmtProperty::place_bound("p1", 1),
                &[],
                &[],
                &inject,
                |_: &str, _: &str, _: u64| {
                    token.cancel();
                    Ok(model(&[1, 1, 0, 0, 1, 1, 2, 2]))
                },
                WitnessOptions::default(),
            )
        };
        // No scope holds the token: its cancellation is nobody's stop.
        assert!(matches!(run(), WitnessOutcome::Violated { ref steps, .. } if steps.len() == 4));

        let token = crate::cancel::CancelToken::new();
        let _scope = crate::total_budget::enter(None, Some(token.clone()));
        assert!(!crate::total_budget::step("witness phase"));
        let run = || {
            run_witness_phase(
                &flat,
                &MarkingStateBuilder::new().build(),
                &SmtProperty::place_bound("p1", 1),
                &[],
                &[],
                &inject,
                |_: &str, _: &str, _: u64| {
                    token.cancel();
                    Ok(model(&[1, 1, 0, 0, 1, 1, 2, 2]))
                },
                WitnessOptions::default(),
            )
        };
        assert_eq!(run(), WitnessOutcome::Stopped);
        assert_eq!(
            crate::total_budget::stopped_reason().as_deref(),
            Some("verification cancelled during witness phase")
        );
        // The stop is sticky: the pipeline's next step finds it.
        assert!(crate::total_budget::step("IC3/PDR query"));
    }

    /// The prefix rule of the trim: a violating initial marking is the run of no steps
    /// whatever the model. Here the model walks the cycle four times and returns to
    /// `M0`; dropping any one of its steps leaves a run that does not replay.
    #[test]
    fn the_witness_phase_reports_the_empty_run_when_the_model_cycles_back_to_a_violating_m0() {
        let (outcome, _) = witness_on(
            &two_cycle(),
            &[("p1", 1)],
            &SmtProperty::place_bound("p1", 0),
            &[],
            WitnessOptions::default(),
            Ok(model(&[0, 1, 0, 1, 0, 1, 0, 1])),
        );
        assert_eq!(outcome, WitnessOutcome::Violated { states: vec![vec![1, 0]], steps: vec![] });
    }

    /// The prefix rule of the trim: a run that passes a violating marking and goes on is
    /// cut there. `t1` marks `p2`; `t2, t1` take the token round once more, and no one
    /// step of `t1, t2, t1` can be dropped from the whole run.
    #[test]
    fn the_witness_phase_cuts_a_run_at_the_first_violating_marking_it_reaches() {
        let (outcome, _) = witness_on(
            &two_cycle(),
            &[("p1", 1)],
            &SmtProperty::place_bound("p2", 0),
            &[],
            WitnessOptions::default(),
            Ok(model(&[0, 1, 0, 2, 2, 2, 2, 2])),
        );
        assert_eq!(
            outcome,
            WitnessOutcome::Violated { states: vec![vec![1, 0], vec![0, 1]], steps: vec!["t1".into()] }
        );
    }

    /// The prefix rule of the trim: what is left after a drop only has to replay up to
    /// its first violating marking. Without `t`, two injections fill `e` to its bound,
    /// which violates; the third injection that follows is not enabled there, and is
    /// cut with everything else past the violation.
    #[test]
    fn the_witness_phase_drops_a_step_when_the_rest_violates_before_its_tail_is_disabled() {
        let (outcome, _) = witness(
            &[],
            &SmtProperty::place_bound("e", 1),
            Some(2),
            WitnessOptions::default(),
            Ok(model(&[1, 0, 1, 1, 2, 2, 2, 2])),
        );
        assert_eq!(
            outcome,
            WitnessOutcome::Violated {
                states: vec![vec![0, 0], vec![1, 0], vec![2, 0]],
                steps: vec!["inject(e)".into(), "inject(e)".into()],
            }
        );
    }

    /// A marking that violates at `M0` is the run of no steps.
    #[test]
    fn the_witness_phase_reports_a_violating_initial_marking_as_the_empty_run() {
        let (outcome, _) = witness(
            &[("p1", 2)],
            &SmtProperty::place_bound("p1", 1),
            Some(2),
            WitnessOptions::default(),
            Ok(model(&[2, 2, 2, 2, 2, 2, 2, 2])),
        );
        assert_eq!(outcome, WitnessOutcome::Violated { states: vec![vec![0, 2]], steps: vec![] });
    }

    /// One query at the depth asked for, not at 8 first, and `unsat` is no proof.
    #[test]
    fn the_witness_phase_asks_once_at_its_depth_and_finds_no_run_on_unsat() {
        let options = WitnessOptions { depth: 12, ..Default::default() };
        let (outcome, calls) =
            witness(&[], &SmtProperty::place_bound("p1", 1), Some(2), options, Ok("unsat".to_string()));
        assert_eq!(outcome, WitnessOutcome::NoRun);
        let headers: Vec<&str> = calls.iter().map(|(header, _, _)| header.as_str()).collect();
        assert_eq!(headers, vec!["; Bounded run (VER-019): 12 steps of the exact step relation from M0, idle"]);
        assert_eq!(WitnessOptions::default(), WitnessOptions { budget_ms: 7_500, depth: 8 });
    }

    /// Everything that is not a replayed run leaves the phase without a verdict, each
    /// with its own reason.
    #[test]
    fn the_witness_phase_steps_aside_on_unknown_a_failed_transport_a_spent_budget_or_a_failed_replay() {
        let property = SmtProperty::place_bound("p1", 1);
        let aside = |reply: Result<String, String>, options: WitnessOptions| {
            let (outcome, calls) = witness(&[], &property, Some(2), options, reply);
            match outcome {
                WitnessOutcome::Inconclusive { reason } => (reason, calls.len()),
                other => panic!("expected inconclusive, got {other:?}"),
            }
        };
        let defaults = WitnessOptions::default();

        let unknown = aside(Ok("unknown".to_string()), defaults);
        assert_eq!(unknown, ("the bounded run at depth 8 answered unknown".to_string(), 1));

        let failed = aside(Err("z3 hard timeout after 3s".to_string()), defaults);
        assert_eq!(failed, ("z3 hard timeout after 3s".to_string(), 1));

        // Nothing is left of the budget once the script is encoded: no query is sent.
        let spent = aside(Ok(model(&[1, 0, 1, 0])), WitnessOptions { budget_ms: 0, ..defaults });
        assert_eq!(spent, ("time budget of 0 ms exhausted".to_string(), 0));

        let not_replayed = "the bounded run did not replay under the exact semantics".to_string();
        // `t` with no token in `e`; a run that ends short of the violation; an
        // injection past the bound; a run that violates after four steps and then takes
        // a `t` that is not enabled (the whole run has to replay before its prefix is
        // believed); and a model with no selector at all.
        for reply in [
            model(&[0]),
            model(&[1, 0, 2]),
            model(&[1, 1, 1, 0, 0]),
            model(&[1, 1, 0, 0, 0]),
            "sat\n()".to_string(),
        ] {
            assert_eq!(aside(Ok(reply), defaults), (not_replayed.clone(), 1));
        }
    }

    /// [NU-055]: a run of counts carries no names, so the witness phase steps aside
    /// before any query.
    #[test]
    fn nu055_the_witness_phase_is_inconclusive_for_name_alignment() {
        let flat = env_pair();
        for property in [SmtProperty::name_aligned(["e", "p1"]), SmtProperty::quiescent_name_aligned(["e", "p1"])] {
            let outcome = run_witness_phase(
                &flat,
                &MarkingStateBuilder::new().build(),
                &property,
                &[],
                &[],
                &[],
                |_: &str, _: &str, _: u64| -> Result<String, String> { panic!("no solver call expected") },
                WitnessOptions::default(),
            );
            match outcome {
                WitnessOutcome::Inconclusive { reason } => {
                    assert!(reason.contains("decided only by the name-partition state-class graph (NU-055, Route B)"), "{reason}");
                }
                other => panic!("expected inconclusive, got {other:?}"),
            }
        }
    }

    /// [VER-025]'s test derivation, at the phase: two injections under a bounded
    /// environment are found and trimmed to the four steps the violation needs; a
    /// violation ten steps away is none at depth 8 and a run at depth 10.
    #[test]
    fn finds_the_run_with_two_injections_through_z3() {
        if !z3_available() {
            eprintln!("skipping finds_the_run_with_two_injections_through_z3: z3 binary not on PATH");
            return;
        }
        let flat = env_pair();
        let m0 = MarkingStateBuilder::new().build();
        let inject = [(flat.place_index["e"], Some(2))];
        let run = |bound: usize, depth: usize| {
            let property = SmtProperty::place_bound("p1", bound);
            let options = WitnessOptions { budget_ms: 30_000, depth };
            run_witness_phase(&flat, &m0, &property, &[], &[], &inject, z3(), options)
        };
        match run(1, 8) {
            WitnessOutcome::Violated { states, mut steps } => {
                assert_eq!(states.len(), 5, "{states:?}");
                assert_eq!(states.last(), Some(&vec![0, 2]));
                steps.sort();
                assert_eq!(steps, vec!["inject(e)", "inject(e)", "t", "t"]);
            }
            other => panic!("expected a violation, got {other:?}"),
        }
        assert_eq!(run(4, 8), WitnessOutcome::NoRun);
        match run(4, 10) {
            WitnessOutcome::Violated { states, steps } => {
                assert_eq!(steps.len(), 10, "{steps:?}");
                assert_eq!(states.last(), Some(&vec![0, 5]));
            }
            other => panic!("expected a violation, got {other:?}"),
        }
    }
}
