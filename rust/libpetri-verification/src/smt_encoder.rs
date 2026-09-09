use crate::marking_state::MarkingState;
use crate::net_flattener::{FlatNet, FlatTransition};
use crate::p_invariant::{PInvariant, nonlinear_places};
use crate::property::SmtProperty;
use crate::rest_set::{ConditionalSinks, stranding_excuses};

/// Encoded SMT-LIB2 string for Z3 Spacer (CHC/Horn clauses).
///
/// The encoding uses Constrained Horn Clauses (CHC) for IC3/PDR verification:
/// - A `Reachable` predicate over integer marking variables
/// - Init rule: the initial marking is reachable
/// - Transition rules: each transition produces a successor marking
/// - Error rule: a marking violating the property is an error
///
/// Z3 Spacer then checks if `Error` is reachable from `Init` through transitions.
///
/// With the state equation ([VER-016], [`encode_net`]) the state is `(M, n)` —
/// one firing counter per flat transition after the places — and every
/// transition rule also conjoins `M' = M0 + C·n'`, which hands Spacer every
/// linear consequence of the marking equation (the inequality conservation laws
/// it cannot invent) at no enumeration cost.
#[derive(Debug, Clone)]
pub struct SmtEncoding {
    pub smt2: String,
    /// The number of flat places (the leading arguments of `Reachable`).
    pub place_count: usize,
    /// The number of firing counters that follow the places in `Reachable`
    /// ([VER-016]): one per flat transition when the state equation is encoded,
    /// else 0.
    pub counter_count: usize,
}

/// Options of [`encode_net`].
#[derive(Debug, Clone, Copy, Default)]
pub struct EncodeOptions<'a> {
    /// Emit `:produce-proofs` and `(get-proof)` so an `unsat` reply carries the
    /// refutation the replay decodes (C3).
    pub produce_proofs: bool,
    /// Conditional sinks ([VER-014]); read by `DeadlockFree` only.
    pub conditional_sinks: &'a [ConditionalSinks],
    /// Carry one firing counter per flat transition and conjoin the marking
    /// equation `M' = M0 + C·n'` ([VER-016]) into every rule body. Off by
    /// default (scripts stay byte-identical).
    pub state_equation: bool,
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
///
/// The positional form of [`encode_net`] with no conditional sinks and no state
/// equation; the scripts are byte-identical.
#[allow(clippy::too_many_arguments)]
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
    encode_net(
        flat,
        initial_marking,
        property,
        invariants,
        sink_places,
        env_bounds,
        env_injection,
        &EncodeOptions {
            produce_proofs,
            ..EncodeOptions::default()
        },
    )
}

/// [`encode`] with named options. With `state_equation` ([VER-016]) the state
/// carries one firing counter per flat transition after the places:
/// `Reachable(M, n)`, the initial fact has `n = 0`, transition `k`'s rule
/// increments `n_k` and copies the others, an injection rule copies them all,
/// and every transition rule's body conjoins `m'_p = M0_p + Σ_t C[p][t]·n'_t`
/// for each place whose column is exact (no consume-all / reset arc, not
/// injected) together with `n' ≥ 0`. The error rule quantifies the counters and
/// constrains only the marking.
#[allow(clippy::too_many_arguments)]
pub fn encode_net(
    flat: &FlatNet,
    initial_marking: &MarkingState,
    property: &SmtProperty,
    invariants: &[PInvariant],
    sink_places: &[String],
    env_bounds: &[(String, usize)],
    env_injection: &[(String, Option<usize>)],
    options: &EncodeOptions<'_>,
) -> SmtEncoding {
    let p = flat.place_count;
    let t_count = if options.state_equation { flat.transitions.len() } else { 0 };
    let mut lines = Vec::new();

    // Resolve injectable env places to (index, bound) once.
    let env_inject = resolve_env_injection(flat, env_injection);

    if options.produce_proofs {
        lines.push("(set-option :produce-proofs true)".to_string());
    }
    lines.push("(set-logic HORN)".to_string());
    lines.push(String::new());

    // Declare Reachable predicate: (declare-fun Reachable (Int Int ... Int) Bool)
    // — one Int per place, then one per firing counter ([VER-016]).
    let int_params = (0..p + t_count).map(|_| "Int").collect::<Vec<_>>().join(" ");
    lines.push(format!("(declare-fun Reachable ({int_params}) Bool)"));
    lines.push("(declare-fun Error () Bool)".to_string());
    lines.push(String::new());

    // Variable names: m0, m1, ..., mP-1 for current marking
    //                 m0p, m1p, ..., mP-1p for next marking
    //                 n0, ..., n{T-1} / n0p, ... for the firing counters
    let m_vars: Vec<String> = (0..p).map(|i| format!("m{i}")).collect();
    let mp_vars: Vec<String> = (0..p).map(|i| format!("m{i}p")).collect();
    let n_vars: Vec<String> = counter_vars(t_count, "");
    let np_vars: Vec<String> = counter_vars(t_count, "p");

    // Init rule: (assert (forall () (Reachable M0 0 ... 0)))
    let mut m0_values: Vec<String> = (0..p)
        .map(|i| {
            let count = initial_marking.count(&flat.places[i]);
            count.to_string()
        })
        .collect();
    m0_values.extend((0..t_count).map(|_| "0".to_string()));
    lines.push(format!("(assert (Reachable {}))", m0_values.join(" ")));
    lines.push(String::new());

    // Transition rules. The strengthening conjuncts of rule k are, in order: the
    // P-invariants, then (with the state equation) the counter update of k, the
    // counters' non-negativity, and the marking-equation rows.
    let equation = if t_count > 0 {
        state_equation_conditions(flat, initial_marking, &env_inject, &np_vars, &mp_vars)
    } else {
        Vec::new()
    };
    for (k, ft) in flat.transitions.iter().enumerate() {
        let mut strengthening = invariant_conditions(invariants, &mp_vars);
        if t_count > 0 {
            strengthening.extend(counter_conditions(Some(k), &n_vars, &np_vars));
            strengthening.extend(equation.iter().cloned());
        }
        let rule = encode_transition_rule(
            flat,
            ft,
            &m_vars,
            &mp_vars,
            &n_vars,
            &np_vars,
            &strengthening,
            env_bounds,
        );
        lines.push(rule);
    }

    // Environment-injection rules (VER-006): per injected env place p,
    //   Reachable(M') :- Reachable(M) [AND m_p < bound] AND m'_p = m_p + 1
    //     AND (for q != p) m'_q = m_q.
    // AlwaysAvailable (None) omits the guard. These are NOT flat transitions, so the
    // deadlock encoding (which iterates flat.transitions) never sees them. No
    // P-invariant strengthening — injection deliberately breaks conservation. The
    // counters are carried unchanged ([VER-016]).
    for &(pid, bound) in &env_inject {
        lines.push(encode_injection_rule(p, pid, bound, &m_vars, &mp_vars, &n_vars, &np_vars));
    }
    lines.push(String::new());

    // Error rule (deadlock check relaxes injectable env inputs).
    let error_rule = encode_error_rule(
        flat,
        property,
        &m_vars,
        &n_vars,
        sink_places,
        &env_inject,
        options.conditional_sinks,
    );
    lines.push(error_rule);
    lines.push(String::new());

    // Query: assert the error state is unreachable. Under HORN/Spacer this is SAT
    // when an inductive invariant excludes every violating state (property PROVEN)
    // and UNSAT when no such invariant exists (property VIOLATED). (A bare
    // `(not Error)` — Error is 0-ary, so no quantifier; `(forall () ...)` is an
    // invalid empty binder that z3 rejects.)
    lines.push("(assert (not Error))".to_string());
    lines.push("(check-sat)".to_string());
    if options.produce_proofs {
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
        counter_count: t_count,
    }
}

/// `n0..n{T-1}` (`suffix` = `"p"` for the primed counters), empty when `T` is 0.
fn counter_vars(t_count: usize, suffix: &str) -> Vec<String> {
    (0..t_count).map(|k| format!("n{k}{suffix}")).collect()
}

// === State equation ([VER-016]) ===

/// The places whose column of the incidence matrix is exact in every step: no
/// consume-all / reset arc on them (H1) and not injected (H3'). Only these carry
/// a marking-equation row; the others are unconstrained by it. `env_inject` is
/// the resolved injection list ([`resolve_env_injection`]).
pub fn equation_places(flat: &FlatNet, env_inject: &[(usize, Option<usize>)]) -> Vec<usize> {
    let mut excluded = nonlinear_places(flat);
    for &(pid, _) in env_inject {
        if pid < excluded.len() {
            excluded[pid] = true;
        }
    }
    (0..flat.place_count).filter(|&p| !excluded[p]).collect()
}

/// The counter update of transition `fired` (`None` for an injection step, which
/// fires no counted transition): `n'_k = n_k + 1` for the fired one, `n'_j = n_j`
/// for the rest, then `n' ≥ 0`.
pub fn counter_conditions(fired: Option<usize>, n_vars: &[String], np_vars: &[String]) -> Vec<String> {
    let mut conditions = Vec::with_capacity(2 * np_vars.len());
    for k in 0..n_vars.len() {
        if Some(k) == fired {
            conditions.push(format!("(= {} (+ {} 1))", np_vars[k], n_vars[k]));
        } else {
            conditions.push(format!("(= {} {})", np_vars[k], n_vars[k]));
        }
    }
    for np in np_vars {
        conditions.push(format!("(>= {np} 0)"));
    }
    conditions
}

/// The marking equation over the given marking and counter variables: for every
/// place of [`equation_places`], `m_p = M0_p + Σ_t C[p][t]·n_t` over the flat
/// transitions with a non-zero effect on `p`, in transition order. A coefficient
/// of 1 is the bare counter, −1 is `(- n)`, any other `(* c n)` with a negative
/// `c` written `(- k)`.
pub fn state_equation_conditions(
    flat: &FlatNet,
    initial_marking: &MarkingState,
    env_inject: &[(usize, Option<usize>)],
    n_vars: &[String],
    m_vars: &[String],
) -> Vec<String> {
    let mut conditions = Vec::new();
    for p in equation_places(flat, env_inject) {
        let mut terms: Vec<String> = Vec::new();
        for (t, ft) in flat.transitions.iter().enumerate() {
            let c = ft.post[p] - ft.pre[p];
            if c == 0 {
                continue;
            }
            terms.push(if c == 1 {
                n_vars[t].clone()
            } else if c == -1 {
                format!("(- {})", n_vars[t])
            } else if c > 0 {
                format!("(* {c} {})", n_vars[t])
            } else {
                format!("(* (- {}) {})", -c, n_vars[t])
            });
        }
        let m0 = initial_marking.count(&flat.places[p]);
        conditions.push(if terms.is_empty() {
            format!("(= {} {m0})", m_vars[p])
        } else {
            format!("(= {} (+ {m0} {}))", m_vars[p], terms.join(" "))
        });
    }
    conditions
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
/// (assert (forall ((m0 Int) ... (m0p Int) ... (n0 Int) ... (n0p Int) ...)
///   (=> (and (Reachable m0 ... mP-1 n0 ... nT-1)
///            enabled(M, t)
///            fire(M, M', t)
///            non-negativity(M')
///            strengthening(M', n, n')   ; invariants, then counters + equation
///            env-bounds(M'))
///       (Reachable m0p ... mP-1p n0p ... nT-1p))))
/// ```
///
/// `n_vars` / `np_vars` are empty without the state equation, and the rule is
/// then byte-identical to the places-only encoding.
#[allow(clippy::too_many_arguments)]
fn encode_transition_rule(
    flat: &FlatNet,
    ft: &FlatTransition,
    m_vars: &[String],
    mp_vars: &[String],
    n_vars: &[String],
    np_vars: &[String],
    strengthening: &[String],
    env_bounds: &[(String, usize)],
) -> String {
    let all_vars = quantified(m_vars, mp_vars, n_vars, np_vars);

    let mut conditions = Vec::new();

    // Reachable(m0, ..., mP-1, n0, ..., nT-1)
    conditions.push(reachable_atom(m_vars, n_vars));
    conditions.extend(firing_conditions(flat, ft, m_vars, mp_vars));
    conditions.extend(strengthening.iter().cloned());
    conditions.extend(env_bound_conditions(flat, env_bounds, mp_vars));

    let body = format!("(and {})", conditions.join("\n            "));

    format!(
        "(assert (forall ({all_vars})\n  (=> {body}\n      {})))",
        reachable_atom(mp_vars, np_vars)
    )
}

/// `(m0 Int) ... (m0p Int) ... (n0 Int) ... (n0p Int) ...` — the quantifier list
/// of a rule, marking variables first, then the counters.
fn quantified(m_vars: &[String], mp_vars: &[String], n_vars: &[String], np_vars: &[String]) -> String {
    m_vars
        .iter()
        .chain(mp_vars.iter())
        .chain(n_vars.iter())
        .chain(np_vars.iter())
        .map(|v| format!("({v} Int)"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// `(Reachable m0 ... n0 ...)` over the given marking and counter variables.
fn reachable_atom(m_vars: &[String], n_vars: &[String]) -> String {
    let state: Vec<&str> = m_vars.iter().chain(n_vars.iter()).map(String::as_str).collect();
    format!("(Reachable {})", state.join(" "))
}

/// Encodes one environment-injection rule (VER-006). `bound` of `None` is
/// unbounded (AlwaysAvailable); `Some(k)` guards injection so the place never
/// exceeds `k` (Bounded). All columns other than `pid` are copied unchanged.
#[allow(clippy::too_many_arguments)]
fn encode_injection_rule(
    p: usize,
    pid: usize,
    bound: Option<usize>,
    m_vars: &[String],
    mp_vars: &[String],
    n_vars: &[String],
    np_vars: &[String],
) -> String {
    let all_vars = quantified(m_vars, mp_vars, n_vars, np_vars);

    let mut conditions = Vec::new();
    conditions.push(reachable_atom(m_vars, n_vars));
    conditions.extend(injection_conditions(p, pid, bound, m_vars, mp_vars));
    if !n_vars.is_empty() {
        // An injection fires no counted transition: every counter is copied.
        conditions.extend(counter_conditions(None, n_vars, np_vars));
    }

    let body = format!("(and {})", conditions.join("\n            "));
    format!(
        "(assert (forall ({all_vars})\n  (=> {body}\n      {})))",
        reachable_atom(mp_vars, np_vars)
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
///
/// With `state_equation` ([VER-016]) the counters `n0..` / `n0p..` move with the
/// step (the fired transition's increments, the rest copy, all stay
/// non-negative); the marking equation itself is strengthening and stays out —
/// the candidate carries it and the VCs re-prove it.
pub(crate) fn encode_step_relation_smt2(
    flat: &FlatNet,
    env_bounds: &[(String, usize)],
    env_injection: &[(String, Option<usize>)],
    state_equation: bool,
) -> String {
    let p = flat.place_count;
    let t_count = if state_equation { flat.transitions.len() } else { 0 };
    let m_vars: Vec<String> = (0..p).map(|i| format!("m{i}")).collect();
    let mp_vars: Vec<String> = (0..p).map(|i| format!("m{i}p")).collect();
    let n_vars = counter_vars(t_count, "");
    let np_vars = counter_vars(t_count, "p");
    let env_inject = resolve_env_injection(flat, env_injection);

    let mut disjuncts = Vec::new();
    for (k, ft) in flat.transitions.iter().enumerate() {
        let mut conditions = firing_conditions(flat, ft, &m_vars, &mp_vars);
        if t_count > 0 {
            conditions.extend(counter_conditions(Some(k), &n_vars, &np_vars));
        }
        conditions.extend(env_bound_conditions(flat, env_bounds, &mp_vars));
        disjuncts.push(conjoin(&conditions));
    }
    for &(pid, bound) in &env_inject {
        let mut conditions = injection_conditions(p, pid, bound, &m_vars, &mp_vars);
        if t_count > 0 {
            conditions.extend(counter_conditions(None, &n_vars, &np_vars));
        }
        disjuncts.push(conjoin(&conditions));
    }

    match disjuncts.as_slice() {
        [] => "false".to_string(),
        [single] => single.clone(),
        _ => format!("(or {})", disjuncts.join("\n    ")),
    }
}

/// Encodes the error rule based on the property. The counters ([VER-016]) are
/// quantified and carried in the body atom; the violation constrains the
/// marking only.
fn encode_error_rule(
    flat: &FlatNet,
    property: &SmtProperty,
    m_vars: &[String],
    n_vars: &[String],
    sink_places: &[String],
    env_inject: &[(usize, Option<usize>)],
    conditional_sinks: &[ConditionalSinks],
) -> String {
    let all_vars = quantified(m_vars, &[], n_vars, &[]);

    let violation = encode_property_violation(
        flat,
        property,
        m_vars,
        sink_places,
        env_inject,
        conditional_sinks,
    );

    format!(
        "(assert (forall ({all_vars})\n  (=> (and {} {violation})\n      Error)))",
        reachable_atom(m_vars, n_vars)
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
    conditional_sinks: &[ConditionalSinks],
) -> String {
    match property {
        // DeadlockFree ([VER-002]): a quiescent marking that STRANDS a token —
        // holds one in a place where resting is not permitted. The empty marking
        // strands nothing and is therefore not a violation (AC4). A conditional
        // sink ([VER-014]) is stranded only while every marker that would excuse
        // it is unmarked.
        SmtProperty::DeadlockFree => {
            let Some(mut conditions) = encode_quiescent(flat, m_vars, env_inject) else {
                return "false".to_string();
            };
            let stranded = stranded_conditions(
                &stranding_excuses(flat, sink_places, conditional_sinks),
                m_vars,
            );
            if stranded.is_empty() {
                // Every place is a declared sink: nothing can ever be stranded.
                return "false".to_string();
            }
            conditions.push(format!("(or {})", stranded.join(" ")));
            join_conditions(conditions)
        }
        // TerminatesAtSink ([VER-002]): a quiescent marking that reached NO
        // declared sink. This is the predicate DeadlockFree carried before the
        // VER-002 split, unchanged.
        SmtProperty::TerminatesAtSink => {
            let Some(mut conditions) = encode_quiescent(flat, m_vars, env_inject) else {
                return "false".to_string();
            };
            for pid in sink_indices(flat, sink_places) {
                conditions.push(format!("(= {} 0)", m_vars[pid]));
            }
            join_conditions(conditions)
        }
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
        // JoinedOrDeadLettered (NU-040 AC4): a quiescent state that still holds
        // a `pending` token is a stranded correlation group. Carries NO sink
        // clause — a declared sink must not excuse a stranded group.
        SmtProperty::JoinedOrDeadLettered { pending } => {
            let Some(&pid) = flat.place_index.get(pending) else {
                // Unknown pending place name: no state can violate.
                return "false".to_string();
            };
            let Some(mut conditions) = encode_quiescent(flat, m_vars, env_inject) else {
                return "false".to_string();
            };
            conditions.push(format!("(>= {} 1)", m_vars[pid]));
            join_conditions(conditions)
        }
    }
}

/// One "a token is stranded here" disjunct per place where resting is not
/// always permitted: `(>= m 1)`, conjoined with `(= marker 0)` for every marker
/// whose presence would excuse it ([VER-014]), markers in place-index order.
/// Shared with the name-coloured encoder through `counts`, which renders a
/// place's count term.
pub(crate) fn stranded_conditions(excuses: &[Option<Vec<usize>>], counts: &[String]) -> Vec<String> {
    let mut stranded = Vec::new();
    for (pid, markers) in excuses.iter().enumerate() {
        let Some(markers) = markers else {
            continue;
        };
        if markers.is_empty() {
            stranded.push(format!("(>= {} 1)", counts[pid]));
        } else {
            let unmarked: Vec<String> = markers.iter().map(|&k| format!("(= {} 0)", counts[k])).collect();
            stranded.push(format!("(and (>= {} 1) {})", counts[pid], unmarked.join(" ")));
        }
    }
    stranded
}

/// Declared sink place names resolved to flat-net indices, ascending, deduped.
fn sink_indices(flat: &FlatNet, sink_places: &[String]) -> Vec<usize> {
    let mut idx: Vec<usize> = sink_places
        .iter()
        .filter_map(|name| flat.place_index.get(name).copied())
        .collect();
    idx.sort_unstable();
    idx.dedup();
    idx
}

/// Joins violation conjuncts into the final `Bad(M)` term. An empty conjunction
/// is vacuously true — a net with no transitions is quiescent everywhere.
fn join_conditions(conditions: Vec<String>) -> String {
    if conditions.is_empty() {
        "true".to_string()
    } else {
        format!("(and {})", conditions.join("\n         "))
    }
}

#[allow(clippy::needless_range_loop)]
/// Encodes quiescence: every transition is disabled.
///
/// Shared core of the three quiescence-sensitive properties ([VER-002]
/// DeadlockFree and TerminatesAtSink, [NU-040] JoinedOrDeadLettered). Each
/// conjoins its own clause on top and none is encoded here, so a change to one
/// predicate cannot silently move the others — which is exactly how the sink
/// clause leaked into JoinedOrDeadLettered before NU-040 AC4.
///
/// Returns `None` when some transition is enabled in every marking: no quiescent
/// marking exists, so every property built on this is unviolatable.
///
/// Environment inputs are treated as injectable (VER-006): an input/read on an
/// injectable env place is satisfiable by external injection, so it is NOT a
/// reason the transition is disabled — AlwaysAvailable always satisfies it,
/// Bounded(k) satisfies it iff the required cardinality is ≤ k. This mirrors the
/// state class graph's always-available enablement so a reactive net merely
/// waiting for input is not reported as quiescent; only a genuinely stuck
/// marking is.
/// Whether NO marking of this net can be quiescent, because some transition is
/// enabled in every marking — an environment-gated one whose input injection can
/// always satisfy it ([VER-006]).
///
/// Every quiescence property is then unviolatable and comes back `Proven` for a
/// reason that has nothing to do with the net's own behaviour: an open net with an
/// always-available source never comes to rest, so "no reachable quiescent marking
/// strands a token" is vacuously true. The verdict is correct and says nothing, and
/// a caller reading it as "this workflow completes properly" is misreading it, so
/// the verifier says so in the report.
pub fn quiescence_unreachable(flat: &FlatNet, env_inject: &[(usize, Option<usize>)]) -> bool {
    let m_vars: Vec<String> = (0..flat.place_count).map(|i| format!("m{i}")).collect();
    encode_quiescent(flat, &m_vars, env_inject).is_none()
}

fn encode_quiescent(
    flat: &FlatNet,
    m_vars: &[String],
    env_inject: &[(usize, Option<usize>)],
) -> Option<Vec<String>> {
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
            // Transition is always enabled (possibly via injection) — never quiescent.
            return None;
        }

        disabled_conditions.push(format!("(or {})", disable_reasons.join(" ")));
    }

    Some(disabled_conditions)
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

    // === State equation ([VER-016]) ===

    /// The fork-or-halt net of the VER-015 tests: p0(1) → f → AND(a, b) | halt;
    /// a → ga → ra; b → gb → rb; ra + rb → join → done. Places in flat order:
    /// a, b, done, halt, p0, ra, rb; f expands to two flat transitions.
    fn fork_or_halt() -> (FlatNet, MarkingState) {
        use libpetri_core::output::{and, xor};
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

    fn unreachable_targets() -> SmtProperty {
        SmtProperty::unreachable(vec!["halt".into(), "ra".into(), "rb".into()])
    }

    #[test]
    fn state_equation_is_off_by_default_and_byte_identical_to_encode() {
        let (flat, m0) = fork_or_halt();
        let prop = unreachable_targets();
        let positional = encode(&flat, &m0, &prop, &[], &[], &[], &[], true);
        let named = encode_net(
            &flat,
            &m0,
            &prop,
            &[],
            &[],
            &[],
            &[],
            &EncodeOptions {
                produce_proofs: true,
                ..EncodeOptions::default()
            },
        );
        assert_eq!(named.smt2, positional.smt2);
        assert_eq!(named.counter_count, 0);
        assert!(!named.smt2.contains("n0"));
    }

    #[test]
    fn state_equation_adds_one_counter_per_flat_transition() {
        let (flat, m0) = fork_or_halt();
        let p = flat.place_count;
        let t = flat.transitions.len();
        assert_eq!(t, 5, "f expands to two flat transitions");
        let enc = encode_net(
            &flat,
            &m0,
            &unreachable_targets(),
            &[],
            &[],
            &[],
            &[],
            &EncodeOptions {
                state_equation: true,
                ..EncodeOptions::default()
            },
        );
        assert_eq!(enc.counter_count, t);
        let arity = (0..p + t).map(|_| "Int").collect::<Vec<_>>().join(" ");
        assert!(enc.smt2.contains(&format!("(declare-fun Reachable ({arity}) Bool)")));
        // Init: M0 then T zeros.
        let init = enc.smt2.lines().find(|l| l.starts_with("(assert (Reachable ")).unwrap();
        assert_eq!(init.split(' ').count() - 2, p + t);
        assert!(init.ends_with(" 0 0 0 0 0))"), "{init}");
        // Rule k increments n_k and copies the others; counters are non-negative.
        assert!(enc.smt2.contains("(= n0p (+ n0 1))"));
        assert!(enc.smt2.contains("(= n1p n1)"));
        assert!(enc.smt2.contains("(>= n4p 0)"));
        // Counters are quantified in every rule and unconstrained in the error rule.
        assert!(enc.smt2.contains("(n0 Int)"));
        assert!(enc.smt2.contains("(n0p Int)"));
        let error_rule = &enc.smt2[enc.smt2.rfind("(assert (forall").unwrap()..];
        let m_list = (0..p).map(|i| format!("m{i}")).collect::<Vec<_>>().join(" ");
        assert!(error_rule.contains(&format!("(Reachable {m_list} n0 n1 n2 n3 n4)")), "{error_rule}");
        assert!(!error_rule.contains("n0p"), "{error_rule}");
    }

    #[test]
    fn state_equation_conjoins_the_marking_equation_over_every_exact_place() {
        let (flat, m0) = fork_or_halt();
        let idx = |n: &str| flat.place_index[n];
        let n_vars: Vec<String> = (0..5).map(|k| format!("n{k}")).collect();
        let m_vars: Vec<String> = (0..flat.place_count).map(|i| format!("m{i}")).collect();
        let conds = state_equation_conditions(&flat, &m0, &[], &n_vars, &m_vars);
        assert_eq!(conds.len(), flat.place_count);
        // f's branches are flat transitions 0 (AND(a,b)) and 1 (halt), in enumeration order.
        assert!(conds.contains(&format!("(= m{} (+ 1 (- n0) (- n1)))", idx("p0"))), "{conds:?}");
        assert!(conds.contains(&format!("(= m{} (+ 0 n1))", idx("halt"))), "{conds:?}");
        assert!(conds.contains(&format!("(= m{} (+ 0 n0 (- n2)))", idx("a"))), "{conds:?}");
        assert!(conds.contains(&format!("(= m{} (+ 0 n4))", idx("done"))), "{conds:?}");
        // The encoding carries them over the primed variables in every transition rule.
        let enc = encode_net(
            &flat,
            &m0,
            &unreachable_targets(),
            &[],
            &[],
            &[],
            &[],
            &EncodeOptions {
                state_equation: true,
                ..EncodeOptions::default()
            },
        );
        assert_eq!(idx("p0"), 4);
        assert_eq!(enc.smt2.matches("(= m4p (+ 1 (- n0p) (- n1p)))").count(), 5);
    }

    #[test]
    fn state_equation_leaves_consume_all_and_injected_places_out() {
        use libpetri_core::input::all;
        let q = Place::<i32>::new("q");
        let r = Place::<i32>::new("r");
        let s_p = Place::<i32>::new("s");
        let env = Place::<i32>::new("env");
        let t = Transition::builder("t").input(all(&q)).output(out_place(&r)).action(fork()).build();
        let u = Transition::builder("u").input(one(&env)).output(out_place(&s_p)).action(fork()).build();
        let flat = flatten(&PetriNet::builder("mixed").transitions([t, u]).build());
        let env_injection = vec![("env".to_string(), None)];
        let env_inject = resolve_env_injection(&flat, &env_injection);
        let exact: Vec<&str> = equation_places(&flat, &env_inject)
            .into_iter()
            .map(|p| flat.places[p].as_str())
            .collect();
        assert_eq!(exact, vec!["r", "s"]);
        let enc = encode_net(
            &flat,
            &MarkingStateBuilder::new().tokens("q", 2).build(),
            &SmtProperty::mutual_exclusion(vec!["r".into(), "s".into()]),
            &[],
            &[],
            &[],
            &env_injection,
            &EncodeOptions {
                state_equation: true,
                ..EncodeOptions::default()
            },
        );
        assert!(!enc.smt2.contains(&format!("(= m{}p (+ 2", flat.place_index["q"])));
        assert!(!enc.smt2.contains(&format!("(= m{}p (+ 0", flat.place_index["env"])));
        // The injection rule carries the counters unchanged.
        assert!(enc.smt2.contains("(= n0p n0)\n            (= n1p n1)"), "{}", enc.smt2);
    }

    #[test]
    fn state_equation_step_relation_moves_counters_but_carries_no_equation() {
        let (flat, _) = fork_or_halt();
        let step = encode_step_relation_smt2(&flat, &[], &[], true);
        assert!(step.contains("(= n2p (+ n2 1))"));
        assert!(!step.contains("(+ 1 (- n0p) (- n1p))"));
        assert!(!encode_step_relation_smt2(&flat, &[], &[], false).contains("n0"));
    }

    // === Conditional sinks ([VER-014]) ===

    /// p0(1) → t → AND(a, b); a → ta → XOR(done | halt); b → tb → done unless
    /// `halt` is marked. Flat place order: a, b, done, halt, p0.
    fn halt_net() -> (FlatNet, MarkingState) {
        use libpetri_core::arc::inhibitor;
        use libpetri_core::output::{and, xor};
        let p0 = Place::<i32>::new("p0");
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let done = Place::<i32>::new("done");
        let halt = Place::<i32>::new("halt");
        let t = Transition::builder("t")
            .input(one(&p0))
            .output(and(vec![out_place(&a), out_place(&b)]))
            .action(fork())
            .build();
        let ta = Transition::builder("ta")
            .input(one(&a))
            .output(xor(vec![out_place(&done), out_place(&halt)]))
            .action(fork())
            .build();
        let tb = Transition::builder("tb")
            .input(one(&b))
            .inhibitor(inhibitor(&halt))
            .output(out_place(&done))
            .action(fork())
            .build();
        let net = PetriNet::builder("haltNet").transitions([t, ta, tb]).build();
        (flatten(&net), MarkingStateBuilder::new().tokens("p0", 1).build())
    }

    fn when(marker: &str, places: &[&str]) -> ConditionalSinks {
        ConditionalSinks {
            marker: marker.to_string(),
            places: places.iter().map(|p| p.to_string()).collect(),
        }
    }

    /// The flat encoder conjoins the marker being unmarked into the stranded
    /// disjunct: `(and (>= m_b 1) (= m_halt 0))`; declared sinks and markers
    /// contribute no disjunct.
    #[test]
    fn conditional_sinks_conjoin_the_marker_being_unmarked_into_the_stranded_disjunct() {
        let (flat, _) = halt_net();
        let idx = |n: &str| flat.place_index[n];
        let m_vars: Vec<String> = (0..flat.place_count).map(|i| format!("m{i}")).collect();
        let sinks = vec!["done".to_string()];
        let bad = encode_property_violation(
            &flat,
            &SmtProperty::DeadlockFree,
            &m_vars,
            &sinks,
            &[],
            &[when("halt", &["b"])],
        );
        assert!(
            bad.contains(&format!("(and (>= m{} 1) (= m{} 0))", idx("b"), idx("halt"))),
            "{bad}"
        );
        assert!(!bad.contains(&format!("(>= m{} 1)", idx("done"))), "{bad}");
        assert!(!bad.contains(&format!("(>= m{} 1)", idx("halt"))), "{bad}");
        // Without the declaration the same place is an unconditional disjunct.
        let plain =
            encode_property_violation(&flat, &SmtProperty::DeadlockFree, &m_vars, &sinks, &[], &[]);
        assert!(plain.contains(&format!("(>= m{} 1)", idx("b"))), "{plain}");
        assert!(plain.contains(&format!("(>= m{} 1)", idx("halt"))), "{plain}");
    }

    /// [VER-014]: scripts without a conditional declaration are byte-identical
    /// to those of [VER-002]; a declaration changes the stranded disjunction and
    /// nothing else.
    #[test]
    fn encode_net_without_conditional_sinks_is_byte_identical_to_encode() {
        let (flat, m0) = halt_net();
        let sinks = vec!["done".to_string()];
        let before = encode(&flat, &m0, &SmtProperty::DeadlockFree, &[], &sinks, &[], &[], false);
        let after = encode_net(
            &flat,
            &m0,
            &SmtProperty::DeadlockFree,
            &[],
            &sinks,
            &[],
            &[],
            &EncodeOptions {
                conditional_sinks: &[],
                ..EncodeOptions::default()
            },
        );
        assert_eq!(after.smt2, before.smt2);
        let declared = encode_net(
            &flat,
            &m0,
            &SmtProperty::DeadlockFree,
            &[],
            &sinks,
            &[],
            &[],
            &EncodeOptions {
                conditional_sinks: &[when("halt", &["b"])],
                ..EncodeOptions::default()
            },
        );
        assert_ne!(declared.smt2, before.smt2);
        assert_eq!(declared.smt2.lines().count(), before.smt2.lines().count());
        assert!(declared.smt2.contains("(= m3 0)"), "{}", declared.smt2);
    }
}
