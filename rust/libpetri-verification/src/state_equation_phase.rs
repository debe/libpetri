//! The refinement loop of the state-equation phase ([VER-018]).
//!
//! One `QF_LIA` query asks whether a marking the marking equation admits violates the
//! property ([`encode_state_equation_query`]). `unsat` proves it. A `sat` model is a
//! candidate, and each round settles it one of three ways, cheapest first:
//!
//! 1. **Witness** — a real run from `M0` within the candidate's firing counts that
//!    reaches a violation ([`search_within_counts`]). The property is violated, and the
//!    run is the counterexample.
//! 2. **Trap** — an initially marked trap the candidate leaves empty
//!    ([`refuting_trap`]); `Σ_{q∈Q} m_q ≥ 1` is added and the query asked again.
//! 3. **Inductive inequality** — `a·M ≤ b`, kept by the exact step relation and
//!    excluding the candidate ([`encode_inductive_inequality`]), re-checked in exact
//!    integer arithmetic and added. When there is none, the same question is asked
//!    *relative to the marking equation* ([`encode_relative_inequality`]), which is where
//!    the spec's `N·out + q ≤ N` shape comes from. A relative inequality is not inductive
//!    on its own, so it cannot be re-checked the same way: the certificate check over the
//!    equation and its refinements is what re-proves it.
//!
//! Every refinement holds in every reachable marking, so an `unsat` after refinement is
//! still a proof, with the refinements as its certificate. When nothing settles a
//! candidate, or the refinement budget or the deadline runs out, the phase is
//! inconclusive and the verifier falls through to the fixpoint query: the phase can add
//! verdicts, never remove them.
//!
//! `env_inject` is the resolved injection list (`smt_encoder::resolve_env_injection`).
//! Reason strings and [`describe_candidate`] are report text, identical to the
//! TypeScript port's.

use std::cell::Cell;

use crate::abstract_replay::violation_predicate;
use crate::invariant_synthesis::{
    DEFAULT_WEIGHT_BOUND, check_inductive_exact, decode_inductive_inequality,
    encode_inductive_inequality, encode_relative_inequality,
};
use crate::marking_state::MarkingState;
use crate::net_flattener::FlatNet;
use crate::parikh_search::{DEFAULT_NODE_BUDGET, WitnessOutcome, search_within_counts};
use crate::property::SmtProperty;
use crate::rest_set::ConditionalSinks;
use crate::state_equation_query::{
    Candidate, InequalityOrigin, MarkingInequality, decode_candidate,
    encode_state_equation_query, holds_at,
};
use crate::trap_refinement::refuting_trap;
use crate::z3_process::{QueryBudget, classify_first_line};

/// Options of [`run_state_equation_phase`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StateEquationPhaseOptions {
    /// The most refinements the phase adds before it gives up (default 32).
    pub max_refinements: usize,
    /// The magnitude bound on an inductive inequality's weights; `None` (the default)
    /// is [`DEFAULT_WEIGHT_BOUND`] or the tokens `M0` holds, whichever is larger.
    pub weight_bound: Option<i64>,
    /// The node budget of each witness search (default [`DEFAULT_NODE_BUDGET`]).
    pub witness_nodes: usize,
    /// Wall-clock budget for the whole phase in milliseconds; each query gets what is
    /// left (default 60 000).
    pub budget_ms: u64,
}

impl Default for StateEquationPhaseOptions {
    fn default() -> Self {
        Self {
            max_refinements: 32,
            weight_bound: None,
            witness_nodes: DEFAULT_NODE_BUDGET,
            budget_ms: 60_000,
        }
    }
}

/// Outcome of [`run_state_equation_phase`]. Every arm carries the refinements added so
/// far, in the order they were added, and the solver queries sent, both dump phases
/// counted: the report prints them whichever way the phase ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StateEquationOutcome {
    /// The query answered `unsat` over the equation and `refinements`. The caller runs
    /// the certificate check before reporting it
    /// ([`refinement_certificate`](crate::state_equation_query::refinement_certificate)).
    Proven {
        refinements: Vec<MarkingInequality>,
        queries: usize,
    },
    /// A run within a candidate's firing counts reaches a violation.
    Violated {
        /// The markings of the run, `M0` first and the violating one last.
        states: Vec<Vec<i64>>,
        /// The flat transitions fired, one per consecutive pair of `states`.
        steps: Vec<String>,
        refinements: Vec<MarkingInequality>,
        queries: usize,
    },
    /// The phase stepped aside, and why.
    Inconclusive {
        reason: String,
        refinements: Vec<MarkingInequality>,
        queries: usize,
        /// The candidate the phase stopped on, when it stopped holding one.
        candidate: Option<Candidate>,
    },
}

impl StateEquationOutcome {
    /// The refinements added, in order, however the phase ended.
    pub fn refinements(&self) -> &[MarkingInequality] {
        match self {
            Self::Proven { refinements, .. }
            | Self::Violated { refinements, .. }
            | Self::Inconclusive { refinements, .. } => refinements,
        }
    }

    /// The solver queries sent, however the phase ended.
    pub fn queries(&self) -> usize {
        match self {
            Self::Proven { queries, .. }
            | Self::Violated { queries, .. }
            | Self::Inconclusive { queries, .. } => *queries,
        }
    }
}

/// Runs the phase on the flat path. The caller runs the certificate check on a
/// [`StateEquationOutcome::Proven`] before reporting it.
///
/// `solver(script, phase, timeout_ms)` runs one script — `phase` is `state-equation` or
/// `invariant`, the dump name of [VER-013] — within `timeout_ms` and returns its stdout,
/// or the reason when the transport failed or the reply carries no verdict line. Takes
/// the same arguments as the firing-bound phase ([VER-019]) and builds the violation
/// predicate itself, so the two phases cannot be handed inconsistent ones.
#[allow(clippy::too_many_arguments)]
pub fn run_state_equation_phase(
    flat: &FlatNet,
    initial_marking: &MarkingState,
    property: &SmtProperty,
    sink_places: &[String],
    conditional_sinks: &[ConditionalSinks],
    env_inject: &[(usize, Option<usize>)],
    solver: impl Fn(&str, &str, u64) -> Result<String, String>,
    options: StateEquationPhaseOptions,
) -> StateEquationOutcome {
    let budget = QueryBudget::start(options.budget_ms);
    let max_refinements = options.max_refinements;
    let place_count = flat.place_count;
    let transition_count = flat.transitions.len();
    let initial: Vec<i64> = flat
        .places
        .iter()
        .map(|name| i64::try_from(initial_marking.count(name)).unwrap_or(i64::MAX))
        .collect();
    // A bound like `N·out + q ≤ N` weighs a flag by the capacity of the queue it guards,
    // so the default bound grows with the tokens the net starts with.
    let weight_bound = options.weight_bound.unwrap_or_else(|| {
        let tokens = initial.iter().fold(0i64, |sum, &v| sum.saturating_add(v));
        DEFAULT_WEIGHT_BOUND.max(tokens)
    });
    let is_bad = violation_predicate(flat, property, sink_places, conditional_sinks, env_inject);
    let queries = Cell::new(0usize);

    let ask = |script: &str, phase: &str| -> Result<String, String> {
        let left = budget.left()?;
        // Counted once the budget lets it go out, whether or not the transport then
        // delivers a reply: a query the solver timed out on was still sent.
        queries.set(queries.get() + 1);
        solver(script, phase, left)
    };

    // The inequality a synthesis query found, `None` when it proved there is none, or
    // why it failed.
    let synthesize = |script: &str| -> Result<Option<MarkingInequality>, String> {
        let reply = ask(script, "invariant")?;
        match classify_first_line(&reply) {
            Some("sat") => decode_inductive_inequality(&reply, place_count)
                .map(Some)
                .ok_or_else(|| "the inductive-inequality model could not be decoded".to_string()),
            Some("unsat") => Ok(None),
            _ => Err("the inductive-inequality query answered unknown".to_string()),
        }
    };

    // The refinement that excludes `candidate`, cheapest first: a trap, then an
    // inequality inductive on its own, then one inductive only relative to the marking
    // equation. The `Err` is the reason the phase cannot go on, not a failure of the net.
    let refine = |candidate: &Candidate| -> Result<MarkingInequality, String> {
        if let Some(trap) = refuting_trap(flat, &initial, &candidate.marking) {
            return Ok(trap);
        }

        // An inequality inductive on its own is cheaper to find and re-checked exactly;
        // one inductive relative to the equation is asked for only when there is none.
        let inductive = synthesize(&encode_inductive_inequality(
            flat,
            &initial,
            &candidate.marking,
            env_inject,
            weight_bound,
        ))?;
        if let Some(inductive) = inductive {
            if !check_inductive_exact(flat, &initial, env_inject, &inductive)
                || holds_at(&inductive, &candidate.marking)
            {
                return Err("an inductive inequality failed the exact re-check".to_string());
            }
            return Ok(inductive);
        }

        let relative = synthesize(&encode_relative_inequality(
            flat,
            &initial,
            &candidate.marking,
            env_inject,
            weight_bound,
        ))?;
        let Some(relative) = relative else {
            return Err(format!(
                "no trap and no inductive inequality with weights within ±{weight_bound} excludes the candidate"
            ));
        };
        // Deliberately not `check_inductive_exact`: the bound holds only relative to the
        // marking equation, so the exact re-check would reject it. The certificate check
        // re-proves it together with the equation before any verdict rests on it.
        if holds_at(&relative, &candidate.marking) {
            return Err("an inductive inequality does not exclude its candidate".to_string());
        }
        // `decode_inductive_inequality` labels every model inductive; the report must
        // tell this one apart.
        Ok(MarkingInequality {
            origin: InequalityOrigin::Relative,
            ..relative
        })
    };

    let mut refinements: Vec<MarkingInequality> = Vec::new();
    loop {
        let query = encode_state_equation_query(
            flat,
            initial_marking,
            property,
            sink_places,
            env_inject,
            conditional_sinks,
            &refinements,
        );
        let reply = match ask(&query, "state-equation") {
            Ok(reply) => reply,
            Err(reason) => {
                return StateEquationOutcome::Inconclusive {
                    reason,
                    refinements,
                    queries: queries.get(),
                    candidate: None,
                };
            }
        };
        match classify_first_line(&reply) {
            Some("unsat") => {
                return StateEquationOutcome::Proven {
                    refinements,
                    queries: queries.get(),
                };
            }
            Some("sat") => {}
            // `None` does not reach here in the verifier, whose solver refuses a reply
            // with no verdict line; a caller's solver that lets one through reads as
            // `unknown`, never as a candidate.
            _ => {
                return StateEquationOutcome::Inconclusive {
                    reason: "the state-equation query answered unknown".to_string(),
                    refinements,
                    queries: queries.get(),
                    candidate: None,
                };
            }
        }
        let Some(candidate) = decode_candidate(&reply, place_count, transition_count) else {
            return StateEquationOutcome::Inconclusive {
                reason: "the state-equation model could not be decoded".to_string(),
                refinements,
                queries: queries.get(),
                candidate: None,
            };
        };

        // `None` and `Exhausted` both leave the candidate to the refinements: neither is
        // a run, and only a run decides the property this way.
        if let WitnessOutcome::Found { states, steps, .. } = search_within_counts(
            flat,
            &initial,
            &candidate.counts,
            env_inject,
            &is_bad,
            options.witness_nodes,
        ) {
            return StateEquationOutcome::Violated {
                states,
                steps,
                refinements,
                queries: queries.get(),
            };
        }
        if refinements.len() >= max_refinements {
            return StateEquationOutcome::Inconclusive {
                reason: format!("refinement budget exhausted ({max_refinements} refinements)"),
                refinements,
                queries: queries.get(),
                candidate: Some(candidate),
            };
        }

        match refine(&candidate) {
            Ok(refinement) => refinements.push(refinement),
            Err(reason) => {
                return StateEquationOutcome::Inconclusive {
                    reason,
                    refinements,
                    queries: queries.get(),
                    candidate: Some(candidate),
                };
            }
        }
    }
}

/// `a=1, b=1 after t0 x1, t2 x1` — a candidate as the report prints it.
pub fn describe_candidate(flat: &FlatNet, candidate: &Candidate) -> String {
    let marked: Vec<String> = flat
        .places
        .iter()
        .zip(&candidate.marking)
        .filter(|&(_, &v)| v != 0)
        .map(|(name, v)| format!("{name}={v}"))
        .collect();
    let fired: Vec<String> = flat
        .transitions
        .iter()
        .zip(&candidate.counts)
        .filter(|&(_, &v)| v != 0)
        .map(|(ft, v)| format!("{} x{v}", ft.name))
        .collect();
    let marked = if marked.is_empty() {
        "{}".to_string()
    } else {
        marked.join(", ")
    };
    let fired = if fired.is_empty() {
        "no firing".to_string()
    } else {
        fired.join(", ")
    };
    format!("{marked} after {fired}")
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::collections::VecDeque;

    use super::*;
    use crate::marking_state::MarkingStateBuilder;
    use crate::net_flattener::flatten;
    use crate::smt_verifier::z3_available;
    use crate::state_equation_query::{format_inequality, refinement_certificate};
    use crate::z3_process::{Z3Solver, failure_reason};
    use libpetri_core::action::fork;
    use libpetri_core::arc::inhibitor;
    use libpetri_core::input::{all, one};
    use libpetri_core::output::{and, out_place, xor};
    use libpetri_core::petri_net::PetriNet;
    use libpetri_core::place::Place;
    use libpetri_core::transition::Transition;

    /// The join of a compiled workflow ([VER-018] test derivation): `route` sends data
    /// down one arm and an empty marker down the other; a data arm writes `hasdata` with
    /// its `ready`, an empty arm `ready` alone; `mergeStart` takes both readies with
    /// `all(hasdata)`, `mergeSkip` both readies under `inhibitor(hasdata)`. `M0 = {start:
    /// 1}`, sinks `done` and `skipped`. Places in flat order: aData, aEmpty, bData,
    /// bEmpty, done, hasdata, ready0, ready1, skipped, start; transitions: route_b0,
    /// route_b1, armAData, armAEmpty, armBData, armBEmpty, mergeStart, mergeSkip.
    fn join_with_skip() -> (FlatNet, MarkingState, Vec<String>) {
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
        let m0 = MarkingStateBuilder::new().tokens("start", 1).build();
        (flatten(&net), m0, vec!["done".to_string(), "skipped".to_string()])
    }

    /// The queue-and-bundle net: `produce: budget → q` inhibited by `s` and `out`,
    /// `signal: src → s`, `bundle: all(q) + s → out`, `bundleEmpty: s, inhibitor(q) → out`,
    /// and with `cancellable` the alternative `cancel: src → cancelled`. `M0 = {budget:
    /// n, src: 1}`; the sinks are `out`, `budget` and, when cancellable, `cancelled`.
    /// Places in flat order: budget, (cancelled,) out, q, s, src.
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

    /// `ab: a → b`, `ba: b → a` from `{a: 1}`: `{a, b}` is an initially marked trap.
    fn ab_loop() -> (FlatNet, MarkingState) {
        let a = Place::<i32>::new("a");
        let b = Place::<i32>::new("b");
        let t = |name: &str| Transition::builder(name).action(fork());
        let net = PetriNet::builder("loop")
            .transitions([
                t("ab").input(one(&a)).output(out_place(&b)).build(),
                t("ba").input(one(&b)).output(out_place(&a)).build(),
            ])
            .build();
        (flatten(&net), MarkingStateBuilder::new().tokens("a", 1).build())
    }

    fn inequality(flat: &FlatNet, terms: &[(&str, i128)], constant: i128) -> MarkingInequality {
        let mut weights = vec![0i128; flat.place_count];
        for (name, w) in terms {
            weights[flat.place_index[*name]] = *w;
        }
        MarkingInequality { weights, constant, origin: InequalityOrigin::Inductive }
    }

    /// A `sat` model defining the named places and transitions, as z3 prints one.
    fn model(flat: &FlatNet, marking: &[(&str, i64)], counts: &[(&str, i64)]) -> String {
        let mut defs: Vec<String> = marking
            .iter()
            .map(|(name, v)| format!("  (define-fun m{} () Int\n    {v})", flat.place_index[*name]))
            .collect();
        for (name, v) in counts {
            let t = flat.transitions.iter().position(|ft| ft.name == *name).expect("a transition");
            defs.push(format!("  (define-fun n{t} () Int\n    {v})"));
        }
        format!("sat\n(\n{}\n)", defs.join("\n"))
    }

    /// A weighting `a·M <= b` as the synthesis queries' model prints it.
    fn weighting(flat: &FlatNet, terms: &[(&str, i64)], bound: i64) -> String {
        let mut defs: Vec<String> = terms
            .iter()
            .map(|(name, w)| {
                let lit = if *w < 0 { format!("(- {})", -w) } else { w.to_string() };
                format!("(define-fun a{} () Int {lit})", flat.place_index[*name])
            })
            .collect();
        defs.push(format!("(define-fun b () Int {bound})"));
        format!("sat\n({})", defs.join(" "))
    }

    /// A scripted solver: hands out the replies in order and records which query each
    /// call was — `state-equation`, `inductive` or `relative`, read off the script's
    /// header — with the dump phase and the timeout it was given.
    struct Stub {
        replies: RefCell<VecDeque<Result<String, String>>>,
        calls: RefCell<Vec<(String, String, u64)>>,
    }

    impl Stub {
        fn new(replies: Vec<Result<String, String>>) -> Self {
            Stub {
                replies: RefCell::new(replies.into()),
                calls: RefCell::new(Vec::new()),
            }
        }

        fn solve(&self, script: &str, phase: &str, timeout_ms: u64) -> Result<String, String> {
            let header = script.lines().next().unwrap_or("");
            let label = if header.starts_with("; State-equation phase") {
                "state-equation"
            } else if header.starts_with("; Inductive-inequality refinement relative") {
                "relative"
            } else if header.starts_with("; Inductive-inequality refinement") {
                "inductive"
            } else {
                panic!("an unexpected script: {header}")
            };
            self.calls.borrow_mut().push((label.to_string(), phase.to_string(), timeout_ms));
            self.replies.borrow_mut().pop_front().expect("no reply scripted for this query")
        }

        fn labels(&self) -> Vec<String> {
            self.calls.borrow().iter().map(|(label, _, _)| label.clone()).collect()
        }
    }

    fn phase(
        flat: &FlatNet,
        m0: &MarkingState,
        sinks: &[String],
        stub: &Stub,
        options: StateEquationPhaseOptions,
    ) -> StateEquationOutcome {
        run_state_equation_phase(
            flat,
            m0,
            &SmtProperty::deadlock_free(),
            sinks,
            &[],
            &[],
            |script: &str, phase: &str, timeout_ms: u64| stub.solve(script, phase, timeout_ms),
            options,
        )
    }

    /// The join's spurious candidate: `mergeSkip` fired after the data arrived.
    fn skipped_after_data(flat: &FlatNet) -> String {
        model(
            flat,
            &[("hasdata", 1), ("skipped", 1)],
            &[("route_b0", 1), ("armAData", 1), ("armBEmpty", 1), ("mergeSkip", 1)],
        )
    }

    /// The same assertions the TypeScript port makes.
    #[test]
    fn encodes_the_query_with_the_refinements_and_reads_a_candidate_back() {
        let (flat, m0, sinks) = join_with_skip();
        let refinement = inequality(&flat, &[("hasdata", 1), ("ready0", -1), ("ready1", -1)], 0);
        let script = encode_state_equation_query(
            &flat,
            &m0,
            &SmtProperty::deadlock_free(),
            &sinks,
            &[],
            &[],
            std::slice::from_ref(&refinement),
        );
        assert!(script.contains("(set-logic QF_LIA)"));
        assert!(script.contains(&format!("(declare-const n{} Int)", flat.transitions.len() - 1)));
        let (h, r0, r1) = (flat.place_index["hasdata"], flat.place_index["ready0"], flat.place_index["ready1"]);
        assert!(script.contains(&format!("(assert (<= (+ m{h} (- m{r0}) (- m{r1})) 0))")));
        let candidate = decode_candidate(
            &format!("sat\n(\n  (define-fun m{h} () Int\n    1)\n  (define-fun n0 () Int\n    1)\n)"),
            flat.place_count,
            flat.transitions.len(),
        )
        .expect("a candidate");
        assert_eq!(candidate.marking[h], 1);
        assert_eq!(candidate.counts[0], 1);
        assert!(!holds_at(&refinement, &candidate.marking));
        assert_eq!(format_inequality(&flat, &refinement), "hasdata <= ready0 + ready1");
        let certificate = refinement_certificate(flat.place_count, flat.transitions.len(), &[refinement]);
        assert!(certificate.contains(&format!("(x!{} Int)", flat.place_count + flat.transitions.len() - 1)));
        assert!(certificate.contains(&format!("(<= (+ x!{h} (- x!{r0}) (- x!{r1})) 0)")));
    }

    #[test]
    fn describes_a_candidate_as_the_report_prints_it() {
        let (flat, _, _) = join_with_skip();
        let candidate = decode_candidate(&skipped_after_data(&flat), flat.place_count, flat.transitions.len())
            .expect("a candidate");
        assert_eq!(
            describe_candidate(&flat, &candidate),
            "hasdata=1, skipped=1 after route_b0 x1, armAData x1, armBEmpty x1, mergeSkip x1"
        );
        let nothing = Candidate { marking: vec![0; flat.place_count], counts: vec![0; flat.transitions.len()] };
        assert_eq!(describe_candidate(&flat, &nothing), "{} after no firing");
        // A negative value is printed as the model has it, not hidden as a zero would be.
        let negative = Candidate { marking: vec![-1, 0], counts: vec![2] };
        let (flat, _) = ab_loop();
        assert_eq!(describe_candidate(&flat, &negative), "a=-1 after ab x2");
    }

    /// The join's round: the candidate has no witness and no trap, the inductive query
    /// finds `hasdata <= ready0 + ready1`, and the query asked again is `unsat`.
    #[test]
    fn proves_after_an_inductive_inequality_excludes_the_candidate() {
        let (flat, m0, sinks) = join_with_skip();
        let stub = Stub::new(vec![
            Ok(skipped_after_data(&flat)),
            Ok(weighting(&flat, &[("hasdata", 1), ("ready0", -1), ("ready1", -1)], 0)),
            Ok("unsat".to_string()),
        ]);
        let outcome = phase(&flat, &m0, &sinks, &stub, StateEquationPhaseOptions::default());
        let join = inequality(&flat, &[("hasdata", 1), ("ready0", -1), ("ready1", -1)], 0);
        assert_eq!(outcome, StateEquationOutcome::Proven { refinements: vec![join], queries: 3 });
        assert_eq!(outcome.queries(), 3);
        assert_eq!(stub.labels(), vec!["state-equation", "inductive", "state-equation"]);
        let calls = stub.calls.borrow();
        let phases: Vec<&str> = calls.iter().map(|(_, phase, _)| phase.as_str()).collect();
        assert_eq!(phases, vec!["state-equation", "invariant", "state-equation"]);
        assert!(calls.iter().all(|&(_, _, timeout)| timeout > 0 && timeout <= 60_000));
    }

    /// The queue's bound holds only relative to the equation: the exact query answers
    /// `unsat`, the relative one `3*out + q <= 3`, which the phase takes without the exact
    /// re-check — that re-check rejects it — and labels relative.
    #[test]
    fn takes_a_relative_inequality_without_the_exact_re_check() {
        let (flat, m0, sinks) = queue_and_bundle(3, false);
        let candidate = model(
            &flat,
            &[("budget", 2), ("out", 1), ("q", 1)],
            &[("produce", 1), ("signal", 1), ("bundleEmpty", 1)],
        );
        let stub = Stub::new(vec![
            Ok(candidate),
            Ok("unsat".to_string()),
            Ok(weighting(&flat, &[("out", 3), ("q", 1)], 3)),
            Ok("unsat".to_string()),
        ]);
        let outcome = phase(&flat, &m0, &sinks, &stub, StateEquationPhaseOptions::default());
        let mut relative = inequality(&flat, &[("out", 3), ("q", 1)], 3);
        let initial = [3, 0, 0, 0, 1];
        assert!(!check_inductive_exact(&flat, &initial, &[], &relative));
        relative.origin = InequalityOrigin::Relative;
        assert_eq!(format_inequality(&flat, &relative), "3*out + q <= 3");
        assert_eq!(outcome, StateEquationOutcome::Proven { refinements: vec![relative], queries: 4 });
        assert_eq!(stub.labels(), vec!["state-equation", "inductive", "relative", "state-equation"]);
        assert_eq!(stub.calls.borrow()[2].1, "invariant");
    }

    /// A trap is found without the solver: the second query follows the first directly.
    #[test]
    fn refines_with_a_trap_before_asking_for_an_inequality() {
        let (flat, m0) = ab_loop();
        let stub = Stub::new(vec![Ok(model(&flat, &[], &[("ab", 1)])), Ok("unsat".to_string())]);
        let outcome = phase(&flat, &m0, &[], &stub, StateEquationPhaseOptions::default());
        match &outcome {
            StateEquationOutcome::Proven { refinements, queries } => {
                assert_eq!(*queries, 2);
                assert_eq!(refinements.len(), 1);
                assert_eq!(refinements[0].origin, InequalityOrigin::Trap);
                assert_eq!(format_inequality(&flat, &refinements[0]), "a + b >= 1");
            }
            other => panic!("expected a proof, got {other:?}"),
        }
        assert_eq!(stub.labels(), vec!["state-equation", "state-equation"]);
    }

    /// A candidate a run within its counts realises is the violation, with that run.
    #[test]
    fn reports_the_run_a_candidate_realises() {
        let (flat, m0, sinks) = queue_and_bundle(3, true);
        let candidate = model(&flat, &[("q", 3), ("cancelled", 1)], &[("produce", 3), ("cancel", 1)]);
        let stub = Stub::new(vec![Ok(candidate)]);
        match phase(&flat, &m0, &sinks, &stub, StateEquationPhaseOptions::default()) {
            StateEquationOutcome::Violated { states, steps, refinements, queries } => {
                assert_eq!(steps, vec!["produce", "produce", "produce", "cancel"]);
                assert_eq!(states.len(), 5);
                assert_eq!(states[4][flat.place_index["q"]], 3);
                assert!(refinements.is_empty());
                assert_eq!(queries, 1);
            }
            other => panic!("expected a violation, got {other:?}"),
        }
    }

    /// Every way the phase steps aside, with the reason the report prints and the
    /// candidate it stopped on.
    #[test]
    fn steps_aside_with_the_reason_and_the_candidate_it_stopped_on() {
        let (flat, m0, sinks) = join_with_skip();
        let decoded = decode_candidate(&skipped_after_data(&flat), flat.place_count, flat.transitions.len());
        let inconclusive = |replies: Vec<Result<String, String>>, options: StateEquationPhaseOptions| {
            let stub = Stub::new(replies);
            match phase(&flat, &m0, &sinks, &stub, options) {
                StateEquationOutcome::Inconclusive { reason, refinements, queries, candidate } => {
                    (reason, refinements.len(), queries, candidate)
                }
                other => panic!("expected inconclusive, got {other:?}"),
            }
        };
        let defaults = StateEquationPhaseOptions::default();
        let sat = || Ok(skipped_after_data(&flat));

        assert_eq!(
            inconclusive(vec![Err("z3 hard timeout after 61s".to_string())], defaults),
            ("z3 hard timeout after 61s".to_string(), 0, 1, None)
        );
        assert_eq!(
            inconclusive(vec![Ok("unknown".to_string())], defaults),
            ("the state-equation query answered unknown".to_string(), 0, 1, None)
        );
        assert_eq!(
            inconclusive(vec![Ok("sat\n(error \"model is not available\")".to_string())], defaults),
            ("the state-equation model could not be decoded".to_string(), 0, 1, None)
        );
        let options = StateEquationPhaseOptions { max_refinements: 0, ..defaults };
        assert_eq!(
            inconclusive(vec![sat()], options),
            ("refinement budget exhausted (0 refinements)".to_string(), 0, 1, decoded.clone())
        );
        assert_eq!(
            inconclusive(vec![sat(), Ok("unknown".to_string())], defaults),
            ("the inductive-inequality query answered unknown".to_string(), 0, 2, decoded.clone())
        );
        assert_eq!(
            inconclusive(vec![sat(), Err("Z3 error: boom".to_string())], defaults),
            ("Z3 error: boom".to_string(), 0, 2, decoded.clone())
        );
        assert_eq!(
            inconclusive(vec![sat(), Ok("sat\n((define-fun a5 () Int 1))".to_string())], defaults),
            ("the inductive-inequality model could not be decoded".to_string(), 0, 2, decoded.clone())
        );
        // Arm B raises hasdata without ready0: not inductive.
        let weaker = weighting(&flat, &[("hasdata", 1), ("ready0", -1)], 0);
        assert_eq!(
            inconclusive(vec![sat(), Ok(weaker)], defaults),
            ("an inductive inequality failed the exact re-check".to_string(), 0, 2, decoded.clone())
        );
        // Inductive — nothing feeds `start` — but the candidate satisfies it too: no
        // progress, so no refinement.
        let vacuous = weighting(&flat, &[("start", 1)], 1);
        let initial = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
        let start_at_most_one = inequality(&flat, &[("start", 1)], 1);
        assert!(check_inductive_exact(&flat, &initial, &[], &start_at_most_one));
        assert_eq!(
            inconclusive(vec![sat(), Ok(vacuous.clone())], defaults),
            ("an inductive inequality failed the exact re-check".to_string(), 0, 2, decoded.clone())
        );
        // The weight bound in the reason: M0 holds one token, so the default of 8.
        assert_eq!(
            inconclusive(vec![sat(), Ok("unsat".to_string()), Ok("unsat".to_string())], defaults),
            (
                "no trap and no inductive inequality with weights within ±8 excludes the candidate".to_string(),
                0,
                3,
                decoded.clone()
            )
        );
        let options = StateEquationPhaseOptions { weight_bound: Some(2), ..defaults };
        assert_eq!(
            inconclusive(vec![sat(), Ok("unsat".to_string()), Ok("unsat".to_string())], options).0,
            "no trap and no inductive inequality with weights within ±2 excludes the candidate"
        );
        assert_eq!(
            inconclusive(vec![sat(), Ok("unsat".to_string()), Ok(vacuous)], defaults),
            ("an inductive inequality does not exclude its candidate".to_string(), 0, 3, decoded.clone())
        );
        // A refinement kept before the phase stepped aside is still reported.
        let join = weighting(&flat, &[("hasdata", 1), ("ready0", -1), ("ready1", -1)], 0);
        assert_eq!(
            inconclusive(vec![sat(), Ok(join), Ok("unknown".to_string())], defaults),
            ("the state-equation query answered unknown".to_string(), 1, 3, None)
        );
        // No budget, no query: the phase never counts one it did not send.
        let options = StateEquationPhaseOptions { budget_ms: 0, ..defaults };
        assert_eq!(
            inconclusive(Vec::new(), options),
            ("time budget of 0 ms exhausted".to_string(), 0, 0, None)
        );
    }

    /// The weight bound grows with the tokens `M0` holds, so a queue of twelve may weigh
    /// its flag by twelve.
    #[test]
    fn the_default_weight_bound_grows_with_the_initial_tokens() {
        let (flat, m0, sinks) = queue_and_bundle(12, false);
        let candidate = model(
            &flat,
            &[("budget", 11), ("out", 1), ("q", 1)],
            &[("produce", 1), ("signal", 1), ("bundleEmpty", 1)],
        );
        let stub = Stub::new(vec![Ok(candidate), Ok("unsat".to_string()), Ok("unsat".to_string())]);
        match phase(&flat, &m0, &sinks, &stub, StateEquationPhaseOptions::default()) {
            StateEquationOutcome::Inconclusive { reason, .. } => assert_eq!(
                reason,
                "no trap and no inductive inequality with weights within ±13 excludes the candidate"
            ),
            other => panic!("expected inconclusive, got {other:?}"),
        }
    }

    /// The transport the verifier uses: one z3 process per script, and a reply without a
    /// verdict line is the failure `failure_reason` names.
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

    /// [VER-018]'s test derivation, at the phase: the join proves after one inductive
    /// inequality, the queue after one relative to the equation, and the cancellable
    /// queue is violated by the run `produce, produce, produce, cancel`.
    #[test]
    fn decides_the_join_and_the_queues_through_z3() {
        if !z3_available() {
            eprintln!("skipping decides_the_join_and_the_queues_through_z3: z3 binary not on PATH");
            return;
        }
        let property = SmtProperty::deadlock_free();
        let options = StateEquationPhaseOptions { budget_ms: 30_000, ..Default::default() };

        let (flat, m0, sinks) = join_with_skip();
        match run_state_equation_phase(&flat, &m0, &property, &sinks, &[], &[], z3(), options) {
            StateEquationOutcome::Proven { refinements, queries } => {
                let printed: Vec<String> = refinements.iter().map(|r| format_inequality(&flat, r)).collect();
                assert_eq!(printed, vec!["hasdata <= ready0 + ready1"]);
                assert_eq!(refinements[0].origin, InequalityOrigin::Inductive);
                assert_eq!(queries, 3);
            }
            other => panic!("expected a proof, got {other:?}"),
        }

        let (flat, m0, sinks) = queue_and_bundle(3, false);
        match run_state_equation_phase(&flat, &m0, &property, &sinks, &[], &[], z3(), options) {
            StateEquationOutcome::Proven { refinements, .. } => {
            // The refinements before it depend on the models z3 returns (4.11 also adds `out + q <= 3`).
                let decisive = refinements.iter().find(|r| format_inequality(&flat, r) == "3*out + q <= 3");
                assert_eq!(decisive.map(|r| r.origin), Some(InequalityOrigin::Relative), "{refinements:?}");
            }
            other => panic!("expected a proof, got {other:?}"),
        }

        let (flat, m0, sinks) = queue_and_bundle(3, true);
        match run_state_equation_phase(&flat, &m0, &property, &sinks, &[], &[], z3(), options) {
            StateEquationOutcome::Violated { states, steps, .. } => {
                assert_eq!(steps.last().map(String::as_str), Some("cancel"));
                assert!(states.last().unwrap()[flat.place_index["q"]] > 0);
                let bad = violation_predicate(&flat, &property, &sinks, &[], &[]);
                assert!(bad(states.last().unwrap()));
            }
            other => panic!("expected a violation, got {other:?}"),
        }
    }
}
