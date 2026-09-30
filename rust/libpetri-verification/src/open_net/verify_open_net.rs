//! A subnet verified on its own against a contract, with its ports played by the
//! environment ([VER-022]).
//!
//! The subnet is closed with the environment its contract describes, and the closed net's
//! untimed state-class graph is enumerated. When the graph closes, the verdict is exact.
//! When it does not, a violation found among the explored classes is still real, and the
//! rest of the contract goes to the SMT pipeline, through the properties it already has.

use std::collections::{BTreeSet, HashSet};
use std::fmt;
use std::time::Instant;

use libpetri_core::petri_net::PetriNet;

use crate::cancel::CancelToken;
use crate::reaping;
use crate::result::Verdict;
use crate::total_budget;
use crate::smt_verifier::SmtVerifier;
use crate::in_flight::{self, InFlight};
use crate::name_fragment;
use crate::terminal_places::inhibit_on_terminals;

use super::closure::close_open_net;
use super::contract::OpenNetContract;
use super::graph_route::decide_on_graph;
use super::report::{ReportInput, render_report};
use super::result::{ContractViolation, OpenNetResult, OpenNetRoute};
use super::smt_route::{SubjectCertificate, decide_via_smt};

/// Configures each [`SmtVerifier`] the SMT route builds, e.g.
/// `Box::new(|v| v.timeout(120_000).state_equation(true))`.
pub type SmtConfigurator = Box<dyn for<'a> Fn(SmtVerifier<'a>) -> SmtVerifier<'a> + Send + Sync>;

/// Options for [`verify_open_net`].
///
/// `#[non_exhaustive]`, as `ExecutorOptions` is: this struct gains options, and each one
/// would break a struct literal. Start from [`Default`] and the `with_*` setters:
///
/// ```ignore
/// OpenNetOptions::default()
///     .with_max_classes(0)
///     .with_configure_smt(Box::new(|v| v.timeout(120_000)))
/// ```
#[non_exhaustive]
pub struct OpenNetOptions {
    /// Class budget for the state-class graph (default 50 000, as for [VER-017]). `0` skips
    /// the graph.
    pub max_classes: usize,
    /// Whether to ask the SMT pipeline when the graph does not close (default `true`).
    pub smt: bool,
    /// Configures each `SmtVerifier` the SMT route builds (default: none).
    pub configure_smt: Option<SmtConfigurator>,
    /// Time for the firing-bound query that decides termination on the SMT route (default
    /// 60 s).
    pub termination_timeout_ms: u64,
    /// Cancels the verification ([VER-013]; default: none). The graph build polls it,
    /// every `SmtVerifier` the SMT route builds gets it (before `configure_smt`, which may
    /// replace it), and the termination query's z3 process is killed at once. A part left
    /// undecided by it reports `verification cancelled during <phase>`, and the verdict is
    /// `Unknown`.
    pub cancel: Option<CancelToken>,
    /// Reads quiescence strictly, as if no `deadline` / `window` transition were ever
    /// reaped ([TIME-013]; default `false`). By default a marking where every enabled
    /// transition is reapable counts as quiescent on both routes, as
    /// [`SmtVerifier::assume_no_reaping`] describes; with `true` the report of a net with
    /// such a transition says the verdict assumes none is reaped.
    pub assume_no_reaping: bool,
    /// Reads every firing as one atomic step ([VER-004]; default `false`). By default a
    /// transition whose output some transition tests with an inhibitor, reset or drain, or
    /// that marks a terminal place ([EXEC-042], which inhibits every transition), is
    /// verified as a start and a completion step on both routes, as
    /// [`SmtVerifier::assume_atomic_firing`] describes; with `true` the report of a net
    /// with such a transition says the verdict assumes atomic firings.
    pub assume_atomic_firing: bool,
}

impl Default for OpenNetOptions {
    fn default() -> Self {
        Self {
            max_classes: DEFAULT_MAX_CLASSES,
            smt: true,
            configure_smt: None,
            termination_timeout_ms: 60_000,
            cancel: None,
            assume_no_reaping: false,
            assume_atomic_firing: false,
        }
    }
}

impl OpenNetOptions {
    /// Sets the class budget for the state-class graph; `0` skips the graph.
    pub fn with_max_classes(mut self, max_classes: usize) -> Self {
        self.max_classes = max_classes;
        self
    }

    /// Sets whether to ask the SMT pipeline when the graph does not close.
    pub fn with_smt(mut self, smt: bool) -> Self {
        self.smt = smt;
        self
    }

    /// Configures each `SmtVerifier` the SMT route builds. Carrier places and mint
    /// transitions declared here also reach the in-flight split and the mint check that
    /// run before either route ([VER-004], [NU-010]).
    pub fn with_configure_smt(mut self, configure: SmtConfigurator) -> Self {
        self.configure_smt = Some(configure);
        self
    }

    /// Sets the time for the firing-bound query that decides termination on the SMT route.
    pub fn with_termination_timeout_ms(mut self, ms: u64) -> Self {
        self.termination_timeout_ms = ms;
        self
    }

    /// Cancels the verification from outside it ([VER-013]).
    pub fn with_cancel(mut self, token: &CancelToken) -> Self {
        self.cancel = Some(token.clone());
        self
    }

    /// Reads quiescence strictly, as if no transition were ever reaped ([TIME-013]).
    pub fn with_assume_no_reaping(mut self, assume: bool) -> Self {
        self.assume_no_reaping = assume;
        self
    }

    /// Reads every firing as one atomic step ([VER-004]).
    pub fn with_assume_atomic_firing(mut self, assume: bool) -> Self {
        self.assume_atomic_firing = assume;
        self
    }
}

impl fmt::Debug for OpenNetOptions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OpenNetOptions")
            .field("max_classes", &self.max_classes)
            .field("smt", &self.smt)
            .field("configure_smt", &self.configure_smt.as_ref().map(|_| ".."))
            .field("termination_timeout_ms", &self.termination_timeout_ms)
            .field("cancel", &self.cancel)
            .field("assume_no_reaping", &self.assume_no_reaping)
            .field("assume_atomic_firing", &self.assume_atomic_firing)
            .finish()
    }
}

const DEFAULT_MAX_CLASSES: usize = 50_000;
const METHOD_ENUMERATION: &str = "open-net contract by state-space enumeration (VER-022)";
const METHOD_SMT: &str = "open-net contract by the SMT pipeline (VER-022)";

/// Why the graph was not built on a net with match transitions. Report text, so identical to
/// TypeScript's.
const GRAPH_SKIPPED_MATCH: &str = "the closed net declares match (ν-join) transitions, which the graph does not model";
/// Why the graph was not built when the class budget is zero.
const GRAPH_SKIPPED_BUDGET: &str = "class budget 0";
/// Why the graph was not built on a net whose in-flight actions the split cannot express.
const GRAPH_SKIPPED_IN_FLIGHT: &str = "the closed net has in-flight actions the verifier cannot split (VER-004)";
/// Why the graph was not built when a declared mint transition is not in the net.
const GRAPH_SKIPPED_MINT: &str = "a declared mint transition is not in the net (NU-010)";
/// The phase a cancellation of the graph build is reported in ([VER-013]).
const PHASE_GRAPH: &str = "open-net state-class graph";

/// Verifies `net` in isolation against `contract` ([VER-022]).
///
/// `Proven` means that, in every run of the environment the contract assumes, every
/// quiescent marking meets the contract, and (unless termination is waived) every run comes
/// to rest. The claim is untimed, priority-blind and value-blind, like every route's
/// ([VER-004]). `Violated` lists every broken part with a shortest witness, and `Unknown`
/// says why neither route decided.
///
/// # Panics
/// When the net violates CORE-043, as every verifier does, or when the closure's names
/// collide with the net's ([`close_open_net`](super::close_open_net)).
pub fn verify_open_net(net: &PetriNet, contract: &OpenNetContract, options: &OpenNetOptions) -> OpenNetResult {
    let start = Instant::now();
    // [EXEC-042] / [VER-022]: the net's own terminal places are designed terminals of the
    // contract, and each inhibits every transition of the closed net, the environment's
    // included — the runtime refuses what arrives after the stop. Neither changes anything
    // for a net without terminal places.
    let merged = contract.with_net_terminals(net);
    let contract = merged.as_ref().unwrap_or(contract);
    let mut closed = close_open_net(net, contract);
    // [NU-051] / [NU-010]: the carrier places and mint transitions a `configure_smt` hook
    // declares. The split below refuses a writer into a carrier as the SMT route's own
    // would, and a declared mint that is not in the net is rejected before either route
    // runs, as `SmtVerifier::verify` rejects it.
    let (carriers, unknown_mint) = match options.configure_smt.as_ref() {
        Some(configure) => {
            let probe = configure(SmtVerifier::for_net(&closed.net));
            let carriers = probe.configured_carrier_places().clone();
            (carriers, name_fragment::unknown_mint_reason(&closed.net, probe.configured_mint_transitions()))
        }
        None => (HashSet::new(), None),
    };
    // [VER-004]: a transition whose output another tests non-monotonically is verified as a
    // start and a completion step, environment transitions included. Before the terminal
    // rewrite, so a terminal counts as a test and inhibits the completion steps too.
    let mut in_flight_refusal: Option<String> = None;
    let mut in_flight_places: Vec<String> = Vec::new();
    let environment: HashSet<String> = closed.environment.iter().map(|(name, _)| name.clone()).collect();
    let in_flight_line = if options.assume_atomic_firing {
        let split = in_flight::in_flight_transitions(&closed.net, &environment);
        (!split.is_empty()).then(|| in_flight::atomic_assumption_note(&split))
    } else {
        match in_flight::split_in_flight(&closed.net, &carriers, &environment) {
            InFlight::Atomic => None,
            InFlight::Split { net: split_net, split } => {
                closed.net = split_net;
                in_flight_places = split.iter().map(|t| in_flight::in_flight_place(t)).collect();
                Some(format!("{}{}", in_flight::split_note(&split), in_flight::FLUSH_NOTE))
            }
            InFlight::Refused { reason } => {
                in_flight_refusal = Some(reason);
                None
            }
        }
    };
    // A terminal stop abandons an action in flight, leaving its in-flight place marked: each
    // net terminal excuses those places too, as it excuses every place of the net.
    let markers: Vec<String> = net.terminals().iter().map(|p| p.name().to_string()).collect();
    let excusing = contract.with_excused(&markers, &in_flight_places);
    let contract = excusing.as_ref().unwrap_or(contract);
    if let Some(inhibited) = inhibit_on_terminals(&closed.net) {
        closed.net = inhibited;
    }
    let max_classes = options.max_classes;
    // [TIME-013]: the closed net's reapable transitions, named before the SMT route strips
    // its timing; none are read so under `assume_no_reaping`.
    let reapable_in_net = reaping::reapable_transitions(&closed.net);
    let reapable = if options.assume_no_reaping { BTreeSet::new() } else { reapable_in_net.clone() };
    let reaping_line = (!reapable_in_net.is_empty()).then(|| {
        let note = if options.assume_no_reaping {
            reaping::no_reaping_assumption_note(&reapable_in_net)
        } else {
            reaping::reap_aware_note(&reapable_in_net)
        };
        note.trim_end().to_string()
    });
    let notes: Vec<String> = [reaping_line, in_flight_line.map(|l| l.trim_end().to_string())]
        .into_iter()
        .flatten()
        .collect();
    let reaping_line = (!notes.is_empty()).then(|| notes.join("\n"));
    // Every place a port trace may mention: the contract's own, plus the closure's. [VER-022]
    // reserves "port" for a place the environment shares with the subnet, which is narrower.
    let traced_places = contract.places();
    // The graph is name-blind: it fires a ν-join on any two tokens, so for a quiescence
    // contract it errs both ways (it reaches the join's output and misses the inputs a
    // non-matching join strands) and neither verdict could stand. As [VER-017] condition 1;
    // the SMT pipeline has exact ν routes.
    let graph_skipped: Option<&'static str> = if unknown_mint.is_some() {
        Some(GRAPH_SKIPPED_MINT)
    } else if in_flight_refusal.is_some() {
        Some(GRAPH_SKIPPED_IN_FLIGHT)
    } else if closed.net.transitions().iter().any(|t| t.match_spec().is_some()) {
        Some(GRAPH_SKIPPED_MATCH)
    } else if max_classes > 0 {
        None
    } else {
        Some(GRAPH_SKIPPED_BUDGET)
    };
    // [VER-013]: a call cancelled before it starts builds nothing; a build the token stops
    // says nothing.
    let cancel = options.cancel.as_ref();
    let mut graph_cancelled = false;
    let graph = if graph_skipped.is_some() {
        None
    } else if cancel.is_some_and(CancelToken::is_cancelled) {
        graph_cancelled = true;
        None
    } else {
        let _stop = total_budget::enter(None, options.cancel.clone());
        let g = decide_on_graph(&closed, contract, max_classes, &traced_places, &reapable);
        graph_cancelled = g.stopped;
        (!g.stopped).then_some(g)
    };

    let result = |verdict: Verdict,
                  route: OpenNetRoute,
                  violations: Vec<ContractViolation>,
                  smt_lines: Option<&[String]>| {
        // [CONC-002]: a witness that starts a transition while an earlier firing of it is
        // in flight is a run of the Rust executor only.
        let restarts: Vec<String> = violations
            .iter()
            .filter_map(|v| in_flight::restart_note(&v.markings, &v.transitions))
            .map(|note| note.trim_end().to_string())
            .fold(Vec::new(), |mut seen, note| {
                if !seen.contains(&note) {
                    seen.push(note);
                }
                seen
            });
        let notes: Vec<&str> = reaping_line.iter().map(String::as_str).chain(restarts.iter().map(String::as_str)).collect();
        let notes = (!notes.is_empty()).then(|| notes.join("\n"));
        let report = render_report(&ReportInput {
            net,
            closed: &closed,
            contract,
            max_classes,
            graph: graph.as_ref(),
            graph_skipped,
            smt_lines,
            reaping: notes.as_deref(),
            verdict: &verdict,
            violations: &violations,
        });
        OpenNetResult {
            verdict,
            violations,
            route,
            class_count: graph.as_ref().map_or(0, |g| g.class_count),
            graph_complete: graph.as_ref().is_some_and(|g| g.complete),
            report,
            closed_net: closed.net.clone(),
            closed_marking: closed.initial_marking.clone(),
            elapsed_ms: start.elapsed().as_millis() as u64,
        }
    };

    if let Some(reason) = unknown_mint {
        return result(Verdict::Unknown { reason }, OpenNetRoute::Enumeration, Vec::new(), None);
    }
    if let Some(reason) = in_flight_refusal {
        return result(Verdict::Unknown { reason }, OpenNetRoute::Enumeration, Vec::new(), None);
    }
    if graph_cancelled {
        let verdict = Verdict::Unknown { reason: total_budget::cancelled_reason(PHASE_GRAPH) };
        return result(verdict, OpenNetRoute::Enumeration, Vec::new(), None);
    }
    if let Some(g) = &graph {
        if !g.violations.is_empty() {
            return result(Verdict::Violated, OpenNetRoute::Enumeration, g.violations.clone(), None);
        }
        if g.complete {
            // No invariant: the exhausted graph is the evidence.
            let verdict = Verdict::Proven { method: METHOD_ENUMERATION.to_string(), inductive_invariant: None };
            return result(verdict, OpenNetRoute::Enumeration, Vec::new(), None);
        }
    }
    let why = match (&graph, graph_skipped) {
        (Some(_), _) => format!("the state-class graph did not close within {max_classes} classes"),
        (None, Some(GRAPH_SKIPPED_MATCH)) => format!("the state-class graph was skipped: {GRAPH_SKIPPED_MATCH}"),
        (None, _) => "the state-class graph was skipped".to_string(),
    };
    if !options.smt {
        let verdict = Verdict::Unknown { reason: format!("{why}, and the SMT route is disabled") };
        return result(verdict, OpenNetRoute::Enumeration, Vec::new(), None);
    }

    let smt = decide_via_smt(
        &closed,
        contract,
        &traced_places,
        options.configure_smt.as_ref(),
        options.termination_timeout_ms,
        cancel,
        &reapable,
        options.assume_atomic_firing,
    );
    if !smt.violations.is_empty() {
        return result(Verdict::Violated, OpenNetRoute::Smt, smt.violations, Some(&smt.lines));
    }
    if smt.undecided.is_empty() {
        let verdict = Verdict::Proven {
            method: METHOD_SMT.to_string(),
            inductive_invariant: combine_certificates(&smt.certificates),
        };
        return result(verdict, OpenNetRoute::Smt, Vec::new(), Some(&smt.lines));
    }
    let verdict = Verdict::Unknown {
        reason: format!("{why}; left undecided by the SMT route: {}", smt.undecided.join("; ")),
    };
    result(verdict, OpenNetRoute::Smt, Vec::new(), Some(&smt.lines))
}

/// The route's certificates, each labelled with the part it proves; the verdict is their
/// conjunction. `None` when no query returned one (a bound or enumeration proves without).
fn combine_certificates(certificates: &[SubjectCertificate]) -> Option<String> {
    if certificates.is_empty() {
        return None;
    }
    let labelled: Vec<String> = certificates.iter().map(|c| format!("[{}] {}", c.subject, c.invariant)).collect();
    Some(labelled.join("\n"))
}
