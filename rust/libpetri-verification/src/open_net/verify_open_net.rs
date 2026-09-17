//! A subnet verified on its own against a contract, with its ports played by the
//! environment ([VER-022]).
//!
//! The subnet is closed with the environment its contract describes, and the closed net's
//! untimed state-class graph is enumerated. When the graph closes, the verdict is exact.
//! When it does not, a violation found among the explored classes is still real, and the
//! rest of the contract goes to the SMT pipeline, through the properties it already has.

use std::fmt;
use std::time::Instant;

use libpetri_core::petri_net::PetriNet;

use crate::result::Verdict;
use crate::smt_verifier::SmtVerifier;

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
}

impl Default for OpenNetOptions {
    fn default() -> Self {
        Self {
            max_classes: DEFAULT_MAX_CLASSES,
            smt: true,
            configure_smt: None,
            termination_timeout_ms: 60_000,
        }
    }
}

impl fmt::Debug for OpenNetOptions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OpenNetOptions")
            .field("max_classes", &self.max_classes)
            .field("smt", &self.smt)
            .field("configure_smt", &self.configure_smt.as_ref().map(|_| ".."))
            .field("termination_timeout_ms", &self.termination_timeout_ms)
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
    let closed = close_open_net(net, contract);
    let max_classes = options.max_classes;
    // Every place a port trace may mention: the contract's own, plus the closure's. [VER-022]
    // reserves "port" for a place the environment shares with the subnet, which is narrower.
    let traced_places = contract.places();
    // The graph is name-blind: it fires a ν-join on any two tokens, so for a quiescence
    // contract it errs both ways (it reaches the join's output and misses the inputs a
    // non-matching join strands) and neither verdict could stand. As [VER-017] condition 1;
    // the SMT pipeline has exact ν routes.
    let graph_skipped: Option<&'static str> = if closed.net.transitions().iter().any(|t| t.match_spec().is_some()) {
        Some(GRAPH_SKIPPED_MATCH)
    } else if max_classes > 0 {
        None
    } else {
        Some(GRAPH_SKIPPED_BUDGET)
    };
    let graph = graph_skipped
        .is_none()
        .then(|| decide_on_graph(&closed, contract, max_classes, &traced_places));

    let result = |verdict: Verdict,
                  route: OpenNetRoute,
                  violations: Vec<ContractViolation>,
                  smt_lines: Option<&[String]>| {
        let report = render_report(&ReportInput {
            net,
            closed: &closed,
            contract,
            max_classes,
            graph: graph.as_ref(),
            graph_skipped,
            smt_lines,
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
