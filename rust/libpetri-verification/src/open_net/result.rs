//! What [`verify_open_net`](super::verify_open_net) returns ([VER-022]), and how a witness
//! becomes a port trace.

use std::collections::HashMap;

use libpetri_core::petri_net::PetriNet;

use crate::marking_state::MarkingState;
use crate::result::Verdict;

use super::closure::{ClosedNet, EnvironmentStep, EnvironmentStepKind};

/// Which part of the contract a violation breaks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ContractViolationKind {
    /// A count clause: too few tokens across its places at quiescence with no terminal
    /// marked, or too many.
    Clause,
    /// A token rests where the contract lets none rest: on an internal place, or on one
    /// only an unmarked terminal excuses.
    Stranded,
    /// A run that never comes to rest: a reachable cycle.
    Termination,
}

impl ContractViolationKind {
    /// `clause`, `stranded` or `termination`, as the report prints it.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Clause => "clause",
            Self::Stranded => "stranded",
            Self::Termination => "termination",
        }
    }
}

/// A token-count change on one contract place.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PortChange {
    pub place: String,
    pub delta: i64,
}

/// A firing that touches the subnet's boundary: an environment step, or a change on a
/// contract place.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PortStep {
    /// The firing's position in [`ContractViolation::transitions`], counting from 1.
    pub step: usize,
    pub transition: String,
    /// Set when the environment fired it: `Arrival` or `Decline` for an arrival group,
    /// `Transition` for one of the contract's environment transitions. `None` for the
    /// subnet.
    pub environment: Option<EnvironmentStepKind>,
    /// Token changes on the contract's places, in the contract's order.
    pub changes: Vec<PortChange>,
}

/// One broken part of the contract, with a firing sequence that breaks it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContractViolation {
    pub kind: ContractViolationKind,
    /// The clause's name, a stranded place's name, or `termination`.
    ///
    /// The two routes attribute a stranding differently: the graph route reports one
    /// violation per stranded place, the SMT route one violation for the whole query,
    /// naming every place its witness strands as a comma-separated list.
    pub subject: String,
    /// What was found, in words.
    pub detail: String,
    /// The firing sequence from the initial marking, environment transitions included.
    pub transitions: Vec<String>,
    /// The marking before the first firing and after each one, when the route has them in
    /// order.
    pub markings: Vec<MarkingState>,
    /// For `Termination`, the index into [`ContractViolation::transitions`] where the
    /// repeating cycle starts.
    pub cycle_start: Option<usize>,
    /// The firings of [`ContractViolation::transitions`] that touch the boundary.
    pub port_trace: Vec<PortStep>,
    /// Whether [`ContractViolation::transitions`] is a real firing sequence in order.
    /// Always on the graph route; on the SMT route it is the counterexample replay's
    /// outcome ([VER-003]).
    pub confirmed: bool,
}

/// Which route decided the verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpenNetRoute {
    Enumeration,
    Smt,
}

impl OpenNetRoute {
    /// `enumeration` or `smt`.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Enumeration => "enumeration",
            Self::Smt => "smt",
        }
    }
}

/// The outcome of [`verify_open_net`](super::verify_open_net).
#[derive(Debug, Clone)]
pub struct OpenNetResult {
    /// `Proven`, `Violated` (see [`OpenNetResult::violations`]), or `Unknown` with the
    /// reason.
    pub verdict: Verdict,
    /// Every broken part found. The graph route lists clauses in contract order, then
    /// stranded places by name, then termination; the SMT route asks for stranding first,
    /// so it lists that, then clauses in contract order, then termination.
    pub violations: Vec<ContractViolation>,
    pub route: OpenNetRoute,
    /// Classes the state-class graph explored; `0` when it was skipped.
    pub class_count: usize,
    /// Whether the state-class graph closed within its budget.
    pub graph_complete: bool,
    pub report: String,
    /// The subnet closed by its environment: what every route verified.
    pub closed_net: PetriNet,
    pub closed_marking: MarkingState,
    pub elapsed_ms: u64,
}

/// A violation as a route finds it, before its port trace is read off.
pub(super) struct Witness {
    pub kind: ContractViolationKind,
    pub subject: String,
    pub detail: String,
    pub transitions: Vec<String>,
    pub markings: Vec<MarkingState>,
    pub cycle_start: Option<usize>,
    pub confirmed: bool,
}

/// A violation with its port trace, read off consecutive markings of the witness. Without
/// one marking per firing plus the initial one there is nothing to read the changes off, so
/// the trace is empty rather than guessed.
pub(super) fn contract_violation(closed: &ClosedNet, traced_places: &[String], w: Witness) -> ContractViolation {
    let mut port_trace: Vec<PortStep> = Vec::new();
    if w.markings.len() == w.transitions.len() + 1 {
        let steps: HashMap<&str, &EnvironmentStep> =
            closed.environment.iter().map(|(name, step)| (name.as_str(), step)).collect();
        for (i, transition) in w.transitions.iter().enumerate() {
            let before = &w.markings[i];
            let after = &w.markings[i + 1];
            let changes: Vec<PortChange> = traced_places
                .iter()
                .filter_map(|p| {
                    let delta = after.count(p) as i64 - before.count(p) as i64;
                    (delta != 0).then(|| PortChange { place: p.clone(), delta })
                })
                .collect();
            let environment = steps.get(transition.as_str()).map(|s| s.kind());
            if !changes.is_empty() || environment.is_some() {
                port_trace.push(PortStep { step: i + 1, transition: transition.clone(), environment, changes });
            }
        }
    }
    ContractViolation {
        kind: w.kind,
        subject: w.subject,
        detail: w.detail,
        transitions: w.transitions,
        markings: w.markings,
        cycle_start: w.cycle_start,
        port_trace,
        confirmed: w.confirmed,
    }
}
