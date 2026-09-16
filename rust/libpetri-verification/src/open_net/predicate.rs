//! The contract's guarantee at one quiescent marking ([VER-022]): which clauses it breaks
//! and which places it strands.
//!
//! The stranding half is the rest set of [VER-014], read through the same module every
//! `DeadlockFree` route reads ([`crate::rest_set`]). The clause places, the rest places and
//! the environment's own places are sinks, and each designed terminal is a conditional
//! sink. That is what lets the SMT route ask for it with `DeadlockFree` and mean the same
//! thing.
//!
//! Everything both routes judge by is derived here once — the rest declaration, the waiver
//! markers and the stranding attribution — and neither route rebuilds any of it: when two
//! call sites each assembled their own copy, they drifted, and one route reported a
//! stranding the other proved impossible.

use std::collections::HashSet;

use crate::graph_decision::{CountBound, count_violation, tokens_across};
use crate::marking_state::MarkingState;
use crate::property::count_across;
use crate::rest_set::{ConditionalSinks, stranded_places};

use super::closure::ClosedNet;
use super::contract::{CountClause, OpenNetContract};

/// The contract's rest set in [VER-014] form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RestDeclaration {
    /// Clause places, then rest places, then the environment's own places, each once.
    pub sinks: Vec<String>,
    pub conditional: Vec<ConditionalSinks>,
}

/// Clause places, rest places and the environment's own places as sinks; each designed
/// terminal as a conditional sink.
pub(super) fn rest_declaration_of(contract: &OpenNetContract, closed: &ClosedNet) -> RestDeclaration {
    let mut seen: HashSet<&str> = HashSet::new();
    let mut sinks: Vec<String> = Vec::new();
    let named = contract
        .clauses()
        .iter()
        .flat_map(|c| c.places.iter())
        .chain(contract.rest().iter())
        .chain(closed.environment_places.iter());
    for p in named {
        if seen.insert(p.as_str()) {
            sinks.push(p.clone());
        }
    }
    let conditional = contract
        .terminals()
        .iter()
        .map(|t| ConditionalSinks { marker: t.marker.clone(), places: t.excused.clone() })
        .collect();
    RestDeclaration { sinks, conditional }
}

/// The clause lower bounds' waivers: every designed terminal's marker ([VER-002]).
///
/// Both routes must waive by the same set in the same order — the graph route reads it
/// through [`count_violation`] and the encoder through its index order — so it is derived
/// here once rather than at each call site.
pub(super) fn waiver_markers(contract: &OpenNetContract) -> Vec<String> {
    contract.terminals().iter().map(|t| t.marker.clone()).collect()
}

/// The places `m` strands, by name, in code-point order.
///
/// This is the predicate both routes must attribute a stranding with, and the reason it
/// lives here rather than at each call site: it asks whether a place is marked **and
/// unexcused**, applying the [VER-014] widening that a token on a place excused by a marked
/// terminal marker is designed residue. A caller that asks only "is this place marked?"
/// reports a stranding the other route proves cannot happen.
pub(super) fn stranded_names(m: &MarkingState, rest: &RestDeclaration) -> Vec<String> {
    stranded_places(m, &rest.sinks, &rest.conditional)
}

/// One thing a quiescent marking breaks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Finding<'c> {
    Clause { clause: &'c CountClause, count: usize, bound: CountBound },
    Stranded { place: String, count: usize },
}

impl Finding<'_> {
    /// The finding's subject: its clause's name or its place's name.
    pub fn subject(&self) -> &str {
        match self {
            Finding::Clause { clause, .. } => &clause.name,
            Finding::Stranded { place, .. } => place,
        }
    }

    /// The finding in words.
    pub fn describe(&self) -> String {
        match self {
            Finding::Stranded { place, count } => {
                format!("{place} holds {count} at quiescence, and nothing in the contract lets a token rest there")
            }
            Finding::Clause { clause, count, bound } => {
                let expected = count_across(clause.min, clause.max, &clause.places);
                match bound {
                    CountBound::Upper => format!(
                        "{expected} at quiescence, found {count} (an upper bound holds under a terminal too)"
                    ),
                    CountBound::Lower => format!("{expected} at quiescence, found {count}"),
                }
            }
        }
    }
}

/// What the quiescent marking `m` breaks: clauses in contract order, then stranded places
/// by name. Empty when `m` meets the contract.
pub(super) fn quiescence_findings<'c>(
    m: &MarkingState,
    contract: &'c OpenNetContract,
    rest: &RestDeclaration,
) -> Vec<Finding<'c>> {
    let mut findings: Vec<Finding<'c>> = Vec::new();
    // The clause is a QuiescentCount with every terminal marker as a waiver ([VER-002]),
    // read through the same predicate the graph routes use for that property.
    let markers = waiver_markers(contract);
    for clause in contract.clauses() {
        if let Some(bound) = count_violation(m, &clause.places, clause.min, clause.max, &markers) {
            findings.push(Finding::Clause { clause, count: tokens_across(m, &clause.places), bound });
        }
    }
    for place in stranded_names(m, rest) {
        let count = m.count(&place);
        findings.push(Finding::Stranded { place, count });
    }
    findings
}
