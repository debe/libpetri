//! The contract asked of the SMT pipeline, for a closed net whose graph does not close
//! ([VER-022]).
//!
//! Each part of the contract is one query on the closed net, and each decides exactly the
//! predicate the graph route reads:
//!
//! - **stranding**: `DeadlockFree` with the clause places, the rest places and the
//!   environment's own places as sinks, and each terminal as a conditional sink ([VER-014]).
//! - **a count clause**: `QuiescentCount(places, min, max, markers)` ([VER-002]), with every
//!   terminal marker as a waiver.
//! - **termination**: the firing-bound ranking of [VER-019] on the closed net. Weights that
//!   every firing lowers bound the length of every run by what they give the initial
//!   marking, so no run goes on forever. When there are none, the part is undecided and the
//!   reason names the firings the marking equation lets repeat.

use crate::bounded_run::{
    check_ranking_exact, decode_ranking, decode_repeatable_vector, encode_ranking_query,
    encode_repeatable_vector_query, format_ranking,
};
use crate::graph_decision::tokens_across;
use crate::net_flattener::flatten;
use crate::property::{SmtProperty, count_across};
use crate::result::{Verdict, VerificationResult};
use crate::rest_set::ConditionalSinks;
use crate::smt_verifier::SmtVerifier;
use crate::z3_process::{Z3Solver, failure_reason};

use super::closure::ClosedNet;
use super::contract::{CountClause, OpenNetContract};
use super::predicate::{RestDeclaration, rest_declaration_of, stranded_names, waiver_markers};
use super::result::{ContractViolation, ContractViolationKind, Witness, contract_violation};
use super::verify_open_net::SmtConfigurator;

/// What the SMT route found.
pub(super) struct SmtRouteOutcome {
    pub violations: Vec<ContractViolation>,
    /// The parts of the contract no query decided, each with its reason.
    pub undecided: Vec<String>,
    /// One report line per query.
    pub lines: Vec<String>,
    /// The inductive invariant each proven query returned, in query order. These are the
    /// route's proof evidence: a `Proven` open-net verdict is their conjunction, one
    /// certificate per part of the contract.
    pub certificates: Vec<SubjectCertificate>,
}

/// One part of the contract and the invariant that proved it.
pub(super) struct SubjectCertificate {
    pub subject: String,
    pub invariant: String,
}

/// What a `Violated` verdict of a query means.
enum Reading<'c> {
    /// The stranding query: read the stranded places off the witness.
    Stranding,
    /// A count clause's query: read the count off the witness.
    Clause(&'c CountClause),
}

struct Query<'c> {
    subject: String,
    property: SmtProperty,
    sinks: Vec<String>,
    conditional: Vec<ConditionalSinks>,
    reading: Reading<'c>,
}

/// A part of the contract: a query to run, or a clause no marking can fail.
///
/// A count clause of `[0, ∞]` is the second kind. `count_violation` reports an upper bound
/// only above `max` and a lower one only below `min`, so every marking satisfies it and both
/// routes agree without asking anything — the graph route's `quiescence_findings` finds
/// nothing for it either. Its places still carry their weight through
/// `rest_declaration_of`, which makes every clause place a sink of the stranding query.
/// Running the query anyway would be strictly worse than skipping it: the answer is
/// `Proven` on a solver that has time and `Unknown` on one that does not. It gets a report
/// line so that skipping it is visible rather than silent.
enum Part<'c> {
    Query(Query<'c>),
    Vacuous { subject: String, detail: String },
}

/// Runs one query per part of the contract, in contract order, then the firing bound.
pub(super) fn decide_via_smt(
    closed: &ClosedNet,
    contract: &OpenNetContract,
    traced_places: &[String],
    configure: Option<&SmtConfigurator>,
    termination_timeout_ms: u64,
) -> SmtRouteOutcome {
    let mut violations: Vec<ContractViolation> = Vec::new();
    let mut undecided: Vec<String> = Vec::new();
    let mut lines: Vec<String> = Vec::new();
    let mut certificates: Vec<SubjectCertificate> = Vec::new();
    // Derived once: the stranding query's sinks and the attribution of its witness must be
    // the same declaration, and the graph route reads that one too.
    let rest = rest_declaration_of(contract, closed);
    for part in parts_for(contract, &rest) {
        let q = match part {
            Part::Vacuous { subject, detail } => {
                lines.push(format!("  [{subject}] {detail}: proven (no query needed)"));
                continue;
            }
            Part::Query(q) => q,
        };
        let mut verifier = SmtVerifier::for_net(&closed.net)
            .initial_marking(closed.initial_marking.clone())
            .property(q.property.clone())
            .sink_places(q.sinks.iter().cloned())
            // The graph route already enumerated as far as its budget allows.
            .enumeration_max_classes(0);
        for c in &q.conditional {
            verifier = verifier.sink_places_when(c.marker.clone(), c.places.iter().cloned());
        }
        if let Some(configure) = configure {
            verifier = configure(verifier);
        }
        let result = verifier.verify();
        let word = verdict_word(&result.verdict);
        match &result.verdict {
            Verdict::Unknown { reason } => {
                lines.push(format!("  [{}] {}: {word} ({reason})", q.subject, query_description(&q.property)));
                undecided.push(format!("{}: {reason}", q.subject));
            }
            Verdict::Violated => {
                lines.push(format!("  [{}] {}: {word}", q.subject, query_description(&q.property)));
                let witness = read_violation(&q, &result, &rest);
                violations.push(contract_violation(closed, traced_places, witness));
            }
            Verdict::Proven { inductive_invariant, .. } => {
                lines.push(format!("  [{}] {}: {word}", q.subject, query_description(&q.property)));
                // A proven part may or may not come with a certificate: the enumeration and
                // bound phases prove without one. Keep the ones that do rather than dropping
                // the evidence.
                if let Some(invariant) = inductive_invariant {
                    certificates.push(SubjectCertificate { subject: q.subject.clone(), invariant: invariant.clone() });
                }
            }
        }
    }
    if contract.requires_termination() {
        match termination_by_ranking(closed, termination_timeout_ms) {
            Ok(detail) => lines.push(format!("  [termination] Firing bound (VER-019): {detail}")),
            Err(reason) => {
                lines.push(format!("  [termination] Firing bound (VER-019): undecided ({reason})"));
                undecided.push(format!("termination: {reason}"));
            }
        }
    }
    SmtRouteOutcome { violations, undecided, lines, certificates }
}

fn parts_for<'c>(contract: &'c OpenNetContract, rest: &RestDeclaration) -> Vec<Part<'c>> {
    let markers = waiver_markers(contract);
    let stranding = Query {
        subject: "stranding".to_string(),
        property: SmtProperty::deadlock_free(),
        sinks: rest.sinks.clone(),
        conditional: rest.conditional.clone(),
        reading: Reading::Stranding,
    };
    let mut parts: Vec<Part<'c>> = vec![Part::Query(stranding)];
    for clause in contract.clauses() {
        let across = count_across(clause.min, clause.max, &clause.places);
        if clause.min == 0 && clause.max.is_none() {
            parts.push(Part::Vacuous { subject: clause.name.clone(), detail: format!("{across} at quiescence") });
            continue;
        }
        parts.push(Part::Query(Query {
            subject: clause.name.clone(),
            property: SmtProperty::quiescent_count(clause.places.clone(), clause.min, clause.max, markers.clone()),
            sinks: Vec::new(),
            conditional: Vec::new(),
            reading: Reading::Clause(clause),
        }));
    }
    parts
}

/// The violation a query's `Violated` verdict means.
fn read_violation(q: &Query<'_>, result: &VerificationResult, rest: &RestDeclaration) -> Witness {
    // The last marking of a replay-confirmed counterexample is the quiescent one it reached.
    let confirmed = result.counterexample_confirmed == Some(true);
    let quiescent = if confirmed { result.counterexample_trace.last() } else { None };
    let (kind, subject, detail) = match q.reading {
        Reading::Stranding => {
            // The verdict does not depend on the replay — the solver's `sat` is the
            // violation. The attribution does: without a confirmed quiescent marking there
            // is nothing to read the stranded places off, so the finding names the query
            // rather than guessing a place.
            let names = quiescent.map(|m| stranded_names(m, rest)).unwrap_or_default();
            if names.is_empty() {
                (
                    ContractViolationKind::Stranded,
                    "stranding".to_string(),
                    "the solver found a reachable quiescent marking that leaves a token where the contract lets none rest"
                        .to_string(),
                )
            } else {
                let joined = names.join(", ");
                let verb = if names.len() == 1 { "holds" } else { "hold" };
                (
                    ContractViolationKind::Stranded,
                    joined.clone(),
                    format!("{joined} {verb} a token at quiescence, and nothing in the contract lets one rest there"),
                )
            }
        }
        Reading::Clause(clause) => {
            let across = count_across(clause.min, clause.max, &clause.places);
            let detail = match quiescent {
                None => format!("{across} at quiescence: the solver found a quiescent marking outside it"),
                Some(m) => format!("{across} at quiescence, found {}", tokens_across(m, &clause.places)),
            };
            (ContractViolationKind::Clause, clause.name.clone(), detail)
        }
    };
    Witness {
        kind,
        subject,
        detail,
        transitions: result.counterexample_transitions.clone(),
        markings: result.counterexample_trace.clone(),
        cycle_start: None,
        confirmed,
    }
}

/// `proven`, `violated` or `unknown`, as the report prints a verdict.
pub(super) fn verdict_word(verdict: &Verdict) -> &'static str {
    match verdict {
        Verdict::Proven { .. } => "proven",
        Verdict::Violated => "violated",
        Verdict::Unknown { .. } => "unknown",
    }
}

/// A query's property as the open-net report names it.
///
/// The TypeScript reference words `DeadlockFree` as `Deadlock-freedom` in this report,
/// where the verifier's own report in this crate says `Deadlock freedom`; the open-net
/// report is pinned byte-for-byte to the reference, so it takes the reference's word here
/// rather than changing the verifier's.
fn query_description(property: &SmtProperty) -> String {
    match property {
        SmtProperty::DeadlockFree => "Deadlock-freedom".to_string(),
        other => other.description(),
    }
}

/// Termination by the firing-bound ranking of [VER-019]: weights `r ≥ 0` that every firing
/// of the closed net lowers by at least one, re-checked in exact arithmetic. No run then
/// has more than `r·M0` firings. When there are none, the Farkas alternative names the
/// firings the marking equation lets repeat.
///
/// `Ok` is the proof in words; `Err` is why termination stays undecided.
fn termination_by_ranking(closed: &ClosedNet, timeout_ms: u64) -> Result<String, String> {
    let flat = flatten(&closed.net);
    // A count past `i64::MAX` cannot be a marking anyone built; saturating keeps the query
    // well-formed, and the exact re-check then refuses a ranking that relies on it.
    let initial: Vec<i64> = flat
        .places
        .iter()
        .map(|p| i64::try_from(closed.initial_marking.count(p)).unwrap_or(i64::MAX))
        .collect();
    let solver = Z3Solver::resolve()?;
    // The soft budget is at least one millisecond, so `-t:0` never means "forever".
    let budget = timeout_ms.max(1);
    let ask = |script: &str| -> Result<String, String> {
        let reply = solver.run(script, "ranking", budget, &[])?;
        match first_line(&reply.stdout) {
            "sat" | "unsat" | "unknown" => Ok(reply.stdout),
            _ => Err(failure_reason(&reply, budget)),
        }
    };

    let ranking = ask(&encode_ranking_query(&flat, &initial))?;
    match first_line(&ranking) {
        "sat" => {
            let bound = decode_ranking(&ranking, flat.place_count)
                .and_then(|weights| check_ranking_exact(&flat, &initial, &weights))
                .ok_or_else(|| "the firing-bound ranking failed the exact re-check".to_string())?;
            Ok(format!(
                "every run has at most {} firings ({} drops on every firing)",
                bound.bound,
                format_ranking(&flat, &bound)
            ))
        }
        "unsat" => {
            let repeat = match ask(&encode_repeatable_vector_query(&flat)) {
                Ok(vector) if first_line(&vector) == "sat" => {
                    decode_repeatable_vector(&vector, flat.transitions.len())
                }
                _ => None,
            };
            Err(match repeat {
                Some(repeat) if !repeat.is_empty() => {
                    let names: Vec<&str> = repeat.iter().map(|&t| flat.transitions[t].name.as_str()).collect();
                    format!("no firing bound: the marking equation lets {} repeat", names.join(", "))
                }
                _ => "no firing bound: no weights drop on every firing".to_string(),
            })
        }
        _ => Err("the firing-bound query answered unknown".to_string()),
    }
}

/// The first non-blank line of a reply, trimmed: where the answer to `(check-sat)` is.
fn first_line(stdout: &str) -> &str {
    stdout.lines().map(str::trim).find(|l| !l.is_empty()).unwrap_or("")
}
