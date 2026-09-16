//! The human-readable report of an open-net verification ([VER-022]).
//!
//! The report is byte-identical to the TypeScript reference's for the same net and
//! contract, markings included, which is why markings are rendered here rather than
//! through [`MarkingState::canonical_key`]: see [`marking_text`].

use std::cmp::Ordering;

use libpetri_core::petri_net::PetriNet;

use crate::marking_state::MarkingState;
use crate::result::Verdict;

use super::closure::{ClosedNet, EnvironmentStepKind};
use super::contract::OpenNetContract;
use super::graph_route::GraphRouteOutcome;
use super::result::{ContractViolation, ContractViolationKind};

pub(super) struct ReportInput<'a> {
    pub net: &'a PetriNet,
    pub closed: &'a ClosedNet,
    pub contract: &'a OpenNetContract,
    pub max_classes: usize,
    pub graph: Option<&'a GraphRouteOutcome>,
    pub smt_lines: Option<&'a [String]>,
    pub verdict: &'a Verdict,
    pub violations: &'a [ContractViolation],
}

pub(super) fn render_report(input: &ReportInput<'_>) -> String {
    let ReportInput { net, closed, contract, graph, smt_lines, verdict, violations, .. } = input;
    let mut lines: Vec<String> =
        vec!["=== OPEN-NET CONTRACT VERIFICATION (VER-022) ===".to_string(), String::new()];
    lines.push(format!(
        "Net: {}, closed by {} environment transitions over {} arrival groups",
        net.name(),
        closed.environment.len(),
        contract.arrivals().len()
    ));
    lines.push("Contract:".to_string());
    lines.extend(contract.describe());
    if !closed.undeclared.is_empty() {
        lines.push(format!(
            "Not declared by the net: {} (no arc touches them; a clause there counts zero)",
            closed.undeclared.join(", ")
        ));
    }
    lines.push(String::new());

    match graph {
        None => lines.push("State-class graph: skipped (class budget 0)".to_string()),
        Some(graph) => {
            lines.push("=== State-class graph (untimed, priority-blind) ===".to_string());
            lines.push(if graph.complete {
                format!("  Classes: {}, closed", graph.class_count)
            } else {
                format!(
                    "  Classes: {}, truncated at the class budget of {}",
                    graph.class_count, input.max_classes
                )
            });
        }
    }
    if let Some(smt_lines) = smt_lines {
        lines.push(String::new());
        lines.push("=== SMT route ===".to_string());
        lines.extend(smt_lines.iter().cloned());
    }

    lines.push(String::new());
    lines.push("=== RESULT ===".to_string());
    match verdict {
        Verdict::Proven { method, .. } => lines.push(format!(
            "PROVEN: every quiescent marking meets the contract{} ({method})",
            if contract.requires_termination() { " and every run comes to rest" } else { "" }
        )),
        Verdict::Unknown { reason } => lines.push(format!("UNKNOWN: {reason}")),
        Verdict::Violated => {
            lines.push(format!(
                "VIOLATED: {} {} of the contract broken",
                violations.len(),
                if violations.len() == 1 { "part" } else { "parts" }
            ));
            for v in violations.iter() {
                render_violation(v, &mut lines);
            }
        }
    }
    lines.join("\n")
}

fn render_violation(v: &ContractViolation, lines: &mut Vec<String>) {
    lines.push(format!("  [{}] {}: {}", v.subject, v.kind.as_str(), v.detail));
    if !v.confirmed {
        lines.push("    (the solver's counterexample did not replay as an ordered firing sequence)".to_string());
    }
    if !v.port_trace.is_empty() {
        lines.push("    Port trace:".to_string());
        for s in &v.port_trace {
            if v.cycle_start.is_some_and(|start| s.step == start + 1) {
                lines.push("      -- the cycle starts here --".to_string());
            }
            let env = match s.environment {
                None => String::new(),
                Some(EnvironmentStepKind::Transition) => " [environment]".to_string(),
                Some(kind) => format!(" [environment {}]", kind.as_str()),
            };
            let changes: Vec<String> = s
                .changes
                .iter()
                .map(|c| format!("{} {}{}", c.place, if c.delta > 0 { "+" } else { "" }, c.delta))
                .collect();
            let changes = changes.join(", ");
            lines.push(format!(
                "      {}. {}{env}{}",
                s.step,
                s.transition,
                if changes.is_empty() { String::new() } else { format!("  {changes}") }
            ));
        }
    }
    match v.cycle_start {
        Some(start) => {
            let stem = &v.transitions[..start.min(v.transitions.len())];
            let cycle = format!("then repeating {}", v.transitions[start.min(v.transitions.len())..].join(", "));
            lines.push(if stem.is_empty() {
                format!("    Firing sequence: {cycle}")
            } else {
                format!("    Firing sequence: {}, {cycle}", stem.join(", "))
            });
        }
        None if !v.transitions.is_empty() => {
            lines.push(format!("    Firing sequence: {}", v.transitions.join(", ")));
        }
        None => {}
    }
    if let Some(last) = v.markings.last() {
        let label = if v.kind == ContractViolationKind::Termination { "Marking on the cycle" } else { "Quiescent marking" };
        lines.push(format!("    {label}: {}", marking_text(last)));
    }
}

/// A marking as the report prints it: `{name:count, …}`, or `{}` when empty.
///
/// The places are listed in the order the TypeScript reference's `MarkingState.toString`
/// lists them, which sorts with `localeCompare`, not by code point: `_budget` before
/// `e1/data` before `X/idle`. The markings are the one part of the report that order
/// reaches, and the report is pinned to the reference byte for byte, so the order is
/// reproduced here rather than the report being allowed to differ ([`locale_order`]).
pub(super) fn marking_text(m: &MarkingState) -> String {
    let mut entries: Vec<(&str, usize)> = m.places().collect();
    if entries.is_empty() {
        return "{}".to_string();
    }
    entries.sort_by(|a, b| locale_order(a.0, b.0));
    let parts: Vec<String> = entries.iter().map(|(p, n)| format!("{p}:{n}")).collect();
    format!("{{{}}}", parts.join(", "))
}

/// The primary collation order of printable ASCII in ICU's root collation, which Node's
/// `localeCompare` uses, with punctuation significant: whitespace, then punctuation, then
/// symbols, then digits, then letters with case ignored.
const PRIMARY_ORDER: &str = " _-,;:!?.'\"()[]{}@*/\\&#%`^+<=>|~$0123456789abcdefghijklmnopqrstuvwxyz";

/// `a.localeCompare(b)` for names of printable ASCII: the primary weights compared first
/// (case-blind, a shorter prefix first), then case, lower before upper, at the first
/// position the case differs.
///
/// Verified against Node's `localeCompare` over half a million random printable-ASCII
/// pairs. A character outside printable ASCII sorts after every one inside it, by code
/// point: the reference's order there depends on the collation tables, which this crate
/// does not carry, and no name the closure generates contains one.
fn locale_order(a: &str, b: &str) -> Ordering {
    fn primary(c: char) -> u32 {
        match PRIMARY_ORDER.find(c.to_ascii_lowercase()) {
            Some(i) if c.is_ascii() => i as u32,
            _ => PRIMARY_ORDER.len() as u32 + c as u32,
        }
    }
    a.chars()
        .map(primary)
        .cmp(b.chars().map(primary))
        .then_with(|| a.chars().map(|c| c.is_ascii_uppercase()).cmp(b.chars().map(|c| c.is_ascii_uppercase())))
        .then_with(|| a.cmp(b))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marking_state::MarkingStateBuilder;

    /// The order Node's `localeCompare` gives these names, the reference's
    /// `MarkingState.toString` order.
    #[test]
    fn marking_text_lists_places_in_locale_order() {
        let m = MarkingStateBuilder::new()
            .tokens("X/in", 1)
            .tokens("_halt", 1)
            .tokens("env:arrivals[0]", 1)
            .tokens("x/in", 1)
            .tokens("X/In", 1)
            .tokens("env/ended", 1)
            .tokens("e1/data", 2)
            .tokens("N/in", 1)
            .tokens("X/in_empty", 1)
            .tokens("_budget", 1)
            .build();
        assert_eq!(
            marking_text(&m),
            "{_budget:1, _halt:1, e1/data:2, env:arrivals[0]:1, env/ended:1, N/in:1, x/in:1, X/in:1, X/In:1, X/in_empty:1}"
        );
        assert_eq!(marking_text(&MarkingState::new()), "{}");
    }

    /// Every printable ASCII character alone, sorted, as Node sorts it.
    #[test]
    fn locale_order_matches_the_reference_on_printable_ascii() {
        let mut chars: Vec<String> = (32u8..127).map(|c| (c as char).to_string()).collect();
        chars.sort_by(|a, b| locale_order(a, b));
        assert_eq!(
            chars.concat(),
            " _-,;:!?.'\"()[]{}@*/\\&#%`^+<=>|~$0123456789aAbBcCdDeEfFgGhHiIjJkKlLmMnNoOpPqQrRsStTuUvVwWxXyYzZ"
        );
        let mut words = vec!["a b", "a_b", "a-b", "a/b", "a1b", "ab", "aB", "Ab", "AB", "ab1"];
        words.reverse();
        words.sort_by(|a, b| locale_order(a, b));
        assert_eq!(words, vec!["a b", "a_b", "a-b", "a/b", "a1b", "ab", "aB", "Ab", "AB", "ab1"]);
    }
}
