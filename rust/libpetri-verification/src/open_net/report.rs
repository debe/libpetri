//! The human-readable report of an open-net verification ([VER-022]).
//!
//! The report is byte-identical to the TypeScript reference's for the same net and
//! contract, markings included, which is why markings are rendered here rather than
//! through [`MarkingState::canonical_key`]: see [`marking_text`].

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
    /// Why the graph was not built, when [`ReportInput::graph`] is `None`.
    pub graph_skipped: Option<&'a str>,
    pub smt_lines: Option<&'a [String]>,
    pub verdict: &'a Verdict,
    pub violations: &'a [ContractViolation],
}

pub(super) fn render_report(input: &ReportInput<'_>) -> String {
    let ReportInput { net, closed, contract, graph, graph_skipped, smt_lines, verdict, violations, .. } = input;
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
        None => lines.push(format!("State-class graph: skipped ({})", graph_skipped.unwrap_or("class budget 0"))),
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
/// The places are listed in Unicode code-point order, the one name order every
/// implementation's report uses, whatever order the marking was built in.
pub(super) fn marking_text(m: &MarkingState) -> String {
    let mut entries: Vec<(&str, usize)> = m.places().collect();
    if entries.is_empty() {
        return "{}".to_string();
    }
    entries.sort_unstable_by(|a, b| a.0.cmp(b.0));
    let parts: Vec<String> = entries.iter().map(|(p, n)| format!("{p}:{n}")).collect();
    format!("{{{}}}", parts.join(", "))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marking_state::MarkingStateBuilder;

    /// Code-point order, not the order the marking was built in and not a locale's:
    /// `X/in` before `_budget` before `e1/data`.
    #[test]
    fn marking_text_lists_places_in_code_point_order() {
        let m = MarkingStateBuilder::new()
            .tokens("x/in", 1)
            .tokens("_halt", 1)
            .tokens("env:arrivals[0]", 1)
            .tokens("X/in", 1)
            .tokens("X/In", 1)
            .tokens("env/ended", 1)
            .tokens("e1/data", 2)
            .tokens("N/in", 1)
            .tokens("X/in_empty", 1)
            .tokens("_budget", 1)
            .build();
        assert_eq!(
            marking_text(&m),
            "{N/in:1, X/In:1, X/in:1, X/in_empty:1, _budget:1, _halt:1, e1/data:2, env/ended:1, env:arrivals[0]:1, x/in:1}"
        );
        assert_eq!(marking_text(&MarkingState::new()), "{}");
    }

    /// The name order every implementation asserts on this vector. UTF-16 code-unit
    /// order would put the two astral-plane names before U+E000; UTF-8 byte order,
    /// which `str`'s `Ord` is, agrees with code-point order everywhere.
    #[test]
    fn names_sort_by_code_point() {
        let expected = [
            "", "Z", "a", "ab", "\u{C4}", "\u{4E2D}", "\u{E000}", "\u{FF21}", "\u{1D400}", "\u{1F600}",
        ];
        let mut names: Vec<&str> = expected.iter().rev().copied().collect();
        names.sort();
        assert_eq!(names, expected);

        let mut builder = MarkingStateBuilder::new();
        for (i, name) in expected.iter().enumerate().rev().filter(|(_, n)| !n.is_empty()) {
            builder = builder.tokens(*name, i);
        }
        assert_eq!(
            marking_text(&builder.build()),
            "{Z:1, a:2, ab:3, \u{C4}:4, \u{4E2D}:5, \u{E000}:6, \u{FF21}:7, \u{1D400}:8, \u{1F600}:9}"
        );
    }
}
