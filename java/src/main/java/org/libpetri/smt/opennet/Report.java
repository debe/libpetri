package org.libpetri.smt.opennet;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.PetriNet;
import org.libpetri.smt.SmtVerificationResult.Verdict;

import java.util.ArrayList;
import java.util.List;

/**
 * The human-readable report of an open-net verification ([VER-022]).
 *
 * <p>The report is byte-identical to the TypeScript reference's for the same net and contract,
 * markings included: every name list in it is in code-point order ([VER-022]).
 */
final class Report {

    private Report() {}

    /**
     * Everything the report reads.
     *
     * @param graph        the graph route's outcome, {@code null} when the graph was not built
     * @param graphSkipped why the graph was not built, when {@code graph} is {@code null}
     * @param smtLines     the SMT route's lines, {@code null} when it did not run
     */
    record Input(
        PetriNet net,
        ClosedNet closed,
        OpenNetContract contract,
        int maxClasses,
        GraphRoute.Outcome graph,
        String graphSkipped,
        List<String> smtLines,
        Verdict verdict,
        List<ContractViolation> violations
    ) {}

    static String render(Input input) {
        var contract = input.contract();
        var lines = new ArrayList<String>();
        lines.add("=== OPEN-NET CONTRACT VERIFICATION (VER-022) ===");
        lines.add("");
        lines.add("Net: " + input.net().name() + ", closed by " + input.closed().environment().size()
            + " environment transitions over " + contract.arrivals().size() + " arrival groups");
        lines.add("Contract:");
        lines.addAll(contract.describe());
        if (!input.closed().undeclared().isEmpty()) {
            lines.add("Not declared by the net: " + String.join(", ", input.closed().undeclared())
                + " (no arc touches them; a clause there counts zero)");
        }
        lines.add("");

        var graph = input.graph();
        if (graph == null) {
            lines.add("State-class graph: skipped ("
                + (input.graphSkipped() == null ? "class budget 0" : input.graphSkipped()) + ")");
        } else {
            lines.add("=== State-class graph (untimed, priority-blind) ===");
            lines.add(graph.complete()
                ? "  Classes: " + graph.classCount() + ", closed"
                : "  Classes: " + graph.classCount() + ", truncated at the class budget of " + input.maxClasses());
        }
        if (input.smtLines() != null) {
            lines.add("");
            lines.add("=== SMT route ===");
            lines.addAll(input.smtLines());
        }

        lines.add("");
        lines.add("=== RESULT ===");
        switch (input.verdict()) {
            case Verdict.Proven(var method, var _) -> lines.add("PROVEN: every quiescent marking meets the contract"
                + (contract.requiresTermination() ? " and every run comes to rest" : "") + " (" + method + ")");
            case Verdict.Unknown(var reason) -> lines.add("UNKNOWN: " + reason);
            case Verdict.Violated() -> {
                var violations = input.violations();
                lines.add("VIOLATED: " + violations.size() + " " + (violations.size() == 1 ? "part" : "parts")
                    + " of the contract broken");
                for (var v : violations) {
                    renderViolation(v, lines);
                }
            }
        }
        return String.join("\n", lines);
    }

    private static void renderViolation(ContractViolation v, List<String> lines) {
        lines.add("  [" + v.subject() + "] " + v.kind().label() + ": " + v.detail());
        if (!v.confirmed()) {
            lines.add("    (the solver's counterexample did not replay as an ordered firing sequence)");
        }
        if (!v.portTrace().isEmpty()) {
            lines.add("    Port trace:");
            for (var s : v.portTrace()) {
                if (v.cycleStart().isPresent() && s.step() == v.cycleStart().getAsInt() + 1) {
                    lines.add("      -- the cycle starts here --");
                }
                String env = s.environment() == null ? ""
                    : s.environment() == EnvironmentStep.Kind.TRANSITION ? " [environment]"
                    : " [environment " + s.environment().label() + "]";
                var changes = new ArrayList<String>(s.changes().size());
                for (var c : s.changes()) {
                    changes.add(c.place() + " " + (c.delta() > 0 ? "+" : "") + c.delta());
                }
                String joined = String.join(", ", changes);
                lines.add("      " + s.step() + ". " + s.transition() + env + (joined.isEmpty() ? "" : "  " + joined));
            }
        }
        var transitions = v.transitions();
        if (v.cycleStart().isPresent()) {
            int start = Math.min(v.cycleStart().getAsInt(), transitions.size());
            var stem = transitions.subList(0, start);
            String cycle = "then repeating " + String.join(", ", transitions.subList(start, transitions.size()));
            lines.add("    Firing sequence: " + (stem.isEmpty() ? cycle : String.join(", ", stem) + ", " + cycle));
        } else if (!transitions.isEmpty()) {
            lines.add("    Firing sequence: " + String.join(", ", transitions));
        }
        if (!v.markings().isEmpty()) {
            lines.add("    " + (v.kind() == ContractViolation.Kind.TERMINATION ? "Marking on the cycle" : "Quiescent marking")
                + ": " + markingText(v.markings().getLast()));
        }
    }

    /**
     * A marking as the report prints it: {@code {name:count, …}}, or {@code {}} when empty, its
     * places in code-point order of their names, as {@link MarkingState#toString()} prints it and
     * every implementation's report does.
     */
    static String markingText(MarkingState m) {
        return m.toString();
    }
}
