package org.libpetri.smt.opennet;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.smt.SmtVerificationResult.Verdict;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * The human-readable report of an open-net verification ([VER-022]).
 *
 * <p>The report is byte-identical to the TypeScript reference's for the same net and contract,
 * markings included, which is why markings are rendered here rather than through
 * {@link MarkingState#toString()}: see {@link #markingText}.
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
     * A marking as the report prints it: {@code {name:count, …}}, or {@code {}} when empty.
     *
     * <p>The places are listed in the order the reference's {@code MarkingState.toString} lists
     * them, which sorts with {@code localeCompare}, not by code point: {@code _budget} before
     * {@code e1/data} before {@code X/idle}. {@link MarkingState#toString()} sorts by
     * {@link String#compareTo}. The markings are the one part of the report that order reaches,
     * and the report is pinned to the reference byte for byte, so the order is reproduced here
     * ({@link #localeOrder}) rather than the report being allowed to differ.
     */
    static String markingText(MarkingState m) {
        if (m.isEmpty()) {
            return "{}";
        }
        var entries = new ArrayList<Map.Entry<Place<?>, Integer>>(m.asMap().entrySet());
        entries.sort((a, b) -> localeOrder(a.getKey().name(), b.getKey().name()));
        var parts = new ArrayList<String>(entries.size());
        for (var e : entries) {
            parts.add(e.getKey().name() + ":" + e.getValue());
        }
        return "{" + String.join(", ", parts) + "}";
    }

    /**
     * The primary collation order of printable ASCII in ICU's root collation, which Node's
     * {@code localeCompare} uses, with punctuation significant: whitespace, then punctuation,
     * then symbols, then digits, then letters with case ignored.
     */
    private static final String PRIMARY_ORDER =
        " _-,;:!?.'\"()[]{}@*/\\&#%`^+<=>|~$0123456789abcdefghijklmnopqrstuvwxyz";

    /**
     * {@code a.localeCompare(b)} for names of printable ASCII: the primary weights compared
     * first (case-blind, a shorter prefix first), then case, lower before upper, at the first
     * position the case differs.
     *
     * <p>Checked against Node's {@code localeCompare} (ICU, {@code en-US}) on random
     * printable-ASCII pairs. A character outside printable ASCII sorts after every one inside
     * it, by code point: the reference's order there depends on the collation tables, which
     * this port does not carry, and no name the closure generates contains one.
     */
    static int localeOrder(String a, String b) {
        int[] pa = a.codePoints().toArray();
        int[] pb = b.codePoints().toArray();
        int n = Math.min(pa.length, pb.length);
        for (int i = 0; i < n; i++) {
            int cmp = Integer.compare(primary(pa[i]), primary(pb[i]));
            if (cmp != 0) {
                return cmp;
            }
        }
        if (pa.length != pb.length) {
            return Integer.compare(pa.length, pb.length);
        }
        for (int i = 0; i < n; i++) {
            int cmp = Boolean.compare(isAsciiUpper(pa[i]), isAsciiUpper(pb[i]));
            if (cmp != 0) {
                return cmp;
            }
        }
        return a.compareTo(b);
    }

    private static int primary(int codePoint) {
        if (codePoint < 0x80) {
            int lower = isAsciiUpper(codePoint) ? codePoint + ('a' - 'A') : codePoint;
            int at = PRIMARY_ORDER.indexOf(lower);
            if (at >= 0) {
                return at;
            }
        }
        return PRIMARY_ORDER.length() + codePoint;
    }

    private static boolean isAsciiUpper(int codePoint) {
        return codePoint >= 'A' && codePoint <= 'Z';
    }
}
