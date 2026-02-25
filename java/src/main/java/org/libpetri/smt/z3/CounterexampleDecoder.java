package org.libpetri.smt.z3;

import com.microsoft.z3.*;
import org.libpetri.analysis.MarkingState;
import org.libpetri.smt.encoding.FlatNet;

import java.util.ArrayList;
import java.util.List;

/**
 * Decodes Z3 Spacer counterexample answers into Petri net marking traces.
 *
 * <p>When Spacer finds a counterexample (property violation), it produces
 * a derivation tree showing how the error state is reachable. This class
 * extracts the marking at each step to produce a human-readable trace.
 *
 * <p><b>Z3 proof tree structure:</b> The answer is a nested function application
 * tree. Interior nodes are rule applications named after the CHC rules
 * (e.g., {@code t_Search}, {@code t_Compose}). Leaf nodes are
 * {@code Reachable(m0, m1, ...)} applications carrying concrete integer
 * markings. The decoder performs a depth-first traversal, collecting
 * {@code Reachable(...)} applications as marking states and {@code t_*}
 * function names as fired transitions.
 */
public final class CounterexampleDecoder {

    private CounterexampleDecoder() {}

    /**
     * Result of counterexample decoding.
     *
     * @param trace       sequence of markings from initial to error state
     * @param transitions names of transitions fired at each step
     */
    public record DecodedTrace(
        List<MarkingState> trace,
        List<String> transitions
    ) {}

    /**
     * Attempts to decode a Z3 counterexample into a marking trace.
     *
     * @param answer  the Z3 Fixedpoint answer expression
     * @param flatNet the flat net (for place info)
     * @return the decoded trace, or a single-state trace if decoding fails
     */
    public static DecodedTrace decode(Expr answer, FlatNet flatNet) {
        var trace = new ArrayList<MarkingState>();
        var transitions = new ArrayList<String>();

        if (answer == null) {
            return new DecodedTrace(trace, transitions);
        }

        try {
            extractTrace(answer, flatNet, trace, transitions);
        } catch (Exception _) {
            // Z3 answer format varies; gracefully degrade
        }

        return new DecodedTrace(List.copyOf(trace), List.copyOf(transitions));
    }

    /**
     * Recursively traverses the Z3 proof tree to extract marking states.
     */
    private static void extractTrace(
            Expr expr, FlatNet flatNet,
            List<MarkingState> trace, List<String> transitions
    ) {
        if (expr == null) return;

        if (expr.isApp()) {
            FuncDecl decl = expr.getFuncDecl();
            String name = decl.getName().toString();

            // Check if this is a Reachable application with integer arguments
            if (name.equals("Reachable") && expr.getNumArgs() == flatNet.placeCount()) {
                var marking = extractMarking(expr, flatNet);
                if (marking != null) {
                    trace.add(marking);
                }
            }

            // Recurse into children to find the derivation chain
            for (int i = 0; i < expr.getNumArgs(); i++) {
                Expr child = expr.getArgs()[i];
                extractTrace(child, flatNet, trace, transitions);
            }

            // Try to extract transition name from rule application
            if (name.startsWith("t_")) {
                transitions.add(name.substring(2));
            }
        }
    }

    /**
     * Extracts a MarkingState from a Reachable(...) application.
     */
    private static MarkingState extractMarking(Expr reachableApp, FlatNet flatNet) {
        int P = flatNet.placeCount();
        if (reachableApp.getNumArgs() != P) return null;

        var builder = MarkingState.builder();
        for (int i = 0; i < P; i++) {
            Expr arg = reachableApp.getArgs()[i];
            if (arg instanceof IntNum intNum) {
                int tokens = intNum.getInt();
                if (tokens > 0) {
                    builder.tokens(flatNet.places().get(i), tokens);
                }
            } else {
                // Non-concrete value in counterexample
                return null;
            }
        }
        return builder.build();
    }
}
