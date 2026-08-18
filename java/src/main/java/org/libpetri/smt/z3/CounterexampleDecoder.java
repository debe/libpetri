package org.libpetri.smt.z3;

import com.microsoft.z3.*;
import org.libpetri.analysis.MarkingState;
import org.libpetri.smt.encoding.FlatNet;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Decodes Z3 Spacer counterexample answers into the set of reachable markings
 * appearing in the derivation.
 *
 * <p>When Spacer finds a counterexample (property violation), it produces a
 * derivation tree showing how the error state is reachable. This class extracts
 * the concrete markings carried by the tree's {@code Reachable(...)}
 * applications.
 *
 * <p><b>Z3 proof tree structure:</b> The answer is a nested function
 * application tree. Interior nodes are rule applications named after the CHC
 * rules (e.g., {@code t_Search}, {@code t_Compose}). Leaf nodes are
 * {@code Reachable(m0, m1, ...)} applications carrying concrete integer
 * markings. The decoder performs a depth-first traversal, collecting
 * {@code Reachable(...)} applications as marking states and {@code t_*}
 * function names as fired transitions.
 *
 * <p><b>Order-free by design:</b> the traversal order of the derivation tree is
 * NOT an execution order (Spacer nests and shares subderivations freely), so
 * the markings are returned both as the raw traversal
 * {@linkplain DecodedStates#trace() trace} (what a report may show verbatim) and
 * as an order-free {@linkplain DecodedStates#states() set}. The execution order
 * is reconstructed — and the counterexample confirmed — by
 * {@link AbstractReplayer}, which chains the set into an actual run of the
 * abstract semantics.
 *
 * <p><b>Graceful degradation:</b> the Z3 answer format varies across versions;
 * any unrecognized shape degrades to whatever states were recovered, with a
 * structured {@link DecodedStates#note()} describing what was lost. Decoding
 * never throws.
 */
public final class CounterexampleDecoder {

    private CounterexampleDecoder() {}

    /**
     * Result of counterexample decoding.
     *
     * @param trace       the markings in derivation-TRAVERSAL order, duplicates
     *                    included — what the raw report shows; NOT a firing order
     * @param states      the same markings as an order-free set (deduplicated) —
     *                    what {@link AbstractReplayer} chains into a firing order
     * @param transitions names of transition rules appearing in the derivation,
     *                    in traversal order (informational — not an execution
     *                    order)
     * @param note        structured reason when decoding degraded (null when
     *                    the whole answer was decoded cleanly)
     */
    public record DecodedStates(
        List<MarkingState> trace,
        Set<MarkingState> states,
        List<String> transitions,
        String note
    ) {}

    /**
     * Attempts to decode a Z3 counterexample into the set of markings it
     * derives. Never throws.
     *
     * @param answer  the Z3 Fixedpoint answer expression (may be null)
     * @param flatNet the flat net (for place info)
     * @return the decoded states; empty with a note if nothing was decodable
     */
    public static DecodedStates decode(Expr answer, FlatNet flatNet) {
        var trace = new ArrayList<MarkingState>();
        var states = new LinkedHashSet<MarkingState>();
        var transitions = new ArrayList<String>();

        if (answer == null) {
            return new DecodedStates(List.of(), Set.of(), List.of(),
                "Spacer returned no counterexample derivation (answer was null)");
        }

        int[] nonConcrete = new int[1];
        String failure = null;
        try {
            extract(answer, flatNet, trace, states, transitions, nonConcrete);
        } catch (Exception e) {
            // Z3 answer format varies; keep whatever was recovered so far.
            failure = "decoding aborted mid-traversal: " + e;
        }

        String note = null;
        if (failure != null) {
            note = failure;
        } else if (nonConcrete[0] > 0) {
            note = nonConcrete[0] + " Reachable application(s) carried non-concrete "
                + "marking arguments and were skipped";
        } else if (states.isEmpty()) {
            note = "no Reachable applications with concrete markings found in the derivation";
        }

        return new DecodedStates(List.copyOf(trace),
            Collections.unmodifiableSet(states), List.copyOf(transitions), note);
    }

    /**
     * Recursively traverses the Z3 proof tree, collecting marking states and
     * rule names.
     */
    private static void extract(
            Expr expr, FlatNet flatNet, List<MarkingState> trace,
            Set<MarkingState> states, List<String> transitions, int[] nonConcrete
    ) {
        if (expr == null || !expr.isApp()) {
            return;
        }

        FuncDecl decl = expr.getFuncDecl();
        String name = decl.getName().toString();

        // A Reachable application with one integer argument per place.
        if (name.equals("Reachable") && expr.getNumArgs() == flatNet.placeCount()) {
            var marking = extractMarking(expr, flatNet);
            if (marking != null) {
                trace.add(marking);
                states.add(marking);
            } else {
                nonConcrete[0]++;
            }
        }

        // Recurse into children to find the rest of the derivation.
        for (int i = 0; i < expr.getNumArgs(); i++) {
            extract(expr.getArgs()[i], flatNet, trace, states, transitions, nonConcrete);
        }

        // Transition rule application names carry the fired transition.
        if (name.startsWith("t_")) {
            transitions.add(name.substring(2));
        }
    }

    /**
     * Extracts a MarkingState from a Reachable(...) application; null if any
     * argument is not a concrete integer.
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
