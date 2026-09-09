package org.libpetri.smt;

import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.StateClass;
import org.libpetri.analysis.StateClassGraph;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

/**
 * Bounded state-space enumeration ([VER-017]): decide a property by building the
 * state-class graph and reading the verdict off it, when the graph closes within a class
 * budget.
 *
 * <p>IC3/PDR is built for state spaces that are wide and shallow. A workflow net is the
 * opposite — narrow and deep: a forty-node pipeline has under two thousand reachable
 * classes, but its <em>diameter</em> is the length of the pipeline, so the fixpoint engine
 * needs a frame per stage and its cost climbs with the cube of the length. Enumerating the
 * same net is linear in the state space and finishes in milliseconds. Measured on a
 * forty-node chain (370 places): 410 s on the fixpoint path, 0.11 s here.
 *
 * <p>The route is exact when the graph closes — sound <em>and</em> complete, so a
 * {@code Violated} is a real firing sequence rather than a possibly-spurious
 * over-approximation, and a {@code Proven} is never the {@code Unknown} a fixpoint search
 * runs out of time for.
 *
 * <p>It applies only to an <b>untimed</b> net — every transition {@code immediate} — and
 * that restriction is what makes the verdict interchangeable with the encoders'. The
 * state-class graph carries firing domains, so on a timed net it would explore only the
 * runs the timing admits and its {@code Proven} would be the weaker timed claim;
 * [VER-004] is explicit that the untimed proof is the stronger one, and a route must not
 * quietly hand back a weaker claim than the one it replaced. On an untimed net no domain
 * excludes anything, the graph explores exactly the untimed reachable set, and the two
 * routes decide the same predicate over the same abstraction — enumeration simply decides
 * it where the search may not.
 *
 * <p>When the graph does not close within the budget the route declines and the caller
 * runs the SMT pipeline unchanged: enumeration never turns a verdict into {@code Unknown}
 * that the solver could have decided.
 */
public final class ScgVerifier {

    private ScgVerifier() {}

    /** The note a decided verdict carries into the report. */
    static final String NOTE_ENUMERATED =
        "\nNote: decided by bounded state-space enumeration — the state-class graph closed, so "
        + "the verdict is sound AND complete: a `violated` is a real firing sequence, not a "
        + "possibly-spurious over-approximation. The net is untimed, so this is the same claim "
        + "the encoders make (VER-017).\n";

    /**
     * Whether every transition is {@code immediate}, so the state-class graph explores the
     * untimed reachable set exactly and its verdict is the encoders' claim rather than the
     * weaker timed one. See this class's header.
     */
    public static boolean isUntimed(PetriNet net) {
        for (var t : net.transitions()) {
            if (!(t.timing() instanceof Timing.Immediate)) {
                return false;
            }
        }
        return true;
    }

    /** Outcome of the enumeration route. */
    public sealed interface Outcome {
        /**
         * The graph closed and decided the property.
         *
         * @param verdict     the verdict read off the closed graph — exact, not an
         *                    over-approximation
         * @param trace       the shortest firing sequence to the witnessing class, as
         *                    markings; empty for a proof
         * @param transitions the transition names along {@code trace}; empty for a proof
         * @param classCount  how many state classes the graph holds
         */
        record Decided(
            SmtVerificationResult.Verdict verdict,
            List<MarkingState> trace,
            List<String> transitions,
            int classCount
        ) implements Outcome {}

        /**
         * The graph hit the class budget; the caller falls through to the SMT pipeline.
         *
         * @param classCount how many classes were explored before the budget bound
         */
        record Truncated(int classCount) implements Outcome {}
    }

    /**
     * Decides {@code property} by enumeration, or reports truncation.
     *
     * @param maxClasses the class budget; {@code <= 0} disables the route (the caller then
     *                   never calls this)
     */
    public static Outcome verify(
            PetriNet net,
            MarkingState initial,
            SmtProperty property,
            Collection<Place<?>> sinkPlaces,
            int maxClasses,
            List<RestSet.ConditionalSinks> conditionalSinks
    ) {
        var graph = StateClassGraph.build(net, initial, maxClasses);
        var classes = List.copyOf(graph.stateClasses());
        if (!graph.isComplete()) {
            return new Outcome.Truncated(classes.size());
        }

        int violating = GraphDecision.decideOverClasses(
            new GraphDecision.ClassView() {
                @Override
                public int count() {
                    return classes.size();
                }

                @Override
                public MarkingState markingOf(int i) {
                    return classes.get(i).marking();
                }

                @Override
                public boolean isQuiescent(int i) {
                    return graph.successors(classes.get(i)).isEmpty();
                }
            },
            property, sinkPlaces, conditionalSinks);

        if (violating >= 0) {
            var path = counterexamplePath(graph, classes.get(violating));
            return new Outcome.Decided(
                new SmtVerificationResult.Verdict.Violated(),
                path.markings(), path.transitions(), classes.size());
        }
        return new Outcome.Decided(
            new SmtVerificationResult.Verdict.Proven("state-space enumeration (VER-017)", null),
            List.of(), List.of(), classes.size());
    }

    private record Path(List<MarkingState> markings, List<String> transitions) {}

    /**
     * Shortest firing sequence from the initial class to {@code target}, as markings and
     * transition names.
     */
    private static Path counterexamplePath(StateClassGraph graph, StateClass target) {
        var parent = new HashMap<StateClass, StateClass>();
        var via = new HashMap<StateClass, String>();
        var seen = new HashSet<StateClass>();
        var queue = new ArrayDeque<StateClass>();
        seen.add(graph.initialClass());
        queue.add(graph.initialClass());
        while (!queue.isEmpty()) {
            var current = queue.poll();
            if (current.equals(target)) {
                break;
            }
            for (var entry : graph.outgoingBranchEdges(current).entrySet()) {
                for (var edge : entry.getValue()) {
                    if (!seen.add(edge.target())) {
                        continue;
                    }
                    parent.put(edge.target(), current);
                    via.put(edge.target(), entry.getKey().name());
                    queue.add(edge.target());
                }
            }
        }
        var chain = new ArrayList<StateClass>();
        for (StateClass cur = target; cur != null; cur = parent.get(cur)) {
            chain.add(cur);
        }
        Collections.reverse(chain);
        var markings = new ArrayList<MarkingState>(chain.size());
        var transitions = new ArrayList<String>(Math.max(0, chain.size() - 1));
        for (int i = 0; i < chain.size(); i++) {
            markings.add(chain.get(i).marking());
            if (i > 0) {
                transitions.add(via.get(chain.get(i)));
            }
        }
        return new Path(List.copyOf(markings), List.copyOf(transitions));
    }
}
