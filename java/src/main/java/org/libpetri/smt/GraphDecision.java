package org.libpetri.smt;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;

import java.util.Collection;
import java.util.List;
import java.util.function.IntPredicate;

/**
 * The property predicate both state-class-graph routes decide, in one place.
 *
 * <p>Two routes enumerate a finite graph of classes and read a verdict off it: the
 * &nu; name-partition quotient of [VER-012] ({@link NuScgVerifier}) and the plain bounded
 * enumeration of [VER-017] ({@link ScgVerifier}). They explore different graphs, but the
 * question they ask of a class is identical, and [VER-002] AC7 requires every route to
 * decide the <em>same</em> predicate. Stating it once is what keeps that true: when the
 * sink clause last lived in two copies, one of them drifted (NU-040 AC4).
 */
final class GraphDecision {

    private GraphDecision() {}

    /** A finite graph of classes, indexed {@code 0 .. count() - 1}, class 0 the initial one. */
    interface ClassView {
        int count();

        /** The marking of class {@code i}. */
        MarkingState markingOf(int i);

        /** Whether class {@code i} has no successor — the graph's quiescence. */
        boolean isQuiescent(int i);
    }

    /**
     * The index of the first class witnessing a violation, or {@code -1} when the property
     * holds across the whole graph.
     *
     * <p>Quiescence-based properties read {@link ClassView#isQuiescent}; reachability-safety
     * properties read the marking alone. {@code DeadlockFree} uses the shared rest set of
     * [VER-014], so a conditional sink excuses a token exactly as it does in the encoders.
     */
    static int decideOverClasses(
            ClassView view,
            SmtProperty property,
            Collection<Place<?>> sinkPlaces,
            List<RestSet.ConditionalSinks> conditionalSinks
    ) {
        return switch (property) {
            case SmtProperty.PlaceBound(var place, var bound) ->
                firstWhere(view, i -> view.markingOf(i).tokens(place) > bound);
            case SmtProperty.BranchPlaceBound(var place, var bound) ->
                firstWhere(view, i -> view.markingOf(i).tokens(place) > bound);
            case SmtProperty.Unreachable(var places) ->
                firstWhere(view, i -> {
                    var m = view.markingOf(i);
                    for (var p : places) {
                        if (!m.hasTokens(p)) {
                            return false;
                        }
                    }
                    return true;
                });
            case SmtProperty.MutualExclusion(var p1, var p2) ->
                firstWhere(view, i -> {
                    var m = view.markingOf(i);
                    return m.hasTokens(p1) && m.hasTokens(p2);
                });
            // DeadlockFree ([VER-002]): a quiescent class that strands a token — some marked
            // place is not where resting is permitted, the conditional sinks of [VER-014]
            // included. The empty marking strands nothing (AC4).
            case SmtProperty.DeadlockFree() ->
                firstWhere(view, i -> view.isQuiescent(i)
                    && RestSet.strandsToken(view.markingOf(i), sinkPlaces, conditionalSinks));
            // TerminatesAtSink ([VER-002]): a quiescent class that marks NO declared sink.
            // Inverts with DeadlockFree on the empty marking, by design.
            case SmtProperty.TerminatesAtSink() ->
                firstWhere(view, i -> view.isQuiescent(i)
                    && !anySinkMarked(view.markingOf(i), sinkPlaces));
            // JoinedOrDeadLettered (NU-040 AC4): a quiescent class still holding a pending
            // token. No sink clause.
            case SmtProperty.JoinedOrDeadLettered(var pending) ->
                firstWhere(view, i -> view.isQuiescent(i) && view.markingOf(i).hasTokens(pending));
        };
    }

    /** Whether any declared sink place holds a token in {@code m} ([VER-002]). */
    private static boolean anySinkMarked(MarkingState m, Collection<Place<?>> sinks) {
        for (var p : m.placesWithTokens()) {
            if (sinks.contains(p)) {
                return true;
            }
        }
        return false;
    }

    private static int firstWhere(ClassView view, IntPredicate pred) {
        for (int i = 0; i < view.count(); i++) {
            if (pred.test(i)) {
                return i;
            }
        }
        return -1;
    }
}
