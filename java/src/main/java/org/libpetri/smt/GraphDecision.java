package org.libpetri.smt;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.OptionalInt;
import java.util.function.IntPredicate;
import java.util.function.Predicate;

/**
 * The property predicate both state-class-graph routes decide, in one place.
 *
 * <p>Two routes enumerate a finite graph of classes and read a verdict off it: the
 * &nu; name-partition quotient of [VER-012] ({@link NuScgVerifier}) and the plain bounded
 * enumeration of [VER-017] ({@link ScgVerifier}). They explore different graphs, but the
 * question they ask of a class is identical, and [VER-002] AC7 requires every route to
 * decide the <em>same</em> predicate. Stating it once is what keeps that true: when the
 * sink clause last lived in two copies, one of them drifted (NU-040 AC4).
 *
 * <p>The reading of a count clause ({@link #tokensAcross}, {@link #countViolation}) is
 * public: the open-net contract of [VER-022] reads a quiescent marking through it, so the
 * contract and {@link SmtProperty.QuiescentCount} cannot read a count differently.
 */
public final class GraphDecision {

    private GraphDecision() {}

    /**
     * A finite graph of classes, indexed {@code 0 .. count() - 1}, class 0 the initial one, in
     * breadth-first discovery order. It may be the explored prefix of a graph that did not close
     * ([VER-017], "Verdicts from a truncated graph"): every class in it is reachable, so the
     * safety properties read every one, but a view of a prefix must answer
     * {@link #isQuiescent} only for a class that was <em>expanded</em> and found without
     * successors — a frontier class was never looked at.
     */
    interface ClassView {
        int count();

        /** The marking of class {@code i}. */
        MarkingState markingOf(int i);

        /** Whether class {@code i} was expanded and has no successor — the graph's quiescence. */
        boolean isQuiescent(int i);
    }

    /**
     * A {@link ClassView} of the &nu; name-partition graph ([NU-050]), whose classes carry a name
     * layer. Only such a view decides a name-alignment property ([NU-055]): a view without names
     * would read every class as aligned.
     */
    interface NamedClassView extends ClassView {
        /** Whether the places named {@code places} together hold at most one name in class {@code i}. */
        boolean namesAligned(int i, List<String> places);
    }

    /**
     * The class predicate of a reachability-safety property: whether class {@code i} of
     * {@code view} violates it.
     */
    @FunctionalInterface
    interface ClassPredicate {
        boolean violates(ClassView view, int i);
    }

    /**
     * The index of the first class witnessing a violation, or {@code -1} when the property
     * holds across the whole graph.
     *
     * <p>Quiescence-based properties read {@link ClassView#isQuiescent}; reachability-safety
     * properties read the class alone. The name-alignment properties of [NU-055] read the name
     * layer of a {@link NamedClassView}, and throw on any other view. {@code DeadlockFree} uses
     * the shared rest set of [VER-014], so a conditional sink excuses a token exactly as it does
     * in the encoders.
     *
     * @throws IllegalArgumentException for a name-alignment property on a view without names
     */
    static int decideOverClasses(
            ClassView view,
            SmtProperty property,
            Collection<Place<?>> sinkPlaces,
            List<RestSet.ConditionalSinks> conditionalSinks
    ) {
        // NU-055: a view without a name layer would read every class as aligned, so refuse before
        // reading any, whether or not a class is quiescent.
        if (NameAlignment.isNameAlignment(property)) {
            requireNames(view, property);
        }
        var violates = safetyViolation(property);
        if (violates != null) {
            return firstWhere(view, i -> violates.violates(view, i));
        }
        return switch (property) {
            // Decided by safetyViolation above.
            case SmtProperty.PlaceBound _, SmtProperty.BranchPlaceBound _,
                 SmtProperty.Unreachable _, SmtProperty.MutualExclusion _, SmtProperty.NameAligned _ -> -1;
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
            // QuiescentCount ([VER-002]): a quiescent class whose count across the places is
            // below the lower bound with no waiver marked, or above the upper bound.
            case SmtProperty.QuiescentCount(var places, var min, var max, var waivedBy) ->
                firstWhere(view, i -> view.isQuiescent(i)
                    && countViolation(view.markingOf(i), places, min, max, waivedBy) != null);
            // QuiescentNameAligned ([NU-055]): a quiescent class whose name layer holds two
            // different names across the places of the property. No sink clause.
            case SmtProperty.QuiescentNameAligned(var places) -> {
                var named = requireNames(view, property);
                var names = placeNames(places);
                yield firstWhere(view, i -> view.isQuiescent(i) && !named.namesAligned(i, names));
            }
        };
    }

    /**
     * The class predicate of a reachability-safety property (whether a class violates it), or
     * {@code null} for a quiescence property, whose predicate also needs to know whether the
     * class has successors. It reads the class alone, so a graph build can apply it to each class
     * as the class is discovered and stop at the first violation ([VER-012]);
     * {@link #decideOverClasses} decides these properties through this same function.
     *
     * <p>{@code NameAligned} ([NU-055]) reads the class's name layer, which only a
     * {@link NamedClassView} has, and throws on any other view; every other property reads the
     * marking alone.
     */
    static ClassPredicate safetyViolation(SmtProperty property) {
        return switch (property) {
            case SmtProperty.PlaceBound(var place, var bound) -> onMarking(m -> m.tokens(place) > bound);
            case SmtProperty.BranchPlaceBound(var place, var bound) -> onMarking(m -> m.tokens(place) > bound);
            case SmtProperty.Unreachable(var places) -> onMarking(m -> {
                for (var p : places) {
                    if (!m.hasTokens(p)) {
                        return false;
                    }
                }
                return true;
            });
            case SmtProperty.MutualExclusion(var p1, var p2) -> onMarking(m -> m.hasTokens(p1) && m.hasTokens(p2));
            case SmtProperty.NameAligned(var places) -> {
                var names = placeNames(places);
                yield (view, i) -> !requireNames(view, property).namesAligned(i, names);
            }
            case SmtProperty.DeadlockFree _, SmtProperty.TerminatesAtSink _,
                 SmtProperty.JoinedOrDeadLettered _, SmtProperty.QuiescentCount _,
                 SmtProperty.QuiescentNameAligned _ -> null;
        };
    }

    /** The names of a name-alignment property's places, mapped once per graph rather than per class. */
    private static List<String> placeNames(List<Place<?>> places) {
        return places.stream().map(Place::name).toList();
    }

    /** The class predicate that reads the class's marking alone. */
    private static ClassPredicate onMarking(Predicate<MarkingState> violates) {
        return (view, i) -> violates.test(view.markingOf(i));
    }

    /**
     * {@code view} as a {@link NamedClassView}, or a throw when it has no name layer: a
     * name-alignment property is decided only by the &nu; name-partition graph ([NU-055] AC4),
     * and a graph without names would read every class as aligned.
     */
    private static NamedClassView requireNames(ClassView view, SmtProperty property) {
        if (view instanceof NamedClassView named) {
            return named;
        }
        throw new IllegalArgumentException(NameAlignment.routeBOnlyReason(property));
    }

    /**
     * The report note of a violation found in the explored prefix of a graph that did not close
     * ([VER-012], [VER-017], [VER-023]).
     */
    static String prefixNote(String graph, int maxClasses) {
        return "\nNote: the " + graph + " was truncated at " + maxClasses + " classes; the violation was found in "
            + "the explored prefix. Every explored class is reachable, so the counterexample is a real firing "
            + "sequence, the shortest within the explored graph. A truncated graph never proves a property.\n";
    }

    /** Which bound of a count a marking breaks ({@link #countViolation}). */
    public enum CountBound {
        /** Fewer than {@code min}, with no waiver marked. */
        LOWER,
        /** More than {@code max}. Never waived. */
        UPPER
    }

    /**
     * The tokens {@code m} holds across {@code places}, each place counted once: a place
     * named twice is still one place, as the encoders read it. Places are the same place
     * when they are equal ({@code Place} equality, name and token type), which is how
     * {@link MarkingState} and the flat net key them. A {@code long}, so a sum of
     * {@code int} counts never wraps into one that reads as within bounds.
     */
    public static long tokensAcross(MarkingState m, Collection<? extends Place<?>> places) {
        var seen = new HashSet<Place<?>>();
        long count = 0;
        for (var p : places) {
            if (seen.add(p)) {
                count += m.tokens(p);
            }
        }
        return count;
    }

    /**
     * Which bound of a count {@code m} breaks: {@link CountBound#LOWER} when it holds fewer
     * than {@code min} across {@code places} while no {@code waivedBy} place is marked,
     * {@link CountBound#UPPER} when it holds more than {@code max} (empty is unbounded)
     * whatever the waivers hold, else {@code null}. The upper bound is checked first, so a
     * marking that could read as both reports the one no waiver excuses.
     *
     * <p>The one reading of a count clause, shared by [VER-002]'s
     * {@link SmtProperty.QuiescentCount} on the graph routes and by the open-net contract of
     * [VER-022], so the two cannot drift.
     */
    public static CountBound countViolation(
            MarkingState m, Collection<? extends Place<?>> places, int min, OptionalInt max,
            Collection<? extends Place<?>> waivedBy
    ) {
        long count = tokensAcross(m, places);
        if (max.isPresent() && count > max.getAsInt()) {
            return CountBound.UPPER;
        }
        if (count < min && !anyMarked(m, waivedBy)) {
            return CountBound.LOWER;
        }
        return null;
    }

    /** Whether any of {@code places} holds a token in {@code m}. */
    private static boolean anyMarked(MarkingState m, Collection<? extends Place<?>> places) {
        for (var p : places) {
            if (m.hasTokens(p)) {
                return true;
            }
        }
        return false;
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
