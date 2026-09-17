package org.libpetri.smt;

import org.libpetri.core.Place;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.OptionalInt;
import java.util.Set;

/**
 * Safety properties that can be verified via IC3/PDR.
 *
 * <p>Each property is encoded as an error condition: if a reachable state
 * violates the property, Spacer finds a counterexample. If no violation
 * is reachable, the property is proven.
 */
public sealed interface SmtProperty {

    /**
     * No reachable quiescent marking strands a token (VER-002).
     *
     * <p>Violated when a reachable marking is quiescent (every transition
     * disabled) and holds a token in a place that is not a declared sink. The
     * empty marking strands nothing and never violates. This is workflow-net
     * proper completion; for the weaker "did the net reach a terminal at all",
     * see {@link TerminatesAtSink}, which inverts on the empty marking.
     */
    record DeadlockFree() implements SmtProperty {}

    /**
     * Every reachable quiescent marking has at least one declared sink marked
     * (VER-002).
     *
     * <p>Violated when a reachable marking is quiescent and no declared sink
     * holds a token. Says nothing about tokens left elsewhere. Meaningful only
     * with at least one sink declared; with none, every quiescent marking
     * violates vacuously.
     */
    record TerminatesAtSink() implements SmtProperty {}

    /**
     * Mutual exclusion: two places never have tokens simultaneously.
     *
     * <p>Useful for verifying resource exclusion properties.
     */
    record MutualExclusion(Place<?> p1, Place<?> p2) implements SmtProperty {}

    /**
     * Place bound: a place never exceeds a given token count.
     *
     * <p>Useful for verifying bounded buffer properties.
     */
    record PlaceBound(Place<?> place, int bound) implements SmtProperty {}

    /**
     * Unreachability: the given set of places never all have tokens simultaneously.
     *
     * <p>A marking where all specified places have tokens is an error state.
     *
     * @param places the places, kept in the order given: the description names them in it, as
     *               every implementation does. Equality is still a set's.
     */
    record Unreachable(Set<Place<?>> places) implements SmtProperty {
        public Unreachable {
            var ordered = new LinkedHashSet<Place<?>>();
            for (var place : places) {
                ordered.add(Objects.requireNonNull(place, "place"));
            }
            places = Collections.unmodifiableSequencedSet(ordered);
        }
    }

    /**
     * Branch / budget place bound: a &nu;-net budget or fork-branch place never
     * exceeds {@code bound} tokens — the bounded-budget decidability lever
     * (NU-040).
     *
     * <p>Encodes identically to {@link PlaceBound} (a linear-integer count
     * bound), but names the &nu;-net intent: the live correlation pool is
     * bounded, keeping the well-structured transition system finite. The
     * matched-transition over-approximation is sound for this safety bound —
     * a {@code Proven} verdict holds for the real net, which fires strictly
     * fewer joins than the over-approximation.
     */
    record BranchPlaceBound(Place<?> place, int bound) implements SmtProperty {}

    /**
     * Joined-or-dead-lettered: every forked name is eventually joined or
     * dead-lettered, so no reachable <em>quiescent</em> (deadlocked) marking
     * still holds a token in {@code pending} (NU-040).
     *
     * <p>Violated when a reachable marking is both quiescent and has
     * {@code pending >= 1} — a stranded correlation group. Encoded as
     * quiescence conjoined with {@code pending} non-emptiness, with NO sink
     * clause: a declared sink holding a token must not excuse a stranded group
     * (NU-040 AC4).
     */
    record JoinedOrDeadLettered(Place<?> pending) implements SmtProperty {}

    /**
     * A token count at quiescence: every reachable quiescent marking holds between
     * {@code min} and {@code max} tokens across {@code places}, and the lower bound is
     * waived while any {@code waivedBy} place holds a token (VER-002).
     *
     * <p>Violated by a reachable quiescent marking that holds fewer than {@code min} while
     * every {@code waivedBy} place is empty, or more than {@code max} whatever the waivers
     * hold. This is the count a designed terminal ([VER-014]) makes conditional: a halted
     * run need not refund its budget, but it never holds more than there is.
     *
     * <p>An empty {@code max} is unbounded and contributes no upper-bound clause. It is an
     * absent optional rather than a sentinel such as {@link Integer#MAX_VALUE}, so no
     * legitimate count can collide with it; the spec leaves the representation to each
     * implementation because it is observable neither in the script nor in the report.
     * A place named twice in {@code places} is counted once.
     *
     * @param places   the places the count is taken across, in declaration order (the
     *                 order the report names them in)
     * @param min      the least count a quiescent marking may hold, waived while any
     *                 {@code waivedBy} place is marked
     * @param max      the most a quiescent marking may hold, never waived; empty when
     *                 unbounded
     * @param waivedBy the markers whose presence waives the lower bound
     * @throws IllegalArgumentException when {@code min} is negative or {@code max} is below
     *     {@code min}: a range no count can satisfy is a caller's error, reported where the
     *     property is built rather than as a verdict ([VER-002] AC9), because it would
     *     otherwise come back violated at the first quiescent marking and read as a finding
     *     about the net
     */
    record QuiescentCount(List<Place<?>> places, int min, OptionalInt max, List<Place<?>> waivedBy)
            implements SmtProperty {
        public QuiescentCount {
            java.util.Objects.requireNonNull(max, "max");
            if (min < 0 || (max.isPresent() && max.getAsInt() < min)) {
                throw new IllegalArgumentException(
                    "quiescentCount needs whole bounds with 0 <= min <= max, got " + min + ".."
                    + (max.isPresent() ? Integer.toString(max.getAsInt()) : "unbounded"));
            }
            places = List.copyOf(places);
            waivedBy = List.copyOf(waivedBy);
        }
    }

    /**
     * The property as the report names it after {@code Property: }. Text is byte-identical
     * across the implementations for {@link QuiescentCount}; see {@link #countAcross}.
     *
     * @return the human-readable description
     */
    default String description() {
        return switch (this) {
            case DeadlockFree() -> "Deadlock-freedom";
            case TerminatesAtSink() -> "Terminates at a declared sink";
            case MutualExclusion me ->
                "Mutual exclusion of " + me.p1().name() + " and " + me.p2().name();
            case PlaceBound pb ->
                "Place " + pb.place().name() + " bounded by " + pb.bound();
            case Unreachable ur ->
                "Unreachability of marking with tokens in {" + names(ur.places()) + "}";
            case BranchPlaceBound bpb ->
                "Branch place bound (ν-budget): " + bpb.place().name() + " <= " + bpb.bound();
            case JoinedOrDeadLettered jdl ->
                "Joined-or-dead-lettered: " + jdl.pending().name() + " = 0 at quiescence";
            case QuiescentCount qc -> {
                String count = "Quiescent count: " + countAcross(qc.min(), qc.max(), qc.places());
                yield qc.waivedBy().isEmpty()
                    ? count
                    : count + "; lower bound waived while {" + names(qc.waivedBy()) + "} is marked";
            }
        };
    }

    // Factory methods

    static DeadlockFree deadlockFree() {
        return new DeadlockFree();
    }

    /**
     * Quiescence reaches a declared sink (VER-002).
     *
     * @return the {@link TerminatesAtSink} property
     */
    static TerminatesAtSink terminatesAtSink() {
        return new TerminatesAtSink();
    }

    static MutualExclusion mutualExclusion(Place<?> p1, Place<?> p2) {
        return new MutualExclusion(p1, p2);
    }

    static PlaceBound placeBound(Place<?> place, int bound) {
        return new PlaceBound(place, bound);
    }

    /**
     * Unreachability of a marking with tokens in every one of {@code places}.
     *
     * @param places the places, named in the description in the order given (a
     *               {@link java.util.LinkedHashSet} or {@link java.util.SequencedSet} keeps one;
     *               {@link Set#of} does not)
     */
    static Unreachable unreachable(Set<Place<?>> places) {
        return new Unreachable(places);
    }

    static BranchPlaceBound branchPlaceBound(Place<?> place, int bound) {
        return new BranchPlaceBound(place, bound);
    }

    static JoinedOrDeadLettered joinedOrDeadLettered(Place<?> pending) {
        return new JoinedOrDeadLettered(pending);
    }

    /**
     * A token count at quiescence (VER-002). See {@link QuiescentCount}.
     *
     * <pre>{@code
     * // The budget is back at k whenever the net comes to rest, unless it halted.
     * SmtProperty.quiescentCount(List.of(budget), k, OptionalInt.of(k), List.of(halt));
     * }</pre>
     *
     * @throws IllegalArgumentException when {@code min} is negative or {@code max} is below it
     */
    static QuiescentCount quiescentCount(
            Collection<? extends Place<?>> places, int min, OptionalInt max,
            Collection<? extends Place<?>> waivedBy
    ) {
        return new QuiescentCount(List.copyOf(places), min, max, List.copyOf(waivedBy));
    }

    /**
     * {@link #quiescentCount(Collection, int, OptionalInt, Collection)} with no waiver: the
     * lower bound holds at every quiescent marking.
     */
    static QuiescentCount quiescentCount(Collection<? extends Place<?>> places, int min, OptionalInt max) {
        return quiescentCount(places, min, max, List.of());
    }

    /**
     * A count's bounds in words: {@code exactly 1}, {@code at most 1}, {@code at least 2},
     * {@code between 1 and 3}, {@code any number}. An empty {@code max} is unbounded.
     *
     * <p>Every implementation renders a count this way, so an unbounded {@code max} reads
     * the same in every report whatever each stores for it ([VER-002]).
     */
    static String countPhrase(int min, OptionalInt max) {
        if (max.isEmpty()) {
            return min == 0 ? "any number" : "at least " + min;
        }
        int upper = max.getAsInt();
        if (min == upper) {
            return "exactly " + min;
        }
        return min == 0 ? "at most " + upper : "between " + min + " and " + upper;
    }

    /**
     * {@code exactly 1 across {a, b}}: a count and the places it is taken over, in the
     * order given.
     *
     * <p>The property description and the open-net contract of [VER-022] must say this the
     * same way about the same clause, so the phrase is built here once rather than at each
     * call site.
     */
    static String countAcross(int min, OptionalInt max, Collection<? extends Place<?>> places) {
        return countPhrase(min, max) + " across {" + names(places) + "}";
    }

    /** The places' names joined by {@code ", "}, in the order given. */
    private static String names(Collection<? extends Place<?>> places) {
        var out = new ArrayList<String>(places.size());
        for (var p : places) {
            out.add(p.name());
        }
        return String.join(", ", out);
    }
}
