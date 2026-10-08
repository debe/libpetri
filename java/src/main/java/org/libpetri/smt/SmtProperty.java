package org.libpetri.smt;

import org.libpetri.core.Place;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
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
     * Mutual exclusion ([VER-002]): {@code p1} and {@code p2} never have tokens simultaneously.
     * Violated by a reachable marking that marks both; {@code mutualExclusion(p, p)} is thus
     * violated by any token in {@code p}.
     *
     * <p>The spec defines mutual exclusion over a list pairwise — violated iff any two listed
     * places are marked at once — and the Rust and Python APIs take a list. Java takes exactly
     * two places, the one pair; conjoin several properties for more.
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
     */
    record QuiescentCount(List<Place<?>> places, int min, OptionalInt max, List<Place<?>> waivedBy)
            implements SmtProperty {
        /**
         * @throws IllegalArgumentException when {@code min} is negative or {@code max} is below
         *     {@code min}: a range no count can satisfy is a caller's error, reported here rather
         *     than as a violation at the first quiescent marking ([VER-002] AC9)
         */
        public QuiescentCount {
            Objects.requireNonNull(max, "max");
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
     * Name alignment ([NU-055]): in every reachable marking, the places of {@code places}
     * together hold at most one distinct name. An empty place imposes nothing, but a place
     * holding two names violates it whatever the others hold, so the singleton
     * {@code nameAligned(p)} says that {@code p} never holds two names. A reachability-safety
     * property: Route B stops at the first misaligned class ([VER-012]).
     *
     * <p>Decided only by Route B, the name-partition state-class graph ([NU-050]), on any net,
     * with or without a matched transition. Every other route gives it no verdict, so a Route B
     * {@code Unknown} is final. The verdict is {@code Unknown}, with a reason naming the cause,
     * when a place is not a coloured place of the fragment Route B classifies for the call
     * (a match key, a declared carrier or a relay target): an uncoloured or absent place carries
     * no name, so the predicate on it would hold vacuously. Carriers and relay targets are
     * coloured only under {@link org.libpetri.analysis.FragmentMode#EXTENDED}. It is
     * {@code Unknown} too when a coloured place starts marked, when the net is outside the
     * fragment, and when the graph does not close and its explored prefix holds no misaligned
     * class. When several refusals apply, the reason is that of the first in the refusal order
     * of [NU-055].
     *
     * @param places the list {@code S}: compared by name, each place kept once, at its first
     *               occurrence in the order given. The order changes no verdict, only the
     *               description and which place a reason names.
     */
    record NameAligned(List<Place<?>> places) implements SmtProperty {
        /** @throws IllegalArgumentException when {@code places} is empty */
        public NameAligned {
            places = alignmentPlaces("nameAligned", places);
        }
    }

    /**
     * Quiescent name alignment ([NU-055]): the predicate of {@link NameAligned}, read only in the
     * reachable quiescent markings (the reap-aware quiescence of [VER-002]). Like
     * {@link JoinedOrDeadLettered} it carries no sink clause. A quiescence property: the graph
     * is built in full.
     *
     * <p>Decided only by Route B, with the {@code Unknown} cases of {@link NameAligned}, and one
     * more: under modelled injection ({@code alwaysAvailable()} or {@code bounded(k)}) a net
     * with a registered environment place is {@code Unknown}, since the graph never consumes the
     * place and a net that reads input from it has no resting class. Model the input with
     * {@code arrivals(k)} instead.
     *
     * @param places the list {@code S}, as for {@link NameAligned}
     */
    record QuiescentNameAligned(List<Place<?>> places) implements SmtProperty {
        /** @throws IllegalArgumentException when {@code places} is empty */
        public QuiescentNameAligned {
            places = alignmentPlaces("quiescentNameAligned", places);
        }
    }

    /**
     * The property as the report names it after {@code Property: }. Text is byte-identical
     * across the implementations for {@link QuiescentCount} (see {@link #countAcross}) and for
     * the name-alignment properties ([NU-055]).
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
            case NameAligned na -> "Name alignment of " + placeList(na.places());
            case QuiescentNameAligned qna -> "Quiescent name alignment of " + placeList(qna.places());
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
     * Name alignment of {@code first} and {@code rest} in every reachable marking (NU-055). See
     * {@link NameAligned}.
     *
     * <pre>{@code
     * SmtProperty.nameAligned(box, list); // box and list never hold two different names between them
     * SmtProperty.nameAligned(reply);     // reply never holds two names
     * }</pre>
     */
    static NameAligned nameAligned(Place<?> first, Place<?>... rest) {
        return new NameAligned(prepend(first, rest));
    }

    /**
     * {@link #nameAligned(Place, Place...)} over a collection, in its iteration order.
     *
     * @throws IllegalArgumentException when {@code places} is empty
     */
    static NameAligned nameAligned(Collection<? extends Place<?>> places) {
        return new NameAligned(List.copyOf(places));
    }

    /** Name alignment of {@code first} and {@code rest} at quiescence (NU-055). See {@link QuiescentNameAligned}. */
    static QuiescentNameAligned quiescentNameAligned(Place<?> first, Place<?>... rest) {
        return new QuiescentNameAligned(prepend(first, rest));
    }

    /**
     * {@link #quiescentNameAligned(Place, Place...)} over a collection, in its iteration order.
     *
     * @throws IllegalArgumentException when {@code places} is empty
     */
    static QuiescentNameAligned quiescentNameAligned(Collection<? extends Place<?>> places) {
        return new QuiescentNameAligned(List.copyOf(places));
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

    /** {@code first} followed by {@code rest}, the arguments of a varargs factory. */
    private static List<Place<?>> prepend(Place<?> first, Place<?>[] rest) {
        var out = new ArrayList<Place<?>>(1 + rest.length);
        out.add(first);
        Collections.addAll(out, rest);
        return out;
    }

    /**
     * The list {@code S} of a name-alignment property ([NU-055]): {@code places} with each name
     * kept once, at its first occurrence. An empty list is the caller's error, not a verdict.
     */
    private static List<Place<?>> alignmentPlaces(String factory, List<Place<?>> places) {
        if (Objects.requireNonNull(places, "places").isEmpty()) {
            throw new IllegalArgumentException(factory + " needs at least one place");
        }
        var seen = new HashSet<String>();
        var out = new ArrayList<Place<?>>(places.size());
        for (var place : places) {
            if (seen.add(Objects.requireNonNull(place, "place").name())) {
                out.add(place);
            }
        }
        return List.copyOf(out);
    }

    /**
     * {@code a}, {@code a and b}, {@code a, b and c}: the place list of a name-alignment
     * description, byte-identical across the implementations ([NU-055]).
     */
    private static String placeList(List<Place<?>> places) {
        int last = places.size() - 1;
        String tail = places.get(last).name();
        return last == 0 ? tail : names(places.subList(0, last)) + " and " + tail;
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
