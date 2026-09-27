package org.libpetri.core.internal;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

import org.libpetri.core.Arc;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;

/**
 * Arc-level structural diagnostics shared by the model, both executors and the verifier, so
 * each rule and its wording live in one place.
 *
 * <ul>
 *   <li>{@link #duplicateInputMessage} — [CORE-030] AC3: two input arcs on one place. The
 *       {@link Transition} builder rejects it; {@code CompiledNet} keeps the same check as a
 *       backstop and raises the same text.</li>
 *   <li>{@link #duplicateInBranch} / {@link #duplicateOutputMessage} — [IO-011]: a place named
 *       twice in one AND branch of an output spec. The {@link Transition} builder rejects it;
 *       instance composition rejects the port-binding form of it first, with the [MOD-020]
 *       message.</li>
 *   <li>{@link #deadArcs} — [CORE-037]: a read, inhibitor or reset arc on a place nothing can
 *       ever mark. Never an error: nets seeded by the initial marking use such arcs
 *       legitimately, so the rule only fires when the place also starts empty.</li>
 * </ul>
 *
 * <p>Internal API: not part of the public contract.
 */
public final class ArcDiagnostics {

    private ArcDiagnostics() {}

    /** The [CORE-030] duplicate-input rejection text, shared by the builder and the compile backstop. */
    public static String duplicateInputMessage(String transition, String place) {
        return ("Transition '%s' declares two input arcs on place '%s'. Duplicate input places "
            + "have no coherent consumption semantics and are rejected (CORE-030). Use a single "
            + "arc with exactly(n) / atLeast(n) instead.").formatted(transition, place);
    }

    /** The [IO-011] rejection text: a place named twice in one AND branch of an output spec. */
    public static String duplicateOutputMessage(String transition, String place) {
        return ("output spec of transition '%s' names place '%s' twice in one AND branch; outputs are "
            + "sets (IO-015) — a weighted output is not supported, add a second place or a follow-up "
            + "transition").formatted(transition, place);
    }

    /**
     * Two leaves of one output branch that stand for the same place ({@link #duplicateInBranch}).
     *
     * @param place  the place both stand for, after the mapping
     * @param first  the first leaf, as the spec names it
     * @param second the second leaf, as the spec names it
     */
    public record BranchDuplicate(Place<?> place, Place<?> first, Place<?> second) {}

    /**
     * The first place a single output branch names twice — one choice at every XOR, nested ANDs
     * flattened ([IO-011]) — or {@code null}. {@code placeOf} maps a leaf to the place it stands
     * for: the identity for a spec as written, the port-to-host binding for composition. The
     * {@code to} place of a {@code ForwardInput} is a leaf, and a {@code Timeout} is read through
     * to its child.
     *
     * <p>Linear in the spec: an AND's children combine by cross product, so a place one child
     * names in any of its branches and a sibling names in any of its branches is named twice by
     * some branch; a XOR's alternatives only pool their leaves.
     */
    public static BranchDuplicate duplicateInBranch(Arc.Out out, Function<Place<?>, Place<?>> placeOf) {
        return scanBranches(out, placeOf, new LinkedHashMap<>());
    }

    /**
     * Adds the leaves of {@code out} to {@code leaves} (mapped place -> first leaf naming it),
     * pooling across XOR alternatives, and returns the first duplicate inside one AND branch.
     */
    private static BranchDuplicate scanBranches(
            Arc.Out out, Function<Place<?>, Place<?>> placeOf, Map<Place<?>, Place<?>> leaves) {
        switch (out) {
            case Arc.Out.Place p -> leaves.putIfAbsent(placeOf.apply(p.place()), p.place());
            case Arc.Out.ForwardInput f -> leaves.putIfAbsent(placeOf.apply(f.to()), f.to());
            case Arc.Out.Timeout t -> {
                return scanBranches(t.child(), placeOf, leaves);
            }
            case Arc.Out.Xor x -> {
                for (var child : x.children()) {
                    var found = scanBranches(child, placeOf, leaves);
                    if (found != null) return found;
                }
            }
            case Arc.Out.And a -> {
                var own = new LinkedHashMap<Place<?>, Place<?>>();
                for (var child : a.children()) {
                    var childLeaves = new LinkedHashMap<Place<?>, Place<?>>();
                    var found = scanBranches(child, placeOf, childLeaves);
                    if (found != null) return found;
                    for (var e : childLeaves.entrySet()) {
                        var prior = own.putIfAbsent(e.getKey(), e.getValue());
                        if (prior != null) return new BranchDuplicate(e.getKey(), prior, e.getValue());
                    }
                }
                own.forEach(leaves::putIfAbsent);
            }
        }
        return null;
    }

    /** Which kind of test-only arc a {@link DeadArc} is. */
    public enum Kind {
        READ("read"),
        INHIBITOR("inhibitor"),
        RESET("reset");

        private final String label;

        Kind(String label) {
            this.label = label;
        }

        /** The kind as the warning names it. */
        public String label() {
            return label;
        }
    }

    /**
     * A read, inhibitor or reset arc of {@code transition} on {@code place}, where no transition
     * consumes from or produces into {@code place}, it is not an environment place, and the
     * initial marking leaves it empty ([CORE-037]).
     */
    public record DeadArc(String transition, Kind kind, Place<?> place) {

        /**
         * The warning text without a severity prefix: the executors emit it as a log message,
         * the verifier prefixes {@code WARNING: }.
         */
        public String message() {
            String effect = switch (kind) {
                case READ -> "the transition can never be enabled";
                case INHIBITOR -> "the arc never blocks";
                case RESET -> "the arc has no effect";
            };
            return kind.label() + " arc of '" + transition + "' on '" + place.name()
                + "': no transition produces into or consumes from it and it starts empty; "
                + effect + ".";
        }
    }

    /**
     * The dead read / inhibitor / reset arcs of {@code transitions} ([CORE-037]), one per arc —
     * two dead arcs on one place are two entries — in transition order and, within a
     * transition, reads, then inhibitors, then resets.
     *
     * @param transitions      every transition of the net
     * @param environmentPlaces places tokens can be injected into from outside
     * @param initiallyMarked  whether the initial marking holds a token on a place
     */
    public static List<DeadArc> deadArcs(
            Iterable<Transition> transitions,
            Predicate<Place<?>> environmentPlaces,
            Predicate<Place<?>> initiallyMarked
    ) {
        var connected = new HashSet<Place<?>>();
        for (var t : transitions) {
            for (var in : t.inputSpecs()) connected.add(in.place());
            if (t.outputSpec() != null) connected.addAll(t.outputSpec().allPlaces());
        }
        var out = new ArrayList<DeadArc>();
        for (var t : transitions) {
            for (var rd : t.reads()) addIfDead(out, t, Kind.READ, rd.place(), connected, environmentPlaces, initiallyMarked);
            for (var inh : t.inhibitors()) addIfDead(out, t, Kind.INHIBITOR, inh.place(), connected, environmentPlaces, initiallyMarked);
            for (var rs : t.resets()) addIfDead(out, t, Kind.RESET, rs.place(), connected, environmentPlaces, initiallyMarked);
        }
        return List.copyOf(out);
    }

    private static void addIfDead(
            List<DeadArc> out, Transition t, Kind kind, Place<?> place, Set<Place<?>> connected,
            Predicate<Place<?>> environmentPlaces, Predicate<Place<?>> initiallyMarked
    ) {
        if (!connected.contains(place) && !environmentPlaces.test(place) && !initiallyMarked.test(place)) {
            out.add(new DeadArc(t.name(), kind, place));
        }
    }
}
