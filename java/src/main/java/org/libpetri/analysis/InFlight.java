package org.libpetri.analysis;

import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;
import org.libpetri.core.internal.CodePointOrder;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * In-flight actions in verification ([VER-004], [EXEC-001], [EXEC-003]).
 *
 * <p>Every route reads a firing as one atomic step. The executor does not fire that way: it
 * consumes a firing's inputs when the action starts and deposits its outputs when the action
 * completes, and other transitions fire in between. An asynchronous action leaves that gap open
 * for as long as it runs; a synchronous one until the end of its firing pass, because a drain
 * later in the same pass does not see the deposit ([EXEC-003] AC5).
 *
 * <p>For most nets the gap changes nothing. A run with {@code t} in flight can be reordered so
 * that {@code t}'s deposit comes right after its start, as long as no step in between tests one
 * of {@code t}'s output places non-monotonically: the steps in between see more tokens there, and
 * a transition that only needs tokens is still enabled and does the same. An inhibitor arc, a
 * reset arc and a draining input ({@code all}, {@code atLeast}) are the non-monotone tests. A
 * terminal place ([EXEC-042]) counts as one, since it inhibits every transition.
 *
 * <p>So a transition {@code t} needs the executor's two-step firing exactly when some transition
 * tests one of {@code t}'s output places that way. {@link #split} splits each such {@code t} into
 * {@code t} itself, with every input, read, inhibitor and reset arc, its timing, priority and
 * match spec, whose only output is the fresh place {@code inflight:<t>}, and
 * {@code complete:<t>}, immediate, consuming {@code inflight:<t>} and depositing {@code t}'s
 * output spec. Every other transition stays atomic, so a net without such a transition is not
 * rewritten and verifies, and scripts, exactly as before.
 *
 * <p>Two more readings test a place without an arc, and the verifier adds them to the tested
 * places ({@link SplitDemand}):
 * <ul>
 *   <li>A <b>terminal place</b> stops the net without waiting for an action in flight
 *       ([EXEC-042]): the action is abandoned, its inputs consumed and its outputs never
 *       deposited. Removing tokens is harmless to every quiescence property but one: a
 *       {@code QuiescentCount} with a lower bound, when some terminal does not waive it. For it
 *       the places the count reads and its waiver places are tested too
 *       ({@link #quiescentCountDemand}), so every transition depositing there is split and the
 *       terminal, which inhibits {@code complete:<t>} as it inhibits every transition, models the
 *       abandonment.</li>
 *   <li><b>Conflict priority</b> on Route B ([NU-052]) fires {@code L} only when no conflicting,
 *       higher-priority {@code H} is enabled, a test of {@code H}'s input and read places that
 *       more tokens can fail. Those places are tested too, and every such {@code H} is split as
 *       well: while {@code inflight:<H>} is marked, {@code H} pre-empts nothing, since the Java
 *       and TypeScript executors do not start {@code H} again while its action runs
 *       ({@link #conflictDemand}).</li>
 * </ul>
 *
 * <p>Three cases are refused rather than split: a transition to split that is a &nu;-join or a
 * writer into a coloured place; a {@code Timeout} forward of more than one token; and a name the
 * split would add that the net already uses. Mirrors Rust's {@code in_flight.rs} and
 * TypeScript's {@code in-flight.ts}.
 */
public final class InFlight {

    private InFlight() {}

    /** What {@link #split} did to a net. */
    public sealed interface Outcome {
        /** No transition needs the two-step firing: verify the net as it is. */
        record Atomic() implements Outcome {}

        /**
         * The rewritten net, and the names of the transitions it split, in net order.
         *
         * @param net   the net with each split transition replaced by its start and its
         *              completion step {@code complete:<name>}
         * @param split the names of the split transitions, in net order
         */
        record Split(PetriNet net, List<String> split) implements Outcome {
            public Split {
                split = List.copyOf(split);
            }
        }

        /**
         * The net needs the two-step firing and the split cannot express it; no route may answer.
         *
         * @param reason why the split cannot express the net, naming the transition
         */
        record Refused(String reason) implements Outcome {}
    }

    /** The in-flight place of transition {@code t}. */
    public static String inFlightPlace(String t) {
        return "inflight:" + t;
    }

    /** The completion transition of transition {@code t}. */
    public static String completionTransition(String t) {
        return "complete:" + t;
    }

    /**
     * Every place some transition tests non-monotonically: an inhibitor, a reset, a draining input
     * ({@code all}, {@code atLeast}), and every terminal place ([EXEC-042]).
     */
    public static Set<String> nonMonotonePlaces(PetriNet net) {
        var out = new HashSet<String>();
        net.terminals().forEach(p -> out.add(p.name()));
        for (var t : net.transitions()) {
            t.inhibitors().forEach(a -> out.add(a.place().name()));
            t.resets().forEach(a -> out.add(a.place().name()));
            for (var s : t.inputSpecs()) {
                if (s instanceof Arc.In.All || s instanceof Arc.In.AtLeast) {
                    out.add(s.place().name());
                }
            }
        }
        return out;
    }

    /**
     * Whether {@code t} is a completion step: {@code complete:<x>}, whose one input is
     * {@code one(inflight:<x>)}, with no read or reset arc. It is itself a single deposit, so it is
     * never split, which makes {@link #split} idempotent, also after the terminal rewrite gave it
     * an inhibitor.
     */
    private static boolean isCompletion(Transition t) {
        if (!t.name().startsWith("complete:")) {
            return false;
        }
        var x = t.name().substring("complete:".length());
        return t.inputSpecs().size() == 1
            && t.inputSpecs().getFirst() instanceof Arc.In.One(var place)
            && place.name().equals(inFlightPlace(x))
            && t.reads().isEmpty()
            && t.resets().isEmpty();
    }

    /**
     * The transition whose completion step {@code t} is ({@code x} for {@code complete:x}), or
     * {@code null} when {@code t} is not a completion step of the split.
     */
    static String completedTransition(Transition t) {
        return isCompletion(t) ? t.name().substring("complete:".length()) : null;
    }

    /**
     * The transitions of {@code net} that need the executor's two-step firing, in net order: those
     * with an output place some transition tests non-monotonically. {@code environment} names the
     * transitions that model the environment rather than an action of the net (the arrivals of
     * [VER-006], the environment of an open-net contract, [VER-022]); they stay atomic, and their
     * arcs still count as tests.
     */
    public static List<String> transitions(PetriNet net, Set<String> environment) {
        return transitions(net, environment, SplitDemand.NONE);
    }

    /**
     * {@link #transitions(PetriNet, Set)} with the places and transitions {@code demand} adds: a
     * transition is split when an output is in {@link #nonMonotonePlaces} or in
     * {@code demand.tested()}, or when {@code demand.forced()} names it. Environment steps and
     * completion steps stay atomic.
     */
    public static List<String> transitions(PetriNet net, Set<String> environment, SplitDemand demand) {
        var tested = nonMonotonePlaces(net);
        tested.addAll(demand.tested());
        var out = new ArrayList<String>();
        for (var t : net.transitions()) {
            if (isCompletion(t) || environment.contains(t.name())) {
                continue;
            }
            if (demand.forced().contains(t.name())
                    || t.outputPlaces().stream().anyMatch(p -> tested.contains(p.name()))) {
                out.add(t.name());
            }
        }
        return out;
    }

    /**
     * What a verification tests beyond the arcs of its net ({@link #nonMonotonePlaces}), and so
     * adds to the split (class docs).
     *
     * @param tested places tested non-monotonically: every transition depositing into one is split
     * @param forced transitions split whatever their outputs
     */
    public record SplitDemand(Set<String> tested, Set<String> forced) {
        /** No demand: the split of the net's own arcs. */
        public static final SplitDemand NONE = new SplitDemand(Set.of(), Set.of());

        public SplitDemand {
            tested = Set.copyOf(tested);
            forced = Set.copyOf(forced);
        }

        /** Both demands at once. */
        public SplitDemand union(SplitDemand other) {
            var t = new HashSet<>(tested);
            t.addAll(other.tested);
            var f = new HashSet<>(forced);
            f.addAll(other.forced);
            return new SplitDemand(t, f);
        }
    }

    /**
     * The places a terminal stop can leave short ([EXEC-042], [VER-004]): the places a
     * {@code QuiescentCount} counts and its waiver places, when its lower bound {@code min} is
     * above zero and {@code net} has a terminal place the waivers do not name. Every other
     * quiescence property holds of a marking whenever it holds of one with more tokens at a
     * terminal rest, which every terminal excuses, so an abandoned action cannot break it. Empty
     * otherwise.
     *
     * @param net      the net
     * @param places   the names of the places the count reads
     * @param min      its lower bound
     * @param waivedBy the names of its waiver places
     */
    public static SplitDemand quiescentCountDemand(
            PetriNet net, List<String> places, int min, List<String> waivedBy) {
        boolean unwaivedTerminal = net.terminals().stream().anyMatch(p -> !waivedBy.contains(p.name()));
        if (min == 0 || !unwaivedTerminal) {
            return SplitDemand.NONE;
        }
        var tested = new HashSet<>(places);
        tested.addAll(waivedBy);
        return new SplitDemand(tested, Set.of());
    }

    /**
     * The transitions of {@code net} that can pre-empt another under conflict priority
     * ([NU-052]): each {@code H} with a strictly higher priority than some other transition that
     * consumes one of {@code H}'s input places. In net order.
     */
    public static List<String> conflictPruners(PetriNet net) {
        var out = new ArrayList<String>();
        for (var h : net.transitions()) {
            var inputs = new HashSet<String>();
            h.inputPlaces().forEach(p -> inputs.add(p.name()));
            boolean prunes = net.transitions().stream().anyMatch(l ->
                !l.name().equals(h.name())
                    && h.priority() > l.priority()
                    && l.inputPlaces().stream().anyMatch(p -> inputs.contains(p.name())));
            if (prunes) {
                out.add(h.name());
            }
        }
        return out;
    }

    /**
     * What conflict priority ([NU-052]) adds to the split: every pruner of
     * {@link #conflictPruners} is forced, and its input and read places are tested, since more
     * tokens there can enable it and so disable the transition it pre-empts.
     */
    public static SplitDemand conflictDemand(PetriNet net) {
        var pruners = new HashSet<>(conflictPruners(net));
        var tested = new HashSet<String>();
        var forced = new HashSet<String>();
        for (var h : net.transitions()) {
            if (!pruners.contains(h.name())) {
                continue;
            }
            h.inputPlaces().forEach(p -> tested.add(p.name()));
            h.reads().forEach(r -> tested.add(r.place().name()));
            forced.add(h.name());
        }
        return new SplitDemand(tested, forced);
    }

    /**
     * Splits every transition of {@link #transitions} into a start and a completion (class docs).
     * {@code coloured} names the places whose tokens carry a &nu; name beyond the match specs' keys
     * and relay targets (the declared carrier places); a transition to split that is a &nu;-join
     * or writes a coloured place is refused. A mint ([NU-010]) mints only into a coloured place, so
     * that covers it too.
     */
    public static Outcome split(PetriNet net, Set<String> coloured, Set<String> environment) {
        return split(net, coloured, environment, SplitDemand.NONE);
    }

    /** {@link #split(PetriNet, Set, Set)} of the transitions {@link #transitions(PetriNet, Set, SplitDemand)} names. */
    public static Outcome split(PetriNet net, Set<String> coloured, Set<String> environment, SplitDemand demand) {
        var split = transitions(net, environment, demand);
        if (split.isEmpty()) {
            return new Outcome.Atomic();
        }
        var unsplittable = firstUnsplittable(net, coloured, split);
        if (unsplittable != null) {
            var t = unsplittable.transition();
            var head = transitions(net, environment).contains(t) ? refusalHead(t) : demandRefusalHead(t);
            return new Outcome.Refused(head + " " + unsplittable.cause());
        }
        var toSplit = new HashSet<>(split);
        var builder = PetriNet.builder(net.name()).places(net.places().toArray(new Place<?>[0]));
        for (var t : net.transitions()) {
            if (toSplit.contains(t.name())) {
                var place = Place.of(inFlightPlace(t.name()), Object.class);
                builder.transition(start(t, place));
                builder.transition(completion(t, place));
            } else {
                builder.transition(t);
            }
        }
        net.terminals().forEach(builder::terminal);
        return new Outcome.Split(builder.build(), split);
    }

    /**
     * A transition the split cannot express, and why.
     *
     * @param transition the transition's name
     * @param cause      the clause that completes the refusal head
     */
    public record Unsplittable(String transition, String cause) {}

    /**
     * The first transition of {@code split}, in net order, that the split cannot express, with the
     * cause, or {@code null}. {@code coloured} is as for {@link #split(PetriNet, Set, Set)}.
     */
    public static Unsplittable firstUnsplittable(PetriNet net, Set<String> coloured, List<String> split) {
        var allColoured = new HashSet<>(coloured);
        for (var t : net.transitions()) {
            if (t.matchSpec() == null) {
                continue;
            }
            t.matchSpec().keys().forEach(k -> allColoured.add(k.place().name()));
            t.matchSpec().relays().forEach(k -> allColoured.add(k.place().name()));
        }
        var names = new HashSet<String>();
        net.places().forEach(p -> names.add(p.name()));
        net.transitions().forEach(t -> names.add(t.name()));
        var toSplit = new HashSet<>(split);
        for (var t : net.transitions()) {
            if (!toSplit.contains(t.name())) {
                continue;
            }
            var cause = refusalCause(t, allColoured, names);
            if (cause != null) {
                return new Unsplittable(t.name(), cause);
            }
        }
        return null;
    }

    /** The opening of the refusal of transition {@code name}. */
    private static String refusalHead(String name) {
        return "transition '" + name + "' must be verified as two steps, since its action runs between "
            + "consuming and depositing and another transition tests one of its outputs with an "
            + "inhibitor, reset or drain (VER-004), but";
    }

    /**
     * The opening of the refusal of transition {@code name} when only a {@link SplitDemand} splits
     * it: a {@code QuiescentCount} lower bound over a place it deposits into, on a net with a
     * terminal place ({@link #quiescentCountDemand}).
     */
    private static String demandRefusalHead(String name) {
        return "transition '" + name + "' must be verified as two steps, since a terminal place can stop "
            + "the net while its action runs and the property's lower bound counts a place it deposits "
            + "into (VER-004, EXEC-042), but";
    }

    /** Why {@code t} cannot be split, or {@code null}: the clause that completes the refusal head. */
    private static String refusalCause(Transition t, Set<String> coloured, Set<String> names) {
        var name = t.name();
        if (t.matchSpec() != null) {
            return "it is a ν-join, whose outputs carry the matched name (NU-020, NU-054)";
        }
        var outs = new ArrayList<String>();
        t.outputPlaces().forEach(p -> outs.add(p.name()));
        outs.sort(CodePointOrder.COMPARATOR);
        for (var p : outs) {
            if (coloured.contains(p)) {
                return "it writes the coloured place '" + p + "', whose tokens carry a ν name";
            }
        }
        var forward = t.outputSpec() == null ? null : multiTokenForward(t.outputSpec(), t, false);
        if (forward != null) {
            return "its timeout forwards input '" + forward.from().name() + "' to '" + forward.to().name()
                + "', one token per token consumed (IO-014), a count its completion step cannot see";
        }
        for (var added : List.of(inFlightPlace(name), completionTransition(name))) {
            if (names.contains(added)) {
                return "the net already uses the name '" + added + "' the split would add";
            }
        }
        return null;
    }

    /** The first {@code forwardInput} under a {@code timeout} whose source input is not {@code one}. */
    private static Arc.Out.ForwardInput multiTokenForward(Arc.Out out, Transition t, boolean underTimeout) {
        return switch (out) {
            case Arc.Out.Place _ -> null;
            case Arc.Out.ForwardInput f -> {
                var spec = t.inputSpecs().stream().filter(s -> s.place().name().equals(f.from().name())).findFirst();
                var single = spec.isEmpty() || spec.get() instanceof Arc.In.One;
                yield underTimeout && !single ? f : null;
            }
            case Arc.Out.Timeout(var _, var child) -> multiTokenForward(child, t, true);
            case Arc.Out.And(var children) -> firstForward(children, t, underTimeout);
            case Arc.Out.Xor(var children) -> firstForward(children, t, underTimeout);
        };
    }

    private static Arc.Out.ForwardInput firstForward(List<Arc.Out> children, Transition t, boolean underTimeout) {
        for (var c : children) {
            var found = multiTokenForward(c, t, underTimeout);
            if (found != null) {
                return found;
            }
        }
        return null;
    }

    /** {@code t}'s output spec for its completion step: a {@code forwardInput(from, to)} leaf becomes {@code to}. */
    private static Arc.Out completionOutput(Arc.Out out) {
        return switch (out) {
            case Arc.Out.Place p -> p;
            case Arc.Out.ForwardInput f -> new Arc.Out.Place(f.to());
            case Arc.Out.And(var children) -> new Arc.Out.And(children.stream().map(InFlight::completionOutput).toList());
            case Arc.Out.Xor(var children) -> new Arc.Out.Xor(children.stream().map(InFlight::completionOutput).toList());
            case Arc.Out.Timeout(var after, var child) -> new Arc.Out.Timeout(after, completionOutput(child));
        };
    }

    /** The start of {@code t}: every arc of it, with {@code place} as the only output. */
    private static Transition start(Transition t, Place<?> place) {
        var b = Transition.builder(t.name())
            .timing(t.timing())
            .priority(t.priority())
            .action(t.action())
            .placeAlias(t.placeAlias())
            .match(t.matchSpec());
        if (!t.inputSpecs().isEmpty()) {
            b.inputs(t.inputSpecs().toArray(new Arc.In[0]));
        }
        t.inhibitors().forEach(b::inhibitorArc);
        t.reads().forEach(b::readArc);
        t.resets().forEach(b::resetArc);
        b.outputs(new Arc.Out.Place(place));
        return b.build();
    }

    /** The completion step of {@code t}: immediate, from {@code place}, depositing {@code t}'s output spec. */
    private static Transition completion(Transition t, Place<?> place) {
        var b = Transition.builder(completionTransition(t.name()))
            .timing(Timing.immediate())
            .priority(t.priority())
            .action(t.action())
            .inputs(new Arc.In.One(place));
        if (t.outputSpec() != null) {
            b.outputs(completionOutput(t.outputSpec()));
        }
        return b.build();
    }

    /** The report line naming the split transitions. */
    public static String splitNote(List<String> split) {
        return "In-flight actions (VER-004): " + String.join(", ", split) + (split.size() == 1 ? " is" : " are")
            + " verified in two steps, a start that consumes and a completion step (complete:<name>) that "
            + "deposits, because another transition tests an output with an inhibitor, reset or drain and "
            + "the executor fires other transitions while an action is in flight.";
    }

    /** The report line of a verdict reached under {@code assumeAtomicFiring} on a net the split would change. */
    public static String atomicAssumptionNote(List<String> split) {
        return "ASSUMPTION: every firing is atomic (the assume-atomic-firing option). Another transition "
            + "tests an output of " + String.join(", ", split) + " with an inhibitor, reset or drain, and the "
            + "executor fires other transitions while an action is in flight (VER-004); this verdict holds "
            + "only for runs in which no such test happens while one of those actions runs.";
    }

    /**
     * Why a verification splits beyond the arcs of its net ({@link SplitDemand}).
     *
     * @param tested   some transition tests an output non-monotonically ({@link #nonMonotonePlaces})
     * @param terminal {@link #quiescentCountDemand} added a transition
     * @param conflict conflict priority is applied with pruners ({@link #conflictDemand})
     */
    public record SplitReasons(boolean tested, boolean terminal, boolean conflict) {
        /** Whether the plain {@link #splitNote} says it all. */
        public boolean plain() {
            return !terminal && !conflict;
        }

        private String clauses() {
            var out = new ArrayList<String>();
            if (tested) {
                out.add("another transition tests an output with an inhibitor, reset or drain");
            }
            if (terminal) {
                out.add("a terminal place stops the net without waiting for an action in flight (EXEC-042) "
                    + "and the property's lower bound counts a place one of them deposits into");
            }
            if (conflict) {
                out.add("conflict priority (NU-052) reads whether a pruning transition is enabled, so a "
                    + "transition pre-empts no other while its own action is in flight");
            }
            return String.join("; ", out);
        }
    }

    /**
     * The report line naming the split transitions when the verification added some
     * ({@link SplitDemand}); {@link #splitNote} when it added none.
     */
    public static String splitNoteFor(List<String> split, SplitReasons reasons) {
        if (reasons.plain()) {
            return splitNote(split);
        }
        return "In-flight actions (VER-004): " + String.join(", ", split) + (split.size() == 1 ? " is" : " are")
            + " verified in two steps, a start that consumes and a completion step (complete:<name>) that "
            + "deposits, because the executor fires other transitions while an action is in flight and "
            + reasons.clauses() + ".";
    }

    /**
     * The report line of a verdict reached under {@code assumeAtomicFiring} on a net with a
     * transition the split would have applied to, when the verification added some
     * ({@link SplitDemand}); {@link #atomicAssumptionNote} when it added none.
     */
    public static String atomicAssumptionNoteFor(List<String> split, SplitReasons reasons) {
        if (reasons.plain()) {
            return atomicAssumptionNote(split);
        }
        return "ASSUMPTION: every firing is atomic (the assume-atomic-firing option). The executor fires "
            + "other transitions while an action of " + String.join(", ", split) + " is in flight, and "
            + reasons.clauses() + " (VER-004); this verdict holds only for runs in which none of those "
            + "actions is in flight when that matters.";
    }

    /**
     * The report line of a verdict reached with conflict priority ([NU-052]) turned off, because
     * {@code transition} has to be split for the pruning to hold and cannot be ({@code cause}, as
     * {@link #firstUnsplittable} gives it).
     */
    public static String conflictOffNote(String transition, String cause) {
        return "Conflict priority (NU-052) is off: it holds only while no pruning transition, and no "
            + "transition depositing into the input or read places of one, has an action in flight, "
            + "which the verifier models by splitting them (VER-004), and transition '" + transition
            + "' cannot be split: " + cause + ". Every enabled transition is explored.";
    }

    /**
     * The transitions a counterexample starts while an earlier firing of each is still in flight
     * ([CONC-002]): step {@code i} fires {@code transitions[i]} from {@code trace[i]}, and names a
     * start whose place {@code inflight:<name>} is marked there. First occurrence order, each
     * once. Empty when the trace is not aligned ({@code trace.size() != transitions.size() + 1}).
     */
    public static List<String> restartedTransitions(List<MarkingState> trace, List<String> transitions) {
        if (trace.size() != transitions.size() + 1) {
            return List.of();
        }
        var out = new ArrayList<String>();
        for (int i = 0; i < transitions.size(); i++) {
            var t = transitions.get(i);
            if (count(trace.get(i), inFlightPlace(t)) > 0 && !out.contains(t)) {
                out.add(t);
            }
        }
        return out;
    }

    /** The tokens {@code m} holds on the place named {@code name}, whatever its token type. */
    private static int count(MarkingState m, String name) {
        int n = 0;
        for (var p : m.placesWithTokens()) {
            if (p.name().equals(name)) {
                n += m.tokens(p);
            }
        }
        return n;
    }

    /**
     * The report line of a counterexample that restarts a transition in flight ([CONC-002],
     * {@link #restartedTransitions}): the split lets a start fire again while its completion is
     * pending, as the Rust executor does, and the Java and TypeScript executors never do.
     * {@code null} when it restarts none.
     */
    public static String restartNote(List<MarkingState> trace, List<String> transitions) {
        var restarted = restartedTransitions(trace, transitions);
        if (restarted.isEmpty()) {
            return null;
        }
        var names = new ArrayList<String>();
        var places = new ArrayList<String>();
        for (var t : restarted) {
            names.add("'" + t + "'");
            places.add(inFlightPlace(t));
        }
        boolean one = restarted.size() == 1;
        return "NOTE (CONC-002): the counterexample starts " + String.join(", ", names) + " again while "
            + (one ? "its" : "their") + " earlier " + (one ? "firing" : "firings") + " " + (one ? "is" : "are")
            + " still in flight (" + String.join(", ", places) + " marked). The Rust executor starts a "
            + "transition again while its action runs; the Java and TypeScript executors never do, so on "
            + "them this counterexample may be a false alarm.";
    }

    /**
     * The name of the transition of the caller's net that {@code name} stands for: {@code t} for
     * the completion step {@code complete:<t>} of a split net, {@code name} itself otherwise.
     */
    public static String sourceTransition(PetriNet net, String name) {
        for (var t : net.transitions()) {
            if (t.name().equals(name)) {
                var completed = completedTransition(t);
                return completed != null ? completed : name;
            }
        }
        return name;
    }
}
