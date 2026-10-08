package org.libpetri.smt;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.NameFragment;
import org.libpetri.analysis.NameStateClassGraph;
import org.libpetri.analysis.PrioritySemantics;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.internal.CodePointOrder;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

/**
 * &nu;-net exact verification via the name-aware state-class-graph name-partition
 * quotient (NU-050, Route B). Bridges {@link NameStateClassGraph} to
 * {@link SmtVerificationResult}.
 *
 * <p>{@link #verify} returns {@code null} when the net is outside the supported
 * mint&rarr;matched-join fragment (the caller falls back to the SMT / Route A
 * path); otherwise an <i>exact</i> verdict when the symbolic graph closes. When it
 * truncates (the live correlation pool is unbounded — undecidability surfaces as
 * truncation, never an unsound verdict) a violation in the explored prefix is still a
 * {@code Violated}; otherwise the verdict is {@code Unknown}. A reachability-safety property
 * stops the build at its first violating class ([VER-012]).
 *
 * <p>A name-alignment property ([NU-055]) is classified on a net without a matched transition
 * too, and an uncoloured property place or a coloured place the initial marking marks is an
 * {@code Unknown} outcome naming the place, not {@code null}: no other route decides it.
 */
final class NuScgVerifier {

    static final String NOTE_EXACT =
        "\nNote: ν-join correlation decided exactly via the state-class-graph name-partition "
        + "quotient — the symbolic graph closed, so the verdict is sound AND complete (no spurious "
        + "different-name counterexample; quiescence is name-aware), beyond the bounded-budget "
        + "fragment (NU-050, Route B).\n";

    /**
     * {@link #NOTE_EXACT} for a graph built on a net in which a transition keeps its latest bound
     * (the on-time executor of {@code assumeNoReaping}, or a direct call on a timed net). The
     * strong-semantics graph fires every transition by its latest bound and reads each firing as
     * one instant step, so its verdict is exact for that executor alone ([VER-004], [TIME-013]).
     */
    static final String NOTE_ON_TIME =
        "\nNote: ν-join correlation decided via the state-class-graph name-partition quotient: the "
        + "symbolic graph closed, and a transition keeps its latest bound in it, so the verdict is exact "
        + "only for an on-time executor whose actions take no time (quiescence is name-aware; NU-050, "
        + "Route B).\n";

    /** The note of a closed graph built on {@code net} ({@link #NOTE_EXACT} or {@link #NOTE_ON_TIME}). */
    private static String closedNote(PetriNet net) {
        return net.transitions().stream().anyMatch(t -> Reaping.hasLatestBound(t.timing())) ? NOTE_ON_TIME : NOTE_EXACT;
    }

    record Outcome(
        SmtVerificationResult.Verdict verdict,
        List<MarkingState> trace,
        List<String> transitions,
        String note,
        int classCount
    ) {}

    private NuScgVerifier() {}

    static Outcome verify(
            PetriNet net,
            MarkingState initial,
            SmtProperty property,
            Set<Place<?>> sinkPlaces,
            Set<EnvironmentPlace<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode,
            int maxClasses,
            FragmentMode fragmentMode,
            Set<String> carrierPlaces,
            Set<String> mintTransitions,
            PrioritySemantics prioritySemantics,
            List<RestSet.ConditionalSinks> conditionalSinks
    ) {
        return verify(net, initial, property, sinkPlaces, environmentPlaces, environmentMode, maxClasses,
            fragmentMode, carrierPlaces, mintTransitions, prioritySemantics, conditionalSinks, true);
    }

    /**
     * {@link #verify} for a late executor ([VER-002], [VER-004], [TIME-006], [TIME-013]):
     * <ul>
     *   <li>the graph is built on {@link Reaping#relaxLate}'s net, in which no transition named in
     *       {@code late} has a latest bound, for <em>every</em> property: a late executor reaps a
     *       deadline / window transition or fires an exact one after its bound, and fires the others
     *       meanwhile, and a strong-semantics {@code Proven} of any property could miss those runs
     *       (Lean: {@code TimedScg/Retrodict.reaping_escapes_timed_graph});</li>
     *   <li>an expanded class rests when every firing out of it is of a transition in
     *       {@code reapable}; only a quiescence property reads it;</li>
     *   <li>{@link PrioritySemantics#CONFLICT} falls back to {@link PrioritySemantics#NONE} when a
     *       transition in {@code reapable} exists: a reapable transition that pre-empts a
     *       conflicting one on time is reaped by a late executor, which then fires the other.</li>
     * </ul>
     * Both empty (the on-time executor of {@code assumeNoReaping}, or a net timed only with
     * {@code immediate} and {@code delayed}), it is {@link #verify} exactly.
     */
    static Outcome verifyReaping(
            PetriNet net,
            MarkingState initial,
            SmtProperty property,
            Set<Place<?>> sinkPlaces,
            Set<EnvironmentPlace<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode,
            int maxClasses,
            FragmentMode fragmentMode,
            Set<String> carrierPlaces,
            Set<String> mintTransitions,
            PrioritySemantics prioritySemantics,
            List<RestSet.ConditionalSinks> conditionalSinks,
            Set<String> reapable,
            Set<String> late
    ) {
        var reapableInNet = new LinkedHashSet<String>();
        var lifted = new LinkedHashSet<String>();
        for (var t : net.transitions()) {
            if (reapable.contains(t.name())) {
                reapableInNet.add(t.name());
            }
            if (late.contains(t.name()) && Reaping.hasLatestBound(t.timing())) {
                lifted.add(t.name());
            }
        }
        if (reapableInNet.isEmpty() && lifted.isEmpty()) {
            return verify(net, initial, property, sinkPlaces, environmentPlaces, environmentMode, maxClasses,
                fragmentMode, carrierPlaces, mintTransitions, prioritySemantics, conditionalSinks);
        }
        boolean pruningOff = !reapableInNet.isEmpty() && prioritySemantics == PrioritySemantics.CONFLICT;
        var semantics = reapableInNet.isEmpty() ? prioritySemantics : PrioritySemantics.NONE;
        // The marking properties read no rest ([VER-004]).
        Set<String> restsOn = GraphDecision.safetyViolation(property) == null ? reapableInNet : Set.of();
        var outcome = verify(Reaping.relaxLate(net, lifted), initial, property, sinkPlaces, environmentPlaces,
            environmentMode, maxClasses, fragmentMode, carrierPlaces, mintTransitions, semantics, conditionalSinks, true, restsOn);
        if (outcome == null || outcome.note().isEmpty() || lifted.isEmpty()) {
            return outcome;
        }
        var names = new TreeSet<String>(CodePointOrder.COMPARATOR);
        names.addAll(lifted);
        return new Outcome(outcome.verdict(), outcome.trace(), outcome.transitions(),
            outcome.note() + "Note: the latest bound of " + String.join(", ", names) + " was lifted"
                + (pruningOff ? " and priority pruning is off" : "")
                + ", so the graph holds the runs of a late executor, which reaps a deadline or window "
                + "transition and fires an exact one after its bound (TIME-006, TIME-013).\n",
            outcome.classCount());
    }

    /**
     * {@code earlyStop = false} builds the graph in full (to the cap) before deciding: the
     * reference the early-stop witness is tested against.
     */
    static Outcome verify(
            PetriNet net,
            MarkingState initial,
            SmtProperty property,
            Set<Place<?>> sinkPlaces,
            Set<EnvironmentPlace<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode,
            int maxClasses,
            FragmentMode fragmentMode,
            Set<String> carrierPlaces,
            Set<String> mintTransitions,
            PrioritySemantics prioritySemantics,
            List<RestSet.ConditionalSinks> conditionalSinks,
            boolean earlyStop
    ) {
        return verify(net, initial, property, sinkPlaces, environmentPlaces, environmentMode, maxClasses,
            fragmentMode, carrierPlaces, mintTransitions, prioritySemantics, conditionalSinks, earlyStop, Set.of());
    }

    private static Outcome verify(
            PetriNet net,
            MarkingState initial,
            SmtProperty property,
            Set<Place<?>> sinkPlaces,
            Set<EnvironmentPlace<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode,
            int maxClasses,
            FragmentMode fragmentMode,
            Set<String> carrierPlaces,
            Set<String> mintTransitions,
            PrioritySemantics prioritySemantics,
            List<RestSet.ConditionalSinks> conditionalSinks,
            boolean earlyStop,
            Set<String> reapable
    ) {
        boolean nameAlignment = NameAlignment.isNameAlignment(property);
        var fragment = NameFragment.classify(net, fragmentMode, carrierPlaces, mintTransitions, nameAlignment);
        if (fragment == null) {
            return null;
        }
        // NU-055: nothing but this graph decides a name-alignment property, so where it cannot, the
        // verdict is Unknown naming the place rather than a decline the caller would route elsewhere.
        if (nameAlignment) {
            String refusal = nameAlignmentRefusal(property, fragment, fragmentMode, initial);
            if (refusal != null) {
                return new Outcome(
                    new SmtVerificationResult.Verdict.Unknown(refusal), List.of(), List.of(), "", 0);
            }
        }
        if (!startsEmpty(fragment, initial)) {
            return null;
        }

        // A reachability-safety property stops the build at its first violating class ([VER-012]):
        // same predicate, same witness, same shortest path as deciding over the finished graph.
        // Quiescence properties need expanded classes, so they build in full.
        var violates = earlyStop ? GraphDecision.safetyViolation(property) : null;
        var scg = NameStateClassGraph.buildStoppingAt(
                net, initial, fragment, maxClasses, environmentPlaces, environmentMode, prioritySemantics,
                violates == null ? null : (g, idx) -> violates.violates(view(g, Set.of()), idx));

        boolean complete = scg.isComplete();
        // On truncation the same predicate runs over the explored prefix ([VER-012] AC3,
        // [VER-017] "Verdicts from a truncated graph"): every stored class is a real reachable
        // class, and only an expanded class counts as quiescent. A hit is a real firing
        // sequence; a prefix never proves anything.
        int violating = decide(scg, property, sinkPlaces, conditionalSinks, reapable);
        if (violating >= 0) {
            // The trace below is an explicit path of the name-aware state-class graph —
            // a genuine run of Route B's semantics by construction. The flat abstract
            // replay does not apply to these state shapes, so the result reports
            // counterexampleConfirmed = null rather than false.
            var path = counterexamplePath(scg, violating);
            return new Outcome(new SmtVerificationResult.Verdict.Violated(), path.markings(), path.transitions(),
                scg.stoppedAt() >= 0 ? earlyStopNote(scg.classCount())
                    : complete ? closedNote(net) : GraphDecision.prefixNote("ν name-aware state-class graph", maxClasses),
                scg.classCount());
        }
        if (!complete) {
            String reason =
                "ν name-aware state-class graph truncated at " + maxClasses + " classes — the live "
                + "correlation pool is not structurally bounded; reachability over unbounded fresh "
                + "names is undecidable (NU-050, Route B). Declare a budget place to bound the live "
                + "pool, or raise nuMaxClasses.";
            return new Outcome(
                new SmtVerificationResult.Verdict.Unknown(reason), List.of(), List.of(), "", scg.classCount());
        }
        return new Outcome(
            new SmtVerificationResult.Verdict.Proven("ν name-partition SCG (NU-050, Route B)", null),
            List.of(), List.of(), closedNote(net), scg.classCount());
    }

    /**
     * The report note of a violation found by stopping the build at the first violating class
     * ([VER-012]). The graph was never finished, so it says nothing about closure.
     */
    static String earlyStopNote(int classCount) {
        return "\nNote: Route B stopped at the first violating class after " + classCount + " classes (VER-012). "
            + "Every explored class is reachable and classes are discovered breadth-first, so the "
            + "counterexample is a real firing sequence and a shortest one to any violation.\n";
    }

    /**
     * Whether no coloured place of {@code fragment} holds a token in {@code initial}: Route B
     * declines a net that fails this (no initial colour assignment is modelled).
     */
    static boolean startsEmpty(NameFragment fragment, MarkingState initial) {
        for (var p : initial.placesWithTokens()) {
            if (fragment.isColoured(p.name())) {
                return false;
            }
        }
        return true;
    }

    /**
     * Why Route B cannot decide the name-alignment {@code property} on {@code fragment} (NU-055),
     * or {@code null}: a property place that is not coloured, whose predicate would hold vacuously
     * (AC2, AC3), or a coloured place the initial marking marks (AC6), since the graph models no
     * initial names. Checked in that order, the last two steps of the NU-055 refusal order: the
     * first uncoloured place of {@code S} in the order of {@code S}, then the first marked coloured
     * place in code-point order.
     */
    private static String nameAlignmentRefusal(
            SmtProperty property, NameFragment fragment, FragmentMode fragmentMode, MarkingState initial
    ) {
        for (var place : SmtVerifier.propertyPlaces(property)) {
            if (!fragment.isColoured(place.name())) {
                String underBase = fragmentMode == FragmentMode.BASE
                    ? "; under BASE only the match keys are coloured, carrier places and relay targets only "
                        + "under the EXTENDED fragment (fragmentMode(EXTENDED), NU-051, NU-054)"
                    : "";
                return "place '" + place.name() + "' is not a coloured place of the ν fragment (a match key, "
                    + "declared carrier or relay target), so it carries no name and name alignment on it would "
                    + "hold vacuously (NU-055)" + underBase;
            }
        }
        return initial.placesWithTokens().stream()
            .map(Place::name)
            .filter(fragment::isColoured)
            .min(CodePointOrder.COMPARATOR)
            .map(marked -> "coloured place '" + marked + "' holds a token in the initial marking; the "
                + "name-partition graph models no initial names, so the coloured places must start empty (NU-055)")
            .orElse(null);
    }

    /**
     * Returns a witnessing class index for a violation, or -1 if the property holds.
     *
     * <p>The predicate itself lives in {@link GraphDecision#decideOverClasses}, shared with
     * the plain enumeration route of [VER-017] so the two cannot drift ([VER-002] AC7).
     */
    private static int decide(
            NameStateClassGraph scg, SmtProperty property, Set<Place<?>> sinkPlaces,
            List<RestSet.ConditionalSinks> conditionalSinks, Set<String> reapable
    ) {
        return GraphDecision.decideOverClasses(view(scg, reapable), property, sinkPlaces, conditionalSinks);
    }

    /** {@code scg} as {@link GraphDecision} reads it, its name layer included ([NU-055]). */
    private static GraphDecision.NamedClassView view(NameStateClassGraph scg, Set<String> reapable) {
        return new GraphDecision.NamedClassView() {
            @Override
            public int count() {
                return scg.classCount();
            }

            @Override
            public MarkingState markingOf(int i) {
                return scg.markingOf(i);
            }

            @Override
            public boolean isQuiescent(int i) {
                // A frontier class of a truncated graph was never expanded: no successors
                // recorded, but not dead. An expanded class rests when nothing fires out of
                // it, or only reapable transitions do ([VER-002] reap-quiescence, [TIME-013]).
                return i < scg.expandedCount() && reapable.containsAll(scg.successorLabelsOf(i));
            }

            @Override
            public boolean namesAligned(int i, List<String> places) {
                return scg.namesAligned(i, places);
            }
        };
    }

    private record Path(List<MarkingState> markings, List<String> transitions) {}

    /**
     * Shortest firing sequence from the initial class (0) to {@code target}: breadth-first over
     * each class's labelled successor list, {@code O(V + E)}. (Scanning the whole edge list for
     * every dequeued class made this {@code O(V·E)}.)
     */
    private static Path counterexamplePath(NameStateClassGraph scg, int target) {
        int n = scg.classCount();
        int[] parent = new int[n];
        String[] via = new String[n];
        boolean[] visited = new boolean[n];
        Arrays.fill(parent, -1);
        visited[0] = true;
        var queue = new ArrayDeque<Integer>();
        queue.add(0);
        while (!queue.isEmpty()) {
            int u = queue.poll();
            if (u == target) break;
            var succ = scg.successorsOf(u);
            var labels = scg.successorLabelsOf(u);
            for (int k = 0; k < succ.size(); k++) {
                int v = succ.get(k);
                if (!visited[v]) {
                    visited[v] = true;
                    parent[v] = u;
                    via[v] = labels.get(k);
                    queue.add(v);
                }
            }
        }
        var chain = new ArrayList<Integer>();
        for (int cur = target; cur != -1; cur = parent[cur]) {
            chain.add(cur);
        }
        Collections.reverse(chain);
        var markings = new ArrayList<MarkingState>();
        var transitions = new ArrayList<String>();
        for (int k = 0; k < chain.size(); k++) {
            markings.add(scg.markingOf(chain.get(k)));
            if (k > 0) {
                transitions.add(via[chain.get(k)]);
            }
        }
        return new Path(markings, transitions);
    }
}
