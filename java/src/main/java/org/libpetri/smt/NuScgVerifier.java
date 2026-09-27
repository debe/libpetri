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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Set;

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
 */
final class NuScgVerifier {

    static final String NOTE_EXACT =
        "\nNote: ν-join correlation decided exactly via the state-class-graph name-partition "
        + "quotient — the symbolic graph closed, so the verdict is sound AND complete (no spurious "
        + "different-name counterexample; quiescence is name-aware), beyond the bounded-budget "
        + "fragment (NU-050, Route B).\n";

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
            PrioritySemantics prioritySemantics,
            List<RestSet.ConditionalSinks> conditionalSinks
    ) {
        return verify(net, initial, property, sinkPlaces, environmentPlaces, environmentMode, maxClasses,
            fragmentMode, carrierPlaces, prioritySemantics, conditionalSinks, true);
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
            PrioritySemantics prioritySemantics,
            List<RestSet.ConditionalSinks> conditionalSinks,
            boolean earlyStop
    ) {
        var fragment = supportedFragment(net, initial, fragmentMode, carrierPlaces);
        if (fragment == null) {
            return null;
        }

        // A reachability-safety property stops the build at its first violating class ([VER-012]):
        // same predicate, same witness, same shortest path as deciding over the finished graph.
        // Quiescence properties need expanded classes, so they build in full.
        var scg = NameStateClassGraph.build(
                net, initial, fragment, maxClasses, environmentPlaces, environmentMode, prioritySemantics,
                earlyStop ? GraphDecision.safetyViolation(property) : null);

        boolean complete = scg.isComplete();
        // On truncation the same predicate runs over the explored prefix ([VER-012] AC3,
        // [VER-017] "Verdicts from a truncated graph"): every stored class is a real reachable
        // class, and only an expanded class counts as quiescent. A hit is a real firing
        // sequence; a prefix never proves anything.
        int violating = decide(scg, property, sinkPlaces, conditionalSinks);
        if (violating >= 0) {
            // The trace below is an explicit path of the name-aware state-class graph —
            // a genuine run of Route B's semantics by construction. The flat abstract
            // replay does not apply to these state shapes, so the result reports
            // counterexampleConfirmed = null rather than false.
            var path = counterexamplePath(scg, violating);
            return new Outcome(new SmtVerificationResult.Verdict.Violated(), path.markings(), path.transitions(),
                scg.stoppedAt() >= 0 ? earlyStopNote(scg.classCount())
                    : complete ? NOTE_EXACT : GraphDecision.prefixNote("ν name-aware state-class graph", maxClasses),
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
            List.of(), List.of(), NOTE_EXACT, scg.classCount());
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
     * The fragment {@link #verify} runs on, or {@code null} when it would decline: the net is
     * outside the mint&rarr;matched-join fragment, or a coloured place starts marked (no
     * initial colour assignment is modelled).
     */
    static NameFragment supportedFragment(
            PetriNet net, MarkingState initial, FragmentMode fragmentMode, Set<String> carrierPlaces
    ) {
        var fragment = NameFragment.classify(net, fragmentMode, carrierPlaces);
        if (fragment == null) {
            return null;
        }
        for (var p : initial.placesWithTokens()) {
            if (fragment.isColoured(p.name())) {
                return null;
            }
        }
        return fragment;
    }

    /**
     * Returns a witnessing class index for a violation, or -1 if the property holds.
     *
     * <p>The predicate itself lives in {@link GraphDecision#decideOverClasses}, shared with
     * the plain enumeration route of [VER-017] so the two cannot drift ([VER-002] AC7).
     */
    private static int decide(
            NameStateClassGraph scg, SmtProperty property, Set<Place<?>> sinkPlaces,
            List<RestSet.ConditionalSinks> conditionalSinks
    ) {
        return GraphDecision.decideOverClasses(
            new GraphDecision.ClassView() {
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
                    // recorded, but not dead.
                    return i < scg.expandedCount() && scg.successorsOf(i).isEmpty();
                }
            },
            property, sinkPlaces, conditionalSinks);
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
