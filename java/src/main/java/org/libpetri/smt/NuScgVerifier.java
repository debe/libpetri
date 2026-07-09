package org.libpetri.smt;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.NameFragment;
import org.libpetri.analysis.NameStateClassGraph;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.function.IntPredicate;

/**
 * &nu;-net exact verification via the name-aware state-class-graph name-partition
 * quotient (NU-050, Route B). Bridges {@link NameStateClassGraph} to
 * {@link SmtVerificationResult}.
 *
 * <p>{@link #verify} returns {@code null} when the net is outside the supported
 * mint&rarr;matched-join fragment (the caller falls back to the SMT / Route A
 * path); otherwise an <i>exact</i> verdict when the symbolic graph closes, or
 * {@code Unknown} when it truncates (the live correlation pool is unbounded —
 * undecidability surfaces as truncation, never an unsound verdict).
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
            Set<String> carrierPlaces
    ) {
        var fragment = NameFragment.classify(net, fragmentMode, carrierPlaces);
        if (fragment == null) {
            return null;
        }
        // We model no initial colour assignment, so coloured places must start empty.
        for (var p : initial.placesWithTokens()) {
            if (fragment.isColoured(p.name())) {
                return null;
            }
        }

        var scg = NameStateClassGraph.build(net, initial, fragment, maxClasses, environmentPlaces, environmentMode);

        if (!scg.isComplete()) {
            String reason =
                "ν name-aware state-class graph truncated at " + maxClasses + " classes — the live "
                + "correlation pool is not structurally bounded; reachability over unbounded fresh "
                + "names is undecidable (NU-050, Route B). Declare a budget place to bound the live "
                + "pool, or raise nuMaxClasses.";
            return new Outcome(
                new SmtVerificationResult.Verdict.Unknown(reason), List.of(), List.of(), "", scg.classCount());
        }

        int violating = decide(scg, property, sinkPlaces);
        SmtVerificationResult.Verdict verdict = violating >= 0
            ? new SmtVerificationResult.Verdict.Violated()
            : new SmtVerificationResult.Verdict.Proven("ν name-partition SCG (NU-050, Route B)", null);

        List<MarkingState> trace = List.of();
        List<String> transitions = List.of();
        if (violating >= 0) {
            var path = counterexamplePath(scg, violating);
            trace = path.markings();
            transitions = path.transitions();
        }
        return new Outcome(verdict, trace, transitions, NOTE_EXACT, scg.classCount());
    }

    /** Returns a witnessing class index for a violation, or -1 if the property holds. */
    private static int decide(NameStateClassGraph scg, SmtProperty property, Set<Place<?>> sinkPlaces) {
        return switch (property) {
            case SmtProperty.PlaceBound(var place, var bound) ->
                firstWhere(scg, i -> scg.markingOf(i).tokens(place) > bound);
            case SmtProperty.BranchPlaceBound(var place, var bound) ->
                firstWhere(scg, i -> scg.markingOf(i).tokens(place) > bound);
            case SmtProperty.Unreachable(var places) ->
                firstWhere(scg, i -> {
                    var m = scg.markingOf(i);
                    for (var p : places) {
                        if (!m.hasTokens(p)) return false;
                    }
                    return true;
                });
            case SmtProperty.MutualExclusion(var p1, var p2) ->
                firstWhere(scg, i -> {
                    var m = scg.markingOf(i);
                    return m.hasTokens(p1) && m.hasTokens(p2);
                });
            case SmtProperty.DeadlockFree() ->
                firstWhere(scg, i -> scg.successorsOf(i).isEmpty() && !allTokensInSinks(scg.markingOf(i), sinkPlaces));
            case SmtProperty.JoinedOrDeadLettered(var pending) ->
                firstWhere(scg, i -> scg.successorsOf(i).isEmpty() && scg.markingOf(i).hasTokens(pending));
        };
    }

    private static boolean allTokensInSinks(MarkingState m, Set<Place<?>> sinks) {
        for (var p : m.placesWithTokens()) {
            if (!sinks.contains(p)) return false;
        }
        return true;
    }

    private static int firstWhere(NameStateClassGraph scg, IntPredicate pred) {
        for (int i = 0; i < scg.classCount(); i++) {
            if (pred.test(i)) return i;
        }
        return -1;
    }

    private record Path(List<MarkingState> markings, List<String> transitions) {}

    /** Shortest firing sequence from the initial class (0) to {@code target}. */
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
            for (var e : scg.edges()) {
                if (e.from() == u && !visited[e.to()]) {
                    visited[e.to()] = true;
                    parent[e.to()] = u;
                    via[e.to()] = e.transitionName();
                    queue.add(e.to());
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
