package org.libpetri.smt.z3;

import org.libpetri.smt.encoding.FlatNet;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.function.Predicate;

/**
 * The witness search of the state-equation phase ([VER-018]): a breadth-first search from
 * {@code M0} under the exact abstract semantics ({@link AbstractReplayer#enabledA} /
 * {@link AbstractReplayer#fireA} — consume-all and reset clearing, inhibitor and read guards)
 * that fires each flat transition at most as often as a candidate's firing counts allow, and
 * stops at the first marking that violates the property. This is the cheap first level of
 * directed reachability (Blondin, Haase and Offtermatt, TACAS 2021): the counts bound the
 * depth by their sum, which on a workflow net is small.
 *
 * <p>{@link WitnessOutcome.Found} is a real firing sequence of the untimed net, so the
 * violation it witnesses is confirmed by construction. {@link WitnessOutcome.None} is a
 * completed search: no run whose firing counts stay within the candidate's reaches a
 * violation. {@link WitnessOutcome.Exhausted} says nothing either way.
 *
 * <p><b>Environment injection splits those three</b>, because an injection is not a counted
 * firing and so is never searched. {@code Found} survives it: the search fires only counted
 * transitions, a run in which the environment injects nothing is still a run of the net, and
 * the quiescence half of {@code Bad(M)} is judged with relax-env enablement
 * ({@link AbstractReplayer#violates}) — a marking it accepts is stuck even against an
 * environment free to inject. {@code None} does not survive it: its claim is that no run
 * reaches a violation, and an injected token could enable a run the search never considered.
 * So under injection the completed search reports {@code Exhausted}, which says nothing either
 * way, rather than a negative it cannot support. The guard sits on that terminal answer and
 * nowhere else: on a net whose environment injects, this search is the only leg of the phase
 * that can produce a witness at all, so it must still run there.
 *
 * <p>Nothing here spawns or parses z3, and nothing is emitted: parity with the TypeScript
 * {@code parikh-search} is behavioural — the same run found, the same node counts, the same
 * reasons.
 */
public final class ParikhSearch {

    private ParikhSearch() {}

    /** The node budget of one witness search when the caller has no reason to pick another. */
    public static final int DEFAULT_NODE_BUDGET = 100_000;

    /** Outcome of {@link #searchWithinCounts}. {@code nodes} counts the nodes admitted, the root included. */
    public sealed interface WitnessOutcome {

        /** The nodes the search admitted, the root included. */
        int nodes();

        /**
         * A run from {@code M0} within the counts that reaches a marking the predicate accepts.
         *
         * @param states the markings of the run, {@code M0 … M_bad} inclusive
         * @param steps  the flat transitions fired, one per consecutive pair of {@code states}
         */
        record Found(List<int[]> states, List<String> steps, int nodes) implements WitnessOutcome {
            public Found {
                states = List.copyOf(states);
                steps = List.copyOf(steps);
            }
        }

        /**
         * Every run within the counts was explored and none reaches a violation. Only ever
         * reported on a net with no environment injection.
         */
        record None(int nodes) implements WitnessOutcome {}

        /**
         * The search proves nothing: the node budget ran out, or it completed on a net the
         * environment injects into.
         *
         * @param reason report-ready
         */
        record Exhausted(String reason, int nodes) implements WitnessOutcome {}
    }

    /** {@link #searchWithinCounts(FlatNet, int[], long[], Predicate, int)} with {@link #DEFAULT_NODE_BUDGET}. */
    public static WitnessOutcome searchWithinCounts(
            FlatNet flatNet, int[] initial, long[] counts, Predicate<int[]> isBad
    ) {
        return searchWithinCounts(flatNet, initial, counts, isBad, DEFAULT_NODE_BUDGET);
    }

    /**
     * Searches the runs from {@code initial} that fire each flat transition {@code t} at most
     * {@code counts[t]} times for one that reaches a marking {@code isBad} accepts. A node is a
     * marking together with the counts still unspent, so two runs meeting there have the same
     * future and the second is dropped. The search is breadth-first and tries transitions in
     * flat order, so the run found is a shortest one and the same run every port finds.
     *
     * <p>The bounded-environment caps ({@link FlatNet#environmentBounds()}) are the post-cap
     * every step of the encoded system carries: a firing that leaves an env place above its
     * cap is not a step, so it is not searched. Injection itself is not searched, so a
     * completed search on a net with injected places reports {@link WitnessOutcome.Exhausted}
     * rather than {@link WitnessOutcome.None} — see the class note for why a
     * {@link WitnessOutcome.Found} run is still reported there.
     *
     * @param initial    {@code M0}, one count per flat place ({@link AbstractReplayer#toVector})
     * @param counts     the candidate's firing counts, one per flat transition; an entry past
     *                   the end reads as {@code 0}, so a short vector never lets a transition
     *                   fire more often than the candidate says
     * @param isBad      the violation predicate, e.g. {@link AbstractReplayer#violates} over
     *                   the verified property
     * @param nodeBudget the nodes admitted, the root included; it trips on {@code >=}, when a
     *                   new node would be admitted
     */
    public static WitnessOutcome searchWithinCounts(
            FlatNet flatNet, int[] initial, long[] counts, Predicate<int[]> isBad, int nodeBudget
    ) {
        var caps = new ArrayList<int[]>();
        for (var entry : flatNet.environmentBounds().entrySet()) {
            int idx = flatNet.indexOf(entry.getKey());
            if (idx >= 0) {
                caps.add(new int[] {idx, entry.getValue()});
            }
        }
        var transitions = flatNet.transitions();
        long[] budget = new long[transitions.size()];
        for (int t = 0; t < budget.length; t++) {
            budget[t] = t < counts.length ? counts[t] : 0;
        }
        var root = new SearchNode(initial.clone(), budget, -1, -1);
        var nodes = new ArrayList<SearchNode>();
        nodes.add(root);
        // The predicate gets a copy throughout: a node's marking is also its key in `seen`,
        // and a predicate that wrote to it would corrupt the search silently.
        if (isBad.test(root.state().clone())) {
            return new WitnessOutcome.Found(List.of(root.state().clone()), List.of(), 1);
        }
        var seen = new HashSet<Key>();
        seen.add(new Key(root.state(), root.remaining()));
        for (int head = 0; head < nodes.size(); head++) {
            var node = nodes.get(head);
            for (int t = 0; t < transitions.size(); t++) {
                if (node.remaining()[t] <= 0) {
                    continue;
                }
                var ft = transitions.get(t);
                if (!AbstractReplayer.enabledA(node.state(), ft)) {
                    continue;
                }
                int[] next = AbstractReplayer.fireA(node.state(), ft);
                if (exceedsCap(next, caps)) {
                    continue;
                }
                long[] remaining = node.remaining().clone();
                remaining[t]--;
                var key = new Key(next, remaining);
                if (seen.contains(key)) {
                    continue;
                }
                if (nodes.size() >= nodeBudget) {
                    return new WitnessOutcome.Exhausted(
                        "search budget exhausted (" + nodeBudget + " nodes)", nodes.size());
                }
                seen.add(key);
                nodes.add(new SearchNode(next, remaining, head, t));
                if (isBad.test(next.clone())) {
                    return reconstruct(nodes, nodes.size() - 1, flatNet);
                }
            }
        }
        // The search ran out of counted runs, not out of budget. That settles `None` only when
        // nothing outside the counted firings can extend a run, so injection downgrades it —
        // here, at the terminal answer, and not at the entry, where it would also discard the
        // witnesses the search can still find.
        return flatNet.environmentInjection().isEmpty()
            ? new WitnessOutcome.None(nodes.size())
            : new WitnessOutcome.Exhausted("environment injection is not searched", nodes.size());
    }

    /**
     * A search node: a marking, the counts it has left, and the step that produced it
     * ({@code parent}/{@code transition} {@code -1} on the root).
     */
    private record SearchNode(int[] state, long[] remaining, int parent, int transition) {}

    /** A marking with the counts still unspent, compared by content: the deduplication key. */
    private record Key(int[] state, long[] remaining) {
        @Override
        public boolean equals(Object o) {
            return o instanceof Key other
                && Arrays.equals(state, other.state)
                && Arrays.equals(remaining, other.remaining);
        }

        @Override
        public int hashCode() {
            return 31 * Arrays.hashCode(state) + Arrays.hashCode(remaining);
        }
    }

    private static boolean exceedsCap(int[] marking, List<int[]> caps) {
        for (int[] cap : caps) {
            if (marking[cap[0]] > cap[1]) {
                return true;
            }
        }
        return false;
    }

    /** The run ending at node {@code last}: its markings from the root, and the transitions between them. */
    private static WitnessOutcome.Found reconstruct(List<SearchNode> nodes, int last, FlatNet flatNet) {
        var states = new ArrayList<int[]>();
        var steps = new ArrayList<String>();
        for (int i = last; i >= 0; i = nodes.get(i).parent()) {
            var node = nodes.get(i);
            states.add(node.state().clone());
            if (node.transition() >= 0) {
                steps.add(flatNet.transitions().get(node.transition()).name());
            }
        }
        Collections.reverse(states);
        Collections.reverse(steps);
        return new WitnessOutcome.Found(states, steps, nodes.size());
    }
}
