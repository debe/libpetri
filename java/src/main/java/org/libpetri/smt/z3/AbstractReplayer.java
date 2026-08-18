package org.libpetri.smt.z3;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.FlatTransition;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Pure-Java replay of a Spacer counterexample under the <em>abstract</em>
 * (untimed, value-blind) semantics of the CHC encoding.
 *
 * <p>When Spacer reports a property violation, {@link CounterexampleDecoder}
 * recovers a <em>set</em> of concrete markings from the derivation tree — but
 * the tree's traversal order is not an execution order, and the decoder can
 * only degrade gracefully on unrecognized answer shapes. This class closes the
 * gap: it re-executes the abstraction on plain {@code int[]} count vectors and
 * tries to chain the decoded states into an actual abstract run from the
 * initial marking to a property-violating marking. A successful chain confirms
 * the counterexample <em>at the abstraction level</em> (it is a real run of the
 * encoded step relation); an impossible chain exposes a spurious CEX or a
 * decoder/encoding mismatch, which {@link org.libpetri.smt.SmtVerifier}
 * downgrades to an inconclusive verdict rather than trusting.
 *
 * <p><b>Semantics.</b> The abstract enablement and firing rules mirror the
 * Lean model {@code lean/Libpetri/Basic.lean} ({@code enabledA} / {@code fireA})
 * and, arm for arm, the Z3 encoder:
 * <ul>
 *   <li>{@link #enabledA}: {@code M[p] >= pre[p]} for inputs, {@code M[p] >= 1}
 *       for read places, {@code M[p] == 0} for inhibited places — the
 *       {@code SmtEncoder.encodeEnabled} conjuncts / Lean {@code enabledA}.</li>
 *   <li>{@link #fireA}: reset place &rarr; {@code M'[p] = post[p]};
 *       consume-all place ({@code All}/{@code AtLeast}, per
 *       {@link FlatTransition#consumeAll()}) &rarr; {@code M'[p] = post[p]};
 *       otherwise {@code M'[p] = M[p] - pre[p] + post[p]} — the
 *       {@code SmtEncoder.encodeFire} arms / Lean {@code fireA}.</li>
 *   <li>{@link #successors}: one step of the <em>unstrengthened</em> step
 *       relation ({@code SmtEncoder.encodeStepRelation}): every enabled flat
 *       transition (subject to the bounded-environment caps on {@code M'}),
 *       plus one environment-injection step per injected env place — adding a
 *       single token while under the injection bound (VER-006).</li>
 *   <li>{@link #violates}: the property-violation predicate
 *       {@code Bad(M)} of {@code SmtEncoder.encodePropertyViolation}, including
 *       the relaxed (injection-aware) enablement inside the deadlock arm.</li>
 * </ul>
 *
 * <p>The strengthening P-invariants are deliberately NOT consulted (same
 * independence argument as {@link CertificateChecker}): replay is a ground-truth
 * check of the bare abstract semantics.
 *
 * <p><b>No JNI.</b> This class never touches Z3, so its unit tests run on
 * machines without the native library.
 */
public final class AbstractReplayer {

    /** Maximum abstract steps bridged between two consecutive decoded states. */
    public static final int MAX_HOP_STEPS = 3;

    /** Default total exploration budget (states expanded across all hops). */
    public static final int DEFAULT_BUDGET = 10_000;

    private AbstractReplayer() {}

    /**
     * One abstract step.
     *
     * @param firing the step label: the flat transition name, or
     *               {@code env_inject_<place>} for an environment injection
     * @param state  the successor count vector
     */
    public record Step(String firing, int[] state) {}

    /** Outcome of an attempted replay. */
    public sealed interface ReplayOutcome {
        /**
         * The decoded states chain into an abstract run reaching a
         * property-violating marking.
         *
         * @param trace   replay-ordered markings, initial marking first,
         *                violating marking last
         * @param firings labels of the steps between consecutive trace states
         *                (transition names, or {@code env_inject_<place>} for
         *                environment injections)
         */
        record Chained(List<MarkingState> trace, List<String> firings) implements ReplayOutcome {}

        /**
         * No abstract run through the decoded states reaches a violation
         * within the hop/budget bounds.
         *
         * @param reason structured description of where the chain broke
         */
        record NotChainable(String reason) implements ReplayOutcome {}
    }

    /**
     * Abstract enablement of one flat transition (Lean {@code enabledA};
     * {@code SmtEncoder.encodeEnabled}, strict form): every input place holds at
     * least {@code pre[p]} tokens, every read place at least one, every
     * inhibited place none.
     */
    public static boolean enabledA(int[] m, FlatTransition ft) {
        int[] pre = ft.preVector();
        for (int p = 0; p < pre.length; p++) {
            if (pre[p] > 0 && m[p] < pre[p]) {
                return false;
            }
        }
        for (int p : ft.readPlaces()) {
            if (m[p] < 1) {
                return false;
            }
        }
        for (int p : ft.inhibitorPlaces()) {
            if (m[p] != 0) {
                return false;
            }
        }
        return true;
    }

    /**
     * Abstract successor marking of one firing (Lean {@code fireA};
     * {@code SmtEncoder.encodeFire}): reset and consume-all places jump to
     * {@code post[p]}, every other place moves by {@code post[p] - pre[p]}.
     */
    public static int[] fireA(int[] m, FlatTransition ft) {
        int P = m.length;
        int[] next = new int[P];
        for (int p = 0; p < P; p++) {
            if (isReset(ft, p) || ft.consumeAll()[p]) {
                next[p] = ft.postVector()[p];
            } else {
                next[p] = m[p] - ft.preVector()[p] + ft.postVector()[p];
            }
        }
        return next;
    }

    /**
     * All abstract successors of {@code m} under the unstrengthened step
     * relation ({@code SmtEncoder.encodeStepRelation}): enabled transitions
     * whose successor respects the bounded-environment caps, plus one
     * environment-injection step per injected env place still under its bound
     * (VER-006). Injection steps are labeled {@code env_inject_<place>}.
     */
    public static List<Step> successors(FlatNet flatNet, int[] m) {
        var out = new ArrayList<Step>();
        for (var ft : flatNet.transitions()) {
            if (!enabledA(m, ft)) {
                continue;
            }
            int[] next = fireA(m, ft);
            if (withinEnvBounds(flatNet, next)) {
                out.add(new Step(ft.name(), next));
            }
        }
        for (var entry : flatNet.environmentInjection().entrySet()) {
            int idx = flatNet.indexOf(entry.getKey());
            if (idx < 0) {
                continue;
            }
            Integer bound = entry.getValue();
            if (bound == null || m[idx] < bound) {
                int[] next = m.clone();
                next[idx]++;
                out.add(new Step("env_inject_" + entry.getKey().name(), next));
            }
        }
        return out;
    }

    /**
     * Java-side evaluation of the property-violation predicate {@code Bad(M)}
     * — the same case analysis as {@code SmtEncoder.encodePropertyViolation},
     * with the deadlock arm using the relaxed (injection-aware) enablement of
     * the Error rule: an input or read requirement on an injected environment
     * place counts as satisfiable by the environment (VER-006).
     *
     * @throws IllegalArgumentException if the property references a place not
     *     in the flattened net (mirrors the encoder)
     */
    public static boolean violates(
            FlatNet flatNet, SmtProperty property, Set<Place<?>> sinkPlaces, int[] m
    ) {
        return switch (property) {
            case SmtProperty.DeadlockFree() -> {
                if (!isDeadlock(flatNet, m)) {
                    yield false;
                }
                for (var sink : sinkPlaces) {
                    int idx = flatNet.indexOf(sink);
                    if (idx >= 0 && m[idx] != 0) {
                        yield false; // resting at a declared sink is not a violation
                    }
                }
                yield true;
            }
            case SmtProperty.MutualExclusion me -> {
                int idx1 = requireIndex(flatNet, me.p1(), "MutualExclusion");
                int idx2 = requireIndex(flatNet, me.p2(), "MutualExclusion");
                yield m[idx1] >= 1 && m[idx2] >= 1;
            }
            case SmtProperty.PlaceBound pb ->
                m[requireIndex(flatNet, pb.place(), "PlaceBound")] > pb.bound();
            case SmtProperty.BranchPlaceBound bpb ->
                m[requireIndex(flatNet, bpb.place(), "BranchPlaceBound")] > bpb.bound();
            case SmtProperty.JoinedOrDeadLettered jdl -> {
                int idx = flatNet.indexOf(jdl.pending());
                if (idx < 0) {
                    yield false; // unknown pending place: no state can violate
                }
                yield isDeadlock(flatNet, m) && m[idx] >= 1;
            }
            case SmtProperty.Unreachable ur -> {
                for (var place : ur.places()) {
                    int idx = flatNet.indexOf(place);
                    if (idx >= 0 && m[idx] < 1) {
                        yield false;
                    }
                }
                yield true;
            }
        };
    }

    /**
     * Replays the decoded counterexample states with the default hop bound
     * ({@value #MAX_HOP_STEPS} abstract steps between consecutive decoded
     * states) and budget ({@value #DEFAULT_BUDGET} expanded states).
     */
    public static ReplayOutcome replay(
            FlatNet flatNet, MarkingState initialMarking, Set<MarkingState> decodedStates,
            SmtProperty property, Set<Place<?>> sinkPlaces
    ) {
        return replay(flatNet, initialMarking, decodedStates, property, sinkPlaces,
            MAX_HOP_STEPS, DEFAULT_BUDGET);
    }

    /**
     * Replays the decoded counterexample states: starting from the initial
     * marking (which must itself be among the decoded states), repeatedly
     * bridges to a not-yet-visited decoded state — or to any marking satisfying
     * {@link #violates} — with a bounded BFS of at most {@code maxHopSteps}
     * abstract steps, expanding at most {@code budget} states in total.
     *
     * <p>Reaching a violating marking confirms the counterexample and yields
     * the replay-ordered {@link ReplayOutcome.Chained} trace; running out of
     * bridgeable decoded states (or budget) yields
     * {@link ReplayOutcome.NotChainable} with the break point named. Decoded
     * states that turn out to be interior duplicates the chain never needs are
     * not required — the chain ends as soon as a violation is reached.
     */
    public static ReplayOutcome replay(
            FlatNet flatNet, MarkingState initialMarking, Set<MarkingState> decodedStates,
            SmtProperty property, Set<Place<?>> sinkPlaces,
            int maxHopSteps, int budget
    ) {
        if (decodedStates.isEmpty()) {
            return new ReplayOutcome.NotChainable("no decoded states to replay");
        }
        Vec m0 = new Vec(toVector(flatNet, initialMarking));
        var remaining = new LinkedHashSet<Vec>();
        for (var state : decodedStates) {
            remaining.add(new Vec(toVector(flatNet, state)));
        }
        if (!remaining.remove(m0)) {
            return new ReplayOutcome.NotChainable(
                "the initial marking " + initialMarking + " is not among the "
                + decodedStates.size() + " decoded state(s)");
        }

        var trace = new ArrayList<int[]>();
        var firings = new ArrayList<String>();
        trace.add(m0.counts());
        Vec current = m0;
        int expanded = 0;

        while (true) {
            if (violates(flatNet, property, sinkPlaces, current.counts())) {
                return new ReplayOutcome.Chained(toMarkings(flatNet, trace), List.copyOf(firings));
            }

            // Bounded BFS from the current chained state for the nearest goal:
            // a violating marking, or a decoded state not yet chained.
            var parents = new HashMap<Vec, Vec>();
            var vias = new HashMap<Vec, String>();
            var visited = new HashSet<Vec>();
            var frontier = new ArrayDeque<Vec>();
            visited.add(current);
            frontier.add(current);
            Vec goal = null;
            boolean goalIsViolation = false;

            search:
            for (int depth = 0; depth < maxHopSteps && !frontier.isEmpty(); depth++) {
                int levelSize = frontier.size();
                for (int i = 0; i < levelSize; i++) {
                    Vec node = frontier.poll();
                    if (++expanded > budget) {
                        return new ReplayOutcome.NotChainable(
                            "replay budget exhausted (" + budget + " expanded states) before the "
                            + "decoded states chained to a violating marking");
                    }
                    for (var step : successors(flatNet, node.counts())) {
                        Vec succ = new Vec(step.state());
                        if (!visited.add(succ)) {
                            continue;
                        }
                        parents.put(succ, node);
                        vias.put(succ, step.firing());
                        if (violates(flatNet, property, sinkPlaces, succ.counts())) {
                            goal = succ;
                            goalIsViolation = true;
                            break search;
                        }
                        if (remaining.contains(succ)) {
                            goal = succ;
                            break search;
                        }
                        frontier.add(succ);
                    }
                }
            }

            if (goal == null) {
                return new ReplayOutcome.NotChainable(
                    "no abstract run of at most " + maxHopSteps + " step(s) leads from "
                    + toMarking(flatNet, current.counts()) + " to another decoded state or to a "
                    + "property-violating marking (" + remaining.size() + " decoded state(s) unchained)");
            }

            // Append the bridging path (goal-side first, reversed onto the trace).
            var hopStates = new ArrayList<Vec>();
            var hopFirings = new ArrayList<String>();
            for (Vec v = goal; !v.equals(current); v = parents.get(v)) {
                hopStates.add(v);
                hopFirings.add(vias.get(v));
            }
            for (int i = hopStates.size() - 1; i >= 0; i--) {
                trace.add(hopStates.get(i).counts());
                firings.add(hopFirings.get(i));
            }
            if (goalIsViolation) {
                return new ReplayOutcome.Chained(toMarkings(flatNet, trace), List.copyOf(firings));
            }
            remaining.remove(goal);
            current = goal;
        }
    }

    /** Projects a {@link MarkingState} onto the flat net's count vector. */
    public static int[] toVector(FlatNet flatNet, MarkingState marking) {
        int P = flatNet.placeCount();
        int[] v = new int[P];
        for (int i = 0; i < P; i++) {
            v[i] = marking.tokens(flatNet.places().get(i));
        }
        return v;
    }

    /** Lifts a count vector back to a {@link MarkingState}. */
    public static MarkingState toMarking(FlatNet flatNet, int[] state) {
        var builder = MarkingState.builder();
        for (int i = 0; i < state.length; i++) {
            if (state[i] > 0) {
                builder.tokens(flatNet.places().get(i), state[i]);
            }
        }
        return builder.build();
    }

    // === internals ===

    /** Count vector with content-based equality, usable as a set/map key. */
    private record Vec(int[] counts) {
        @Override
        public boolean equals(Object o) {
            return o instanceof Vec other && Arrays.equals(counts, other.counts);
        }

        @Override
        public int hashCode() {
            return Arrays.hashCode(counts);
        }
    }

    private static List<MarkingState> toMarkings(FlatNet flatNet, List<int[]> states) {
        var out = new ArrayList<MarkingState>(states.size());
        for (var state : states) {
            out.add(toMarking(flatNet, state));
        }
        return List.copyOf(out);
    }

    private static boolean isReset(FlatTransition ft, int p) {
        for (int rp : ft.resetPlaces()) {
            if (rp == p) {
                return true;
            }
        }
        return false;
    }

    private static boolean withinEnvBounds(FlatNet flatNet, int[] m) {
        for (var entry : flatNet.environmentBounds().entrySet()) {
            int idx = flatNet.indexOf(entry.getKey());
            if (idx >= 0 && m[idx] > entry.getValue()) {
                return false;
            }
        }
        return true;
    }

    /**
     * Deadlock predicate of the Error rule ({@code SmtEncoder.encodeDeadlock}):
     * no transition is enabled, with input/read requirements on injected
     * environment places treated as satisfiable by injection (VER-006).
     */
    private static boolean isDeadlock(FlatNet flatNet, int[] m) {
        Map<Integer, Integer> envInj = injectedEnvIndices(flatNet);
        for (var ft : flatNet.transitions()) {
            if (enabledRelaxed(m, ft, envInj)) {
                return false;
            }
        }
        return true;
    }

    /** Relaxed enablement ({@code SmtEncoder.encodeEnabled} with {@code relaxEnv}). */
    private static boolean enabledRelaxed(int[] m, FlatTransition ft, Map<Integer, Integer> envInj) {
        int[] pre = ft.preVector();
        for (int p = 0; p < pre.length; p++) {
            if (pre[p] <= 0) {
                continue;
            }
            if (envInj.containsKey(p)) {
                Integer bound = envInj.get(p);
                if (bound != null && pre[p] > bound) {
                    return false; // never enableable, even by injection
                }
                continue; // satisfiable by injection
            }
            if (m[p] < pre[p]) {
                return false;
            }
        }
        for (int p : ft.readPlaces()) {
            if (envInj.containsKey(p)) {
                Integer bound = envInj.get(p);
                if (bound != null && bound < 1) {
                    return false;
                }
                continue;
            }
            if (m[p] < 1) {
                return false;
            }
        }
        for (int p : ft.inhibitorPlaces()) {
            if (m[p] != 0) {
                return false;
            }
        }
        return true;
    }

    /** Injected environment-place index -&gt; injection bound (null = unbounded). */
    private static Map<Integer, Integer> injectedEnvIndices(FlatNet flatNet) {
        var out = new HashMap<Integer, Integer>();
        for (var entry : flatNet.environmentInjection().entrySet()) {
            int idx = flatNet.indexOf(entry.getKey());
            if (idx >= 0) {
                out.put(idx, entry.getValue());
            }
        }
        return out;
    }

    private static int requireIndex(FlatNet flatNet, Place<?> place, String property) {
        int idx = flatNet.indexOf(place);
        if (idx < 0) {
            throw new IllegalArgumentException(
                property + " property references unknown place: " + place.name());
        }
        return idx;
    }
}
