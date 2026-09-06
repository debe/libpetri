package org.libpetri.smt.z3;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.FlatTransition;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
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

    /** Maximum abstract steps allowed between two decoded states (the segment budget). */
    public static final int MAX_SEGMENT_STEPS = 3;

    /**
     * Default search budget, counted in nodes ADMITTED to the search: the root
     * plus every non-dominated successor, tripped with {@code >=}. The same unit
     * and the same comparison in all four implementations, so a net that
     * exhausts the budget in one exhausts it in all.
     */
    public static final int DEFAULT_NODE_BUDGET = 10_000;

    private AbstractReplayer() {}

    /**
     * One abstract step.
     *
     * @param firing the step label: the flat transition name, or
     *               {@code inject(<place>)} for an environment injection
     * @param state  the successor count vector
     */
    public record Step(String firing, int[] state) {}

    /**
     * Outcome of an attempted replay. Only {@link ReplayOutcome.NoChain} — a
     * search that ran to completion and found no chain — may withdraw a VIOLATED
     * verdict; {@link ReplayOutcome.Exhausted} means the search could not settle
     * the question and the verdict stands, unconfirmed.
     */
    public sealed interface ReplayOutcome {
        /**
         * The decoded states chain into an abstract run reaching a
         * property-violating marking.
         *
         * @param trace   replay-ordered markings, initial marking first,
         *                violating marking last
         * @param firings labels of the steps between consecutive trace states
         *                (transition names, or {@code inject(<place>)} for
         *                environment injections)
         */
        record Confirmed(List<MarkingState> trace, List<String> firings) implements ReplayOutcome {}

        /**
         * The search space was covered and no abstract run through the decoded
         * states reaches a violation: the counterexample is spurious or the
         * decoder mis-read the derivation.
         */
        record NoChain() implements ReplayOutcome {}

        /**
         * The search could not decide: a budget ran out (node or segment), or
         * there was nothing anchored to search from (no decoded states, or the
         * initial marking is not among them).
         *
         * @param reason what stopped the search
         */
        record Exhausted(String reason) implements ReplayOutcome {}
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
        int[] pre = ft.preVector();
        int[] post = ft.postVector();
        boolean[] consumeAll = ft.consumeAll();
        int[] next = new int[P];
        for (int p = 0; p < P; p++) {
            next[p] = consumeAll[p] ? post[p] : m[p] - pre[p] + post[p];
        }
        // Reset places are few and indexed, so they are applied after the sweep
        // rather than re-scanned inside it.
        for (int rp : ft.resetPlaces()) {
            if (rp >= 0 && rp < P) {
                next[rp] = post[rp];
            }
        }
        return next;
    }

    /**
     * All abstract successors of {@code m} under the unstrengthened step
     * relation ({@code SmtEncoder.encodeStepRelation}): enabled transitions
     * whose successor respects the bounded-environment caps, plus one
     * environment-injection step per injected env place still under its bound
     * (VER-006). Injection steps are labeled {@code inject(<place>)}.
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
                out.add(new Step("inject(" + entry.getKey().name() + ")", next));
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
        return violates(flatNet, property, sinkPlaces, m, injectedEnvIndices(flatNet));
    }

    /**
     * {@link #violates} with the injected-env-place map precomputed — the form the
     * replay search uses, so the map is built once per replay instead of per state.
     */
    static boolean violates(
            FlatNet flatNet, SmtProperty property, Set<Place<?>> sinkPlaces, int[] m,
            Map<Integer, Integer> envInj
    ) {
        return switch (property) {
            // DeadlockFree (VER-002): quiescent AND some marked place is not a declared
            // sink. Mirrors the encoder's `stranded` disjunction.
            case SmtProperty.DeadlockFree() -> {
                if (!quiescent(flatNet, m, envInj)) {
                    yield false;
                }
                var sinks = sinkIndices(flatNet, sinkPlaces);
                boolean stranded = false;
                for (int pid = 0; pid < flatNet.placeCount(); pid++) {
                    if (!sinks.contains(pid) && m[pid] >= 1) {
                        stranded = true;
                        break;
                    }
                }
                yield stranded;
            }
            // TerminatesAtSink (VER-002): quiescent AND no declared sink marked.
            case SmtProperty.TerminatesAtSink() -> {
                if (!quiescent(flatNet, m, envInj)) {
                    yield false;
                }
                boolean anySinkMarked = false;
                for (int pid : sinkIndices(flatNet, sinkPlaces)) {
                    if (m[pid] != 0) {
                        anySinkMarked = true;
                        break;
                    }
                }
                yield !anySinkMarked;
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
            // JoinedOrDeadLettered (NU-040 AC4): quiescent AND `pending` marked. No sink
            // clause — a marked sink must not excuse a stranded group.
            case SmtProperty.JoinedOrDeadLettered jdl -> {
                int idx = flatNet.indexOf(jdl.pending());
                if (idx < 0) {
                    yield false; // unknown pending place: no state can violate
                }
                yield quiescent(flatNet, m, envInj) && m[idx] >= 1;
            }
            case SmtProperty.Unreachable ur -> {
                // The non-empty guard is load-bearing: with every place unresolved the
                // encoder's conjunction is over nothing, so an all-unresolved property
                // must never be violated — otherwise EVERY marking would be Bad and the
                // replay would "confirm" at M0.
                boolean anyResolved = false;
                boolean allMarked = true;
                for (var place : ur.places()) {
                    int idx = flatNet.indexOf(place);
                    if (idx < 0) {
                        continue;
                    }
                    anyResolved = true;
                    if (m[idx] < 1) {
                        allMarked = false;
                        break;
                    }
                }
                yield anyResolved && allMarked;
            }
        };
    }

    /**
     * Replays the decoded counterexample states with the default segment bound
     * ({@value #MAX_SEGMENT_STEPS} abstract steps between decoded states) and node
     * budget ({@value #DEFAULT_NODE_BUDGET} nodes admitted).
     */
    public static ReplayOutcome replay(
            FlatNet flatNet, MarkingState initialMarking, Set<MarkingState> decodedStates,
            SmtProperty property, Set<Place<?>> sinkPlaces
    ) {
        return replay(flatNet, initialMarking, decodedStates, property, sinkPlaces,
            MAX_SEGMENT_STEPS, DEFAULT_NODE_BUDGET);
    }

    /**
     * Replays the decoded counterexample states: one breadth-first search over
     * abstract successors, from the initial marking (which must be among the
     * decoded states) to any marking satisfying {@link #violates}.
     *
     * <p>The decoded set is order-free, so it is used as a set of ANCHORS rather
     * than as a sequence. Every node carries the number of steps taken since the
     * last anchor it passed through; reaching an anchor resets that counter, and a
     * node at {@code maxSegmentSteps} is not expanded further. A node is dominated
     * — and dropped — when the same marking was already reached with an equal or
     * smaller counter, since a smaller counter can only reach more. The search is
     * therefore global: no waypoint is ever committed to, so a dead-end anchor
     * cannot make replay fail on a net where a chain exists.
     *
     * <p>{@code budget} counts nodes ADMITTED to the search across the whole run:
     * the root plus every non-dominated successor, tripped with {@code >=}. A
     * dominated successor is dropped before it counts.
     *
     * <p>Dropping a node at the segment bound leaves the successor space only
     * partly covered, so a search that pruned that way reports
     * {@link ReplayOutcome.Exhausted}, never {@link ReplayOutcome.NoChain}: a
     * budget is an absence of evidence, not evidence of absence, and only
     * {@code NoChain} may withdraw a verdict.
     *
     * @return {@link ReplayOutcome.Confirmed} with the replay-ordered trace when a
     *     violating marking is reached; {@link ReplayOutcome.NoChain} when the
     *     search covered the space and found none; {@link ReplayOutcome.Exhausted}
     *     when it could not run to completion (either budget, or nothing to
     *     anchor on)
     */
    public static ReplayOutcome replay(
            FlatNet flatNet, MarkingState initialMarking, Set<MarkingState> decodedStates,
            SmtProperty property, Set<Place<?>> sinkPlaces,
            int maxSegmentSteps, int budget
    ) {
        if (decodedStates.isEmpty()) {
            return new ReplayOutcome.Exhausted("no decoded states to replay");
        }
        var anchors = new HashSet<Vec>();
        for (var state : decodedStates) {
            anchors.add(new Vec(toVector(flatNet, state)));
        }
        Vec m0 = new Vec(toVector(flatNet, initialMarking));
        if (!anchors.contains(m0)) {
            return new ReplayOutcome.Exhausted(
                "the initial marking " + initialMarking + " is not among the "
                + decodedStates.size() + " decoded state(s)");
        }

        // Built once, then shared by every violates() call in the search.
        Map<Integer, Integer> envInj = injectedEnvIndices(flatNet);
        if (violates(flatNet, property, sinkPlaces, m0.counts(), envInj)) {
            return new ReplayOutcome.Confirmed(
                List.of(toMarking(flatNet, m0.counts())), List.of());
        }

        var bestSegment = new HashMap<Vec, Integer>();
        bestSegment.put(m0, 0);
        var frontier = new ArrayDeque<Node>();
        frontier.add(new Node(m0, 0, null, null));
        // Nodes admitted to the search, the root included — the budget's unit.
        int admitted = 1;
        // Set when a node was dropped for sitting at the segment bound: the space
        // was then NOT covered in full, so an empty frontier afterwards is
        // exhaustion, not proof that no chain exists.
        boolean segmentPruned = false;

        while (!frontier.isEmpty()) {
            Node node = frontier.poll();
            if (node.segment() >= maxSegmentSteps) {
                segmentPruned = true;
                continue; // the next step would leave the segment unanchored
            }
            for (var step : successors(flatNet, node.state().counts())) {
                Vec succ = new Vec(step.state());
                int segment = anchors.contains(succ) ? 0 : node.segment() + 1;
                Integer best = bestSegment.get(succ);
                if (best != null && best <= segment) {
                    continue; // dominated: a smaller counter can only reach more
                }
                bestSegment.put(succ, segment);
                if (admitted >= budget) {
                    return new ReplayOutcome.Exhausted(
                        "replay budget exhausted (" + budget + " nodes admitted) before the "
                        + "decoded states chained to a violating marking");
                }
                admitted++;
                var child = new Node(succ, segment, node, step.firing());
                if (violates(flatNet, property, sinkPlaces, succ.counts(), envInj)) {
                    return chained(flatNet, child);
                }
                frontier.add(child);
            }
        }
        if (segmentPruned) {
            return new ReplayOutcome.Exhausted(
                "segment budget of " + maxSegmentSteps
                + " step(s) between decoded states exhausted");
        }
        return new ReplayOutcome.NoChain();
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

    /**
     * A search node: a marking, the steps taken since the last decoded anchor, and
     * the step that produced it (null at the root).
     */
    private record Node(Vec state, int segment, Node parent, String via) {}

    /** Walks a node's parents into the replay-ordered trace and firing labels. */
    private static ReplayOutcome.Confirmed chained(FlatNet flatNet, Node goal) {
        var states = new ArrayList<int[]>();
        var firings = new ArrayList<String>();
        for (Node n = goal; n != null; n = n.parent()) {
            states.add(n.state().counts());
            if (n.via() != null) {
                firings.add(n.via());
            }
        }
        Collections.reverse(states);
        Collections.reverse(firings);
        return new ReplayOutcome.Confirmed(toMarkings(flatNet, states), List.copyOf(firings));
    }

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

    private static boolean withinEnvBounds(FlatNet flatNet, int[] m) {
        for (var entry : flatNet.environmentBounds().entrySet()) {
            int idx = flatNet.indexOf(entry.getKey());
            if (idx >= 0 && m[idx] > entry.getValue()) {
                return false;
            }
        }
        return true;
    }

    /** Declared sink place names resolved to flat-net indices. */
    private static Set<Integer> sinkIndices(FlatNet flatNet, Set<Place<?>> sinkPlaces) {
        var idx = new HashSet<Integer>();
        for (var sink : sinkPlaces) {
            int i = flatNet.indexOf(sink);
            if (i >= 0) {
                idx.add(i);
            }
        }
        return idx;
    }

    /**
     * Concrete evaluation of {@code SmtEncoder.encodeQuiescent} at {@code m}: every
     * transition is disabled, with input/read requirements on injected environment
     * places treated as satisfiable by injection (VER-006).
     *
     * <p>Carries no sink handling: each property in {@link #violates} conjoins its own
     * clause, exactly as the encoder does.
     */
    private static boolean quiescent(FlatNet flatNet, int[] m, Map<Integer, Integer> envInj) {
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
