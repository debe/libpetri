package org.libpetri.smt.z3;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.SmtVerifier;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.z3.BoundedRun.DepthAnswer;
import org.libpetri.smt.z3.BoundedRun.DepthStep;
import org.libpetri.smt.z3.BoundedRun.FiringBound;
import org.libpetri.smt.z3.BoundedRun.FiringBoundOutcome;
import org.libpetri.smt.z3.BoundedRun.FiringBoundSolver;
import org.libpetri.smt.z3.BoundedRun.Options;
import org.libpetri.smt.z3.BoundedRun.Phase;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

import java.math.BigInteger;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.function.IntFunction;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.smt.z3.StateEquationNets.*;

/**
 * [VER-019] the firing-bound phase: the ranking and repeatable-vector queries, the bounded
 * model check, their decoders, the exact re-check and replay, and the phase that drives them.
 * Mirrors the firing-bound cases of {@code typescript/tests/verification/state-equation-phase.test.ts}
 * at the phase; the phase through {@code SmtVerifier} is {@code StateEquationPhaseVerifierTest}'s.
 *
 * <p>The pinned scripts, decoded models and phase outcomes below were diffed byte-identical
 * against the TypeScript port when this port landed.
 */
class BoundedRunTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    /** {@code p0 → t0 → p1 → t1 → p2 → t2 → p0}: no ranking exists. */
    record Ring(FlatNet flat, MarkingState m0, Place<String> p0) {}

    static Ring ring() {
        var p0 = place("p0");
        var p1 = place("p1");
        var p2 = place("p2");
        var net = PetriNet.builder("ring").transitions(
            Transition.builder("t0").inputs(In.one(p0)).outputs(Out.place(p1)).build(),
            Transition.builder("t1").inputs(In.one(p1)).outputs(Out.place(p2)).build(),
            Transition.builder("t2").inputs(In.one(p2)).outputs(Out.place(p0)).build()
        ).build();
        return new Ring(flatten(net), MarkingState.builder().tokens(p0, 1).build(), p0);
    }

    /**
     * Every clearing and guard shape at once: {@code t1} resets the place it inhibits and reads
     * {@code gate}, {@code t2} takes two of {@code x} and reads {@code gate}, {@code t3} takes
     * {@code atLeast(2, z)} and resets {@code x}, and {@code t4} reads the place it inhibits, so
     * it can never fire. Flat places: gate, p, r, x, y, z.
     */
    static FlatNet clearing() {
        var p = place("p");
        var gate = place("gate");
        var r = place("r");
        var x = place("x");
        var y = place("y");
        var z = place("z");
        var net = PetriNet.builder("clearing").transitions(
            Transition.builder("t1").inputs(In.one(p)).reads(gate).resets(r).inhibitors(r).outputs(Out.place(z)).build(),
            Transition.builder("t2").inputs(In.exactly(2, x)).reads(gate).outputs(Out.place(y)).build(),
            Transition.builder("t3").inputs(In.one(y), In.atLeast(2, z)).resets(x).outputs(Out.and(r, x)).build(),
            Transition.builder("t4").inputs(In.one(z)).reads(p).inhibitors(p).outputs(Out.place(p)).build()
        ).build();
        return flatten(net);
    }

    /** {@code fill: start → q}, {@code gate: sig + gateOpen → done}. Flat places: done, gateOpen, q, sig, start. */
    static FlatNet gated(EnvironmentAnalysisMode mode) {
        var start = place("start");
        var q = place("q");
        var gateOpen = place("gateOpen");
        var done = place("done");
        var sig = EnvironmentPlace.of(place("sig"));
        var net = PetriNet.builder("gated").transitions(
            Transition.builder("fill").inputs(In.one(start)).outputs(Out.place(q)).build(),
            Transition.builder("gate").inputs(In.one(sig.place()), In.one(gateOpen)).outputs(Out.place(done)).build()
        ).build();
        return NetFlattener.flatten(net, Set.of(sig), mode);
    }

    static List<BigInteger> weights(FlatNet flat, Object... nameWeights) {
        var w = new ArrayList<BigInteger>();
        for (int i = 0; i < flat.placeCount(); i++) {
            w.add(BigInteger.ZERO);
        }
        for (int i = 0; i < nameWeights.length; i += 2) {
            var value = nameWeights[i + 1];
            w.set(indexOf(flat, (String) nameWeights[i]),
                value instanceof BigInteger big ? big : BigInteger.valueOf((Integer) value));
        }
        return w;
    }

    static int transition(FlatNet flat, String name) {
        for (int t = 0; t < flat.transitionCount(); t++) {
            if (flat.transitions().get(t).name().equals(name)) {
                return t;
            }
        }
        throw new IllegalArgumentException("no transition " + name);
    }

    static List<BigInteger> big(long... values) {
        var out = new ArrayList<BigInteger>();
        for (long v : values) {
            out.add(BigInteger.valueOf(v));
        }
        return out;
    }

    // ==================== ranking ====================

    @Test
    void reChecksARankingExactlyAndRejectsOneSomeFiringDoesNotLower() {
        var queue = queueAndBundle(3, false);
        var flat = queue.flat();
        int[] initial = AbstractReplayer.toVector(flat, queue.m0());
        var bound = BoundedRun.checkRankingExact(flat, initial, weights(flat, "budget", 1, "src", 2, "s", 1));
        assertNotNull(bound);
        assertEquals(BigInteger.valueOf(5), bound.bound());
        assertEquals("budget + s + 2*src", BoundedRun.formatRanking(flat, bound));
        // Without a weight on s, bundleEmpty (s -> out) lowers nothing.
        assertNull(BoundedRun.checkRankingExact(flat, initial, weights(flat, "budget", 1, "src", 2)));
    }

    @Test
    void rejectsANegativeOrMisSizedRankingAndReadsAnyMagnitudeExactly() {
        var queue = queueAndBundle(3, false);
        var flat = queue.flat();
        int[] initial = AbstractReplayer.toVector(flat, queue.m0());
        assertNull(BoundedRun.checkRankingExact(flat, initial, weights(flat, "budget", 1, "src", 2, "s", 1, "q", -1)));
        assertNull(BoundedRun.checkRankingExact(flat, initial, big(1, 0, 0, 1)));
        // No magnitude wraps: a ranking 2^100 times the least one is still a ranking, with the
        // bound it gives.
        var scale = BigInteger.TWO.pow(100);
        var huge = BoundedRun.checkRankingExact(flat, initial,
            weights(flat, "budget", scale, "src", scale.multiply(BigInteger.TWO), "s", scale));
        assertNotNull(huge);
        assertEquals(scale.multiply(BigInteger.valueOf(5)), huge.bound());

        // A transition that can never fire needs no decrease: `t4` raises `2*p + z` by one, and
        // the ranking still holds. A clearing arc counts at its weight: `t3` resets `x` and puts
        // one back, a column entry of +1.
        var clearing = clearing();
        int[] start = {1, 1, 0, 3, 0, 0};
        var clearingBound = BoundedRun.checkRankingExact(clearing, start, weights(clearing, "p", 2, "x", 1, "y", 1, "z", 1));
        assertNotNull(clearingBound);
        assertEquals(BigInteger.valueOf(5), clearingBound.bound());
        assertEquals("2*p + x + y + z", BoundedRun.formatRanking(clearing, clearingBound));
        assertEquals("0", BoundedRun.formatRanking(clearing, new FiringBound(big(0, 0, 0, 0, 0, 0), BigInteger.ZERO)));
    }

    @Test
    void encodesTheRankingAndRepeatableVectorQueries() {
        var queue = queueAndBundle(2, true);
        var flat = queue.flat();
        int[] initial = AbstractReplayer.toVector(flat, queue.m0());
        assertEquals("""
            ; Firing bound (VER-019): weights r >= 0 that every firing lowers by at least one
            ; (r.C_t <= -1, a clearing arc counted at its weight); every run from M0 then has
            ; at most r.M0 firings. sat with the least r.M0.
            (set-logic QF_LIA)
            (declare-const r0 Int)
            (declare-const r1 Int)
            (declare-const r2 Int)
            (declare-const r3 Int)
            (declare-const r4 Int)
            (declare-const r5 Int)
            (assert (>= r0 0))
            (assert (>= r1 0))
            (assert (>= r2 0))
            (assert (>= r3 0))
            (assert (>= r4 0))
            (assert (>= r5 0))
            (assert (<= (+ (- r0) r3) (- 1)))
            (assert (<= (+ r4 (- r5)) (- 1)))
            (assert (<= (+ r2 (- r3) (- r4)) (- 1)))
            (assert (<= (+ r2 (- r4)) (- 1)))
            (assert (<= (+ r1 (- r5)) (- 1)))
            (minimize (+ (* 2 r0) r5))
            (check-sat)
            (get-model)""", BoundedRun.encodeRankingQuery(flat, initial));
        assertEquals("""
            ; No firing bound (VER-019): firing counts y >= 0, not all zero, with C.y >= 0 on
            ; every place, so the marking equation lets them repeat forever.
            (set-logic QF_LIA)
            (declare-const y0 Int)
            (declare-const y1 Int)
            (declare-const y2 Int)
            (declare-const y3 Int)
            (declare-const y4 Int)
            (assert (>= y0 0))
            (assert (>= y1 0))
            (assert (>= y2 0))
            (assert (>= y3 0))
            (assert (>= y4 0))
            (assert (>= (+ y0 y1 y2 y3 y4) 1))
            (assert (>= (- y0) 0))
            (assert (>= y4 0))
            (assert (>= (+ y2 y3) 0))
            (assert (>= (+ y0 (- y2)) 0))
            (assert (>= (+ y1 (- y2) (- y3)) 0))
            (assert (>= (+ (- y1) (- y4)) 0))
            (minimize (+ y0 y1 y2 y3 y4))
            (check-sat)
            (get-model)""", BoundedRun.encodeRepeatableVectorQuery(flat));
        // Depth 0 asks the property of M0 itself.
        assertEquals("""
            ; Bounded run (VER-019): 0 steps of the exact step relation from M0, idle
            ; only at the end; sat = a run to a violating marking.
            (set-logic QF_LIA)
            (assert (and (or (< 2 1) (> 0 0) (> 0 0))
                     (or (< 1 1))
                     (or (< 0 1) (< 0 1))
                     (or (< 0 1) (> 0 0))
                     (or (< 1 1))
                     (or (>= 0 1) (>= 0 1) (>= 1 1))))
            (check-sat)
            (get-model)""",
            BoundedRun.encodeBoundedRun(flat, initial, SmtProperty.deadlockFree(), queue.sinks(true), List.of(), 0));

        // A transition that can never fire contributes no row; clearing arcs count at their weight.
        var clearing = clearing();
        int[] start = {1, 1, 0, 3, 0, 0};
        assertTrue(BoundedRun.encodeRankingQuery(clearing, start).contains("""
            (assert (<= (+ (- r1) r5) (- 1)))
            (assert (<= (+ (* (- 2) r3) r4) (- 1)))
            (assert (<= (+ r2 r3 (- r4) (* (- 2) r5)) (- 1)))
            (minimize (+ r0 r1 (* 3 r3)))"""));
        // Three nested `ite`s, the first toucher outermost, in the order TypeScript nests them.
        String script = BoundedRun.encodeBoundedRun(clearing, start, SmtProperty.deadlockFree(), Set.of(), List.of(), 1);
        assertTrue(script.contains("(assert (= m1_5 (ite (= s0 0) (+ 0 1) (ite (= s0 2) 0 (ite (= s0 3) (- 0 1) 0)))))"), script);
        assertTrue(script.contains("(assert (=> (= s0 0) (and (>= 1 1) (= 0 0) (>= 1 1))))"), script);

        assertTrue(BoundedRun.encodeRepeatableVectorQuery(ring().flat()).contains(
            "(assert (>= (+ (- y0) y2) 0))\n(assert (>= (+ y0 (- y1)) 0))\n(assert (>= (+ y1 (- y2)) 0))\n"));
    }

    // ==================== bounded model check ====================

    @Test
    void encodesABoundedRunWithOneSelectorPerStepAndReplaysOnlyARealFiringSequence() {
        var queue = queueAndBundle(1, true);
        var flat = queue.flat();
        int[] initial = AbstractReplayer.toVector(flat, queue.m0());
        var sinks = queue.sinks(true);
        String script = BoundedRun.encodeBoundedRun(flat, initial, SmtProperty.deadlockFree(), sinks, List.of(), 2);
        int transitions = flat.transitionCount();
        assertTrue(script.contains("(declare-const s1 Int)"));
        assertTrue(script.contains("(assert (=> (= s0 " + transitions + ") (= s1 " + transitions + ")))"));
        // The ite chains keep one nesting order at every step: step 1 reads the same order as step 0.
        assertEquals("""
            ; Bounded run (VER-019): 2 steps of the exact step relation from M0, idle
            ; only at the end; sat = a run to a violating marking.
            (set-logic QF_LIA)
            (declare-const s0 Int)
            (declare-const s1 Int)
            (declare-const m1_0 Int)
            (declare-const m1_1 Int)
            (declare-const m1_2 Int)
            (declare-const m1_3 Int)
            (declare-const m1_4 Int)
            (declare-const m1_5 Int)
            (declare-const m2_0 Int)
            (declare-const m2_1 Int)
            (declare-const m2_2 Int)
            (declare-const m2_3 Int)
            (declare-const m2_4 Int)
            (declare-const m2_5 Int)
            (assert (and (>= s0 0) (<= s0 5)))
            (assert (=> (= s0 5) (= s1 5)))
            (assert (=> (= s0 0) (and (>= 1 1) (= 0 0) (= 0 0))))
            (assert (=> (= s0 1) (>= 1 1)))
            (assert (=> (= s0 2) (and (>= 0 1) (>= 0 1))))
            (assert (=> (= s0 3) (and (>= 0 1) (= 0 0))))
            (assert (=> (= s0 4) (>= 1 1)))
            (assert (= m1_0 (ite (= s0 0) (- 1 1) 1)))
            (assert (= m1_1 (ite (= s0 4) (+ 0 1) 0)))
            (assert (= m1_2 (ite (= s0 2) (+ 0 1) (ite (= s0 3) (+ 0 1) 0))))
            (assert (= m1_3 (ite (= s0 0) (+ 0 1) (ite (= s0 2) 0 0))))
            (assert (= m1_4 (ite (= s0 1) (+ 0 1) (ite (= s0 2) (- 0 1) (ite (= s0 3) (- 0 1) 0)))))
            (assert (= m1_5 (ite (= s0 1) (- 1 1) (ite (= s0 4) (- 1 1) 1))))
            (assert (and (>= s1 0) (<= s1 5)))
            (assert (=> (= s1 0) (and (>= m1_0 1) (= m1_4 0) (= m1_2 0))))
            (assert (=> (= s1 1) (>= m1_5 1)))
            (assert (=> (= s1 2) (and (>= m1_3 1) (>= m1_4 1))))
            (assert (=> (= s1 3) (and (>= m1_4 1) (= m1_3 0))))
            (assert (=> (= s1 4) (>= m1_5 1)))
            (assert (= m2_0 (ite (= s1 0) (- m1_0 1) m1_0)))
            (assert (= m2_1 (ite (= s1 4) (+ m1_1 1) m1_1)))
            (assert (= m2_2 (ite (= s1 2) (+ m1_2 1) (ite (= s1 3) (+ m1_2 1) m1_2))))
            (assert (= m2_3 (ite (= s1 0) (+ m1_3 1) (ite (= s1 2) 0 m1_3))))
            (assert (= m2_4 (ite (= s1 1) (+ m1_4 1) (ite (= s1 2) (- m1_4 1) (ite (= s1 3) (- m1_4 1) m1_4)))))
            (assert (= m2_5 (ite (= s1 1) (- m1_5 1) (ite (= s1 4) (- m1_5 1) m1_5))))
            (assert (and (or (< m2_0 1) (> m2_4 0) (> m2_2 0))
                     (or (< m2_5 1))
                     (or (< m2_3 1) (< m2_4 1))
                     (or (< m2_4 1) (> m2_3 0))
                     (or (< m2_5 1))
                     (or (>= m2_3 1) (>= m2_4 1) (>= m2_5 1))))
            (check-sat)
            (get-model)""", script);

        var bad = AbstractReplayer.violationPredicate(flat, SmtProperty.deadlockFree(), sinks, List.of());
        int produce = transition(flat, "produce");
        int cancel = transition(flat, "cancel");
        int bundle = transition(flat, "bundle");
        var run = BoundedRun.replayRun(flat, initial, List.of(produce, cancel), bad);
        assertNotNull(run);
        assertEquals(List.of("produce", "cancel"), run.steps());
        assertEquals(3, run.states().size());
        assertArrayEquals(initial, run.states().getFirst());
        assertNull(BoundedRun.replayRun(flat, initial, List.of(bundle), bad));
        // A run that ends anywhere but a violation is not one.
        assertNull(BoundedRun.replayRun(flat, initial, List.of(produce), bad));
        assertEquals(List.of(produce), BoundedRun.decodeBoundedRun(
            "sat\n(\n  (define-fun s0 () Int\n    " + produce + ")\n  (define-fun s1 () Int\n    " + transitions + ")\n)",
            transitions, 2));
    }

    /** A bounded injection's cap follows every step, as {@code envBounds(M')} does in the encoder; an unbounded one carries none. */
    @Test
    void capsABoundedInjectionAfterEveryStepAndReplaysAgainstTheCap() {
        var bounded = gated(EnvironmentAnalysisMode.bounded(2));
        int[] initial = {0, 0, 0, 0, 1};
        Set<Place<?>> done = Set.of(place("done"));
        String script = BoundedRun.encodeBoundedRun(bounded, initial, SmtProperty.deadlockFree(), done, List.of(), 2);
        assertTrue(script.contains("(assert (= m1_4 (ite (= s0 0) (- 1 1) 1)))\n(assert (<= m1_3 2))\n"), script);
        assertTrue(script.contains("(assert (= m2_4 (ite (= s1 0) (- m1_4 1) m1_4)))\n(assert (<= m2_3 2))\n(assert "), script);
        var unbounded = gated(EnvironmentAnalysisMode.alwaysAvailable());
        assertFalse(BoundedRun.encodeBoundedRun(unbounded, initial, SmtProperty.deadlockFree(), done, List.of(), 2)
            .contains("(assert (<= m"));

        // A state already over the cap cannot reach a replayed step.
        int[] over = {0, 1, 0, 3, 1};
        int fill = transition(bounded, "fill");
        assertNull(BoundedRun.replayRun(bounded, over, List.of(fill), state -> true));
        assertNotNull(BoundedRun.replayRun(unbounded, over, List.of(fill), state -> true));
    }

    @Test
    void decodesModelsAsTheTypeScriptPortDoes() {
        // z3's line break before a literal, the negation form, and an index past the net.
        assertEquals(big(1, 0, 0, -2, 0), BoundedRun.decodeRanking(
            "sat\n(\n  (define-fun r0 () Int\n    1)\n  (define-fun r3 () Int\n    (- 2))\n  (define-fun r9 () Int 4)\n)", 5));
        // A malformed name, a `Real`, and a missing space are no definition of a weight.
        assertEquals(big(0, 0, 6, 0, 0), BoundedRun.decodeRanking(
            "sat\n((define-fun r+2 () Int 5) (define-fun r0 () Real 1.0) (define-fun r1 ()Int 1) (define-fun r002 () Int 6))", 5));
        assertNull(BoundedRun.decodeRanking("unsat\n(error \"model is not available\")", 5));
        // A weight of any size is read exactly, as a bigint reads it, and an index of any size is
        // past the net; the last definition of a name wins.
        String huge = "9".repeat(44);
        var decoded = BoundedRun.decodeRanking("sat\n((define-fun r0 () Int " + huge + ") (define-fun r1 () Int 1))", 5);
        assertEquals(List.of(new BigInteger(huge), BigInteger.ONE, BigInteger.ZERO, BigInteger.ZERO, BigInteger.ZERO), decoded);
        assertEquals(big(0, 3, 0, 0, 0), BoundedRun.decodeRanking(
            "sat\n((define-fun r99999999999999999999 () Int 7) (define-fun r1 () Int 2) (define-fun r1 () Int 3))", 5));

        // Only the sign of a count matters, whatever its size; `(- 0)` is zero.
        assertEquals(List.of(1, 4), BoundedRun.decodeRepeatableVector(
            "sat\n((define-fun y0 () Int 0) (define-fun y2 () Int (- 0)) (define-fun y1 () Int " + huge
                + ") (define-fun y3 () Int (- 5)) (define-fun y4 () Int 1 ) (define-fun y5 () Int 1))", 5));
        assertNull(BoundedRun.decodeRepeatableVector("sat\n((define-fun y0 () Int 0))", 5));

        // The run stops at the first idle step; `(- 0)` selects transition 0.
        String reply = "sat\n((define-fun s0 () Int 2) (define-fun s1 () Int (- 0)) (define-fun s2 () Int 3) (define-fun s3 () Int 0))";
        assertEquals(List.of(2, 0), BoundedRun.decodeBoundedRun(reply, 3, 2));
        assertEquals(List.of(2, 0), BoundedRun.decodeBoundedRun(reply, 3, 4));
        // A selector too large for any integer type, or negative, is idle.
        assertEquals(List.of(1), BoundedRun.decodeBoundedRun(
            "sat\n((define-fun s0 () Int 1) (define-fun s1 () Int " + huge + ") (define-fun s2 () Int 0))", 3, 4));
        assertEquals(List.of(), BoundedRun.decodeBoundedRun("sat\n((define-fun s1 () Int 1) (define-fun s0 () Int (- 1)))", 3, 2));
        // No selector at a positive depth is no run; depth 0 needs none.
        assertNull(BoundedRun.decodeBoundedRun("sat\n((define-fun s5 () Int 1))", 3, 4));
        assertEquals(List.of(), BoundedRun.decodeBoundedRun("sat\n((define-fun m0 () Int 1))", 3, 0));
    }

    // ==================== the phase ====================

    /** A scripted solver: answers by the script's first line, records every call. */
    static final class Stub implements FiringBoundSolver {
        final Object ranking;
        final IntFunction<Object> bmc;
        Object vector = "unknown";
        final List<String> labels = new ArrayList<>();
        final List<Phase> phases = new ArrayList<>();
        final List<Long> timeouts = new ArrayList<>();

        /** {@code ranking} and each {@code bmc} answer are a reply, or an exception to throw. */
        Stub(Object ranking, IntFunction<Object> bmc) {
            this.ranking = ranking;
            this.bmc = bmc;
        }

        @Override
        public String run(String script, Phase phase, long timeoutMs) throws Exception {
            String header = script.lines().findFirst().orElse("");
            String label;
            Object answer;
            if (header.startsWith("; Firing bound")) {
                label = "ranking";
                answer = ranking;
            } else if (header.startsWith("; No firing bound")) {
                label = "vector";
                answer = vector;
            } else {
                int depth = Integer.parseInt(header.substring("; Bounded run (VER-019): ".length()).split(" ")[0]);
                label = "bmc " + depth;
                answer = bmc.apply(depth);
            }
            labels.add(label);
            phases.add(phase);
            timeouts.add(timeoutMs);
            if (answer instanceof Exception e) {
                throw e;
            }
            return (String) answer;
        }
    }

    /** {@code budget + s + 2*src} on the queue without cancel: places budget, out, q, s, src. */
    static final String QUEUE_RANKING = "sat\n((define-fun r0 () Int 1) (define-fun r3 () Int 1) (define-fun r4 () Int 2))";
    /** The same ranking on the cancellable queue: places budget, cancelled, out, q, s, src. */
    static final String CANCEL_RANKING = "sat\n((define-fun r0 () Int 1) (define-fun r4 () Int 1) (define-fun r5 () Int 2))";

    static FiringBoundOutcome phase(QueueAndBundle queue, boolean cancellable, Stub stub, Options options) {
        return BoundedRun.runFiringBoundPhase(queue.flat(), queue.m0(), SmtProperty.deadlockFree(),
            queue.sinks(cancellable), List.of(), stub, options);
    }

    static DepthStep step(int depth, DepthAnswer answer) {
        return new DepthStep(depth, answer);
    }

    static <T extends FiringBoundOutcome> T as(Class<T> kind, FiringBoundOutcome outcome) {
        assertInstanceOf(kind, outcome, () -> "got " + outcome);
        return kind.cast(outcome);
    }

    @Test
    void provesAtTheBoundAfterDoublingAndStopsAtTheDepthLimit() {
        var queue = queueAndBundle(12, false);
        var stub = new Stub(QUEUE_RANKING, d -> "unsat");
        var bound = new FiringBound(big(1, 0, 0, 1, 2), BigInteger.valueOf(14));
        assertEquals(new FiringBoundOutcome.Proven(bound, List.of(step(8, DepthAnswer.UNSAT), step(14, DepthAnswer.UNSAT))),
            phase(queue, false, stub, Options.DEFAULT));
        assertEquals(List.of("ranking", "bmc 8", "bmc 14"), stub.labels);
        assertEquals(List.of(Phase.RANKING, Phase.BMC, Phase.BMC), stub.phases);
        assertEquals("ranking", Phase.RANKING.label());
        assertEquals("bmc", Phase.BMC.label());
        assertTrue(stub.timeouts.stream().allMatch(t -> t > 0 && t <= 60_000), stub.timeouts::toString);

        assertEquals(new FiringBoundOutcome.Inconclusive("the firing bound 14 exceeds the depth limit 8", bound,
                List.of(step(8, DepthAnswer.UNSAT))),
            phase(queue, false, new Stub(QUEUE_RANKING, d -> "unsat"), Options.DEFAULT.withMaxDepth(8)));
        assertEquals(new FiringBoundOutcome.Inconclusive("the firing bound 14 exceeds the depth limit 0", bound,
                List.of(step(0, DepthAnswer.UNSAT))),
            phase(queue, false, new Stub(QUEUE_RANKING, d -> "unsat"), Options.DEFAULT.withMaxDepth(0)));

        // A bound below the first depth is model-checked at the bound itself.
        var empty = queueAndBundle(0, false);
        var proven = as(FiringBoundOutcome.Proven.class, phase(empty, false, new Stub(QUEUE_RANKING, d -> "unsat"), Options.DEFAULT));
        assertEquals(List.of(step(2, DepthAnswer.UNSAT)), proven.depths());
    }

    @Test
    void reportsARunOnlyOnceItReplays() {
        var queue = queueAndBundle(1, true);
        var flat = queue.flat();
        int produce = transition(flat, "produce");
        int cancel = transition(flat, "cancel");
        int bundle = transition(flat, "bundle");
        var stub = new Stub(CANCEL_RANKING, d -> "sat\n((define-fun s0 () Int " + produce
            + ") (define-fun s1 () Int " + cancel + ") (define-fun s2 () Int 5))");
        var violated = as(FiringBoundOutcome.Violated.class, phase(queue, true, stub, Options.DEFAULT));
        assertEquals(BigInteger.valueOf(3), violated.bound().bound());
        assertEquals(List.of(step(3, DepthAnswer.SAT)), violated.depths());
        assertEquals(List.of("produce", "cancel"), violated.steps());
        assertEquals(1, violated.states().getLast()[indexOf(flat, "q")]);

        assertEquals(new FiringBoundOutcome.Inconclusive("the bounded run did not replay under the exact semantics",
                new FiringBound(big(1, 0, 0, 0, 1, 2), BigInteger.valueOf(3)), List.of(step(3, DepthAnswer.SAT))),
            phase(queue, true, new Stub(CANCEL_RANKING, d -> "sat\n((define-fun s0 () Int " + bundle + "))"), Options.DEFAULT));
        // A sat reply with no selector is no run either.
        var noRun = as(FiringBoundOutcome.Inconclusive.class,
            phase(queue, true, new Stub(CANCEL_RANKING, d -> "sat"), Options.DEFAULT));
        assertEquals("the bounded run did not replay under the exact semantics", noRun.reason());
    }

    @Test
    void keepsEveryAnsweredDepthWhenALaterOneAnswersUnknown() {
        var queue = queueAndBundle(12, false);
        var unknown = as(FiringBoundOutcome.Inconclusive.class,
            phase(queue, false, new Stub(QUEUE_RANKING, d -> d == 8 ? "unsat" : "unknown"), Options.DEFAULT));
        assertEquals("the bounded run at depth 14 answered unknown", unknown.reason());
        assertEquals(BigInteger.valueOf(14), unknown.bound().bound());
        assertEquals(List.of(step(8, DepthAnswer.UNSAT)), unknown.depths());

        var failed = as(FiringBoundOutcome.Inconclusive.class,
            phase(queue, false, new Stub(QUEUE_RANKING, d -> new Exception("z3 hard timeout after 3s")), Options.DEFAULT));
        assertEquals("z3 hard timeout after 3s", failed.reason());
        assertTrue(failed.depths().isEmpty());
    }

    @Test
    void namesTheRepeatableVectorWhenNoRankingExists() {
        var ring = ring();
        var property = SmtProperty.placeBound(ring.p0(), 1);
        var stub = new Stub("unsat", d -> fail("no bounded run without a bound"));
        stub.vector = "sat\n((define-fun y0 () Int 1) (define-fun y2 () Int 1) (define-fun y1 () Int 1))";
        assertEquals(new FiringBoundOutcome.Unbounded(List.of(0, 1, 2)),
            BoundedRun.runFiringBoundPhase(ring.flat(), ring.m0(), property, Set.of(), List.of(), stub));
        assertEquals(List.of("ranking", "vector"), stub.labels);
        assertEquals(List.of(Phase.RANKING, Phase.RANKING), stub.phases);

        // Without an answer from the second query the net is still unbounded, unnamed.
        for (Object vector : List.of(new Exception("Z3 error: (error \"boom\")"), "unsat", "unknown")) {
            stub.vector = vector;
            assertEquals(new FiringBoundOutcome.Unbounded(null),
                BoundedRun.runFiringBoundPhase(ring.flat(), ring.m0(), property, Set.of(), List.of(), stub));
        }
    }

    @Test
    void stepsAsideOnInjectionAnUnknownRankingAFailedReCheckOrASpentBudget() {
        var queue = queueAndBundle(3, false);

        // The gate is the DECLARED environment: a declared place the net never reads refuses the
        // phase as surely as one it does, and nothing is asked.
        var elsewhere = EnvironmentPlace.of(place("elsewhere"));
        var declared = NetFlattener.flatten(queue.net(), Set.of(elsewhere), EnvironmentAnalysisMode.alwaysAvailable());
        assertTrue(SmtEncoder.resolveEnvInjection(declared).isEmpty());
        var stub = new Stub(QUEUE_RANKING, d -> fail("not asked"));
        assertEquals(new FiringBoundOutcome.Inconclusive("environment injection has no firing bound", null, List.of()),
            BoundedRun.runFiringBoundPhase(declared, queue.m0(), SmtProperty.deadlockFree(), queue.sinks(false),
                List.of(), stub));
        assertTrue(stub.labels.isEmpty());
        var gated = gated(EnvironmentAnalysisMode.alwaysAvailable());
        assertEquals(new FiringBoundOutcome.Inconclusive("environment injection has no firing bound", null, List.of()),
            BoundedRun.runFiringBoundPhase(gated, MarkingState.builder().tokens(place("start"), 1).build(),
                SmtProperty.deadlockFree(), Set.of(place("done")), List.of(), stub));
        // Ignored, the declaration injects nothing, and the phase runs.
        var ignored = NetFlattener.flatten(queue.net(), Set.of(elsewhere), EnvironmentAnalysisMode.ignore());
        assertInstanceOf(FiringBoundOutcome.Proven.class, BoundedRun.runFiringBoundPhase(ignored, queue.m0(),
            SmtProperty.deadlockFree(), queue.sinks(false), List.of(), new Stub(QUEUE_RANKING, d -> "unsat")));

        assertEquals(new FiringBoundOutcome.Inconclusive("the ranking query answered unknown", null, List.of()),
            phase(queue, false, new Stub("unknown", d -> fail("not asked")), Options.DEFAULT));
        assertEquals(new FiringBoundOutcome.Inconclusive("the ranking query answered unknown", null, List.of()),
            phase(queue, false, new Stub("", d -> fail("not asked")), Options.DEFAULT));

        // No weight on s: bundleEmpty lowers nothing, so the model is not a ranking.
        var reCheck = new FiringBoundOutcome.Inconclusive("the ranking failed the exact re-check", null, List.of());
        assertEquals(reCheck, phase(queue, false,
            new Stub("sat\n((define-fun r0 () Int 1) (define-fun r4 () Int 2))", d -> fail("not asked")), Options.DEFAULT));
        assertEquals(reCheck, phase(queue, false,
            new Stub("sat\n((define-fun y0 () Int 1))", d -> fail("not asked")), Options.DEFAULT));

        var tooLarge = as(FiringBoundOutcome.Inconclusive.class, phase(queue, false, new Stub(
            "sat\n((define-fun r0 () Int 9007199254740992) (define-fun r3 () Int 1) (define-fun r4 () Int 2))",
            d -> fail("not asked")), Options.DEFAULT));
        assertEquals("firing bound 27021597764222978 is too large", tooLarge.reason());
        assertEquals(new BigInteger("27021597764222978"), tooLarge.bound().bound());

        var spent = new Stub(QUEUE_RANKING, d -> fail("not asked"));
        assertEquals(new FiringBoundOutcome.Inconclusive("time budget of 0 ms exhausted", null, List.of()),
            phase(queue, false, spent, Options.DEFAULT.withBudgetMs(0)));
        assertTrue(spent.labels.isEmpty());
    }

    @Test
    void rethrowsADefectInTheSolverRatherThanReportIt() {
        var queue = queueAndBundle(3, false);
        var stub = new Stub(new NullPointerException("a defect"), d -> fail("not asked"));
        assertThrows(NullPointerException.class, () -> phase(queue, false, stub, Options.DEFAULT));
        assertThrows(IllegalArgumentException.class, () -> Options.DEFAULT.withMaxDepth(-1));
    }

    /**
     * The transport {@code SmtVerifier} uses for the linear bound: one z3 process per script; an
     * {@code (error …)} other than a missing model, or a reply without a verdict line, is the
     * failure the phase reports.
     */
    static FiringBoundSolver z3() throws Exception {
        var solver = Z3Solver.resolve();
        return (script, phase, timeoutMs) -> {
            var reply = solver.run(script, phase.label(), Duration.ofMillis(timeoutMs), List.of());
            String unexpected = (reply.stdout() + "\n" + reply.stderr()).lines()
                .map(SmtText::errorLine)
                .filter(line -> line != null && !line.contains("model is not available"))
                .findFirst()
                .orElse(null);
            if (unexpected != null) {
                throw new Exception("z3 reported an error: " + unexpected);
            }
            if (SmtText.classifyFirstLine(reply.stdout()) == null) {
                throw new Exception(Z3Process.failureReason(reply, Z3Solver.timeoutMs(Duration.ofMillis(timeoutMs))));
            }
            return reply.stdout();
        };
    }

    /**
     * [VER-019]'s test derivation, at the phase: the queue's ranking gives the bound 5 and the
     * bounded run at depth 5 proves it; with the cancel alternative a replayed run violates it;
     * the ring has no ranking, and its three transitions repeat.
     */
    @Test
    @EnabledIf("z3Available")
    void decidesTheQueueAndNamesTheRingThroughZ3() throws Exception {
        var options = Options.DEFAULT.withBudgetMs(30_000);
        var property = SmtProperty.deadlockFree();

        var queue = queueAndBundle(3, false);
        var proven = as(FiringBoundOutcome.Proven.class, BoundedRun.runFiringBoundPhase(queue.flat(), queue.m0(),
            property, queue.sinks(false), List.of(), z3(), options));
        assertEquals(BigInteger.valueOf(5), proven.bound().bound());
        assertEquals("budget + s + 2*src", BoundedRun.formatRanking(queue.flat(), proven.bound()));
        assertEquals(List.of(step(5, DepthAnswer.UNSAT)), proven.depths());

        var cancellable = queueAndBundle(3, true);
        var flat = cancellable.flat();
        var violated = as(FiringBoundOutcome.Violated.class, BoundedRun.runFiringBoundPhase(flat, cancellable.m0(),
            property, cancellable.sinks(true), List.of(), z3(), options));
        assertEquals(BigInteger.valueOf(5), violated.bound().bound());
        assertEquals(List.of(step(5, DepthAnswer.SAT)), violated.depths());
        assertTrue(violated.steps().contains("cancel"), violated.steps()::toString);
        int[] last = violated.states().getLast();
        assertTrue(last[indexOf(flat, "q")] > 0);
        assertTrue(AbstractReplayer.violationPredicate(flat, property, cancellable.sinks(true), List.of()).test(last));

        var ring = ring();
        assertEquals(new FiringBoundOutcome.Unbounded(List.of(0, 1, 2)), BoundedRun.runFiringBoundPhase(ring.flat(),
            ring.m0(), SmtProperty.placeBound(ring.p0(), 1), Set.of(), List.of(), z3(), options));
    }
}
