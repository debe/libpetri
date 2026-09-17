package org.libpetri.smt.z3;

import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Transition;
import org.libpetri.smt.SmtVerifier;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.z3.StateEquationQuery.MarkingInequality;
import org.libpetri.smt.z3.StateEquationQuery.Origin;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

import java.math.BigInteger;
import java.time.Duration;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.smt.z3.StateEquationNets.*;

/**
 * [VER-018] inductive-inequality refinement: the two synthesis queries, the model decoder
 * and the exact re-check. Mirrors the inductive case of
 * {@code typescript/tests/verification/state-equation-phase.test.ts}; the row assertions are
 * lines of the scripts that were diffed byte-identical against the TypeScript encoders.
 */
class InvariantSynthesisTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    /**
     * Every clearing and guard shape at once: {@code t1} resets the place it inhibits and reads
     * {@code gate}, {@code t2} takes two of {@code x} and reads {@code gate}, {@code t3} takes
     * {@code atLeast(2, z)} and resets {@code x}, and {@code t4} reads the place it inhibits, so
     * it can never fire. Flat places: gate, p, r, x, y, z.
     */
    private static FlatNet clearing() {
        var p = place("p");
        var gate = place("gate");
        var r = place("r");
        var x = place("x");
        var y = place("y");
        var z = place("z");
        return flatten(PetriNet.builder("clearing").transitions(
            Transition.builder("t1").inputs(In.one(p)).read(gate).reset(r).inhibitor(r).outputs(Out.place(z)).build(),
            Transition.builder("t2").inputs(In.exactly(2, x)).read(gate).outputs(Out.place(y)).build(),
            Transition.builder("t3").inputs(In.one(y), In.atLeast(2, z)).reset(x).outputs(Out.and(r, x)).build(),
            Transition.builder("t4").inputs(In.one(z)).read(p).inhibitor(p).outputs(Out.place(p)).build()
        ).build());
    }

    private static long count(String haystack, String needle) {
        return haystack.split(java.util.regex.Pattern.quote(needle), -1).length - 1;
    }

    @Test
    void acceptsTheJoinInequalityAsInductiveAndRejectsAWeakerCousin() {
        var join = joinWithSkip();
        var flat = join.flat();
        int[] initial = AbstractReplayer.toVector(flat, join.m0());
        assertTrue(InvariantSynthesis.checkInductiveExact(flat, initial,
            inequality(flat, 0, "hasdata", 1, "ready0", -1, "ready1", -1)));
        // Arm B raises hasdata without ready0.
        assertFalse(InvariantSynthesis.checkInductiveExact(flat, initial,
            inequality(flat, 0, "hasdata", 1, "ready0", -1)));
        // A mis-sized inequality is rejected rather than read short.
        assertFalse(InvariantSynthesis.checkInductiveExact(flat, initial,
            new MarkingInequality(List.of(BigInteger.ZERO), BigInteger.ZERO, Origin.INDUCTIVE)));
    }

    /**
     * Why the relative inequality is never re-checked here: {@code 3*out + q <= 3} holds only
     * where the marking equation does, and {@code produce} raises {@code q} from a marking the
     * exact step relation alone does not bound.
     */
    @Test
    void rejectsTheRelativeQueueBoundItDoesNotReCheck() {
        var queue = queueAndBundle(3, false);
        var flat = queue.flat();
        int[] initial = AbstractReplayer.toVector(flat, queue.m0());
        var relative = inequality(flat, 3, "out", 3, "q", 1);
        assertEquals("3*out + q <= 3", StateEquationQuery.formatInequality(flat, relative));
        assertFalse(InvariantSynthesis.checkInductiveExact(flat, initial, relative));
        assertTrue(InvariantSynthesis.checkInductiveExact(flat, initial, inequality(flat, 1, "src", 1, "s", 1, "out", 1)));
    }

    /** {@code sig + done <= 1} is kept by both firings, and broken once the environment may inject into {@code sig}. */
    @Test
    void aPositiveWeightOnAnInjectedPlaceFailsTheCheck() {
        var closed = gatedStrand(false);
        var open = gatedStrand(true);
        var bound = inequality(open.flat(), 1, "sig", 1, "done", 1);
        assertTrue(InvariantSynthesis.checkInductiveExact(closed.flat(), closed.initial(), bound));
        assertFalse(InvariantSynthesis.checkInductiveExact(open.flat(), open.initial(), bound));
    }

    @Test
    void encodesOneConsecutionRowPerTransitionThatCanFire() {
        var join = joinWithSkip();
        var flat = join.flat();
        int[] initial = AbstractReplayer.toVector(flat, join.m0());
        String script = InvariantSynthesis.encodeInductiveInequality(flat, initial,
            candidate(flat, "hasdata", 1, "skipped", 1));
        assertTrue(script.startsWith(
            "; Inductive-inequality refinement (VER-018): a.M <= b holding at M0, kept by every\n"));
        assertTrue(script.contains("(set-logic QF_LIA)\n(declare-const a0 Int)\n"));
        assertTrue(script.contains("(declare-const b Int)\n(declare-const upos Int)\n"));
        assertTrue(script.contains("(assert (and (>= a0 (- 8)) (<= a0 8)))"));
        assertTrue(script.contains("(assert (= upos (+ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9)))"));
        assertTrue(script.contains("(assert (<= a9 b))"));
        assertTrue(script.contains("(assert (>= (+ a5 a8) (+ b 1)))"));
        // mergeStart clears hasdata (a5 >= 0); mergeSkip is guarded by its inhibitor (u5 free).
        assertTrue(script.contains(
            "(assert (or (and (>= a5 0) (<= (+ a4 (- a5) (- a6) (- a7)) 0)) (and (= upos u5) (<= a4 b))))"));
        assertTrue(script.contains("(assert (or (<= (+ (- a6) (- a7) a8) 0) (and (= upos u5) (<= a8 b))))"));
        assertEquals(flat.transitionCount(), count(script, "(assert (or "));
        assertTrue(script.endsWith(
            "(minimize (+ u0 w0 u1 w1 u2 w2 u3 w3 u4 w4 u5 w5 u6 w6 u7 w7 u8 w8 u9 w9))\n(check-sat)\n(get-model)"));

        // A transition that can never fire contributes nothing, and the weight bound is honoured.
        var cl = clearing();
        script = InvariantSynthesis.encodeInductiveInequality(cl, marking(cl, "p", 1, "gate", 1, "x", 3),
            candidate(cl, "r", 1, "y", 2, "z", 1), 3);
        assertEquals(3, count(script, "(assert (or "));
        assertTrue(script.contains("(assert (and (>= a0 (- 3)) (<= a0 3)))"));
        // t1 clears r while inhibiting it: post only, no sign condition, and u2 free.
        assertTrue(script.contains("(assert (or (<= (+ (- a1) a5) 0) (and (= upos u2) (<= (+ a0 a5) b))))"));

        // An injected place may not carry a positive weight.
        var open = gatedStrand(true);
        script = InvariantSynthesis.encodeInductiveInequality(open.flat(), open.initial(),
            candidate(open.flat(), "q", 1, "done", 1));
        assertTrue(script.contains("(assert (<= a3 0))\n(minimize "));
    }

    @Test
    void encodesOneFarkasWeightingOfTheEquationPerTransitionThatCanFire() {
        var join = joinWithSkip();
        var flat = join.flat();
        int[] initial = AbstractReplayer.toVector(flat, join.m0());
        String script = InvariantSynthesis.encodeRelativeInequality(flat, initial,
            candidate(flat, "hasdata", 1, "skipped", 1));
        assertTrue(script.contains("(set-logic QF_LIRA)"));
        assertFalse(script.contains("upos"));
        // hasdata's row is an upper bound (mergeStart clears it), so its weighting is signed.
        assertTrue(script.contains("(declare-const e6_9 Real)\n(assert (>= e6_5 0))\n"));
        assertTrue(script.contains("(assert (<= (+ e6_0 e6_3 (- e6_9)) 0.0))"));
        assertTrue(script.contains(
            "(assert (or (and (>= e0_0 0.0) (>= e0_1 0.0) (>= e0_2 0.0) (>= e0_3 0.0) (>= e0_4 0.0) "
                + "(>= e0_5 0.0) (>= e0_6 0.0) (>= e0_7 0.0) (>= e0_8 0.0) (>= e0_9 0.0) "
                + "(<= (+ (to_real a0) (to_real a3) (- (to_real a9))) (+ (- e0_9) e0_9))) "
                + "(and (<= (to_real a0) e0_0) (<= (to_real a1) e0_1) (<= (to_real a2) e0_2) "
                + "(<= (to_real a3) e0_3) (<= (to_real a4) e0_4) (<= (to_real a5) e0_5) "
                + "(<= (to_real a6) e0_6) (<= (to_real a7) e0_7) (<= (to_real a8) e0_8) "
                + "(<= (to_real a9) e0_9) (<= (- (+ (to_real a0) (to_real a3) (- (to_real a9))) (to_real b)) "
                + "(+ (- e0_9) (- e0_9 (to_real a9)))))))"));

        // A transition that can never fire gets no weighting.
        var cl = clearing();
        script = InvariantSynthesis.encodeRelativeInequality(cl, marking(cl, "p", 1, "gate", 1, "x", 3),
            candidate(cl, "r", 1, "y", 2, "z", 1), 3);
        assertEquals(3, count(script, "(assert (or "));
        assertFalse(script.contains("e3_"));

        // An injected place has no row: no weighting variable, and `0.0` in its place.
        var open = gatedStrand(true);
        script = InvariantSynthesis.encodeRelativeInequality(open.flat(), open.initial(),
            candidate(open.flat(), "q", 1, "done", 1));
        assertTrue(script.contains("(assert (>= (+ a0 a2) (+ b 1)))\n(assert (<= a3 0))\n(declare-const e0_0 Real)"));
        assertFalse(script.contains("_3 Real"));
        assertTrue(script.contains("(>= 0.0 0.0)"));
        assertTrue(script.contains("(<= (to_real a3) 0.0)"));
    }

    /** z3's own reply to the join query: line breaks before a literal, the negation form, and the auxiliary names. */
    @Test
    void decodesTheWeightsAndBoundOfAModel() {
        var flat = joinWithSkip().flat();
        String reply = "sat\n(\n  (define-fun w6 () Int\n    1)\n  (define-fun a7 () Int\n    (- 1))\n  "
            + "(define-fun a6 () Int\n    (- 1))\n  (define-fun a5 () Int\n    1)\n  "
            + "(define-fun b () Int\n    0)\n  (define-fun upos () Int\n    1)\n  "
            + "(define-fun u5 () Int\n    1)\n  (define-fun a0 () Int\n    0)\n)";
        var decoded = InvariantSynthesis.decodeInductiveInequality(reply, flat.placeCount());
        assertNotNull(decoded);
        assertEquals(Origin.INDUCTIVE, decoded.origin());
        assertEquals(BigInteger.ZERO, decoded.constant());
        assertEquals("hasdata <= ready0 + ready1", StateEquationQuery.formatInequality(flat, decoded));
        assertEquals(Origin.RELATIVE, decoded.withOrigin(Origin.RELATIVE).origin());
    }

    @Test
    void decodesNothingWithoutABoundAndSkipsWhatIsNotAWeight() {
        assertNull(InvariantSynthesis.decodeInductiveInequality("unsat\n(error \"model is not available\")", 2));
        assertNull(InvariantSynthesis.decodeInductiveInequality("sat\n((define-fun a0 () Int 1))", 2));
        // A weight index past the net, a real weighting and a malformed name are skipped.
        var decoded = InvariantSynthesis.decodeInductiveInequality(
            "sat\n((define-fun a9 () Int 4) (define-fun e0_1 () Real 3.0) "
                + "(define-fun a1 () Int (- 2)) (define-fun a+1 () Int 5) (define-fun b () Int 7))", 2);
        assertNotNull(decoded);
        assertEquals(List.of(BigInteger.ZERO, BigInteger.valueOf(-2)), decoded.weights());
        assertEquals(BigInteger.valueOf(7), decoded.constant());
        // Exact at any magnitude, as TypeScript's bigint is: nothing overflows.
        String huge = "1".repeat(40);
        decoded = InvariantSynthesis.decodeInductiveInequality(
            "sat\n((define-fun a0 () Int " + huge + ") (define-fun b () Int (- " + huge + ")))", 2);
        assertNotNull(decoded);
        assertEquals(new BigInteger(huge), decoded.weights().getFirst());
        assertEquals(new BigInteger(huge).negate(), decoded.constant());
    }

    private static String solve(String script) throws Exception {
        return Z3Solver.resolve().run(script, "invariant", Duration.ofSeconds(30), List.of()).stdout();
    }

    /** [VER-018] AC2's refinement, found by z3 from the Java script and re-checked exactly. */
    @Test
    @EnabledIf("z3Available")
    void synthesizesTheJoinInequalityThroughZ3() throws Exception {
        var join = joinWithSkip();
        var flat = join.flat();
        int[] initial = AbstractReplayer.toVector(flat, join.m0());
        String reply = solve(InvariantSynthesis.encodeInductiveInequality(flat, initial,
            candidate(flat, "hasdata", 1, "skipped", 1)));
        assertEquals("sat", SmtText.classifyFirstLine(reply), reply);
        var found = InvariantSynthesis.decodeInductiveInequality(reply, flat.placeCount());
        assertNotNull(found, reply);
        assertEquals("hasdata <= ready0 + ready1", StateEquationQuery.formatInequality(flat, found));
        assertTrue(InvariantSynthesis.checkInductiveExact(flat, initial, found));
    }

    /** The queue's bound exists only relative to the equation: the exact query has no answer, the relative one finds it. */
    @Test
    @EnabledIf("z3Available")
    void theQueueBoundNeedsTheEquationAsAPremise() throws Exception {
        var queue = queueAndBundle(3, false);
        var flat = queue.flat();
        int[] initial = AbstractReplayer.toVector(flat, queue.m0());
        long[] stranded = candidate(flat, "q", 1, "out", 1);
        String reply = solve(InvariantSynthesis.encodeInductiveInequality(flat, initial, stranded));
        assertEquals("unsat", SmtText.classifyFirstLine(reply), reply);
        reply = solve(InvariantSynthesis.encodeRelativeInequality(flat, initial, stranded));
        assertEquals("sat", SmtText.classifyFirstLine(reply), reply);
        var found = InvariantSynthesis.decodeInductiveInequality(reply, flat.placeCount());
        assertNotNull(found, reply);
        assertEquals("3*out + q <= 3", StateEquationQuery.formatInequality(flat, found));
        assertFalse(StateEquationQuery.holdsAt(found, stranded));
    }
}
