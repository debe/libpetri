package org.libpetri.smt.z3;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.internal.VerificationDeadline;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.SmtVerifier;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.z3.BoundedRun.FiringBoundSolver;
import org.libpetri.smt.z3.BoundedRun.Phase;
import org.libpetri.smt.z3.BoundedRun.WitnessOutcome;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.smt.z3.StateEquationNets.*;

/**
 * [VER-025] the bounded witness phase below the verifier: the injection steps of the bounded
 * run, their decode and replay, the trim, and the driver's outcomes. The phase through
 * {@code SmtVerifier} is {@code org.libpetri.smt.WitnessPhaseVerifierTest}'s.
 *
 * <p>The net is {@link BoundedRunTest#gated}: {@code fill: start → q},
 * {@code gate: sig + gateOpen → done}, {@code sig} an environment place. Flat places: done,
 * gateOpen, q, sig, start. Selectors: 0 fill, 1 gate, 2 inject(sig), 3 idle.
 */
class WitnessPhaseTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    /** gateOpen and start marked: {@code gate} waits for one injection, {@code fill} is a detour. */
    static final int[] INITIAL = {0, 1, 0, 0, 1};

    static MarkingState m0() {
        return MarkingState.builder().tokens(place("gateOpen"), 1).tokens(place("start"), 1).build();
    }

    /** {@code done >= 1}. */
    static final Predicate<int[]> DONE = state -> state[0] >= 1;

    static SmtProperty doneStaysEmpty() {
        return SmtProperty.placeBound(place("done"), 0);
    }

    static FlatNet bounded() {
        return BoundedRunTest.gated(EnvironmentAnalysisMode.bounded(2));
    }

    static String model(int... selectors) {
        var defs = new ArrayList<String>();
        for (int i = 0; i < selectors.length; i++) {
            defs.add("(define-fun s" + i + " () Int " + selectors[i] + ")");
        }
        return "sat\n(" + String.join(" ", defs) + ")";
    }

    static WitnessOutcome phase(FlatNet flat, FiringBoundSolver solver, long budgetMs, int depth) {
        return BoundedRun.runWitnessPhase(flat, m0(), doneStaysEmpty(), Set.of(), List.of(), solver, budgetMs, depth);
    }

    // ==================== the script ====================

    @Test
    void unrollsABoundedInjectionAsItsOwnSelectorAfterTheTransitions() {
        String script = BoundedRun.encodeBoundedRun(bounded(), INITIAL, doneStaysEmpty(), Set.of(), List.of(), 2);
        // Two transitions and one injection: idle is 3.
        assertTrue(script.contains("(assert (and (>= s0 0) (<= s0 3)))\n(assert (=> (= s0 3) (= s1 3)))\n"), script);
        // The injection's guard follows the transitions' guards; M0 is read as literals at step 0.
        assertTrue(script.contains(
            "(assert (=> (= s0 1) (and (>= 1 1) (>= 0 1))))\n(assert (=> (= s0 2) (< 0 2)))\n"), script);
        assertTrue(script.contains("(assert (=> (= s1 2) (< m1_3 2)))\n"), script);
        // sig: gate takes one, the injection adds one, nested from the last toucher inward.
        assertTrue(script.contains(
            "(assert (= m1_3 (ite (= s0 1) (- 0 1) (ite (= s0 2) (+ 0 1) 0))))\n"), script);
        assertTrue(script.contains(
            "(assert (= m2_3 (ite (= s1 1) (- m1_3 1) (ite (= s1 2) (+ m1_3 1) m1_3))))\n"), script);
    }

    @Test
    void anUnboundedInjectionHasAnUpdateAndNoGuard() {
        var unbounded = BoundedRunTest.gated(EnvironmentAnalysisMode.alwaysAvailable());
        String script = BoundedRun.encodeBoundedRun(unbounded, INITIAL, doneStaysEmpty(), Set.of(), List.of(), 2);
        assertTrue(script.contains("(<= s0 3)"), script);
        assertFalse(script.contains("(assert (=> (= s0 2)"), script);
        assertTrue(script.contains("(ite (= s0 2) (+ 0 1) 0)"), script);
    }

    /** [VER-019] is unchanged: a net that injects nothing keeps today's selector range and chains. */
    @Test
    void aNetWithoutInjectionKeepsTheTransitionOnlyScript() {
        var ignored = BoundedRunTest.gated(EnvironmentAnalysisMode.ignore());
        String script = BoundedRun.encodeBoundedRun(ignored, INITIAL, doneStaysEmpty(), Set.of(), List.of(), 2);
        assertTrue(script.contains("(assert (and (>= s0 0) (<= s0 2)))\n(assert (=> (= s0 2) (= s1 2)))\n"), script);
        assertTrue(script.contains("(assert (= m1_3 (ite (= s0 1) (- 0 1) 0)))\n"), script);
        assertFalse(script.contains("(= s0 3)"), script);
    }

    // ==================== decode and replay ====================

    @Test
    void decodesAnInjectionSelectorAsAStepOnlyWithTheInjectionsCounted() {
        assertEquals(List.of(2, 1), BoundedRun.decodeBoundedRun(model(2, 1), 3, 2));
        // Read against the transitions alone, the injection is an idle step and the run is lost.
        assertEquals(List.of(), BoundedRun.decodeBoundedRun(model(2, 1), 2, 2));
    }

    @Test
    void replaysAnInjectionStepUnderItsBoundAndLabelsIt() {
        var run = BoundedRun.replayRun(bounded(), INITIAL, List.of(2, 1), DONE);
        assertNotNull(run);
        assertEquals(List.of("inject(sig)", "gate"), run.steps());
        assertArrayEquals(new int[] {0, 1, 0, 1, 1}, run.states().get(1));
        assertArrayEquals(new int[] {1, 0, 0, 0, 1}, run.states().get(2));

        // The bound is 2: a third injection is not a step of the net.
        assertNotNull(BoundedRun.replayRun(bounded(), INITIAL, List.of(2, 2), state -> true));
        assertNull(BoundedRun.replayRun(bounded(), INITIAL, List.of(2, 2, 2), state -> true));
        var unbounded = BoundedRunTest.gated(EnvironmentAnalysisMode.alwaysAvailable());
        assertNotNull(BoundedRun.replayRun(unbounded, INITIAL, List.of(2, 2, 2), state -> true));

        // gate before the injection is not enabled, and a run that stops short does not violate.
        assertNull(BoundedRun.replayRun(bounded(), INITIAL, List.of(1, 2), DONE));
        assertNull(BoundedRun.replayRun(bounded(), INITIAL, List.of(2), DONE));
    }

    // ==================== the trim ====================

    @Test
    void trimsTheStepsARunDoesNotNeedAndKeepsItsOrder() {
        assertEquals(List.of(2, 1), BoundedRun.trimRun(bounded(), INITIAL, List.of(2, 2, 1, 0), DONE));
        assertEquals(List.of(2, 1), BoundedRun.trimRun(bounded(), INITIAL, List.of(0, 2, 1, 2), DONE));
        // Nothing to drop: every step is needed.
        assertEquals(List.of(2, 1), BoundedRun.trimRun(bounded(), INITIAL, List.of(2, 1), DONE));
        // M0 violates: no step is needed at all.
        assertEquals(List.of(), BoundedRun.trimRun(bounded(), INITIAL, List.of(0, 2), state -> true));
    }

    /**
     * {@code M0} violates and the model walks the ring twice. No single step can be dropped from
     * a cycle, so only the cut at the first violating marking gives the empty run.
     */
    @Test
    void anInitialViolationIsTheEmptyRunWhateverTheModelWalked() {
        var ring = BoundedRunTest.ring();
        int[] initial = {1, 0, 0};
        Predicate<int[]> p0Marked = state -> state[0] >= 1;
        assertNotNull(BoundedRun.replayRun(ring.flat(), initial, List.of(0, 1, 2, 0, 1, 2), p0Marked));
        assertEquals(List.of(), BoundedRun.trimRun(ring.flat(), initial, List.of(0, 1, 2, 0, 1, 2), p0Marked));
    }

    /** A run that passes a violating marking and wanders on is cut where it first violates. */
    @Test
    void cutsARunAtTheFirstViolatingMarking() {
        var ring = BoundedRunTest.ring();
        int[] initial = {1, 0, 0};
        Predicate<int[]> p1Marked = state -> state[1] >= 1;
        assertEquals(List.of(0), BoundedRun.trimRun(ring.flat(), initial, List.of(0, 1, 2, 0), p1Marked));
    }

    /**
     * Dropping the injection leaves {@code gate} disabled, but the run without it already
     * violates after {@code fill}: the steps past the first violation are not taken, so they
     * need not be enabled.
     */
    @Test
    void acceptsADropWhoseTailNoLongerFires() {
        // q marked while sig is empty: after inject, fill, gate; or after fill alone.
        Predicate<int[]> queuedWithoutSignal = state -> state[2] >= 1 && state[3] == 0;
        assertNotNull(BoundedRun.replayRun(bounded(), INITIAL, List.of(2, 0, 1), queuedWithoutSignal));
        assertNull(BoundedRun.replayRun(bounded(), INITIAL, List.of(0, 1), queuedWithoutSignal));
        assertEquals(List.of(0), BoundedRun.trimRun(bounded(), INITIAL, List.of(2, 0, 1), queuedWithoutSignal));
    }

    /**
     * One pass is not enough: with {@code fill} in the run both injections are needed, and
     * {@code fill} is the last step a pass tries. Only the next pass can drop the injection
     * that the first one made needless.
     */
    @Test
    void aLaterPassDropsWhatAnEarlierDropMadeNeedless() {
        // done marked, and either nothing queued or a signal left over.
        Predicate<int[]> bad = state -> state[0] >= 1 && (state[2] == 0 || state[3] >= 1);
        assertNotNull(BoundedRun.replayRun(bounded(), INITIAL, List.of(0, 2, 2, 1), bad));
        // With fill, neither injection can go: gate would leave q marked and sig empty.
        assertNull(BoundedRun.replayRun(bounded(), INITIAL, List.of(0, 2, 1), bad));
        assertEquals(List.of(2, 1), BoundedRun.trimRun(bounded(), INITIAL, List.of(0, 2, 2, 1), bad));
    }

    /** [VER-013]: the trim polls the deadline before every candidate, so a spent budget stops it. */
    @Test
    void theTrimStopsAtASpentTotalBudget() {
        var spent = new VerificationDeadline(0);
        assertThrows(VerificationDeadline.Exhausted.class, () ->
            ScopedValue.where(VerificationDeadline.carrier(), spent)
                .call(() -> BoundedRun.trimRun(bounded(), INITIAL, List.of(2, 2, 1, 0), DONE)));
        // Outside a verify() call no deadline is bound, and the trim runs to its end.
        assertEquals(List.of(2, 1), BoundedRun.trimRun(bounded(), INITIAL, List.of(2, 2, 1, 0), DONE));
    }

    @Test
    void aRunThatDoesNotViolateIsADefectInTheCaller() {
        assertThrows(IllegalArgumentException.class,
            () -> BoundedRun.trimRun(bounded(), INITIAL, List.of(2), DONE));
    }

    // ==================== the driver ====================

    @Test
    void aSatRunIsReplayedTrimmedAndReported() {
        var phases = new ArrayList<Phase>();
        var headers = new ArrayList<String>();
        var outcome = phase(bounded(), (script, phase, timeoutMs) -> {
            phases.add(phase);
            headers.add(script.lines().findFirst().orElse(""));
            // Padded as the solver pads: a second injection and the fill detour.
            return model(2, 2, 1, 0);
        }, 60_000, 4);
        var violated = assertInstanceOf(WitnessOutcome.Violated.class, outcome);
        assertEquals(List.of("inject(sig)", "gate"), violated.steps());
        assertEquals(3, violated.states().size());
        assertTrue(Arrays.equals(INITIAL, violated.states().getFirst()));
        assertEquals(List.of(Phase.WITNESS), phases);
        assertEquals("witness", Phase.WITNESS.label());
        assertEquals(List.of("; Bounded run (VER-019): 4 steps of the exact step relation from M0, idle"), headers);
    }

    @Test
    void unsatIsNoRunAndNeverAProof() {
        assertEquals(new WitnessOutcome.NoRun(), phase(bounded(), (script, phase, timeoutMs) -> "unsat", 60_000, 4));
    }

    @Test
    void everyOtherAnswerIsInconclusiveWithItsReason() {
        assertEquals(new WitnessOutcome.Inconclusive("the bounded run at depth 4 answered unknown"),
            phase(bounded(), (script, phase, timeoutMs) -> "unknown", 60_000, 4));
        assertEquals(new WitnessOutcome.Inconclusive("z3 crashed"),
            phase(bounded(), (script, phase, timeoutMs) -> { throw new Exception("z3 crashed"); }, 60_000, 4));
        // gate first: the model is not a run of the net, so it is not believed.
        assertEquals(new WitnessOutcome.Inconclusive("the bounded run did not replay under the exact semantics"),
            phase(bounded(), (script, phase, timeoutMs) -> model(1, 2, 3, 3), 60_000, 4));
        // A sat reply without a selector is not a run either.
        assertEquals(new WitnessOutcome.Inconclusive("the bounded run did not replay under the exact semantics"),
            phase(bounded(), (script, phase, timeoutMs) -> "sat\n()", 60_000, 4));
    }

    @Test
    void aSpentBudgetSendsNothing() {
        assertEquals(new WitnessOutcome.Inconclusive("time budget of 0 ms exhausted"),
            phase(bounded(), (script, phase, timeoutMs) -> { throw new AssertionError("no solver call expected"); }, 0, 4));
    }

    @Test
    void theQueryGetsWhatIsLeftOfTheBudget() {
        var timeouts = new ArrayList<Long>();
        phase(bounded(), (script, phase, timeoutMs) -> {
            timeouts.add(timeoutMs);
            return "unsat";
        }, 3_600_000, 4);
        // An hour, so that no load on the host can spend it before the query is sent.
        assertEquals(1, timeouts.size());
        assertTrue(timeouts.getFirst() > 0 && timeouts.getFirst() <= 3_600_000, timeouts.toString());
    }

    @Test
    void aDepthBelowOneIsADefectInTheCaller() {
        var e = assertThrows(IllegalArgumentException.class,
            () -> phase(bounded(), (script, phase, timeoutMs) -> "unsat", 60_000, 0));
        assertEquals("depth must be positive, got 0", e.getMessage());
    }

    @Test
    @EnabledIf("z3Available")
    void theSolverFindsTheRunThatNeedsAnInjection() throws Exception {
        var violated = assertInstanceOf(WitnessOutcome.Violated.class,
            phase(bounded(), BoundedRunTest.z3(), 60_000, BoundedRun.DEFAULT_WITNESS_DEPTH));
        assertEquals(List.of("inject(sig)", "gate"), violated.steps());
        // Under Ignore the flat net has no injection step, and gate never fires.
        assertEquals(new WitnessOutcome.NoRun(), phase(BoundedRunTest.gated(EnvironmentAnalysisMode.ignore()),
            BoundedRunTest.z3(), 60_000, BoundedRun.DEFAULT_WITNESS_DEPTH));
    }
}
