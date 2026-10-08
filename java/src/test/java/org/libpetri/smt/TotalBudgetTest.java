package org.libpetri.smt;

import java.time.Duration;
import java.util.List;
import java.util.Set;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [VER-013] total budget: one wall-clock limit on the whole {@code verify()} call. The z3 clamp
 * itself is pinned against a stub solver in {@link StubZ3Test}; these cover the solver-free
 * work no per-call timeout bounds, the cache rule, and the unset case.
 */
class TotalBudgetTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static Place<Object> p(String name) {
        return Place.of(name, Object.class);
    }

    /**
     * {@code k} independent toggles {@code a_i <-> b_i}: 2^k reachable markings, every one of
     * them live. Untimed, so the enumeration route takes it.
     */
    private static PetriNet toggles(int k, boolean timed) {
        var b = PetriNet.builder("toggles-" + k);
        for (int i = 0; i < k; i++) {
            var on = Transition.builder("on_" + i).inputs(In.one(p("a_" + i))).outputs(Out.place(p("b_" + i)));
            if (timed) on.timing(Timing.delayed(Duration.ofMillis(1)));
            b.transition(on.build());
            b.transition(Transition.builder("off_" + i).inputs(In.one(p("b_" + i))).outputs(Out.place(p("a_" + i))).build());
        }
        return StructureOnly.bind(b.build());
    }

    private static MarkingState allA(int k) {
        var m = MarkingState.builder();
        for (int i = 0; i < k; i++) m.tokens(p("a_" + i), 1);
        return m.build();
    }

    @Test
    @Timeout(value = 60, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    void enumerationCutByTheTotalBudget_isUnknownNamingTheBudget() {
        int k = 22; // ~4M classes: minutes of enumeration without the budget
        long t0 = System.nanoTime();
        var r = SmtVerifier.forNet(toggles(k, false)).linearBound(false).initialMarking(allA(k))
            .property(SmtProperty.placeBound(p("a_0"), 1))
            .enumerationMaxClasses(10_000_000)
            .timeout(Duration.ofSeconds(60))
            .totalBudget(Duration.ofMillis(300))
            .verify();
        long ms = (System.nanoTime() - t0) / 1_000_000;

        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, r.verdict(), r.report());
        assertEquals("total verification budget of 300 ms exhausted during state-space enumeration",
            unknown.reason());
        assertTrue(r.report().endsWith("UNKNOWN: " + unknown.reason() + "\n"), r.report());
        assertEquals(SmtVerificationResult.Route.ENUMERATION, r.route());
        assertTrue(ms < 10_000, "returned after " + ms + " ms");
    }

    @Test
    @Timeout(value = 60, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    @EnabledIf("z3Available")
    void timedCheckCutByTheTotalBudget_isTimedUndecided_verdictStands() {
        // The same toggles with one timed transition: the SMT pipeline decides the violation of
        // placeBound(b_0, 0) quickly, then the timed graph of 2^k classes runs into the deadline.
        int k = 22;
        var r = SmtVerifier.forNet(toggles(k, true)).initialMarking(allA(k))
            .property(SmtProperty.placeBound(p("b_0"), 0))
            .enumerationMaxClasses(10_000_000)
            .timedCounterexampleCheck(true)
            .totalBudget(Duration.ofSeconds(3))
            .verify();

        assertTrue(r.isViolated(), "a verdict reached before the deadline stands:\n" + r.report());
        assertEquals(SmtVerificationResult.CounterexampleTiming.TIMED_UNDECIDED, r.counterexampleTiming(), r.report());
        assertTrue(r.report().contains(
                "  UNDECIDED: the total verification budget of 3000 ms ran out before the timed state-class graph closed."), r.report());
    }

    @Test
    @Timeout(value = 120, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    void aCutBuildIsNotATruncation_theCacheIsLeftAsFound() {
        int k = 12; // 4 096 classes: most of a second to build, many times the budget below
        var net = toggles(k, false);
        var cache = new StateSpaceCache();
        var cut = SmtVerifier.forNet(net).linearBound(false).initialMarking(allA(k))
            .property(SmtProperty.placeBound(p("a_0"), 1))
            .enumerationMaxClasses(100_000)
            .stateSpaceCache(cache)
            .totalBudget(Duration.ofMillis(50))
            .verify();
        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, cut.verdict(), cut.report());
        assertTrue(unknown.reason().endsWith("during state-space enumeration"), unknown.reason());
        assertEquals(0, cache.size(), "a deadline cut is not recorded as a truncation");

        // AC10: a later query with more time and the same class budget builds rather than declines.
        var ok = SmtVerifier.forNet(net).linearBound(false).initialMarking(allA(k))
            .property(SmtProperty.placeBound(p("a_0"), 1))
            .enumerationMaxClasses(100_000)
            .stateSpaceCache(cache)
            .verify();
        assertEquals(SmtVerificationResult.Route.ENUMERATION, ok.route(), ok.report());
        assertTrue(ok.isProven(), ok.report());
        assertTrue(!ok.report().contains("cached truncation"), ok.report());
        assertEquals(1, cache.size());
    }

    @Test
    @EnabledIf("z3Available")
    void unset_isUnchanged_andAGenerousBudgetOnlyAddsItsHeaderLine() {
        var a = p("a");
        var bad = p("bad");
        var net = StructureOnly.bind(PetriNet.builder("chain")
            .transition(Transition.builder("t").inputs(In.one(a)).outputs(Out.place(bad))
                .timing(Timing.delayed(Duration.ofMillis(5))).build()).build());
        var m0 = MarkingState.builder().tokens(a, 1).build();
        var unset = SmtVerifier.forNet(net).initialMarking(m0)
            .property(SmtProperty.unreachable(Set.of(bad))).verify();
        var generous = SmtVerifier.forNet(net).initialMarking(m0)
            .property(SmtProperty.unreachable(Set.of(bad))).totalBudget(Duration.ofMinutes(5)).verify();

        assertTrue(!unset.report().contains("Total budget"), unset.report());
        assertEquals(unset.verdict(), generous.verdict());
        assertEquals(unset.route(), generous.route());
        assertEquals(unset.counterexampleTransitions(), generous.counterexampleTransitions());
        assertEquals(unset.report(), generous.report().replace("Total budget: 300000 ms\n", ""));
        assertEquals(List.of("t"), unset.counterexampleTransitions());
    }

    @Test
    void aNegativeBudget_isRejected() {
        var v = SmtVerifier.forNet(toggles(1, false));
        org.junit.jupiter.api.Assertions.assertThrows(IllegalArgumentException.class,
            () -> v.totalBudget(Duration.ofMillis(-1)));
    }

    /**
     * [VER-013]: a call whose budget is already spent (or that is cancelled) before it starts
     * says so, ahead of the refusal of a property naming a place the net does not declare.
     */
    @Test
    void aSpentBudgetOrACancelledCall_beatsTheAbsentPlaceRefusal() {
        var property = SmtProperty.placeBound(p("nowhere"), 0);
        var spent = SmtVerifier.forNet(toggles(1, false)).initialMarking(allA(1))
            .property(property).totalBudget(Duration.ZERO).verify();
        assertEquals("total verification budget of 0 ms exhausted during net preparation",
            assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, spent.verdict(), spent.report()).reason());

        Thread.currentThread().interrupt();
        SmtVerificationResult cancelled;
        try {
            cancelled = SmtVerifier.forNet(toggles(1, false)).initialMarking(allA(1)).property(property).verify();
        } finally {
            Thread.interrupted();
        }
        assertEquals("verification cancelled during net preparation",
            assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, cancelled.verdict(), cancelled.report()).reason());
    }

    /**
     * [VER-013]: a stop names the step that was running when the budget ran out, never the one
     * about to start — entering a step checks the deadline before it names the step.
     */
    @Test
    void aStopNamesTheStepThatWasRunning_notTheOneAboutToStart() {
        var spent = new org.libpetri.core.internal.VerificationDeadline(50);
        spent.enter("first step");
        // The budget has run out by now; entering the next step must blame the first.
        while (!spent.expired()) Thread.onSpinWait();
        var e = org.junit.jupiter.api.Assertions.assertThrows(
            org.libpetri.core.internal.VerificationDeadline.Exhausted.class, () -> spent.enter("second step"));
        assertEquals("total verification budget of 50 ms exhausted during first step", e.reason());
        assertEquals("first step", spent.phase());
    }

    /**
     * {@code verify()} is re-entrant: two calls sharing one verifier on different threads keep
     * their own deadline and running step. Before, both lived in instance fields, so one call
     * named its stop after the other's step (or read the field after the other nulled it).
     */
    @Test
    @Timeout(value = 120, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    void concurrentCallsOnOneVerifier_doNotShareTheirDeadlineOrStep() throws Exception {
        int k = 22;
        var verifier = SmtVerifier.forNet(toggles(k, false)).linearBound(false).initialMarking(allA(k))
            .property(SmtProperty.placeBound(p("a_0"), 1))
            .enumerationMaxClasses(10_000_000)
            .totalBudget(Duration.ofMillis(40));
        try (var pool = java.util.concurrent.Executors.newFixedThreadPool(2)) {
            for (int round = 0; round < 25; round++) {
                var start = new java.util.concurrent.CountDownLatch(1);
                java.util.concurrent.Callable<SmtVerificationResult> call = () -> {
                    start.await();
                    return verifier.verify();
                };
                var first = pool.submit(call);
                var second = pool.submit(call);
                start.countDown();
                for (var result : List.of(first.get(), second.get())) {
                    var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class,
                        result.verdict(), result.report());
                    assertEquals("total verification budget of 40 ms exhausted during state-space enumeration",
                        unknown.reason(), "round " + round);
                    assertEquals(SmtVerificationResult.Route.ENUMERATION, result.route(), "round " + round);
                    assertTrue(result.report().contains("Total budget: 40 ms\n"), result.report());
                }
            }
        }
    }
}
