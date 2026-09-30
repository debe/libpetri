package org.libpetri.smt;

import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.AllMints;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.SmtVerificationResult.CounterexampleTiming;
import org.libpetri.smt.opennet.OpenNetContract;
import org.libpetri.smt.opennet.OpenNetOptions;
import org.libpetri.smt.opennet.OpenNetResult;
import org.libpetri.smt.opennet.OpenNetVerifier;

import java.time.Duration;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Deadline reaping in the verifier's quiescence ([VER-002], [VER-004], [TIME-013]).
 *
 * <p>A {@code deadline} / {@code window} transition a late executor reaps keeps its input tokens
 * and is not re-enabled until one of its input places changes, so the executor can rest at a
 * marking the untimed net still enables. Lean: {@code Libpetri/Novel/ReapingVsUntimed.lean},
 * {@code reaping_refutes_ver004_ac3}, whose witness is {@link #witness()}. Mirrors
 * {@code rust/libpetri-verification/tests/reaping.rs}.
 */
class ReapingTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final Place<Object> P0 = Place.of("p0", Object.class);
    private static final Place<Object> P1 = Place.of("p1", Object.class);
    private static final Timing WINDOW = Timing.window(Duration.ofMillis(3), Duration.ofMillis(5));

    private static Transition arc(String name, Place<Object> from, Place<Object> to, Timing timing) {
        return Transition.builder(name).inputs(In.one(from)).outputs(Out.place(to)).timing(timing).build();
    }

    /** {@code p0 —t→ p1}, {@code t = window(3, 5)}: the Lean witness. */
    private static PetriNet witness() {
        return StructureOnly.bind(PetriNet.builder("reaping-witness").transition(arc("t", P0, P1, WINDOW)).build());
    }

    private static SmtVerifier verifier(PetriNet net, SmtProperty property) {
        return SmtVerifier.forNet(net).mintTransitions(AllMints.names(net))
            .initialMarking(MarkingState.builder().tokens(P0, 1).build())
            .property(property)
            .sinkPlaces(P1)
            .timeout(Duration.ofSeconds(30));
    }

    @Test
    void deadlineAndWindowAreReapableAndNothingElseIs() {
        assertTrue(Reaping.isReapable(Timing.deadline(Duration.ofMillis(5))));
        assertTrue(Reaping.isReapable(WINDOW));
        assertFalse(Reaping.isReapable(Timing.exact(Duration.ofMillis(5))));
        assertFalse(Reaping.isReapable(Timing.delayed(Duration.ofMillis(5))));
        assertFalse(Reaping.isReapable(Timing.immediate()));
    }

    @Test
    void relaxingDropsEveryLatestBoundAndKeepsTheEarliest() {
        var net = PetriNet.builder("reap")
            .transition(arc("d", P0, P1, Timing.deadline(Duration.ofMillis(5))))
            .transition(arc("w", P0, P1, WINDOW))
            .transition(arc("w0", P0, P1, Timing.window(Duration.ZERO, Duration.ofMillis(5))))
            .transition(arc("x", P0, P1, Timing.exact(Duration.ofMillis(4))))
            .transition(arc("x0", P0, P1, Timing.exact(Duration.ZERO)))
            .transition(arc("y", P0, P1, Timing.delayed(Duration.ofMillis(2))))
            .transition(arc("i", P0, P1, Timing.immediate()))
            .build();
        assertEquals(Set.of("d", "w", "w0"), Reaping.reapableTransitions(net));
        var late = Reaping.lateTransitions(net);
        assertEquals(Set.of("d", "w", "w0", "x", "x0"), late);
        var relaxed = Reaping.relaxLate(net, late);
        java.util.function.Function<String, Timing> timing = name ->
            relaxed.transitions().stream().filter(t -> t.name().equals(name)).findFirst().orElseThrow().timing();
        assertInstanceOf(Timing.Immediate.class, timing.apply("d"));
        assertEquals(Timing.delayed(Duration.ofMillis(3)), timing.apply("w"));
        assertInstanceOf(Timing.Immediate.class, timing.apply("w0"));
        assertEquals(Timing.delayed(Duration.ofMillis(4)), timing.apply("x"));
        assertInstanceOf(Timing.Immediate.class, timing.apply("x0"));
        assertEquals(Timing.delayed(Duration.ofMillis(2)), timing.apply("y"));
        assertInstanceOf(Timing.Immediate.class, timing.apply("i"));
        assertSame(net, Reaping.relaxLate(net, Set.of()));
    }

    @Test
    void aNetWithoutLatestBoundsIsNotRelaxed() {
        var net = PetriNet.builder("plain")
            .transition(arc("y", P0, P1, Timing.delayed(Duration.ofMillis(2))))
            .transition(arc("i", P0, P1, Timing.immediate()))
            .build();
        assertTrue(Reaping.lateTransitions(net).isEmpty());
        assertSame(net, Reaping.relaxLate(net, Set.of("y", "i")));
    }

    @Test
    void theQuiescenceClauseSkipsTheReapableTransition() {
        var reaping = verifier(witness(), SmtProperty.deadlockFree()).encodeScripts().horn();
        var strict = verifier(witness(), SmtProperty.deadlockFree()).assumeNoReaping(true).encodeScripts().horn();
        assertTrue(strict.contains("(< m0 1)"), strict);
        assertFalse(reaping.contains("(< m0 1)"), reaping);
    }

    @Test
    void markingPropertyScriptsDoNotChange() {
        var reaping = verifier(witness(), SmtProperty.placeBound(P1, 1)).encodeScripts().horn();
        var strict = verifier(witness(), SmtProperty.placeBound(P1, 1)).assumeNoReaping(true).encodeScripts().horn();
        assertEquals(strict, reaping);
    }

    @Test
    @EnabledIf("z3Available")
    void theWitnessRestsAtItsInitialMarking() {
        var r = verifier(witness(), SmtProperty.deadlockFree()).verify();
        assertTrue(r.isViolated(), r.report());
        assertTrue(r.counterexampleTransitions().isEmpty(), r.report());
        assertEquals(1, r.counterexampleTrace().getFirst().tokens(P0), r.report());
        assertTrue(r.report().contains("Reaping (TIME-013): t can be reaped"), r.report());
    }

    @Test
    @EnabledIf("z3Available")
    void assumeNoReapingRestoresTheStrictVerdict() {
        var r = verifier(witness(), SmtProperty.deadlockFree()).assumeNoReaping(true).verify();
        assertTrue(r.isProven(), r.report());
        assertTrue(r.report().contains("ASSUMPTION: no transition is reaped (the assume-no-reaping option)"), r.report());
    }

    @Test
    @EnabledIf("z3Available")
    void theFixpointQueryAloneFindsTheReapedRest() {
        var r = verifier(witness(), SmtProperty.deadlockFree()).stateEquationPhase(false).firingBound(false).verify();
        assertTrue(r.isViolated(), r.report());
        assertEquals(SmtVerificationResult.Route.SMT, r.route(), r.report());
        assertTrue(r.counterexampleTransitions().isEmpty(), r.report());
        assertEquals(1, r.counterexampleTrace().size(), r.report());
    }

    @Test
    @EnabledIf("z3Available")
    void terminatesAtSinkSeesTheReapedRestToo() {
        var r = verifier(witness(), SmtProperty.terminatesAtSink()).verify();
        assertTrue(r.isViolated(), r.report());
        assertTrue(r.counterexampleTransitions().isEmpty(), r.report());
        assertTrue(verifier(witness(), SmtProperty.terminatesAtSink()).assumeNoReaping(true).verify().isProven());
    }

    @Test
    @EnabledIf("z3Available")
    void aShadowedReapableTransitionChangesNothing() {
        var net = StructureOnly.bind(PetriNet.builder("shadowed")
            .transition(arc("t", P0, P1, WINDOW))
            .transition(arc("u", P0, P1, Timing.immediate()))
            .build());
        var r = verifier(net, SmtProperty.deadlockFree()).verify();
        assertTrue(r.isProven(), r.report());
    }

    @Test
    @EnabledIf("z3Available")
    void aReapableSelfLoopIsNotProvenStructurally() {
        var a = Place.of("a", Object.class);
        var net = StructureOnly.bind(PetriNet.builder("self-loop").transition(arc("t", a, a, WINDOW)).build());
        java.util.function.Function<Boolean, SmtVerificationResult> run = noReaping -> SmtVerifier.forNet(net).mintTransitions(AllMints.names(net))
            .enumerationMaxClasses(0)
            .initialMarking(MarkingState.builder().tokens(a, 1).build())
            .property(SmtProperty.deadlockFree())
            .assumeNoReaping(noReaping)
            .timeout(Duration.ofSeconds(30))
            .verify();
        var reaping = run.apply(false);
        assertNotEquals(SmtVerificationResult.Route.STRUCTURAL, reaping.route(), reaping.report());
        assertTrue(reaping.isViolated(), reaping.report());
        assertTrue(reaping.counterexampleTransitions().isEmpty(), reaping.report());
        assertTrue(run.apply(true).isProven());
    }

    @Test
    @EnabledIf("z3Available")
    void theTimedCheckConfirmsTheReapedRest() {
        var r = verifier(witness(), SmtProperty.deadlockFree()).timedCounterexampleCheck(true).verify();
        assertTrue(r.isViolated(), r.report());
        assertEquals(CounterexampleTiming.TIMED_CONFIRMED, r.counterexampleTiming(), r.report());
    }

    /**
     * Route B on the same-mint join at {@code window(50, 200)}: on time the join fires and the run
     * rests at {@code {merged}}; a late executor reaps it and rests with both branches marked.
     */
    @Test
    void routeBReadsAReapedJoinAsResting() {
        var source = Place.of("source", Object.class);
        var a = Place.of("branchA", String.class);
        var b = Place.of("branchB", String.class);
        var merged = Place.of("merged", String.class);
        var fork = Transition.builder("fork").inputs(In.one(source)).outputs(Out.and(a, b)).build();
        var join = Transition.builder("join")
            .inputs(In.one(a), In.one(b))
            .match(org.libpetri.core.MatchSpec.builder()
                .key(a, org.libpetri.core.NameId::of)
                .key(b, org.libpetri.core.NameId::of)
                .build())
            .outputs(Out.place(merged))
            .timing(Timing.window(Duration.ofMillis(50), Duration.ofMillis(200)))
            .build();
        var net = StructureOnly.bind(PetriNet.builder("reaped_join").transitions(fork, join).build());
        var initial = MarkingState.builder().tokens(source, 1).build();
        java.util.function.Function<Set<String>, NuScgVerifier.Outcome> run = reapable -> NuScgVerifier.verifyReaping(
            net, initial, SmtProperty.deadlockFree(), Set.of(merged), Set.of(),
            org.libpetri.analysis.EnvironmentAnalysisMode.ignore(), 1_000, org.libpetri.analysis.FragmentMode.BASE,
            Set.of(), AllMints.of(net), org.libpetri.analysis.PrioritySemantics.CONFLICT, List.of(), reapable, reapable);
        assertInstanceOf(SmtVerificationResult.Verdict.Proven.class, run.apply(Set.of()).verdict());
        var reaping = run.apply(Set.of("join"));
        assertInstanceOf(SmtVerificationResult.Verdict.Violated.class, reaping.verdict());
        assertEquals(List.of("fork"), reaping.transitions());
        assertTrue(reaping.note().contains("latest bound of join was lifted"), reaping.note());
    }

    @Test
    @EnabledIf("z3Available")
    void openNetRoutesReadAReapedRelayAsResting() {
        var q = Place.of("q", Object.class);
        var out = Place.of("out", Object.class);
        var net = StructureOnly.bind(PetriNet.builder("reaped-relay").transition(arc("relay", q, out, WINDOW)).build());
        var contract = OpenNetContract.builder().arrive(1, q).expect("out", 1, out).build();
        OpenNetResult graph = OpenNetVerifier.verifyOpenNet(net, contract, OpenNetOptions.DEFAULT);
        assertInstanceOf(SmtVerificationResult.Verdict.Violated.class, graph.verdict(), graph.report());
        assertEquals(OpenNetResult.Route.ENUMERATION, graph.route());
        assertTrue(graph.report().contains("Reaping (TIME-013): relay can be reaped"), graph.report());
        var strict = OpenNetVerifier.verifyOpenNet(net, contract, OpenNetOptions.DEFAULT.withAssumeNoReaping(true));
        assertInstanceOf(SmtVerificationResult.Verdict.Proven.class, strict.verdict(), strict.report());
        assertTrue(strict.report().contains("ASSUMPTION: no transition is reaped"), strict.report());
        for (boolean noReaping : List.of(false, true)) {
            var smt = OpenNetVerifier.verifyOpenNet(net, contract,
                OpenNetOptions.DEFAULT.withMaxClasses(0).withAssumeNoReaping(noReaping));
            assertEquals(OpenNetResult.Route.SMT, smt.route(), smt.report());
            Class<? extends SmtVerificationResult.Verdict> expected = noReaping
                ? SmtVerificationResult.Verdict.Proven.class : SmtVerificationResult.Verdict.Violated.class;
            assertTrue(expected.isInstance(smt.verdict()), smt.report());
        }
    }

    // ==================== lateness on Route B ([TIME-006], [TIME-013]) ====================

    private static final Place<Object> P = Place.of("p", Object.class);
    private static final Place<Object> A = Place.of("a", Object.class);
    private static final Place<Object> B = Place.of("b", Object.class);

    /**
     * {@code t1: p → a} at {@code early}, {@code t2: p → b} at {@code delayed(10)}, beside a
     * same-mint ν-join so the query runs on Route B. On time {@code t1} always wins the race for
     * {@code p}; a late executor reaps a deadline / window {@code t1}, or fires an exact one after
     * {@code t2}, and marks {@code b}. Lean: {@code TimedScg/Retrodict.reaping_escapes_timed_graph}.
     */
    private static PetriNet lateRace(Timing early) {
        var source = Place.of("source", Object.class);
        var ba = Place.of("branchA", String.class);
        var bb = Place.of("branchB", String.class);
        var merged = Place.of("merged", String.class);
        var fork = Transition.builder("fork").inputs(In.one(source)).outputs(Out.and(ba, bb)).build();
        var join = Transition.builder("join")
            .inputs(In.one(ba), In.one(bb))
            .match(org.libpetri.core.MatchSpec.builder()
                .key(ba, org.libpetri.core.NameId::of)
                .key(bb, org.libpetri.core.NameId::of)
                .build())
            .outputs(Out.place(merged))
            .build();
        return StructureOnly.bind(PetriNet.builder("late-race")
            .transition(arc("t1", P, A, early))
            .transition(arc("t2", P, B, Timing.delayed(Duration.ofMillis(10))))
            .transitions(fork, join)
            .build());
    }

    private static SmtVerificationResult verifyLateRace(Timing early, boolean noReaping) {
        var source = Place.of("source", Object.class);
        return SmtVerifier.forNet(lateRace(early)).mintTransitions(AllMints.names(lateRace(early)))
            .initialMarking(MarkingState.builder().tokens(P, 1).tokens(source, 1).build())
            .property(SmtProperty.unreachable(Set.of(B)))
            .assumeNoReaping(noReaping)
            .timeout(Duration.ofSeconds(30))
            .verify();
    }

    @Test
    void routeBMarkingPropertiesSeeAReapedRace() {
        for (var early : List.of(Timing.deadline(Duration.ofMillis(5)), WINDOW)) {
            var late = verifyLateRace(early, false);
            assertEquals(SmtVerificationResult.Route.NU_SCG, late.route(), late.report());
            assertTrue(late.isViolated(), early + ": a reaped t1 lets t2 mark b\n" + late.report());
            assertEquals("t2", late.counterexampleTransitions().getLast(), late.report());
            var onTime = verifyLateRace(early, true);
            assertEquals(SmtVerificationResult.Route.NU_SCG, onTime.route(), onTime.report());
            assertTrue(onTime.isProven(), early + ": on time t1 always wins\n" + onTime.report());
            assertTrue(onTime.report().contains("ASSUMPTION: no transition is reaped"), onTime.report());
            assertTrue(onTime.report().contains("on-time executor"), onTime.report());
        }
    }

    @Test
    void routeBLiftsTheLatestBoundOfExact() {
        var exact = Timing.exact(Duration.ofMillis(5));
        var late = verifyLateRace(exact, false);
        assertEquals(SmtVerificationResult.Route.NU_SCG, late.route(), late.report());
        assertTrue(late.isViolated(), late.report());
        assertTrue(late.report().contains("latest bound of t1 was lifted"), late.report());
        var onTime = verifyLateRace(exact, true);
        assertTrue(onTime.isProven(), onTime.report());
        assertTrue(onTime.report().contains("on-time executor"), onTime.report());
    }

    @Test
    void routeBLeavesANetWithoutLatestBoundsAlone() {
        var delayed = Timing.delayed(Duration.ofMillis(5));
        var late = verifyLateRace(delayed, false);
        var onTime = verifyLateRace(delayed, true);
        assertEquals(SmtVerificationResult.Route.NU_SCG, late.route(), late.report());
        assertTrue(late.isViolated(), late.report());
        assertFalse(late.report().contains("lifted"), late.report());
        assertFalse(late.report().contains("TIME-013"), late.report());
        java.util.function.Function<String, String> strip = r -> r.lines()
            .filter(l -> !l.startsWith("Elapsed") && !l.contains("Elapsed")).collect(java.util.stream.Collectors.joining("\n"));
        assertEquals(strip.apply(late.report()), strip.apply(onTime.report()));
    }

    // ==================== reap-awareness on every quiescence route ====================

    @Test
    @EnabledIf("z3Available")
    void theFiringBoundReadsTheReapedRest() {
        var r = verifier(witness(), SmtProperty.deadlockFree()).stateEquationPhase(false).verify();
        assertTrue(r.isViolated(), r.report());
        assertTrue(r.report().contains("Firing bound (VER-019)"), r.report());
        assertTrue(r.counterexampleTransitions().isEmpty(), r.report());
        assertTrue(verifier(witness(), SmtProperty.deadlockFree()).stateEquationPhase(false)
            .assumeNoReaping(true).verify().isProven());
    }

    @Test
    @EnabledIf("z3Available")
    void theStateEquationPhaseReadsTheReapedRest() {
        var r = verifier(witness(), SmtProperty.deadlockFree()).firingBound(false).verify();
        assertTrue(r.isViolated(), r.report());
        assertTrue(r.report().contains("State-equation phase (VER-018)"), r.report());
        assertTrue(verifier(witness(), SmtProperty.deadlockFree()).firingBound(false)
            .assumeNoReaping(true).verify().isProven());
    }

    /** Route A (NU-053): Route B capped at one class, so the budgeted quiescence query falls through. */
    @Test
    @EnabledIf("z3Available")
    void routeAReadsAReapedJoinAsResting() {
        var source = Place.of("source", Object.class);
        var budget = Place.of("budget", Object.class);
        var ba = Place.of("branchA", String.class);
        var bb = Place.of("branchB", String.class);
        var merged = Place.of("merged", String.class);
        var fork = Transition.builder("fork").inputs(In.one(source), In.one(budget)).outputs(Out.and(ba, bb)).build();
        var join = Transition.builder("join")
            .inputs(In.one(ba), In.one(bb))
            .match(org.libpetri.core.MatchSpec.builder()
                .key(ba, org.libpetri.core.NameId::of)
                .key(bb, org.libpetri.core.NameId::of)
                .build())
            .outputs(Out.place(merged))
            .timing(Timing.window(Duration.ofMillis(50), Duration.ofMillis(200)))
            .build();
        var net = StructureOnly.bind(PetriNet.builder("reaped-join-route-a").transitions(fork, join).build());
        java.util.function.Function<Boolean, SmtVerificationResult> run = noReaping -> SmtVerifier.forNet(net).mintTransitions(AllMints.names(net))
            .enumerationMaxClasses(0)
            .initialMarking(MarkingState.builder().tokens(source, 1).tokens(budget, 1).build())
            .property(SmtProperty.deadlockFree())
            .sinkPlaces(merged)
            .budgetPlaces(budget)
            .nuMaxClasses(1)
            .assumeNoReaping(noReaping)
            .timeout(Duration.ofSeconds(30))
            .verify();
        var reaping = run.apply(false);
        assertTrue(reaping.report().contains("ν-encoding: name-coloured"), reaping.report());
        assertTrue(reaping.isViolated(), reaping.report());
        assertFalse(run.apply(true).isViolated());
    }

    // ==================== the timed check of VER-023 ====================

    @Test
    @EnabledIf("z3Available")
    void theTimedCheckNeverTurnsAViolationAndNamesItsAssumptions() {
        var net = StructureOnly.bind(PetriNet.builder("race")
            .transition(arc("t1", P, A, WINDOW))
            .transition(arc("t2", P, B, Timing.delayed(Duration.ofMillis(10))))
            .build());
        var r = SmtVerifier.forNet(net).mintTransitions(AllMints.names(net))
            .initialMarking(MarkingState.builder().tokens(P, 1).build())
            .property(SmtProperty.unreachable(Set.of(B)))
            .timedCounterexampleCheck(true)
            .timeout(Duration.ofSeconds(30))
            .verify();
        assertTrue(r.isViolated(), r.report());
        assertEquals(CounterexampleTiming.SPURIOUS_UNDER_TIMING, r.counterexampleTiming(), r.report());
        assertTrue(r.report().contains("assumes an on-time executor"), r.report());
        assertTrue(r.report().contains("atomic"), r.report());
    }
}
