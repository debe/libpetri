package org.libpetri.smt;

import org.libpetri.analysis.AllMints;
import java.time.Duration;
import java.util.List;
import java.util.Set;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.SmtVerificationResult.CounterexampleTiming;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [VER-003] {@code counterexampleTiming} and the opt-in timed counterexample check of
 * [VER-023]. The watchdog net is the lab's {@code TimedNets.watchdogs(2, false)}
 * (research/net-metrics/lab): each call answers within {@code window(0, 2)} and its watchdog
 * fires after {@code delayed(5)}, so no call ever times out under timing, while the untimed
 * abstraction lets every watchdog fire.
 */
class CounterexampleTimingTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static Place<Object> p(String name) {
        return Place.of(name, Object.class);
    }

    private record Watchdogs(PetriNet net, MarkingState m0) {}

    private static Watchdogs watchdogs(int n, Duration watchdogDelay) {
        var b = PetriNet.builder("watchdog-timing-" + n);
        var m = MarkingState.builder();
        for (int i = 0; i < n; i++) {
            var req = p("REQ_" + i);
            var calling = p("CALLING_" + i);
            b.transition(Transition.builder("start_" + i).inputs(In.one(req)).outputs(Out.place(calling)).build());
            b.transition(Transition.builder("answer_" + i).timing(Timing.window(Duration.ZERO, Duration.ofMillis(2)))
                .inputs(In.one(calling)).outputs(Out.place(p("RESP_" + i))).build());
            b.transition(Transition.builder("watchdog_" + i).timing(Timing.delayed(watchdogDelay))
                .inputs(In.one(calling)).outputs(Out.place(p("TIMEOUT_" + i))).build());
            m.tokens(req, 1);
        }
        return new Watchdogs(StructureOnly.bind(b.build()), m.build());
    }

    private static SmtVerifier noTimeout0(Watchdogs w) {
        return SmtVerifier.forNet(w.net()).initialMarking(w.m0())
            .property(SmtProperty.unreachable(Set.of(p("TIMEOUT_0"))))
            .timeout(Duration.ofSeconds(60));
    }

    @Test
    @EnabledIf("z3Available")
    void watchdog_default_isUntimedAbstraction() {
        var r = noTimeout0(watchdogs(2, Duration.ofMillis(5))).verify();

        assertTrue(r.isViolated(), r.report());
        assertEquals(SmtVerificationResult.Route.SMT, r.route());
        assertEquals(CounterexampleTiming.UNTIMED_ABSTRACTION, r.counterexampleTiming(), r.report());
        assertTrue(r.report().contains("  WARNING: This counterexample is in UNTIMED semantics.\n"), r.report());
        assertTrue(!r.report().contains("Timed counterexample check"), "off by default:\n" + r.report());
    }

    @Test
    @EnabledIf("z3Available")
    void watchdog_checkOn_isSpuriousUnderTiming_verdictKept() {
        var off = noTimeout0(watchdogs(2, Duration.ofMillis(5))).verify();
        var r = noTimeout0(watchdogs(2, Duration.ofMillis(5))).timedCounterexampleCheck(true).verify();

        assertTrue(r.isViolated(), "the verdict is never changed (VER-023 AC6):\n" + r.report());
        assertEquals(CounterexampleTiming.SPURIOUS_UNDER_TIMING, r.counterexampleTiming(), r.report());
        assertTrue(r.report().contains("SPURIOUS UNDER TIMING: the timed state-class graph closed with 10 classes"),
            r.report());
        assertEquals(off.counterexampleTransitions(), r.counterexampleTransitions(), "the untimed trace is kept");
        assertEquals(off.counterexampleConfirmed(), r.counterexampleConfirmed());
        assertEquals(off.route(), r.route());
    }

    @Test
    @EnabledIf("z3Available")
    void timingRealViolation_isTimedConfirmed_withTheTimedPath() {
        var r = noTimeout0(watchdogs(1, Duration.ofMillis(1))).timedCounterexampleCheck(true).verify();

        assertTrue(r.isViolated(), r.report());
        assertEquals(CounterexampleTiming.TIMED_CONFIRMED, r.counterexampleTiming(), r.report());
        assertEquals(List.of("start_0", "watchdog_0"), r.counterexampleTransitions(), r.report());
        assertEquals(3, r.counterexampleTrace().size());
        assertTrue(r.counterexampleTrace().getLast().hasTokens(p("TIMEOUT_0")));
        assertEquals(Boolean.TRUE, r.counterexampleConfirmed());
        assertTrue(r.report().contains("REPLACED by the shortest timed-graph path"), r.report());
    }

    @Test
    @EnabledIf("z3Available")
    void timedConfirmed_isConfirmed_evenWhenTheUntimedReplayDidNotRun() {
        // Replay off leaves counterexampleConfirmed null on the fixpoint path; the timed path is
        // an ordered firing sequence, so TIMED_CONFIRMED reports it confirmed (VER-023).
        var r = noTimeout0(watchdogs(1, Duration.ofMillis(1)))
            .stateEquationPhase(false).firingBound(false).counterexampleReplay(false)
            .timedCounterexampleCheck(true).verify();

        assertTrue(r.isViolated(), r.report());
        assertEquals(CounterexampleTiming.TIMED_CONFIRMED, r.counterexampleTiming(), r.report());
        assertEquals(Boolean.TRUE, r.counterexampleConfirmed());
    }

    @Test
    @EnabledIf("z3Available")
    void classBudgetBelowTheTimedGraph_isTimedUndecided() {
        var r = noTimeout0(watchdogs(2, Duration.ofMillis(5)))
            .timedCounterexampleCheck(true).enumerationMaxClasses(3).verify();

        assertTrue(r.isViolated(), r.report());
        assertEquals(CounterexampleTiming.TIMED_UNDECIDED, r.counterexampleTiming(), r.report());
        assertTrue(r.report().contains("exceeded 3 classes"), r.report());
    }

    @Test
    void untimedNet_isUntimedNet() {
        var a = p("a");
        var bad = p("bad");
        var net = StructureOnly.bind(PetriNet.builder("untimed")
            .transition(Transition.builder("t").inputs(In.one(a)).outputs(Out.place(bad)).build()).build());
        var r = SmtVerifier.forNet(net).initialMarking(MarkingState.builder().tokens(a, 1).build())
            .property(SmtProperty.unreachable(Set.of(bad))).timedCounterexampleCheck(true).verify();

        assertTrue(r.isViolated(), r.report());
        assertEquals(SmtVerificationResult.Route.ENUMERATION, r.route());
        assertEquals(CounterexampleTiming.UNTIMED_NET, r.counterexampleTiming());
    }

    @Test
    void notViolated_hasNoTiming() {
        var a = p("a");
        var net = StructureOnly.bind(PetriNet.builder("proven")
            .transition(Transition.builder("t").inputs(In.one(a)).outputs(Out.place(p("b")))
                .timing(Timing.delayed(Duration.ofMillis(5))).build()).build());
        var r = SmtVerifier.forNet(net).initialMarking(MarkingState.builder().tokens(a, 1).build())
            .property(SmtProperty.placeBound(a, 1)).timedCounterexampleCheck(true).verify();

        assertTrue(r.isProven(), r.report());
        assertNull(r.counterexampleTiming());
    }

    @Test
    @EnabledIf("z3Available")
    void environmentPlaces_checkDoesNotRun() {
        var w = watchdogs(1, Duration.ofMillis(5));
        var r = noTimeout0(w).timedCounterexampleCheck(true)
            .environmentPlaces(EnvironmentPlace.of(p("REQ_0")))
            .environmentMode(EnvironmentAnalysisMode.alwaysAvailable())
            .verify();

        assertTrue(r.isViolated(), r.report());
        assertEquals(CounterexampleTiming.UNTIMED_ABSTRACTION, r.counterexampleTiming(), r.report());
        assertTrue(!r.report().contains("Timed counterexample check"), r.report());
    }

    /** MINT co-mints one name into COL_A and COL_B; a ν-JOIN matches them; a delayed drain steals COL_A. */
    private static PetriNet nuFixture() {
        var seed = Place.of("SEED", String.class);
        var colA = Place.of("COL_A", String.class);
        var colB = Place.of("COL_B", String.class);
        var mint = Transition.builder("MINT").inputs(Arc.In.one(seed)).outputs(Arc.Out.and(colA, colB)).build();
        var join = Transition.builder("JOIN").inputs(Arc.In.one(colA), Arc.In.one(colB))
            .match(MatchSpec.builder()
                .key(colA, (String s) -> NameId.of(s))
                .key(colB, (String s) -> NameId.of(s))
                .build())
            .outputs(Arc.Out.place(Place.of("OUT", String.class))).build();
        var drain = Transition.builder("DRAIN_A").inputs(Arc.In.one(colA))
            .timing(Timing.delayed(Duration.ofSeconds(5))).priority(-10)
            .outputs(Arc.Out.place(Place.of("DEADLETTER", String.class))).build();
        return StructureOnly.bind(PetriNet.builder("nu-timed").transitions(mint, join, drain).build());
    }

    @Test
    void routeBOnATimedNet_isTimedExact_evenWithTheCheckOn() {
        var r = SmtVerifier.forNet(nuFixture()).mintTransitions(AllMints.names(nuFixture()))
            .initialMarking(MarkingState.builder().tokens(Place.of("SEED", String.class), 1).build())
            .property(SmtProperty.deadlockFree())
            .sinkPlaces(Place.of("OUT", String.class), Place.of("DEADLETTER", String.class))
            .fragmentMode(FragmentMode.EXTENDED)
            .timedCounterexampleCheck(true)
            .verify();

        assertTrue(r.isViolated(), r.report());
        assertEquals(SmtVerificationResult.Route.NU_SCG, r.route());
        assertEquals(CounterexampleTiming.TIMED_EXACT, r.counterexampleTiming());
        assertTrue(!r.report().contains("Timed counterexample check"), r.report());
    }

    /** {@code S -> d -> X}, {@code d} at {@code delayed(5)}: the class holding S is not a deadlock. */
    @Test
    @EnabledIf("z3Available")
    void deadlockFree_delayedTransitionStillFiresOutOfItsClass() {
        var s = p("S");
        var net = StructureOnly.bind(PetriNet.builder("delayed")
            .transition(Transition.builder("d").inputs(In.one(s)).outputs(Out.place(p("X")))
                .timing(Timing.delayed(Duration.ofMillis(5))).build()).build());
        var r = SmtVerifier.forNet(net).initialMarking(MarkingState.builder().tokens(s, 1).build())
            .property(SmtProperty.deadlockFree()).timedCounterexampleCheck(true).verify();

        assertTrue(r.isViolated(), r.report());
        assertEquals(CounterexampleTiming.TIMED_CONFIRMED, r.counterexampleTiming(), r.report());
        assertEquals(List.of("d"), r.counterexampleTransitions(), "the stranded X, not the empty run:\n" + r.report());
    }

    /** {@code fast} (window 0..2) always beats {@code slow} (delayed 5): STUCK is never marked under timing. */
    @Test
    @EnabledIf("z3Available")
    void deadlockFree_raceWonByTiming_isSpuriousUnderTiming() {
        var s = p("S");
        var a = p("A");
        var done = p("DONE");
        var net = StructureOnly.bind(PetriNet.builder("race")
            .transition(Transition.builder("start").inputs(In.one(s)).outputs(Out.place(a)).build())
            .transition(Transition.builder("fast").inputs(In.one(a)).outputs(Out.place(done))
                .timing(Timing.window(Duration.ZERO, Duration.ofMillis(2))).build())
            .transition(Transition.builder("slow").inputs(In.one(a)).outputs(Out.place(p("STUCK")))
                .timing(Timing.delayed(Duration.ofMillis(5))).build())
            .build());
        SmtVerifier v = SmtVerifier.forNet(net).initialMarking(MarkingState.builder().tokens(s, 1).build())
            .property(SmtProperty.deadlockFree()).sinkPlaces(done);

        var off = v.verify();
        assertTrue(off.isViolated(), off.report());
        assertEquals(CounterexampleTiming.UNTIMED_ABSTRACTION, off.counterexampleTiming());

        var on = SmtVerifier.forNet(net).initialMarking(MarkingState.builder().tokens(s, 1).build())
            .property(SmtProperty.deadlockFree()).sinkPlaces(done).timedCounterexampleCheck(true).verify();
        assertTrue(on.isViolated(), on.report());
        assertEquals(CounterexampleTiming.SPURIOUS_UNDER_TIMING, on.counterexampleTiming(), on.report());
    }

    @Test
    @EnabledIf("z3Available")
    void checkOff_reportIsByteIdenticalToAVerifierWithoutTheOption() {
        var w = watchdogs(2, Duration.ofMillis(5));
        var plain = noTimeout0(w).verify();
        var off = noTimeout0(w).timedCounterexampleCheck(false).verify();
        assertEquals(plain.report(), off.report());
    }
}
