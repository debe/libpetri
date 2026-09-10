package org.libpetri.analysis;

import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;
import org.libpetri.core.TransitionAction;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * [VER-010] AC1: a class's identity is its marking and its full firing domain, independent
 * of the order in which its transitions became enabled. Mirrors the "canonical class
 * identity" cases of {@code typescript/tests/verification/analysis/state-class-graph.test.ts}.
 *
 * <p>Two independent chains {@code a→c→e} and {@code b→d→f}. From {@code {c, d}} the enabled
 * set is {@code {u, v}} whichever chain moved first, but {@code fireTransition} lays clocks
 * out persistent-then-new, so the two arrivals used to carry the orders {@code [u, v]} and
 * {@code [v, u]} and count as two classes. Untimed, every zone is {@code [0, ∞)} per clock,
 * so the marking is the whole identity: 3 × 3 = 9 markings, 9 classes.
 */
class StateClassGraphTest {

    private static final Place<String> A = Place.of("a", String.class);
    private static final Place<String> B = Place.of("b", String.class);
    private static final Place<String> C = Place.of("c", String.class);
    private static final Place<String> D = Place.of("d", String.class);
    private static final Place<String> E = Place.of("e", String.class);
    private static final Place<String> F = Place.of("f", String.class);

    private static Transition chain(String name, Place<?> from, Place<?> to, boolean timed) {
        var builder = Transition.builder(name).inputs(In.one(from)).outputs(Out.place(to))
            .action(TransitionAction.fork());
        if (timed) {
            builder.timing(new Timing.Window(Duration.ZERO, Duration.ofMillis(2000)));
        }
        return builder.build();
    }

    private static PetriNet twoChains(boolean timed) {
        return PetriNet.builder("two-chains")
            .transitions(chain("tx", A, C, timed), chain("ty", B, D, timed), chain("u", C, E, timed),
                chain("v", D, F, timed))
            .build();
    }

    private static MarkingState initial() {
        return MarkingState.builder().tokens(A, 1).tokens(B, 1).build();
    }

    private static MarkingState atCD() {
        return MarkingState.builder().tokens(C, 1).tokens(D, 1).build();
    }

    @Test
    void countsOneMarkingOnce_whateverTheEnablingOrder_untimed() {
        var scg = StateClassGraph.build(twoChains(false), initial(), 1000);
        assertTrue(scg.isComplete());
        assertEquals(9, scg.reachableMarkings().size());
        assertEquals(9, scg.size());
        var classes = scg.classesWithMarking(atCD());
        assertEquals(1, classes.size());
        assertEquals(List.of("u", "v"), classes.iterator().next().firingDomain().clockNames());
    }

    @Test
    void keepsClocks_enabledList_andEarliestReadyTimesAligned_afterReordering() {
        var scg = StateClassGraph.build(twoChains(true), initial(), 1000);
        assertTrue(scg.isComplete());
        // Same zone from both paths (v and u are each fresh when enabled), so one class.
        var classes = scg.classesWithMarking(atCD());
        assertEquals(1, classes.size());
        var sc = classes.iterator().next();
        assertEquals(sc.firingDomain().clockNames(),
            sc.enabledTransitions().stream().map(Transition::name).toList());
        assertEquals(sc.enabledTransitions().size(), sc.readyEarliest().length);
        for (var t : sc.enabledTransitions()) {
            assertTrue(sc.canFire(t));
        }
    }

    @Test
    void ordersTheInitialClassCanonicallyToo() {
        var x = Place.of("x", String.class);
        // Declared in the order tz, ty — the initial clocks come out ty, tz.
        var tz = Transition.builder("tz").inputs(In.one(B)).outputs(Out.place(x)).action(TransitionAction.fork()).build();
        var ty = Transition.builder("ty").inputs(In.one(A)).outputs(Out.place(x)).action(TransitionAction.fork()).build();
        var net = PetriNet.builder("initial-order").transitions(tz, ty).build();
        var scg = StateClassGraph.build(net, initial(), 100);
        assertEquals(List.of("ty", "tz"), scg.initialClass().firingDomain().clockNames());
        assertEquals(List.of("ty", "tz"),
            scg.initialClass().enabledTransitions().stream().map(Transition::name).toList());
    }

    /**
     * [TIME-012] Berthomieu-Diaz intermediate semantics: a transition keeps its clock across
     * another firing only if the intermediate marking (inputs consumed, resets drained) still
     * enables it. Refresh fires within [50, 100] ms and CloseSession within [200, 300] ms, so
     * after Refresh a newly enabled CloseSession carries the fresh interval [0.2, 0.3] s and a
     * persistent one the residual [0.1, 0.25] s (reported as its earliest-ready time and upper
     * bound).
     */
    @Nested
    class IntermediateMarkingPersistence {

        private final Place<String> timer = Place.of("timer", String.class);
        private final Place<String> activity = Place.of("activity", String.class);
        private final Place<String> armed = Place.of("armed", String.class);
        private final Place<String> closed = Place.of("closed", String.class);

        private final Timing refreshWindow = new Timing.Window(Duration.ofMillis(50), Duration.ofMillis(100));
        private final Timing closeWindow = new Timing.Window(Duration.ofMillis(200), Duration.ofMillis(300));

        /** Takes the activity token and the timer token, and puts the timer token back. */
        private Transition refresh() {
            return Transition.builder("Refresh").inputs(In.one(activity), In.one(timer))
                .outputs(Out.place(timer)).timing(refreshWindow).action(TransitionAction.fork()).build();
        }

        private Transition closeSession() {
            return Transition.builder("CloseSession").inputs(In.one(timer))
                .outputs(Out.place(closed)).timing(closeWindow).action(TransitionAction.fork()).build();
        }

        /** CloseSession's {earliest-ready, upper bound} in the class Refresh leads to. */
        private double[] closeSessionAfter(Transition refresh, Transition closeSession, MarkingState initial) {
            var net = PetriNet.builder("refresh").transitions(refresh, closeSession).build();
            var scg = StateClassGraph.build(net, initial, 100);
            var edges = scg.branchEdges(scg.initialClass(), refresh);
            assertEquals(1, edges.size(), "Refresh fires first from the initial class");
            var after = edges.getFirst().target();
            int idx = after.transitionIndex(closeSession);
            assertTrue(idx >= 0, "CloseSession is enabled after Refresh");
            return new double[] {after.readyEarliest()[idx], after.firingDomain().getUpperBound(idx)};
        }

        @Test
        void conservedRefresh_restartsTheDependentClock() {
            var bounds = closeSessionAfter(refresh(), closeSession(),
                MarkingState.builder().tokens(timer, 1).tokens(activity, 1).build());
            assertArrayEquals(new double[] {0.2, 0.3}, bounds, 1e-9);
        }

        @Test
        void surplusToken_keepsTheDependentClock() {
            var bounds = closeSessionAfter(refresh(), closeSession(),
                MarkingState.builder().tokens(timer, 2).tokens(activity, 1).build());
            assertArrayEquals(new double[] {0.1, 0.25}, bounds, 1e-9);
        }

        @Test
        void resetArcRefresh_restartsTheDependentClock() {
            var resetRefresh = Transition.builder("Refresh").inputs(In.one(activity)).reset(timer)
                .outputs(Out.place(timer)).timing(refreshWindow).action(TransitionAction.fork()).build();
            var bounds = closeSessionAfter(resetRefresh, closeSession(),
                MarkingState.builder().tokens(timer, 1).tokens(activity, 1).build());
            assertArrayEquals(new double[] {0.2, 0.3}, bounds, 1e-9);
        }

        @Test
        void readArcDependent_restartsTheClockToo() {
            var readingClose = Transition.builder("CloseSession").inputs(In.one(armed)).read(timer)
                .outputs(Out.place(closed)).timing(closeWindow).action(TransitionAction.fork()).build();
            var bounds = closeSessionAfter(refresh(), readingClose,
                MarkingState.builder().tokens(timer, 1).tokens(activity, 1).tokens(armed, 1).build());
            assertArrayEquals(new double[] {0.2, 0.3}, bounds, 1e-9);
        }
    }
}
