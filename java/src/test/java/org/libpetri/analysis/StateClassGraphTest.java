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
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
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

    /**
     * [VER-004], used by [VER-022]: {@code t1} must fire within 5 ms and {@code t2} waits
     * 10 ms, so the timed graph never fires {@code t2}; the untimed one reaches the marking the
     * timing excludes. Mirrors the TypeScript {@code untimed exploration} test.
     */
    @Test
    void untimedExploration_reachesAMarkingTheTimingExcludes() {
        var p = Place.of("p", String.class);
        var a = Place.of("a", String.class);
        var b = Place.of("b", String.class);
        var t1 = Transition.builder("t1").inputs(In.one(p)).outputs(Out.place(a))
            .timing(Timing.deadline(Duration.ofMillis(5))).action(TransitionAction.fork()).build();
        var t2 = Transition.builder("t2").inputs(In.one(p)).outputs(Out.place(b))
            .timing(Timing.delayed(Duration.ofMillis(10))).action(TransitionAction.fork()).build();
        var net = PetriNet.builder("race").transitions(t1, t2).build();
        var m0 = MarkingState.builder().tokens(p, 1).build();
        java.util.function.Predicate<StateClassGraph> marksB =
            g -> g.stateClasses().stream().anyMatch(sc -> sc.marking().hasTokens(b));
        var timed = StateClassGraph.build(net, m0, 100);
        var untimed = StateClassGraph.build(net, m0, 100, java.util.Set.of(), EnvironmentAnalysisMode.ignore(),
            StateClassGraph.Options.UNTIMED);
        assertFalse(marksB.test(timed));
        assertTrue(marksB.test(untimed));
        // The timed options are the graph every other overload builds.
        var byOptions = StateClassGraph.build(net, m0, 100, java.util.Set.of(), EnvironmentAnalysisMode.ignore(),
            StateClassGraph.Options.TIMED);
        assertEquals(timed.stateClasses().size(), byOptions.stateClasses().size());
        assertFalse(marksB.test(byOptions));
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
     * The canonical clock order is code-point order, as in the other implementations: fullwidth
     * {@code Ａ} (U+FF21) before mathematical bold {@code 𝐀} (U+1D400), whose UTF-16 units
     * {@link String#compareTo} would put first.
     */
    @Test
    void ordersClocksByCodePoint_notByUtf16Unit() {
        var x = Place.of("x", String.class);
        var bold = Transition.builder("\uD835\uDC00").inputs(In.one(A)).outputs(Out.place(x)).action(TransitionAction.fork()).build();
        var fullwidth = Transition.builder("\uFF21").inputs(In.one(B)).outputs(Out.place(x)).action(TransitionAction.fork()).build();
        var net = PetriNet.builder("code-points").transitions(bold, fullwidth).build();
        var scg = StateClassGraph.build(net, initial(), 100);
        assertEquals(List.of("\uFF21", "\uD835\uDC00"), scg.initialClass().firingDomain().clockNames());
        assertEquals(List.of(fullwidth, bold), List.copyOf(scg.outgoingBranchEdges(scg.initialClass()).keySet()));
    }

    /**
     * The graph lists everything in the order the build found it, as the reference's
     * {@code Map} and {@code Set} do: classes breadth-first, a class's edges by transition in
     * enabled order and branch order, successors and predecessors by first edge. The witness a
     * graph route reports is read in that order, so a hash order here changed it between JVM
     * runs. A token with twenty ways on and twenty ways back to one place gives classes twenty
     * successors and predecessors, past the length at which the lists index their elements, and
     * an XOR split beside it adds two edges under one transition.
     */
    @Nested
    class BuildOrder {

        private StateClassGraph fan() {
            var transitions = new ArrayList<Transition>();
            var start = Place.of("start", String.class);
            var end = Place.of("end", String.class);
            for (int i = 19; i >= 0; i--) {
                var via = Place.of("via" + i, String.class);
                transitions.add(chain("out" + i, start, via, false));
                transitions.add(chain("back" + i, via, end, false));
            }
            var split = Place.of("split", String.class);
            transitions.add(Transition.builder("x").inputs(In.one(split))
                .outputs(Out.xor(Out.place(Place.of("left", String.class)), Out.place(Place.of("right", String.class))))
                .action(TransitionAction.fork()).build());
            var net = PetriNet.builder("fan").transitions(transitions.toArray(new Transition[0])).build();
            return StateClassGraph.build(net, MarkingState.builder().tokens(split, 1).tokens(start, 1).build(), 100_000);
        }

        @Test
        void listsClassesBreadthFirst_andEdgesInEnabledThenBranchOrder() {
            var scg = fan();
            assertEquals(22 * 3, scg.size());

            var discovered = new LinkedHashSet<StateClass>();
            var queue = new ArrayDeque<StateClass>();
            discovered.add(scg.initialClass());
            queue.add(scg.initialClass());
            while (!queue.isEmpty()) {
                var sc = queue.poll();
                var edges = scg.outgoingBranchEdges(sc);
                assertEquals(sc.enabledTransitions(), List.copyOf(edges.keySet()), "transitions in enabled order");
                assertEquals(List.copyOf(edges.keySet()), List.copyOf(scg.enabledTransitions(sc)));
                var targets = new LinkedHashSet<StateClass>();
                for (var entry : edges.entrySet()) {
                    assertEquals(entry.getValue(), scg.branchEdges(sc, entry.getKey()));
                    for (int b = 0; b < entry.getValue().size(); b++) {
                        assertEquals(b, entry.getValue().get(b).branchIndex(), "branch order");
                        var target = entry.getValue().get(b).target();
                        targets.add(target);
                        if (discovered.add(target)) {
                            queue.add(target);
                        }
                    }
                }
                assertEquals(List.copyOf(targets), List.copyOf(scg.successors(sc)), "successors by first edge");
            }
            assertEquals(List.copyOf(discovered), List.copyOf(scg.stateClasses()), "classes breadth-first");
        }

        @Test
        void listsPredecessorsInTheOrderTheBuildExpandedThem() {
            var scg = fan();
            var expected = new IdentityHashMap<StateClass, LinkedHashSet<StateClass>>();
            for (var sc : scg.stateClasses()) {
                for (var edges : scg.outgoingBranchEdges(sc).values()) {
                    for (var edge : edges) {
                        expected.computeIfAbsent(edge.target(), _ -> new LinkedHashSet<>()).add(sc);
                    }
                }
            }
            int widest = 0;
            for (var sc : scg.stateClasses()) {
                var preds = expected.getOrDefault(sc, new LinkedHashSet<>());
                assertEquals(List.copyOf(preds), List.copyOf(scg.predecessors(sc)));
                widest = Math.max(widest, preds.size());
            }
            assertEquals(21, widest, "a last class has one predecessor per way back, and the split");
            assertEquals(22, scg.successors(scg.initialClass()).size(), "twenty ways on and two branches");
        }

        @Test
        void pointsEveryEdgeAtTheGraphsOwnInstance_andFindsEqualCopies() {
            var scg = fan();
            var own = Collections.newSetFromMap(new IdentityHashMap<StateClass, Boolean>());
            own.addAll(scg.stateClasses());
            for (var sc : scg.stateClasses()) {
                for (var edges : scg.outgoingBranchEdges(sc).values()) {
                    for (var edge : edges) {
                        assertTrue(own.contains(edge.target()), "edge target is the graph's instance");
                    }
                }
            }
            var initial = scg.initialClass();
            var next = scg.successors(initial).iterator().next();
            var copy = new StateClass(next.marking(), next.firingDomain(), next.enabledTransitions(), next.readyEarliest());
            assertNotSame(next, copy);
            assertTrue(scg.successors(initial).contains(copy));
            assertTrue(scg.predecessors(copy).contains(initial));
            assertTrue(scg.stateClasses().contains(copy));
            assertFalse(scg.successors(copy).contains(initial));
        }

        @Test
        void returnsReadOnlyViews() {
            var scg = fan();
            var initial = scg.initialClass();
            var t0 = initial.enabledTransitions().getFirst();
            assertThrows(UnsupportedOperationException.class, () -> scg.stateClasses().remove(initial));
            assertThrows(UnsupportedOperationException.class, () -> scg.successors(initial).clear());
            assertThrows(UnsupportedOperationException.class, () -> scg.predecessors(initial).add(initial));
            assertThrows(UnsupportedOperationException.class, () -> scg.outgoingBranchEdges(initial).remove(t0));
            assertThrows(UnsupportedOperationException.class, () -> scg.branchEdges(initial, t0).clear());
            assertThrows(UnsupportedOperationException.class, () -> scg.enabledTransitions(initial).clear());
        }
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
