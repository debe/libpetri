package org.libpetri.smt;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.*;

/**
 * [VER-024]: stubborn-set reduction of the enumeration route.
 *
 * <p>{@code fork: start -> s0_0 ... s(k-1)_0}, then per subnet {@code i} a cycle (or, with
 * {@code chain}, a chain ending in {@code s(i)_n}) {@code s(i)_j -> s(i)_(j+1)}.
 */
class StubbornSetsTest {

    private record Forked(PetriNet net, MarkingState m0, List<Place<?>> ends) {}

    private static Place<String> s(int i, int j) {
        return Place.of("s" + i + "_" + j, String.class);
    }

    private static Forked forked(int k, int n, boolean chain) {
        var start = Place.of("start", String.class);
        var transitions = new ArrayList<Transition>();
        var firsts = new Place<?>[k];
        for (int i = 0; i < k; i++) firsts[i] = s(i, 0);
        transitions.add(Transition.builder("fork").inputs(In.one(start)).outputs(Out.and(firsts)).build());
        var ends = new ArrayList<Place<?>>();
        for (int i = 0; i < k; i++) {
            for (int j = 0; j < n; j++) {
                var to = chain ? s(i, j + 1) : s(i, (j + 1) % n);
                transitions.add(Transition.builder("t" + i + "_" + j)
                    .inputs(In.one(s(i, j))).outputs(Out.place(to)).build());
            }
            ends.add(s(i, n));
        }
        var net = StructureOnly.bind(PetriNet.builder("fork-" + k + "x" + n + (chain ? "-chain" : ""))
            .transitions(transitions.toArray(new Transition[0])).build());
        return new Forked(net, MarkingState.builder().tokens(start, 1).build(), List.copyOf(ends));
    }

    private static int classes(SmtVerificationResult result) {
        var m = Pattern.compile("State classes: (\\d+)").matcher(result.report());
        assertTrue(m.find(), result.report());
        return Integer.parseInt(m.group(1));
    }

    @Test
    void closesKIndependentCyclesInOnePlusNClassesInsteadOfOnePlusNToTheK_AC2() {
        var f = forked(3, 4, false);
        var reduced = SmtVerifier.forNet(f.net()).initialMarking(f.m0())
            .property(SmtProperty.deadlockFree()).verify();
        var full = SmtVerifier.forNet(f.net()).initialMarking(f.m0())
            .property(SmtProperty.deadlockFree()).partialOrderReduction(false).verify();
        assertTrue(reduced.isProven(), reduced.report());
        assertTrue(full.isProven(), full.report());
        assertEquals(SmtVerificationResult.Route.ENUMERATION, reduced.route(), reduced.report());
        assertEquals(1 + 4, classes(reduced));
        assertEquals(1 + 64, classes(full));
        assertTrue(reduced.report().contains("  Stubborn-set reduction (VER-024): on"), reduced.report());
        assertFalse(full.report().contains("Stubborn-set reduction"), full.report());
    }

    @Test
    void keepsEveryDeadMarking_AC1() {
        var f = forked(3, 3, true);
        var violated = SmtVerifier.forNet(f.net()).initialMarking(f.m0())
            .property(SmtProperty.deadlockFree()).verify();
        assertTrue(violated.isViolated(), violated.report());
        assertEquals(1 + 3 * 3, violated.counterexampleTransitions().size(), violated.report());
        assertEquals(Boolean.TRUE, violated.counterexampleConfirmed());
        assertEquals(2 + 3 * 3, classes(violated));
        var proven = SmtVerifier.forNet(f.net()).initialMarking(f.m0())
            .property(SmtProperty.deadlockFree()).sinkPlaces(f.ends().toArray(new Place<?>[0])).verify();
        assertTrue(proven.isProven(), proven.report());
    }

    @Test
    void treatsAResetAndADepositOnOnePlaceAsDependent() {
        // a_produce deposits into r, b_reset empties it. Firing b_reset last leaves r empty,
        // firing it first strands the token a_produce deposits later: only that order violates.
        var x = Place.of("x", String.class);
        var y = Place.of("y", String.class);
        var r = Place.of("r", String.class);
        var done = Place.of("done", String.class);
        var net = StructureOnly.bind(PetriNet.builder("reset-vs-deposit").transitions(
            Transition.builder("a_produce").inputs(In.one(x)).outputs(Out.place(r)).build(),
            Transition.builder("b_reset").inputs(In.one(y)).reset(r).outputs(Out.place(done)).build()
        ).build());
        var m0 = MarkingState.builder().tokens(x, 1).tokens(y, 1).build();
        for (boolean reduce : new boolean[] {true, false}) {
            // Atomic firing: the reset would otherwise split a_produce in flight ([VER-004]).
            var result = SmtVerifier.forNet(net).initialMarking(m0).property(SmtProperty.deadlockFree())
                .sinkPlaces(done).assumeAtomicFiring(true).partialOrderReduction(reduce).verify();
            assertTrue(result.isViolated(), result.report());
            if (reduce) assertEquals(List.of("b_reset", "a_produce"), result.counterexampleTransitions());
        }
    }

    @Test
    void leavesASafetyPropertyOnTheFullGraph_AC3() {
        var f = forked(3, 4, false);
        var result = SmtVerifier.forNet(f.net()).initialMarking(f.m0())
            .property(SmtProperty.placeBound(s(0, 0), 1)).linearBound(false).verify();
        assertTrue(result.isProven(), result.report());
        assertEquals(SmtVerificationResult.Route.ENUMERATION, result.route(), result.report());
        assertEquals(1 + 64, classes(result));
        assertFalse(result.report().contains("Stubborn-set reduction"), result.report());
    }
}
