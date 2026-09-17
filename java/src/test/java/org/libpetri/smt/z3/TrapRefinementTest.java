package org.libpetri.smt.z3;

import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.smt.z3.StateEquationQuery.Origin;
import org.junit.jupiter.api.Test;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.smt.z3.StateEquationNets.*;

/**
 * [VER-018] trap refinement: an initially marked trap the candidate leaves empty, with
 * consume-all and reset arcs counted as removals. Mirrors the trap case of
 * {@code typescript/tests/verification/state-equation-phase.test.ts}.
 */
class TrapRefinementTest {

    private static final Place<String> A = place("a");
    private static final Place<String> B = place("b");
    private static final Place<String> C = place("c");

    private static Transition ab() {
        return Transition.builder("ab").inputs(In.one(A)).outputs(Out.place(B)).build();
    }

    private static Transition ba() {
        return Transition.builder("ba").inputs(In.one(B)).outputs(Out.place(A)).build();
    }

    @Test
    void findsAnInitiallyMarkedTrapTheCandidateEmpties() {
        // {a, b} is a trap: ab moves a token a -> b, ba moves it back.
        var flat = flatten(PetriNet.builder("loop").transitions(ab(), ba()).build());
        var trap = TrapRefinement.refutingTrap(flat, marking(flat, "a", 1), candidate(flat));
        assertNotNull(trap);
        assertEquals(Origin.TRAP, trap.origin());
        assertEquals(BigInteger.ONE.negate(), trap.constant());
        assertEquals("a + b >= 1", StateEquationQuery.formatInequality(flat, trap));
    }

    @Test
    void aConsumeAllDrainIsARemoval() {
        // drain: all(b) -> c empties b without feeding {a, b}: no longer a trap.
        var drain = Transition.builder("drain").inputs(In.all(B)).outputs(Out.place(C)).build();
        var flat = flatten(PetriNet.builder("drained").transitions(ab(), ba(), drain).build());
        assertNull(TrapRefinement.refutingTrap(flat, marking(flat, "a", 1), candidate(flat, "c", 1)));
    }

    @Test
    void aResetArcIsARemoval() {
        // clear resets b while it feeds only c.
        var clear = Transition.builder("clear").inputs(In.one(C)).reset(B).outputs(Out.place(C)).build();
        var flat = flatten(PetriNet.builder("resetDrain").transitions(ab(), ba(), clear).build());
        assertNull(TrapRefinement.refutingTrap(flat, marking(flat, "a", 1), candidate(flat, "c", 1)));
        // {c} is a trap of its own, and the smallest one marked.
        var trap = TrapRefinement.refutingTrap(flat, marking(flat, "a", 1, "c", 1), candidate(flat));
        assertEquals("c >= 1", StateEquationQuery.formatInequality(flat, trap));
    }

    @Test
    void shrinksTheTrapToALocallyMinimalOne() {
        var cc = Transition.builder("cc").inputs(In.one(C)).outputs(Out.place(C)).build();
        var flat = flatten(PetriNet.builder("shrink").transitions(ab(), ba(), cc).build());
        // {a, b, c} is a marked trap; {c} is the first smaller one that stays marked.
        assertEquals("c >= 1", StateEquationQuery.formatInequality(flat,
            TrapRefinement.refutingTrap(flat, marking(flat, "a", 1, "c", 1), candidate(flat))));
        // With c marked in the candidate, only {a, b} is left to refute it.
        assertEquals("a + b >= 1", StateEquationQuery.formatInequality(flat,
            TrapRefinement.refutingTrap(flat, marking(flat, "a", 1, "c", 1), candidate(flat, "c", 2))));
        // A trap nothing marks at M0 proves nothing.
        assertNull(TrapRefinement.refutingTrap(flat, marking(flat), candidate(flat)));
    }

    @Test
    void theJoinLeavesTheSkippedCandidateWithoutATrap() {
        var join = joinWithSkip();
        var flat = join.flat();
        int[] initial = AbstractReplayer.toVector(flat, join.m0());
        assertNull(TrapRefinement.refutingTrap(flat, initial, candidate(flat, "hasdata", 1, "skipped", 1)));
        assertEquals("bData + bEmpty + done + ready1 + skipped + start >= 1",
            StateEquationQuery.formatInequality(flat, TrapRefinement.refutingTrap(flat, initial, candidate(flat))));
    }
}
