package org.libpetri.analysis;

import org.junit.jupiter.api.Test;
import org.libpetri.analysis.BranchOutcomes.Deposit;
import org.libpetri.analysis.BranchOutcomes.Outcome;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.core.TransitionAction;

import java.time.Duration;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [IO-013] / [IO-014]: the ways one firing can deposit, for every analysis that expands an
 * output spec ({@link BranchOutcomes}).
 */
class BranchOutcomesTest {

    private static final Place<Integer> A = Place.of("a", Integer.class);
    private static final Place<Integer> B = Place.of("b", Integer.class);
    private static final Place<Integer> C = Place.of("c", Integer.class);

    private static Transition forward(In input) {
        return Transition.builder("t")
            .inputs(input)
            .outputs(Out.xor(Out.place(C), Out.timeout(Duration.ofMillis(50), Out.forwardInput(A, B))))
            .action(TransitionAction.fork())
            .build();
    }

    /** The repro of the wrong Proven: the timeout forwards both consumed tokens. */
    @Test
    void anExactlyTwoForwardDepositsTwo() {
        var got = BranchOutcomes.outcomes(forward(In.exactly(2, A)));
        assertEquals(3, got.size());
        assertEquals(Map.of(C, new Deposit.Tokens(1)), got.get(0).deposits());
        // The action may write the forward's target itself: one token ([IO-016]).
        assertEquals(Map.of(B, new Deposit.Tokens(1)), got.get(1).deposits());
        // The timeout forwards both consumed tokens ([IO-014]).
        assertEquals(Map.of(B, new Deposit.Tokens(2)), got.get(2).deposits());
    }

    /** A One forward deposits one token, which the action branch already models. */
    @Test
    void aOneForwardAddsNoOutcome() {
        assertEquals(2, BranchOutcomes.outcomes(forward(In.one(A))).size());
    }

    /** On timeout the marking receives the child's tokens and nothing else ([IO-013] AC5). */
    @Test
    void aTimeoutDoesNotWriteItsSiblings() {
        var t = Transition.builder("t")
            .inputs(In.one(A))
            .outputs(Out.and(Out.place(C), Out.timeout(Duration.ofMillis(50), Out.place(B))))
            .action(TransitionAction.fork())
            .build();
        var got = BranchOutcomes.outcomes(t);
        assertEquals(2, got.size());
        assertEquals(Map.of(B, new Deposit.Tokens(1), C, new Deposit.Tokens(1)), got.get(0).deposits());
        assertEquals(Map.of(B, new Deposit.Tokens(1)), got.get(1).deposits());
    }

    @Test
    void aDrainedForwardIsMarkingDependentAndFound() {
        for (var input : new In[] {In.all(A), In.atLeast(2, A)}) {
            var t = forward(input);
            var got = BranchOutcomes.outcomes(t);
            assertEquals(Map.of(B, new Deposit.Drained(A)), got.get(2).deposits());
            var found = BranchOutcomes.drainedForward(PetriNet.builder("n").transition(t).build());
            assertTrue(found.isPresent());
            assertEquals("a", found.get().from());
            assertEquals("b", found.get().to());
        }
    }

    @Test
    void noOutputSpecIsOneEmptyOutcome() {
        var t = Transition.builder("t").inputs(In.one(A)).build();
        assertEquals(List.of(Outcome.EMPTY), BranchOutcomes.outcomes(t));
    }

    /** `t: <input on a> -> xor(c, timeout(50, forwardInput(a, b)))` from `a = 2`. */
    private static TreeSet<Integer> bCounts(In input) {
        var net = PetriNet.builder("forward").transition(forward(input)).build();
        var graph = StateClassGraph.build(net, MarkingState.builder().tokens(A, 2).build(), 100);
        assertTrue(graph.isComplete());
        var counts = new TreeSet<Integer>();
        graph.stateClasses().forEach(sc -> counts.add(sc.marking().tokens(B)));
        return counts;
    }

    /**
     * [IO-014]: Exactly(2) puts two tokens in b; the action may also write b itself, one token
     * ([IO-016]).
     */
    @Test
    void anExactlyTwoForwardDepositsTwoInTheStateSpace() {
        assertEquals(new TreeSet<>(List.of(0, 1, 2)), bCounts(In.exactly(2, A)));
    }

    /** All drains the batch and the timeout forwards all of it. */
    @Test
    void anAllForwardDepositsTheDrainedBatchInTheStateSpace() {
        assertEquals(new TreeSet<>(List.of(0, 1, 2)), bCounts(In.all(A)));
    }
}
