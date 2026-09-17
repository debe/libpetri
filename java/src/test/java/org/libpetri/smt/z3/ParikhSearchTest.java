package org.libpetri.smt.z3;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.z3.ParikhSearch.WitnessOutcome;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.smt.z3.StateEquationNets.*;

/**
 * [VER-018] the witness search within a candidate's firing counts, and the environment
 * guard split: a found run survives injection, a completed search does not. Mirrors the
 * search cases of {@code typescript/tests/verification/state-equation-phase.test.ts}; the
 * predicate is {@link AbstractReplayer#violates}, the bad-state check replay already uses.
 */
class ParikhSearchTest {

    private static Predicate<int[]> deadlock(FlatNet flat, Set<Place<?>> sinks) {
        return state -> AbstractReplayer.violates(flat, SmtProperty.deadlockFree(), sinks, state);
    }

    /** {@code produce} may fire {@code produce} times and {@code cancel} once; nothing else fires. */
    private static long[] produceThenCancel(FlatNet flat, long produce) {
        return flat.transitions().stream()
            .mapToLong(ft -> ft.name().equals("produce") ? produce : ft.name().equals("cancel") ? 1 : 0)
            .toArray();
    }

    @Test
    void searchesRunsWithinTheFiringCountsAndFindsTheViolationTheyReach() {
        var queue = queueAndBundle(2, true);
        var flat = queue.flat();
        int[] initial = AbstractReplayer.toVector(flat, queue.m0());
        var bad = deadlock(flat, queue.sinks(true));
        // Both units produced and the signal cancelled: nothing is enabled and q strands.
        var found = ParikhSearch.searchWithinCounts(flat, initial, produceThenCancel(flat, 2), bad);
        var run = assertInstanceOf(WitnessOutcome.Found.class, found);
        assertEquals(List.of("produce", "produce", "cancel"), run.steps());
        assertEquals(run.steps().size() + 1, run.states().size());
        assertArrayEquals(initial, run.states().getFirst());
        assertArrayEquals(marking(flat, "q", 2, "cancelled", 1), run.states().getLast());
        assertEquals(6, run.nodes());
        // One unit leaves the producer enabled, so no run within these counts is quiescent.
        assertEquals(new WitnessOutcome.None(4),
            ParikhSearch.searchWithinCounts(flat, initial, produceThenCancel(flat, 1), bad));
    }

    @Test
    void theQueueRunIsTheOneTheSpecNames() {
        var queue = queueAndBundle(3, true);
        var flat = queue.flat();
        var found = ParikhSearch.searchWithinCounts(flat, AbstractReplayer.toVector(flat, queue.m0()),
            produceThenCancel(flat, 3), deadlock(flat, queue.sinks(true)));
        var run = assertInstanceOf(WitnessOutcome.Found.class, found);
        assertEquals(List.of("produce", "produce", "produce", "cancel"), run.steps());
    }

    /**
     * The guard split. {@code gatedStrand} strands {@code q} behind a gate that never opens.
     * {@code Found} must survive injection: the run fires only counted transitions, and
     * {@code gate} stays disabled under relax-env enablement because {@code gateOpen} is not
     * injectable, so the marking really is stuck against any environment.
     */
    @Test
    void searchesANetTheEnvironmentCanInjectIntoAndReportsAWitnessItReaches() {
        var env = gatedStrand(true);
        assertEquals(1, env.flat().environmentInjection().size());
        // Refusing at the door would have answered `Exhausted` here, and the leg would never run.
        var found = ParikhSearch.searchWithinCounts(env.flat(), env.initial(), env.counts(1), env.bad());
        var run = assertInstanceOf(WitnessOutcome.Found.class, found);
        assertEquals(List.of("fill"), run.steps());
    }

    /** {@code None} must not survive injection: an injected token could enable a run the search never considered. */
    @Test
    void downgradesACompletedSearchToExhaustedUnderInjectionWhereItWouldAnswerNone() {
        // Counts that permit no firing: the initial marking is not quiescent, so nothing is bad
        // and the search completes having explored every run it is allowed.
        var plain = gatedStrand(false);
        assertTrue(plain.flat().environmentInjection().isEmpty());
        assertEquals(new WitnessOutcome.None(1),
            ParikhSearch.searchWithinCounts(plain.flat(), plain.initial(), plain.counts(0), plain.bad()));

        var env = gatedStrand(true);
        var outcome = ParikhSearch.searchWithinCounts(env.flat(), env.initial(), env.counts(0), env.bad());
        var exhausted = assertInstanceOf(WitnessOutcome.Exhausted.class, outcome);
        assertTrue(exhausted.reason().contains("environment injection"), exhausted.reason());
        // The search ran before reporting, rather than refusing at the door.
        assertTrue(exhausted.nodes() > 0);
    }

    /**
     * The budget counts admitted nodes, root included, and trips when a new node would be
     * admitted. Five nodes cover {@code M0} and the distinct runs of up to two firings; the
     * witness is the sixth.
     */
    @Test
    void stopsAtTheNodeBudgetWithTheReasonItReports() {
        var queue = queueAndBundle(2, true);
        var flat = queue.flat();
        int[] initial = AbstractReplayer.toVector(flat, queue.m0());
        var bad = deadlock(flat, queue.sinks(true));
        assertEquals(new WitnessOutcome.Exhausted("search budget exhausted (5 nodes)", 5),
            ParikhSearch.searchWithinCounts(flat, initial, produceThenCancel(flat, 2), bad, 5));
        assertInstanceOf(WitnessOutcome.Found.class,
            ParikhSearch.searchWithinCounts(flat, initial, produceThenCancel(flat, 2), bad, 6));
        // A marking that is already bad needs no node beyond the root, whatever the budget.
        var stuck = ParikhSearch.searchWithinCounts(flat, marking(flat, "q", 1), produceThenCancel(flat, 2), bad, 0);
        var run = assertInstanceOf(WitnessOutcome.Found.class, stuck);
        assertEquals(List.of(), run.steps());
        assertEquals(1, run.nodes());
    }

    /**
     * A {@code Bounded(k)} environment caps what a firing may leave in the env place:
     * {@code emit} puts a second token into {@code sig} past the cap of one, so that run is not
     * a step of the encoded system and the search does not take it.
     */
    @Test
    void prunesAFiringThatBreaksTheEnvironmentCap() {
        var start = place("start");
        var over = place("over");
        var sig = EnvironmentPlace.of(place("sig"));
        var net = PetriNet.builder("capped").transitions(
            Transition.builder("emit").inputs(In.one(start)).outputs(Out.place(sig.place())).build(),
            Transition.builder("overflow").inputs(In.one(sig.place())).outputs(Out.place(over)).build()
        ).build();
        long[] counts = {1, 1};
        var uncapped = flatten(net);
        int sigIdx = indexOf(uncapped, "sig");
        var found = ParikhSearch.searchWithinCounts(uncapped, marking(uncapped, "start", 1, "sig", 1), counts,
            state -> state[sigIdx] > 1);
        assertEquals(List.of("emit"), assertInstanceOf(WitnessOutcome.Found.class, found).steps());

        var capped = NetFlattener.flatten(net, Set.of(sig), EnvironmentAnalysisMode.bounded(1));
        // `emit` first breaks the cap and is pruned; `overflow` then `emit` stays within it. The
        // search completes without a witness, and injection downgrades the answer.
        assertEquals(new WitnessOutcome.Exhausted("environment injection is not searched", 3),
            ParikhSearch.searchWithinCounts(capped, marking(capped, "start", 1, "sig", 1), counts,
                state -> state[sigIdx] > 1));
    }

    /** A short counts vector never lets a transition fire. */
    @Test
    void readsAMissingCountAsZero() {
        var queue = queueAndBundle(1, true);
        var flat = queue.flat();
        assertEquals(new WitnessOutcome.None(1), ParikhSearch.searchWithinCounts(flat,
            AbstractReplayer.toVector(flat, queue.m0()), new long[0], deadlock(flat, queue.sinks(true))));
    }
}
