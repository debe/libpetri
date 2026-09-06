package org.libpetri.smt.z3;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.NetFlattener;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for {@link AbstractReplayer} — the pure (JNI-free) abstract
 * semantics used to confirm Spacer counterexamples (C3).
 *
 * <p>None of these tests touch Z3, so they run on machines without the native
 * library. The semantics under test mirror {@code lean/Libpetri/Basic.lean}
 * ({@code enabledA} / {@code fireA}) and the encoder arms
 * ({@code SmtEncoder.encodeEnabled} / {@code encodeFire} /
 * {@code encodeStepRelation} / {@code encodePropertyViolation}).
 */
class AbstractReplayerTest {

    private static final Place<String> A = Place.of("A", String.class);
    private static final Place<String> B = Place.of("B", String.class);
    private static final Place<String> R = Place.of("R", String.class);
    private static final Place<String> I = Place.of("I", String.class);
    private static final Place<String> C = Place.of("C", String.class);

    private static FlatNet flatten(PetriNet net) {
        return NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
    }

    private static MarkingState marking(Object... placeCounts) {
        var builder = MarkingState.builder();
        for (int i = 0; i < placeCounts.length; i += 2) {
            builder.tokens((Place<?>) placeCounts[i], (Integer) placeCounts[i + 1]);
        }
        return builder.build();
    }

    private static int[] vec(FlatNet flatNet, MarkingState m) {
        return AbstractReplayer.toVector(flatNet, m);
    }

    // === enabledA / fireA (Basic.lean enabledA/fireA; encodeEnabled/encodeFire arms) ===

    @Test
    void oneArc_enabledAndFire() {
        var t = Transition.builder("T").inputs(In.one(A)).outputs(Out.place(B)).build();
        var flat = flatten(PetriNet.builder("one").transitions(t).build());
        var ft = flat.transitions().getFirst();

        assertTrue(AbstractReplayer.enabledA(vec(flat, marking(A, 1)), ft));
        assertFalse(AbstractReplayer.enabledA(vec(flat, marking()), ft));

        int[] next = AbstractReplayer.fireA(vec(flat, marking(A, 1)), ft);
        assertEquals(marking(B, 1), AbstractReplayer.toMarking(flat, next));
    }

    @Test
    void consumeAll_allArc_emptiesThePlace() {
        // fireA consume-all arm: M'[p] = post[p] for an All place (Basic.lean
        // consumeAllAt; the encoder's consume-all arm).
        var t = Transition.builder("T").inputs(In.all(A)).outputs(Out.place(B)).build();
        var flat = flatten(PetriNet.builder("all").transitions(t).build());
        var ft = flat.transitions().getFirst();

        assertTrue(AbstractReplayer.enabledA(vec(flat, marking(A, 3)), ft));
        int[] next = AbstractReplayer.fireA(vec(flat, marking(A, 3)), ft);
        assertEquals(marking(B, 1), AbstractReplayer.toMarking(flat, next),
            "All must drain the place to post[p]=0 and add exactly one B token");
    }

    @Test
    void consumeAll_atLeastArc_gatesOnMinimumThenDrains() {
        var t = Transition.builder("T").inputs(In.atLeast(2, A)).outputs(Out.place(B)).build();
        var flat = flatten(PetriNet.builder("atleast").transitions(t).build());
        var ft = flat.transitions().getFirst();

        assertFalse(AbstractReplayer.enabledA(vec(flat, marking(A, 1)), ft),
            "AtLeast(2) must not enable below the minimum");
        assertTrue(AbstractReplayer.enabledA(vec(flat, marking(A, 3)), ft));
        int[] next = AbstractReplayer.fireA(vec(flat, marking(A, 3)), ft);
        assertEquals(marking(B, 1), AbstractReplayer.toMarking(flat, next),
            "AtLeast drains all available tokens (consume-all arm)");
    }

    @Test
    void resetArc_clearsToPostCount() {
        var t = Transition.builder("T").inputs(In.one(A)).reset(C).outputs(Out.place(B)).build();
        var flat = flatten(PetriNet.builder("reset").transitions(t).build());
        var ft = flat.transitions().getFirst();

        int[] next = AbstractReplayer.fireA(vec(flat, marking(A, 1, C, 5)), ft);
        assertEquals(marking(B, 1), AbstractReplayer.toMarking(flat, next),
            "reset place must jump to post[p] (= 0 here), not decrement");
    }

    @Test
    void inhibitorAndRead_gateWithoutConsuming() {
        var t = Transition.builder("T")
            .inputs(In.one(A)).read(R).inhibitor(I).outputs(Out.place(B)).build();
        var flat = flatten(PetriNet.builder("gates").transitions(t).build());
        var ft = flat.transitions().getFirst();

        assertTrue(AbstractReplayer.enabledA(vec(flat, marking(A, 1, R, 1)), ft));
        assertFalse(AbstractReplayer.enabledA(vec(flat, marking(A, 1)), ft),
            "read place empty must disable");
        assertFalse(AbstractReplayer.enabledA(vec(flat, marking(A, 1, R, 1, I, 1)), ft),
            "inhibited place marked must disable");

        int[] next = AbstractReplayer.fireA(vec(flat, marking(A, 1, R, 1)), ft);
        assertEquals(marking(B, 1, R, 1), AbstractReplayer.toMarking(flat, next),
            "a read place is tested, never consumed");
    }

    // === successors: unstrengthened step relation incl. env injection (VER-006) ===

    @Test
    void successors_includeEnvInjection_underTheBound() {
        var e = Place.of("E", String.class);
        var env = EnvironmentPlace.of(e);
        var t = Transition.builder("T").inputs(In.one(e)).outputs(Out.place(B)).build();
        var net = PetriNet.builder("env").transitions(t).build();
        var flat = NetFlattener.flatten(net, Set.of(env), EnvironmentAnalysisMode.bounded(1));

        // Empty marking: only the injection step exists.
        var fromEmpty = AbstractReplayer.successors(flat, vec(flat, marking()));
        assertEquals(1, fromEmpty.size());
        assertEquals("inject(E)", fromEmpty.getFirst().firing());
        assertEquals(marking(e, 1), AbstractReplayer.toMarking(flat, fromEmpty.getFirst().state()));

        // At the bound: injection is gated off, only the transition fires.
        var atBound = AbstractReplayer.successors(flat, vec(flat, marking(e, 1)));
        assertEquals(1, atBound.size());
        assertEquals("T", atBound.getFirst().firing());
        assertEquals(marking(B, 1), AbstractReplayer.toMarking(flat, atBound.getFirst().state()));
    }

    // === violates: the Bad(M) predicate (encodePropertyViolation arms) ===

    @Test
    void violates_deadlock_respectsSinkPlaces() {
        var t01 = Transition.builder("t01").inputs(In.one(A)).outputs(Out.place(B)).build();
        var t12 = Transition.builder("t12").inputs(In.one(B)).outputs(Out.place(C)).build();
        var flat = flatten(PetriNet.builder("chain").transitions(t01, t12).build());
        var dead = vec(flat, marking(C, 1));

        assertTrue(AbstractReplayer.violates(flat, SmtProperty.deadlockFree(), Set.of(), dead),
            "quiescent non-sink marking is a deadlock violation");
        assertFalse(AbstractReplayer.violates(flat, SmtProperty.deadlockFree(), Set.of(C), dead),
            "resting at a declared sink is not a violation");
        assertFalse(AbstractReplayer.violates(
            flat, SmtProperty.deadlockFree(), Set.of(), vec(flat, marking(A, 1))),
            "a marking with an enabled transition is not a deadlock");
    }

    /**
     * [VER-002] AC3–AC6: the two sink-sensitive predicates INVERT on the empty quiescent
     * marking, so neither subsumes the other. The replayer must decide each arm exactly
     * as {@code SmtEncoder.encodePropertyViolation} does.
     */
    @Test
    void violates_deadlockFreeAndTerminatesAtSink_invertOnTheEmptyMarking() {
        // Partial terminal: the only quiescent marking marks the sink B AND strands C.
        var fork = Transition.builder("t").inputs(In.one(A)).outputs(Out.and(B, C)).build();
        var partial = flatten(PetriNet.builder("partial").transitions(fork).build());
        var resting = vec(partial, marking(B, 1, C, 1));

        assertTrue(AbstractReplayer.violates(
            partial, SmtProperty.deadlockFree(), Set.of(B), resting),
            "AC3: a quiescent marking that strands C violates DeadlockFree, sink or not");
        assertFalse(AbstractReplayer.violates(
            partial, SmtProperty.terminatesAtSink(), Set.of(B), resting),
            "AC5: the sink B is marked, so TerminatesAtSink is satisfied");

        // Drained terminal: the only quiescent marking is the empty one.
        var sink = Transition.builder("t").inputs(In.one(A)).build();
        var drained = flatten(PetriNet.builder("drained").places(B).transitions(sink).build());
        var empty = vec(drained, marking());

        assertFalse(AbstractReplayer.violates(
            drained, SmtProperty.deadlockFree(), Set.of(B), empty),
            "AC4: the empty quiescent marking strands nothing");
        assertTrue(AbstractReplayer.violates(
            drained, SmtProperty.terminatesAtSink(), Set.of(B), empty),
            "AC6: no declared sink was reached");
    }

    @Test
    void violates_deadlock_relaxesInjectableEnvInputs() {
        // A transition waiting only on an injectable env input is NOT deadlocked
        // (VER-006 relaxed enablement, mirroring the Error rule).
        var e = Place.of("E", String.class);
        var env = EnvironmentPlace.of(e);
        var t = Transition.builder("T").inputs(In.one(e)).outputs(Out.place(B)).build();
        var net = PetriNet.builder("env").transitions(t).build();

        // B carries the token: under [VER-002] AC4 the EMPTY quiescent marking strands
        // nothing and is not a DeadlockFree violation, so the stuck case needs a token
        // parked in a non-sink place to stay meaningful.
        var injectable = NetFlattener.flatten(net, Set.of(env), EnvironmentAnalysisMode.alwaysAvailable());
        assertFalse(AbstractReplayer.violates(
            injectable, SmtProperty.deadlockFree(), Set.of(), vec(injectable, marking(B, 1))),
            "waiting for injectable env input is not a deadlock");

        var ignored = NetFlattener.flatten(net, Set.of(env), EnvironmentAnalysisMode.ignore());
        assertTrue(AbstractReplayer.violates(
            ignored, SmtProperty.deadlockFree(), Set.of(), vec(ignored, marking(B, 1))),
            "without injection modeling the same marking is genuinely stuck");
    }

    @Test
    void violates_mutualExclusion_boundAndUnreachable() {
        var t = Transition.builder("T").inputs(In.one(A)).outputs(Out.and(B, C)).build();
        var flat = flatten(PetriNet.builder("props").transitions(t).build());

        assertTrue(AbstractReplayer.violates(
            flat, SmtProperty.mutualExclusion(B, C), Set.of(), vec(flat, marking(B, 1, C, 1))));
        assertFalse(AbstractReplayer.violates(
            flat, SmtProperty.mutualExclusion(B, C), Set.of(), vec(flat, marking(B, 1))));

        assertTrue(AbstractReplayer.violates(
            flat, SmtProperty.placeBound(B, 1), Set.of(), vec(flat, marking(B, 2))));
        assertFalse(AbstractReplayer.violates(
            flat, SmtProperty.placeBound(B, 1), Set.of(), vec(flat, marking(B, 1))));

        assertTrue(AbstractReplayer.violates(
            flat, SmtProperty.unreachable(Set.of(B, C)), Set.of(), vec(flat, marking(B, 1, C, 1))));
        assertFalse(AbstractReplayer.violates(
            flat, SmtProperty.unreachable(Set.of(B, C)), Set.of(), vec(flat, marking(C, 1))));
    }

    // === replay: chaining the order-free decoded set into an abstract run ===

    /** p0(1) -> t01 -> p1 -> t12 -> p2, then stuck: the dead-end chain. */
    private static FlatNet deadEndChain() {
        var t01 = Transition.builder("t01").inputs(In.one(A)).outputs(Out.place(B)).build();
        var t12 = Transition.builder("t12").inputs(In.one(B)).outputs(Out.place(C)).build();
        return flatten(PetriNet.builder("dead-end").transitions(t01, t12).build());
    }

    @Test
    void replay_chainsDecodedStates_toTheDeadlock() {
        var flat = deadEndChain();
        var decoded = Set.of(marking(A, 1), marking(B, 1), marking(C, 1));

        var outcome = AbstractReplayer.replay(
            flat, marking(A, 1), decoded, SmtProperty.deadlockFree(), Set.of());

        var chained = assertInstanceOf(AbstractReplayer.ReplayOutcome.Confirmed.class, outcome);
        assertEquals(List.of(marking(A, 1), marking(B, 1), marking(C, 1)), chained.trace(),
            "the replay must order the set into the actual run");
        assertEquals(List.of("t01", "t12"), chained.firings());
    }

    @Test
    void replay_bridgesGapsOfUpToThreeSteps() {
        // Decoded set holds only the endpoints; the three firings in between
        // must be bridged by the bounded BFS.
        var t = Transition.builder("t").inputs(In.one(A)).outputs(Out.place(B)).build();
        var flat = flatten(PetriNet.builder("conserved").transitions(t).build());
        var decoded = Set.of(marking(A, 3), marking(B, 3));

        var outcome = AbstractReplayer.replay(
            flat, marking(A, 3), decoded, SmtProperty.placeBound(B, 2), Set.of());

        var chained = assertInstanceOf(AbstractReplayer.ReplayOutcome.Confirmed.class, outcome);
        assertEquals(4, chained.trace().size(), "3 bridged steps: (3,0) .. (0,3)");
        assertEquals(marking(B, 3), chained.trace().getLast());
        assertEquals(List.of("t", "t", "t"), chained.firings());
    }

    @Test
    void replay_violationAtTheInitialMarking() {
        var t = Transition.builder("t").inputs(In.one(A)).outputs(Out.place(B)).build();
        var flat = flatten(PetriNet.builder("trivial").transitions(t).build());

        var outcome = AbstractReplayer.replay(
            flat, marking(A, 1), Set.of(marking(A, 1)), SmtProperty.placeBound(A, 0), Set.of());

        var chained = assertInstanceOf(AbstractReplayer.ReplayOutcome.Confirmed.class, outcome);
        assertEquals(List.of(marking(A, 1)), chained.trace());
        assertTrue(chained.firings().isEmpty());
    }

    @Test
    void replay_initialMarkingMissingFromSet_isExhausted() {
        // Nothing to anchor the search on: the verdict must stand, unconfirmed.
        var flat = deadEndChain();

        var outcome = AbstractReplayer.replay(
            flat, marking(A, 1), Set.of(marking(B, 1)), SmtProperty.deadlockFree(), Set.of());

        var exhausted = assertInstanceOf(AbstractReplayer.ReplayOutcome.Exhausted.class, outcome);
        assertTrue(exhausted.reason().contains("initial marking"), exhausted.reason());
    }

    @Test
    void replay_noChainExists_isNoChain() {
        // The garbage state is unreachable and the property is never violated, so
        // the search covers the space and comes back empty — the only outcome that
        // may withdraw a VIOLATED verdict.
        var flat = deadEndChain();
        var decoded = Set.of(marking(A, 1), marking(A, 7, B, 7, C, 7));

        var outcome = AbstractReplayer.replay(
            flat, marking(A, 1), decoded, SmtProperty.placeBound(C, 5), Set.of());

        assertInstanceOf(AbstractReplayer.ReplayOutcome.NoChain.class, outcome);
    }

    @Test
    void replay_budgetExhaustion_isExhausted() {
        var flat = deadEndChain();
        var decoded = Set.of(marking(A, 1), marking(C, 1));

        var outcome = AbstractReplayer.replay(
            flat, marking(A, 1), decoded, SmtProperty.deadlockFree(), Set.of(),
            AbstractReplayer.MAX_SEGMENT_STEPS, 0);

        var exhausted = assertInstanceOf(AbstractReplayer.ReplayOutcome.Exhausted.class, outcome);
        assertTrue(exhausted.reason().contains("budget"), exhausted.reason());
    }

    @Test
    void replay_emptySet_isExhausted() {
        var outcome = AbstractReplayer.replay(
            deadEndChain(), marking(A, 1), Set.of(), SmtProperty.deadlockFree(), Set.of());
        assertInstanceOf(AbstractReplayer.ReplayOutcome.Exhausted.class, outcome);
    }

    @Test
    void replay_deadEndDecodedState_stillFindsTheChain() {
        // A(1) forks: t_dead moves the token to the dead-end place D (nothing left to
        // fire, but D is NOT a violation), t_ab starts the chain A -> B -> C that
        // violates placeBound(C, 0). D is among the decoded states and sits one step
        // from M0, so a greedy hop-by-hop search takes it first, deletes it from the
        // remaining set and gets stuck — the divergence this global search removes.
        var d = Place.of("D", String.class);
        var tDead = Transition.builder("t_dead").inputs(In.one(A)).outputs(Out.place(d)).build();
        var tAb = Transition.builder("t_ab").inputs(In.one(A)).outputs(Out.place(B)).build();
        var tBc = Transition.builder("t_bc").inputs(In.one(B)).outputs(Out.place(C)).build();
        var flat = flatten(PetriNet.builder("fork").transitions(tDead, tAb, tBc).build());
        var decoded = Set.of(marking(A, 1), marking(d, 1), marking(B, 1), marking(C, 1));
        assertEquals("t_dead", AbstractReplayer.successors(flat, vec(flat, marking(A, 1))).getFirst().firing(),
            "the dead end must be the first successor, or this net would not pin the greedy failure");

        var outcome = AbstractReplayer.replay(
            flat, marking(A, 1), decoded, SmtProperty.placeBound(C, 0), Set.of());

        var confirmed = assertInstanceOf(AbstractReplayer.ReplayOutcome.Confirmed.class, outcome);
        assertEquals(List.of(marking(A, 1), marking(B, 1), marking(C, 1)), confirmed.trace());
        assertEquals(List.of("t_ab", "t_bc"), confirmed.firings());
    }

    @Test
    void replay_unchainableSet_isExhaustedNotNoChain() {
        // Five firings between the only two decoded states: no segment of at most
        // MAX_SEGMENT_STEPS bridges them, so the search is CUT SHORT at the segment
        // bound. That is an absence of evidence, not evidence of absence — reporting
        // NoChain here would withdraw a correct VIOLATED verdict (C4).
        var t = Transition.builder("t").inputs(In.one(A)).outputs(Out.place(B)).build();
        var flat = flatten(PetriNet.builder("conserved").transitions(t).build());
        var decoded = Set.of(marking(A, 5), marking(B, 5));

        var outcome = AbstractReplayer.replay(
            flat, marking(A, 5), decoded, SmtProperty.placeBound(B, 4), Set.of());

        var exhausted = assertInstanceOf(AbstractReplayer.ReplayOutcome.Exhausted.class, outcome);
        assertTrue(exhausted.reason().contains("segment budget"), exhausted.reason());
    }

    @Test
    void replay_nodeBudgetCountsAdmittedNodesIncludingTheRoot() {
        // The budget unit is nodes ADMITTED to the search — the root plus every
        // non-dominated successor — tripped with >=. A budget of 1 is therefore
        // already spent by the root, so not one successor is admitted; a budget of 2
        // admits exactly one more, which is the violating marking here.
        var t = Transition.builder("t").inputs(In.one(A)).outputs(Out.place(B)).build();
        var flat = flatten(PetriNet.builder("conserved").transitions(t).build());
        var decoded = Set.of(marking(A, 2), marking(A, 1, B, 1));

        var atOne = AbstractReplayer.replay(
            flat, marking(A, 2), decoded, SmtProperty.placeBound(B, 0), Set.of(),
            AbstractReplayer.MAX_SEGMENT_STEPS, 1);
        var exhausted = assertInstanceOf(AbstractReplayer.ReplayOutcome.Exhausted.class, atOne);
        assertTrue(exhausted.reason().contains("1 nodes admitted"), exhausted.reason());

        var atTwo = AbstractReplayer.replay(
            flat, marking(A, 2), decoded, SmtProperty.placeBound(B, 0), Set.of(),
            AbstractReplayer.MAX_SEGMENT_STEPS, 2);
        var confirmed = assertInstanceOf(AbstractReplayer.ReplayOutcome.Confirmed.class, atTwo);
        assertEquals(List.of(marking(A, 2), marking(A, 1, B, 1)), confirmed.trace());
    }

    @Test
    void replay_dominatedSuccessorsDoNotSpendTheBudget() {
        // A diamond re-reaches the same marking by two routes; the second arrival is
        // dominated and dropped BEFORE the budget is charged. Counting generated
        // successors instead would make this net exhaust at a budget the search
        // provably does not need.
        var tAb = Transition.builder("t_ab").inputs(In.one(A)).outputs(Out.place(B)).build();
        var tAr = Transition.builder("t_ar").inputs(In.one(A)).outputs(Out.place(R)).build();
        var tBc = Transition.builder("t_bc").inputs(In.one(B)).outputs(Out.place(C)).build();
        var tRc = Transition.builder("t_rc").inputs(In.one(R)).outputs(Out.place(C)).build();
        var flat = flatten(
            PetriNet.builder("diamond").transitions(tAb, tAr, tBc, tRc).build());
        var decoded = Set.of(marking(A, 1));

        // Admitted: root, B, R, C = 4. The second route to C is dominated.
        var outcome = AbstractReplayer.replay(
            flat, marking(A, 1), decoded, SmtProperty.placeBound(C, 0), Set.of(),
            AbstractReplayer.MAX_SEGMENT_STEPS, 4);

        var confirmed = assertInstanceOf(AbstractReplayer.ReplayOutcome.Confirmed.class, outcome);
        assertEquals(marking(C, 1), confirmed.trace().getLast());
    }
}
