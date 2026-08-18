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
        assertEquals("env_inject_E", fromEmpty.getFirst().firing());
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

    @Test
    void violates_deadlock_relaxesInjectableEnvInputs() {
        // A transition waiting only on an injectable env input is NOT deadlocked
        // (VER-006 relaxed enablement, mirroring the Error rule).
        var e = Place.of("E", String.class);
        var env = EnvironmentPlace.of(e);
        var t = Transition.builder("T").inputs(In.one(e)).outputs(Out.place(B)).build();
        var net = PetriNet.builder("env").transitions(t).build();

        var injectable = NetFlattener.flatten(net, Set.of(env), EnvironmentAnalysisMode.alwaysAvailable());
        assertFalse(AbstractReplayer.violates(
            injectable, SmtProperty.deadlockFree(), Set.of(), vec(injectable, marking())),
            "waiting for injectable env input is not a deadlock");

        var ignored = NetFlattener.flatten(net, Set.of(env), EnvironmentAnalysisMode.ignore());
        assertTrue(AbstractReplayer.violates(
            ignored, SmtProperty.deadlockFree(), Set.of(), vec(ignored, marking())),
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

        var chained = assertInstanceOf(AbstractReplayer.ReplayOutcome.Chained.class, outcome);
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

        var chained = assertInstanceOf(AbstractReplayer.ReplayOutcome.Chained.class, outcome);
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

        var chained = assertInstanceOf(AbstractReplayer.ReplayOutcome.Chained.class, outcome);
        assertEquals(List.of(marking(A, 1)), chained.trace());
        assertTrue(chained.firings().isEmpty());
    }

    @Test
    void replay_initialMarkingMissingFromSet_isNotChainable() {
        var flat = deadEndChain();

        var outcome = AbstractReplayer.replay(
            flat, marking(A, 1), Set.of(marking(B, 1)), SmtProperty.deadlockFree(), Set.of());

        var notChainable = assertInstanceOf(AbstractReplayer.ReplayOutcome.NotChainable.class, outcome);
        assertTrue(notChainable.reason().contains("initial marking"), notChainable.reason());
    }

    @Test
    void replay_unchainableSet_isNotChainable() {
        // The garbage state is unreachable and the property is never violated,
        // so the chain must break with a structured reason.
        var flat = deadEndChain();
        var decoded = Set.of(marking(A, 1), marking(A, 7, B, 7, C, 7));

        var outcome = AbstractReplayer.replay(
            flat, marking(A, 1), decoded, SmtProperty.placeBound(C, 5), Set.of());

        var notChainable = assertInstanceOf(AbstractReplayer.ReplayOutcome.NotChainable.class, outcome);
        assertTrue(notChainable.reason().contains("decoded state"), notChainable.reason());
    }

    @Test
    void replay_budgetExhaustion_isNotChainable() {
        var flat = deadEndChain();
        var decoded = Set.of(marking(A, 1), marking(C, 1));

        var outcome = AbstractReplayer.replay(
            flat, marking(A, 1), decoded, SmtProperty.deadlockFree(), Set.of(),
            AbstractReplayer.MAX_HOP_STEPS, 0);

        var notChainable = assertInstanceOf(AbstractReplayer.ReplayOutcome.NotChainable.class, outcome);
        assertTrue(notChainable.reason().contains("budget"), notChainable.reason());
    }

    @Test
    void replay_emptySet_isNotChainable() {
        var outcome = AbstractReplayer.replay(
            deadEndChain(), marking(A, 1), Set.of(), SmtProperty.deadlockFree(), Set.of());
        assertInstanceOf(AbstractReplayer.ReplayOutcome.NotChainable.class, outcome);
    }
}
