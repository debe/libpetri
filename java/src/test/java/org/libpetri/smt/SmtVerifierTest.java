package org.libpetri.smt;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.core.*;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.fixtures.PaperNetworks;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

import java.time.Duration;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for the SMT verifier.
 *
 * <p>Tests that don't require Z3 native libraries test the encoding/invariant
 * layers directly. Tests that use Z3 are gated on native library availability.
 */
class SmtVerifierTest {

    // Place is a record, so Place.of("Pending", String.class) equals the one in PaperNetworks
    private static final Place<String> PENDING = Place.of("Pending", String.class);

    static boolean z3Available() {
        try {
            new com.microsoft.z3.Context().close();
            return true;
        } catch (UnsatisfiedLinkError | NoClassDefFoundError _) {
            return false;
        }
    }

    // === Encoding-layer tests (no Z3 needed) ===

    @Test
    void basicTpn_flatteningProducesCorrectStructure() {
        var net = PaperNetworks.createBasicTpn();
        var flatNet = org.libpetri.smt.encoding.NetFlattener.flatten(
            net, java.util.Set.of(), EnvironmentAnalysisMode.ignore());

        // BasicTPN has 9 places and 7 transitions (no XOR)
        assertEquals(9, flatNet.placeCount());
        assertEquals(7, flatNet.transitionCount());
    }

    @Test
    void extendedTpn_flatteningExpandsXor() {
        var net = PaperNetworks.createExtendedTpn();
        var flatNet = org.libpetri.smt.encoding.NetFlattener.flatten(
            net, java.util.Set.of(), EnvironmentAnalysisMode.ignore());

        // ExtendedTPN has 11 transitions, Search and Compose each have 2 XOR branches
        // So we get 9 non-XOR + 4 expanded = 13
        assertEquals(13, flatNet.transitionCount());
    }

    @Test
    void extendedTpn_pInvariantsFound() {
        var net = PaperNetworks.createExtendedTpn();
        var flatNet = org.libpetri.smt.encoding.NetFlattener.flatten(
            net, java.util.Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = org.libpetri.smt.encoding.IncidenceMatrix.from(flatNet);

        var marking = org.libpetri.analysis.MarkingState.builder()
            .tokens(PENDING, 1).build();

        var invariants = org.libpetri.smt.invariant.PInvariantComputer.compute(matrix, flatNet, marking);

        // The extended TPN should have some conservation invariants
        assertFalse(invariants.isEmpty(), "Should find P-invariants for ExtendedTPN");
    }

    // === Z3-dependent tests ===

    @Test
    @EnabledIf("z3Available")
    void basicTpn_noDeadlockInUntimedSemantics() {
        var net = PaperNetworks.createBasicTpn();

        var result = SmtVerifier.forNet(net)
            .initialMarking(m -> m.tokens(PENDING, 1))
            .property(SmtProperty.deadlockFree())
            .timeout(Duration.ofSeconds(30))
            .verify();

        assertNotNull(result);
        assertNotNull(result.report());
        // BasicTPN has Guard and Intent as read-only transitions on Ready.
        // In untimed marking semantics, they can fire repeatedly, producing
        // unlimited Validated/Understood tokens. This means Topic and Search
        // can both fire, Compose gets all inputs, and no deadlock occurs.
        // (Timing constraints would limit this, but SMT operates untimed.)
        assertFalse(result.isViolated(),
            "BasicTPN should not deadlock in untimed semantics (read arcs allow repeated firing)\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void mutualExclusionNet_provesProperty() {
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);

        var t1 = Transition.builder("AtoB")
            .inputs(In.one(p1))
            .outputs(Out.place(p2))
            .build();
        var t2 = Transition.builder("BtoA")
            .inputs(In.one(p2))
            .outputs(Out.place(p1))
            .build();

        var net = PetriNet.builder("MutualExclusion").transitions(t1, t2).build();

        var result = SmtVerifier.forNet(net)
            .initialMarking(m -> m.tokens(p1, 1))
            .property(SmtProperty.mutualExclusion(p1, p2))
            .timeout(Duration.ofSeconds(10))
            .verify();

        assertTrue(result.isProven(), "Single-token circular net should prove mutual exclusion\n" + result.report());
        assertFalse(result.discoveredInvariants().isEmpty(),
            "IC3 should synthesize an inductive invariant\n" + result.report());
        System.out.println("=== Mutual Exclusion Invariant ===");
        result.discoveredInvariants().forEach(System.out::println);
    }

    @Test
    @EnabledIf("z3Available")
    void deadlockNet_findsViolation() {
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);
        var p3 = Place.of("C", String.class);

        // T1: needs A, produces B
        // T2: needs B AND C, produces A
        // With initial marking: A=1, C=0 -> T1 fires, B=1
        // Then T2 needs B=1 AND C=1, but C=0 -> DEADLOCK
        var t1 = Transition.builder("T1")
            .inputs(In.one(p1))
            .outputs(Out.place(p2))
            .build();
        var t2 = Transition.builder("T2")
            .inputs(In.one(p2), In.one(p3))
            .outputs(Out.place(p1))
            .build();

        var net = PetriNet.builder("DeadlockNet").transitions(t1, t2).build();

        var result = SmtVerifier.forNet(net)
            .initialMarking(m -> m.tokens(p1, 1))
            .property(SmtProperty.deadlockFree())
            .timeout(Duration.ofSeconds(10))
            .verify();

        assertTrue(result.isViolated(), "Net with missing C token should deadlock\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void placeBound_provesForBoundedNet() {
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);

        var t1 = Transition.builder("AtoB")
            .inputs(In.one(p1))
            .outputs(Out.place(p2))
            .build();
        var t2 = Transition.builder("BtoA")
            .inputs(In.one(p2))
            .outputs(Out.place(p1))
            .build();

        var net = PetriNet.builder("Bounded").transitions(t1, t2).build();

        var result = SmtVerifier.forNet(net)
            .initialMarking(m -> m.tokens(p1, 1))
            .property(SmtProperty.placeBound(p2, 1))
            .timeout(Duration.ofSeconds(10))
            .verify();

        assertTrue(result.isProven(), "B should be bounded by 1 in single-token circular net\n" + result.report());
        assertFalse(result.discoveredInvariants().isEmpty(),
            "IC3 should synthesize an inductive invariant\n" + result.report());
        System.out.println("=== Place Bound Invariant ===");
        result.discoveredInvariants().forEach(System.out::println);
    }

    @Test
    @EnabledIf("z3Available")
    void unreachableProperty_provesForSeparateSubnets() {
        // Two disconnected cycles: A<->B and C<->D
        // With A=1, C=0: tokens in A and C simultaneously is unreachable
        var pA = Place.of("A", String.class);
        var pB = Place.of("B", String.class);
        var pC = Place.of("C", String.class);

        var t1 = Transition.builder("AtoB")
            .inputs(In.one(pA))
            .outputs(Out.place(pB))
            .build();
        var t2 = Transition.builder("BtoA")
            .inputs(In.one(pB))
            .outputs(Out.place(pA))
            .build();
        var t3 = Transition.builder("AtoC")
            .inputs(In.one(pA))
            .outputs(Out.place(pC))
            .build();

        // Net: A -> B -> A, A -> C
        // With 1 token in A: after AtoC fires, A=0 C=1. A and C simultaneously having
        // tokens requires 2 tokens total, but conservation law says A+B+C=1.
        var net = PetriNet.builder("Unreachable").transitions(t1, t2, t3).build();

        var result = SmtVerifier.forNet(net)
            .initialMarking(m -> m.tokens(pA, 1))
            .property(SmtProperty.unreachable(Set.of(pA, pC)))
            .timeout(Duration.ofSeconds(10))
            .verify();

        // A+B+C=1 conservation law means A>=1 AND C>=1 requires at least 2 tokens
        assertFalse(result.isViolated(),
            "A and C simultaneously marked should be unreachable with 1 token\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void tightTimeout_returnsUnknownOrProven() {
        // Use a net complex enough that 1ms timeout is likely insufficient
        var net = PaperNetworks.createExtendedTpn();

        var result = SmtVerifier.forNet(net)
            .initialMarking(m -> m.tokens(PENDING, 1))
            .property(SmtProperty.deadlockFree())
            .timeout(Duration.ofMillis(1))
            .verify();

        // With 1ms timeout, solver should return Unknown (or Proven if structural check suffices)
        assertNotNull(result);
        assertNotNull(result.verdict());
        // We don't assert Unknown specifically because the structural pre-check or
        // a very fast solver might still produce a result — just verify no crash
    }

    @Test
    @EnabledIf("z3Available")
    void deadlockNet_counterexampleTraceIsPopulated() {
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);
        var p3 = Place.of("C", String.class);

        var t1 = Transition.builder("T1")
            .inputs(In.one(p1))
            .outputs(Out.place(p2))
            .build();
        var t2 = Transition.builder("T2")
            .inputs(In.one(p2), In.one(p3))
            .outputs(Out.place(p1))
            .build();

        var net = PetriNet.builder("DeadlockNet").transitions(t1, t2).build();

        var result = SmtVerifier.forNet(net)
            .initialMarking(m -> m.tokens(p1, 1))
            .property(SmtProperty.deadlockFree())
            .timeout(Duration.ofSeconds(10))
            .verify();

        assertTrue(result.isViolated(), "Net should deadlock\n" + result.report());

        // Counterexample trace should contain at least the deadlocked state
        assertFalse(result.counterexampleTrace().isEmpty(),
            "Counterexample trace should not be empty\n" + result.report());

        // The deadlocked state should have B=1 (after T1 fires from A=1)
        var lastState = result.counterexampleTrace().getLast();
        assertEquals(1, lastState.tokens(p2),
            "Deadlocked state should have 1 token in B\n" + result.report());
        assertEquals(0, lastState.tokens(p1),
            "Deadlocked state should have 0 tokens in A\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void xorBranchToSink_deadlocksWithEnvironmentPlace() {
        // Idle=1 (processing resource), Trigger=env (external events)
        // Dispatch: Idle + Trigger -> XOR(Active, Rejected)
        // Complete: Active -> Idle (loop back)
        // Rejected is a sink — no transition consumes from it.
        // XOR expansion means the solver considers the Rejected branch:
        //   Dispatch fires -> Rejected=1, Idle=0 -> no transition enabled -> DEADLOCK
        var idle = Place.of("Idle", String.class);
        var trigger = EnvironmentPlace.of(Place.of("Trigger", String.class));
        var active = Place.of("Active", String.class);
        var rejected = Place.of("Rejected", String.class);

        var dispatch = Transition.builder("Dispatch")
            .inputs(In.one(idle), In.one(trigger.place()))
            .outputs(Out.xor(active, rejected))
            .build();
        var complete = Transition.builder("Complete")
            .inputs(In.one(active))
            .outputs(Out.place(idle))
            .build();

        var net = PetriNet.builder("XorSinkNet").transitions(dispatch, complete).build();

        var result = SmtVerifier.forNet(net)
            .initialMarking(m -> m.tokens(idle, 1))
            .environmentPlaces(trigger)
            .environmentMode(EnvironmentAnalysisMode.alwaysAvailable())
            .property(SmtProperty.deadlockFree())
            .timeout(Duration.ofSeconds(30))
            .verify();

        assertTrue(result.isViolated(),
            "XOR branch to sink should cause deadlock\n" + result.report());
        assertFalse(result.counterexampleTrace().isEmpty(),
            "Counterexample trace should not be empty\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void resetArc_correctEncoding() {
        // A -> T1 (reset B) -> C
        // T1 consumes from A, resets B to 0, produces to C
        var pA = Place.of("A", String.class);
        var pB = Place.of("B", String.class);
        var pC = Place.of("C", String.class);

        var t1 = Transition.builder("T1")
            .inputs(In.one(pA))
            .reset(pB)
            .outputs(Out.place(pC))
            .build();
        var t2 = Transition.builder("T2")
            .inputs(In.one(pC))
            .outputs(Out.place(pA))
            .build();

        var net = PetriNet.builder("ResetNet").transitions(t1, t2).build();

        // With A=1, B=5: T1 fires -> A=0, B=0, C=1 (B is reset)
        // Then T2 fires -> A=1, B=0, C=0
        // B should be bounded by 5 (initial value, never increases)
        var result = SmtVerifier.forNet(net)
            .initialMarking(m -> { m.tokens(pA, 1); m.tokens(pB, 5); })
            .property(SmtProperty.placeBound(pB, 5))
            .timeout(Duration.ofSeconds(10))
            .verify();

        assertFalse(result.isViolated(),
            "B with reset arc should never exceed initial value\n" + result.report());
    }
}
