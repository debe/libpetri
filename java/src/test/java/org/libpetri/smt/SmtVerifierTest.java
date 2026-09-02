package org.libpetri.smt;

import org.libpetri.fixtures.StructureOnly;
import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.core.*;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.fixtures.PaperNetworks;
import org.libpetri.smt.z3.CertificateChecker;
import org.libpetri.smt.z3.CounterexampleDecoder;
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

    @Test
    void structuralEarlyProof_saysTheCertificateCheckDoesNotApply() {
        // The siphon/trap proof returns before the CHC encoding, so there is no IC3
        // certificate to re-validate — the report must say so rather than stay silent.
        // No Z3: this path never opens a solver.
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);
        var t1 = Transition.builder("AtoB").inputs(In.one(p1)).outputs(Out.place(p2)).build();
        var t2 = Transition.builder("BtoA").inputs(In.one(p2)).outputs(Out.place(p1)).build();
        var net = PetriNet.builder("cycle").transitions(t1, t2).build();

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
            .initialMarking(m -> m.tokens(p1, 1))
            .property(SmtProperty.deadlockFree())
            .timeout(Duration.ofSeconds(5))
            .verify();

        assertTrue(result.isProven(), result.report());
        assertTrue(result.report().contains("PROVEN (structural)"), result.report());
        assertTrue(result.report().contains(
            "  Certificate check: not applicable (structural proof)"), result.report());
        assertNull(result.counterexampleConfirmed(),
            "a proven verdict never carries a replay outcome\n" + result.report());
    }

    // === Z3-dependent tests ===

    @Test
    @EnabledIf("z3Available")
    void basicTpn_noDeadlockInUntimedSemantics() {
        var net = PaperNetworks.createBasicTpn();

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
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

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
            .initialMarking(m -> m.tokens(p1, 1))
            .property(SmtProperty.mutualExclusion(p1, p2))
            .timeout(Duration.ofSeconds(10))
            .verify();

        assertTrue(result.isProven(), "Single-token circular net should prove mutual exclusion\n" + result.report());
        assertTrue(result.report().contains("Certificate check: PASSED (init, consecution, safety)"),
            "A flat IC3 proof must carry a validated certificate\n" + result.report());
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

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
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

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
            .initialMarking(m -> m.tokens(p1, 1))
            .property(SmtProperty.placeBound(p2, 1))
            .timeout(Duration.ofSeconds(10))
            .verify();

        assertTrue(result.isProven(), "B should be bounded by 1 in single-token circular net\n" + result.report());
        assertTrue(result.report().contains("Certificate check: PASSED (init, consecution, safety)"),
            "A flat IC3 proof must carry a validated certificate\n" + result.report());
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

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
            .initialMarking(m -> m.tokens(pA, 1))
            .property(SmtProperty.unreachable(Set.of(pA, pC)))
            .timeout(Duration.ofSeconds(10))
            .verify();

        // A+B+C=1 conservation law means A>=1 AND C>=1 requires at least 2 tokens
        assertTrue(result.isProven(),
            "A and C simultaneously marked should be unreachable with 1 token\n" + result.report());
        assertTrue(result.report().contains("Certificate check: PASSED (init, consecution, safety)"),
            "A flat IC3 proof must carry a validated certificate\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void tightTimeout_returnsUnknownOrProven() {
        // Use a net complex enough that 1ms timeout is likely insufficient
        var net = PaperNetworks.createExtendedTpn();

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
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

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
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

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
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
        // Strengthened (VER-006): the violation must be the real Rejected-sink path
        // (Dispatch fired via env injection), NOT the frozen initial state. Pre-fix
        // this passed for the wrong reason (Trigger=0 forever -> initial {Idle:1} was
        // itself reported as a deadlock).
        boolean reachedRejected = result.counterexampleTrace().stream()
            .anyMatch(m -> m.tokens(rejected) > 0);
        assertTrue(reachedRejected,
            "Deadlock must reach the Rejected sink, not freeze at the initial marking\n"
            + result.report());
    }

    // === VER-006: Environment injection soundness ===
    // Regression for the bug where SmtVerifier vacuously "proved" safety bounds on
    // nets with environment places (env columns could only be consumed, never
    // produced, so the reachable set froze at the initial marking).

    @Test
    @EnabledIf("z3Available")
    void ver006_envSource_alwaysAvailable_placeBoundViolated() {
        // env IN -> T -> OUT. AlwaysAvailable lets IN be injected without bound, so
        // OUT grows without bound: placeBound(OUT, k) is violated for every finite k.
        var in = EnvironmentPlace.of(Place.of("IN", String.class));
        var out = Place.of("OUT", String.class);
        var t = Transition.builder("T").inputs(In.one(in.place())).outputs(Out.place(out)).build();
        var net = PetriNet.builder("env-source").transitions(t).build();

        for (int k : new int[] {0, 1, 5}) {
            var result = SmtVerifier.forNet(StructureOnly.bind(net))
                .environmentPlaces(in)
                .environmentMode(EnvironmentAnalysisMode.alwaysAvailable())
                .property(SmtProperty.placeBound(out, k))
                .timeout(Duration.ofSeconds(15))
                .verify();
            assertTrue(result.isViolated(),
                "placeBound(OUT, " + k + ") must be violated under env injection\n" + result.report());
        }
    }

    @Test
    @EnabledIf("z3Available")
    void ver006_boundedGatesByMultiplicity() {
        // T2 needs EXACTLY 2 tokens from env IN per firing. bounded(1) starves it
        // (OUT stays 0 -> proven), alwaysAvailable feeds it (OUT unbounded -> violated).
        // Also exercises the env-aware P-invariant: the closed-net law IN + 2*OUT = 0
        // must be discarded so OUT is not vacuously pinned.
        java.util.function.Supplier<PetriNet> build = () -> {
            var in = Place.of("IN", String.class);
            var out = Place.of("OUT", String.class);
            var t = Transition.builder("T2").inputs(In.exactly(2, in)).outputs(Out.place(out)).build();
            return PetriNet.builder("env-mult").transitions(t).build();
        };
        var in = EnvironmentPlace.of(Place.of("IN", String.class));
        var out = Place.of("OUT", String.class);

        var bounded1 = SmtVerifier.forNet(StructureOnly.bind(build.get()))
            .environmentPlaces(in)
            .environmentMode(EnvironmentAnalysisMode.bounded(1))
            .property(SmtProperty.placeBound(out, 0))
            .timeout(Duration.ofSeconds(15))
            .verify();
        assertTrue(bounded1.isProven(),
            "bounded(1) starves a 2-token env input -> OUT stays 0\n" + bounded1.report());
        assertTrue(bounded1.report().contains("Certificate check: PASSED (init, consecution, safety)"),
            "The certificate must validate against the injection-aware step relation\n" + bounded1.report());

        var always = SmtVerifier.forNet(StructureOnly.bind(build.get()))
            .environmentPlaces(in)
            .environmentMode(EnvironmentAnalysisMode.alwaysAvailable())
            .property(SmtProperty.placeBound(out, 0))
            .timeout(Duration.ofSeconds(15))
            .verify();
        assertTrue(always.isViolated(),
            "alwaysAvailable feeds the 2-token env input -> OUT unbounded\n" + always.report());
    }

    @Test
    @EnabledIf("z3Available")
    void ver006_ignoreModeWithEnvPlaces_downgradesToUnknown() {
        // Ignore mode does not model injection; a "proven" here would be vacuous.
        var in = EnvironmentPlace.of(Place.of("IN", String.class));
        var out = Place.of("OUT", String.class);
        var t = Transition.builder("T").inputs(In.one(in.place())).outputs(Out.place(out)).build();
        var net = PetriNet.builder("env-source").transitions(t).build();

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
            .environmentPlaces(in)
            .environmentMode(EnvironmentAnalysisMode.ignore())
            .property(SmtProperty.placeBound(out, 1))
            .timeout(Duration.ofSeconds(15))
            .verify();
        assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(),
            "ignore mode with env places must not silently prove\n" + result.report());
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
        var result = SmtVerifier.forNet(StructureOnly.bind(net))
            .initialMarking(m -> { m.tokens(pA, 1); m.tokens(pB, 5); })
            .property(SmtProperty.placeBound(pB, 5))
            .timeout(Duration.ofSeconds(10))
            .verify();

        assertTrue(result.isProven(),
            "B with reset arc should never exceed initial value\n" + result.report());
        assertTrue(result.report().contains("Certificate check: PASSED (init, consecution, safety)"),
            "The certificate must validate against the reset-arc step semantics\n" + result.report());
    }

    // === NU-040 / NU-050: ν-net verification (sound carve-out, Stage 6a) ===
    // The untimed encoder over-approximates ν-join name equality. That is sound
    // for reachability-safety bounds (a Proven holds for the real net) — so the
    // bounded-budget decidability lever is checkable today — but not for
    // quiescence properties, and not for unbounded fresh names.

    /**
     * Structural scatter-gather: {@code fork} consumes a {@code budget} token and
     * stamps a {@code pending} token plus both branches; {@code join} correlates
     * the branches by name, consumes {@code pending}, and returns the
     * {@code budget} token. The conservation laws {@code budget + pending = k}
     * and {@code branchA = branchB = pending} hold regardless of names, so the
     * over-approximation can prove the bounds.
     */
    private static PetriNet nuScatterGatherNet() {
        var source = Place.of("source", Integer.class);
        var budget = Place.of("budget", Integer.class);
        var pending = Place.of("pending", Integer.class);
        var a = Place.of("branchA", String.class);
        var b = Place.of("branchB", String.class);
        var merged = Place.of("merged", String.class);

        var fork = Transition.builder("fork")
            .inputs(Arc.In.one(source), Arc.In.one(budget))
            .outputs(Arc.Out.and(a, b, pending))
            .build();

        var join = Transition.builder("join")
            .inputs(Arc.In.one(a), Arc.In.one(b), Arc.In.one(pending))
            .match(MatchSpec.builder()
                .key(a, (String s) -> NameId.of(s))
                .key(b, (String s) -> NameId.of(s))
                .build())
            .outputs(Arc.Out.and(merged, budget))
            .build();

        return PetriNet.builder("nuScatterGatherVerify").transitions(fork, join).build();
    }

    private static final Place<Integer> NU_BUDGET = Place.of("budget", Integer.class);
    private static final Place<Integer> NU_PENDING = Place.of("pending", Integer.class);
    private static final Place<Integer> NU_SOURCE = Place.of("source", Integer.class);

    @Test
    @EnabledIf("z3Available")
    void nuZeroBudget_quiescenceDecidedByZeroSlotPlan() {
        // NU-053 AC6: a mid-phase marking with no budget token — the covering semiflow's
        // initial sum is zero — is decided exactly by the zero-slot coloured plan instead of
        // being downgraded to Unknown. Route B is forced to truncate (nuMaxClasses(1)) so the
        // deferral to Route A is exercised. No sink: the initial marking is quiescent with
        // `source` tokens stranded.
        var violated = SmtVerifier.forNet(StructureOnly.bind(nuScatterGatherNet()))
            .initialMarking(m -> { m.tokens(NU_SOURCE, 3); m.tokens(NU_BUDGET, 0); })
            .property(SmtProperty.deadlockFree())
            .budgetPlaces(NU_BUDGET)
            .nuMaxClasses(1)
            .timeout(Duration.ofSeconds(15))
            .verify();
        assertTrue(violated.report().contains("exact within budget k=0"),
            "the zero-slot plan must be taken\n" + violated.report());
        assertTrue(violated.isViolated(),
            "no budget, no sink: the initial marking is a deadlock\n" + violated.report());
        // Declaring `source` a sink makes that marking a legitimate end state.
        var proven = SmtVerifier.forNet(StructureOnly.bind(nuScatterGatherNet()))
            .initialMarking(m -> { m.tokens(NU_SOURCE, 3); m.tokens(NU_BUDGET, 0); })
            .property(SmtProperty.deadlockFree())
            .budgetPlaces(NU_BUDGET)
            .sinkPlaces(NU_SOURCE)
            .nuMaxClasses(1)
            .timeout(Duration.ofSeconds(15))
            .verify();
        assertTrue(proven.report().contains("exact within budget k=0"), proven.report());
        assertTrue(proven.isProven(),
            "with `source` a sink the only quiescent marking is a sink state\n" + proven.report());
    }

    @Test
    @EnabledIf("z3Available")
    void nuBranchBudgetBound_provenWithDeclaredBudget() {
        // NU-040 #1: with the budget declared, the live correlation pool is
        // bounded — BranchPlaceBound(budget, k) is proven by conservation.
        var result = SmtVerifier.forNet(StructureOnly.bind(nuScatterGatherNet()))
            .initialMarking(m -> { m.tokens(NU_SOURCE, 3); m.tokens(NU_BUDGET, 2); })
            .property(SmtProperty.branchPlaceBound(NU_BUDGET, 2))
            .budgetPlaces(NU_BUDGET)
            .timeout(Duration.ofSeconds(15))
            .verify();
        assertTrue(result.isProven(),
            "BranchPlaceBound(budget, 2) must be proven for the bounded scatter-gather\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void nuPendingBound_provenExact() {
        // NU-040 #2 (bound half): at most k live groups — Pending is bounded by k.
        var result = SmtVerifier.forNet(StructureOnly.bind(nuScatterGatherNet()))
            .initialMarking(m -> { m.tokens(NU_SOURCE, 3); m.tokens(NU_BUDGET, 2); })
            .property(SmtProperty.branchPlaceBound(NU_PENDING, 2))
            .budgetPlaces(NU_BUDGET)
            .timeout(Duration.ofSeconds(15))
            .verify();
        assertTrue(result.isProven(),
            "BranchPlaceBound(pending, 2) must be proven for the bounded scatter-gather\n" + result.report());
        // The scatter-gather is in the name-coloured fragment, so the bound is
        // decided exactly (NU-050 #1), not via the name-blind over-approximation.
        assertTrue(result.report().contains("name-coloured"),
            "a bounded ν-net in the supported fragment uses the exact name-coloured encoding\n" + result.report());
        // The IC3 certificate check covers the flat count encoding only, and says so.
        assertTrue(result.report().contains(
            "  Certificate check: not applicable (name-coloured encoding)"),
            "the coloured path must state that the certificate check does not apply\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void unresolvedPropertyPlace_reportsUnknownNotVacuousProven() {
        // A property naming a place absent from the net must NOT silently certify. The
        // name-coloured (Route A) encoder emits no encoding for a typo'd place, so the
        // verifier reports Unknown instead of a vacuous PROVEN (an unresolved place would
        // otherwise make the Error rule unsatisfiable → trivially "proven"). Contrast
        // nuPendingBound_provenExact, which proves the real `pending` bound on this net.
        var typo = Place.of("pnding", Integer.class); // typo of "pending"
        var result = SmtVerifier.forNet(StructureOnly.bind(nuScatterGatherNet()))
            .initialMarking(m -> { m.tokens(NU_SOURCE, 3); m.tokens(NU_BUDGET, 2); })
            .property(SmtProperty.branchPlaceBound(typo, 2))
            .budgetPlaces(NU_BUDGET)
            .timeout(Duration.ofSeconds(15))
            .verify();
        assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(),
            "a property naming an unresolved place must be Unknown, not a vacuous Proven\n" + result.report());
    }

    @Test
    void nuStructurallyBounded_withoutDeclaredBudget_decidedByRouteB() {
        // NU-050 Route B: without a DECLARED budget place the SMT/Route-A path
        // returns Unknown, but the name-aware SCG name-partition quotient discovers
        // the structural bound (the budget token caps live groups) and proves the
        // bound exactly — the beyond-bounded win. Pure SCG, so no Z3 binary needed.
        var result = SmtVerifier.forNet(StructureOnly.bind(nuScatterGatherNet()))
            .initialMarking(m -> { m.tokens(NU_SOURCE, 3); m.tokens(NU_BUDGET, 2); })
            .property(SmtProperty.branchPlaceBound(NU_BUDGET, 2))
            .verify();
        assertTrue(result.isProven(),
            "Route B decides a structurally-bounded ν-net without a declared budget\n" + result.report());
        assertTrue(result.report().contains("Route B"), "expected the Route B note\n" + result.report());
    }

    @Test
    void nuJoinedOrDeadLettered_provenByRouteB() {
        // NU-050 Route B: quiescence on a ν-net is decided exactly by the name-aware
        // SCG. Same-mint siblings always join, so no quiescent state strands
        // `pending` -> Proven (the SMT path returned Unknown here). No Z3.
        var result = SmtVerifier.forNet(StructureOnly.bind(nuScatterGatherNet()))
            .initialMarking(m -> { m.tokens(NU_SOURCE, 3); m.tokens(NU_BUDGET, 2); })
            .property(SmtProperty.joinedOrDeadLettered(NU_PENDING))
            .verify();
        assertTrue(result.isProven(),
            "every same-mint group joins -> no stranded pending -> Proven\n" + result.report());
        assertTrue(result.report().contains("Route B"), "expected the Route B note\n" + result.report());
    }

    @Test
    void nuDeadlockFree_violatedByRouteB() {
        // NU-050 Route B: DeadlockFree is now exact. The net quiesces when `source`
        // is exhausted (budget returned, no group in flight) — a genuine deadlock
        // with no declared sinks -> Violated (was Unknown). No Z3.
        var result = SmtVerifier.forNet(StructureOnly.bind(nuScatterGatherNet()))
            .initialMarking(m -> { m.tokens(NU_SOURCE, 3); m.tokens(NU_BUDGET, 2); })
            .property(SmtProperty.deadlockFree())
            .verify();
        assertTrue(result.isViolated(),
            "the net quiesces when source is exhausted -> DeadlockFree violated\n" + result.report());
        assertTrue(result.report().contains("Route B"), "expected the Route B note\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void joinedOrDeadLettered_provenOnNonNuNet() {
        // On a net WITHOUT ν-matching the encoding is exact for quiescence.
        // `pending` always drains before quiescence -> Proven.
        var start = Place.of("start", Integer.class);
        var pending = Place.of("pending", Integer.class);
        var done = Place.of("done", Integer.class);
        var produce = Transition.builder("gen")
            .inputs(Arc.In.one(start)).outputs(Arc.Out.place(pending)).build();
        var fin = Transition.builder("fin")
            .inputs(Arc.In.one(pending)).outputs(Arc.Out.place(done)).build();
        var net = PetriNet.builder("pendingDrains").transitions(produce, fin).build();

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
            .initialMarking(m -> m.tokens(start, 1))
            .property(SmtProperty.joinedOrDeadLettered(pending))
            .timeout(Duration.ofSeconds(15))
            .verify();
        assertTrue(result.isProven(),
            "every group joins/dead-letters before quiescence -> Proven\n" + result.report());
        assertTrue(result.report().contains("Certificate check: PASSED (init, consecution, safety)"),
            "A flat IC3 proof must carry a validated certificate\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void joinedOrDeadLettered_violatedOnNonNuNet() {
        // A stranded `pending` token: `leak` produces into `pending` but nothing
        // consumes it -> the quiescent marking still holds pending -> Violated.
        var start = Place.of("start", Integer.class);
        var pending = Place.of("pending", Integer.class);
        var leak = Transition.builder("leak")
            .inputs(Arc.In.one(start)).outputs(Arc.Out.place(pending)).build();
        var net = PetriNet.builder("pendingStrands").transitions(leak).build();

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
            .initialMarking(m -> m.tokens(start, 1))
            .property(SmtProperty.joinedOrDeadLettered(pending))
            .timeout(Duration.ofSeconds(15))
            .verify();
        assertTrue(result.isViolated(),
            "a stranded pending token at quiescence -> Violated\n" + result.report());
    }

    // === NU-050 #1: name-coloured exact ν-verification (Stage 6b, Route A) ===
    // The flat encoder over-approximates ν-join name equality (name-blind). The
    // bounded name-coloured encoding (k = budget) decides it exactly: a join fires
    // only on same-coloured tokens, so a counterexample requiring two distinct
    // names to be equal is eliminated.

    /**
     * Two INDEPENDENT mints feed one join: {@code forkA} mints a name into
     * {@code branchA}, {@code forkB} mints a <em>different</em> name into
     * {@code branchB}. Their names can never be equal, so the join can never
     * correlate them and {@code merged} is unreachable. The name-blind
     * over-approximation would (wrongly) fire the join — exactly the spurious "two
     * distinct names are equal" counterexample NU-050 #1 kills.
     */
    private static PetriNet nuDistinctMintsNet() {
        var sourceA = Place.of("sourceA", Integer.class);
        var sourceB = Place.of("sourceB", Integer.class);
        var budget = Place.of("budget", Integer.class);
        var a = Place.of("branchA", String.class);
        var b = Place.of("branchB", String.class);
        var merged = Place.of("merged", String.class);

        var forkA = Transition.builder("forkA")
            .inputs(Arc.In.one(sourceA), Arc.In.one(budget))
            .outputs(Arc.Out.place(a))
            .build();
        var forkB = Transition.builder("forkB")
            .inputs(Arc.In.one(sourceB), Arc.In.one(budget))
            .outputs(Arc.Out.place(b))
            .build();
        var join = Transition.builder("join")
            .inputs(Arc.In.one(a), Arc.In.one(b))
            .match(MatchSpec.builder()
                .key(a, (String s) -> NameId.of(s))
                .key(b, (String s) -> NameId.of(s))
                .build())
            .outputs(Arc.Out.place(merged))
            .build();

        return PetriNet.builder("nuDistinctMints").transitions(forkA, forkB, join).build();
    }

    private static final Place<Integer> NU_SOURCE_A = Place.of("sourceA", Integer.class);
    private static final Place<Integer> NU_SOURCE_B = Place.of("sourceB", Integer.class);
    private static final Place<String> NU_MERGED = Place.of("merged", String.class);

    @Test
    @EnabledIf("z3Available")
    void nuDistinctMints_mergedUnreachable_provenExact() {
        // NU-050 #1: distinct-mint names can never join -> `merged` unreachable.
        // The name-blind over-approximation would report this Violated (spurious);
        // the name-coloured encoding proves it.
        var result = SmtVerifier.forNet(StructureOnly.bind(nuDistinctMintsNet()))
            .initialMarking(m -> { m.tokens(NU_SOURCE_A, 1); m.tokens(NU_SOURCE_B, 1); m.tokens(NU_BUDGET, 2); })
            .property(SmtProperty.unreachable(Set.of(NU_MERGED)))
            .budgetPlaces(NU_BUDGET)
            .timeout(Duration.ofSeconds(15))
            .verify();
        assertTrue(result.isProven(),
            "distinct-mint names can never correlate -> merged unreachable -> Proven\n" + result.report());
        assertTrue(result.report().contains("name-coloured"),
            "must use the exact name-coloured encoding\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void nuSameMint_mergedReachable_violated() {
        // Companion (non-vacuity): the SAME-mint scatter-gather stamps both branches
        // with one name, so the join CAN fire and `merged` IS reachable. The
        // colouring tracks real reachability — Unreachable(merged) is Violated.
        var result = SmtVerifier.forNet(StructureOnly.bind(nuScatterGatherNet()))
            .initialMarking(m -> { m.tokens(NU_SOURCE, 3); m.tokens(NU_BUDGET, 2); })
            .property(SmtProperty.unreachable(Set.of(NU_MERGED)))
            .budgetPlaces(NU_BUDGET)
            .timeout(Duration.ofSeconds(15))
            .verify();
        assertTrue(result.isViolated(),
            "same-mint siblings can join -> merged reachable -> Violated\n" + result.report());
    }

    // === NU-050 Route B: exact name-aware SCG name-partition quotient ===

    /**
     * Two independent mints feed one join, with NO budget place: {@code forkA}
     * mints into {@code branchA}, {@code forkB} a different name into
     * {@code branchB}. Their names can never be equal, so {@code merged} is
     * unreachable — the beyond-bounded win Route A cannot do (no declared budget).
     */
    private static PetriNet nuDistinctMintsNoBudgetNet() {
        var sourceA = Place.of("sourceA", Integer.class);
        var sourceB = Place.of("sourceB", Integer.class);
        var a = Place.of("branchA", String.class);
        var b = Place.of("branchB", String.class);
        var merged = Place.of("merged", String.class);
        var forkA = Transition.builder("forkA").inputs(Arc.In.one(sourceA)).outputs(Arc.Out.place(a)).build();
        var forkB = Transition.builder("forkB").inputs(Arc.In.one(sourceB)).outputs(Arc.Out.place(b)).build();
        var join = Transition.builder("join")
            .inputs(Arc.In.one(a), Arc.In.one(b))
            .match(MatchSpec.builder().key(a, (String s) -> NameId.of(s)).key(b, (String s) -> NameId.of(s)).build())
            .outputs(Arc.Out.place(merged))
            .build();
        return PetriNet.builder("nuDistinctMintsNoBudget").transitions(forkA, forkB, join).build();
    }

    @Test
    void nuDistinctMints_noBudget_mergedUnreachable_provenByRouteB() {
        var result = SmtVerifier.forNet(StructureOnly.bind(nuDistinctMintsNoBudgetNet()))
            .initialMarking(m -> { m.tokens(NU_SOURCE_A, 1); m.tokens(NU_SOURCE_B, 1); })
            .property(SmtProperty.unreachable(Set.of(NU_MERGED)))
            .verify();
        assertTrue(result.isProven(),
            "distinct-mint names can never correlate -> merged unreachable (no budget needed)\n" + result.report());
        assertTrue(result.report().contains("name-partition quotient"), result.report());
        assertTrue(result.report().contains("Route B"), result.report());
    }

    /**
     * A self-refilling fork mints a fresh name every firing with no join able to
     * consume it ({@code branchB} is never produced) — the name-aware graph grows
     * without bound, so it truncates and the verdict is Unknown (NU-050 #2
     * generalised).
     */
    private static PetriNet nuUnboundedMintNet() {
        var source = Place.of("source", Integer.class);
        var a = Place.of("branchA", String.class);
        var b = Place.of("branchB", String.class);
        var merged = Place.of("merged", String.class);
        var fork = Transition.builder("fork")
            .inputs(Arc.In.one(source)).outputs(Arc.Out.and(source, a)).build();
        var join = Transition.builder("join")
            .inputs(Arc.In.one(a), Arc.In.one(b))
            .match(MatchSpec.builder().key(a, (String s) -> NameId.of(s)).key(b, (String s) -> NameId.of(s)).build())
            .outputs(Arc.Out.place(merged))
            .build();
        return PetriNet.builder("nuUnboundedMint").transitions(fork, join).build();
    }

    @Test
    void nuUnboundedMint_truncatesToUnknown() {
        var result = SmtVerifier.forNet(StructureOnly.bind(nuUnboundedMintNet()))
            .initialMarking(m -> m.tokens(NU_SOURCE, 1))
            .property(SmtProperty.unreachable(Set.of(NU_MERGED)))
            .nuMaxClasses(40)
            .verify();
        assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(),
            "an unbounded ν-mint must truncate to Unknown\n" + result.report());
        var reason = ((SmtVerificationResult.Verdict.Unknown) result.verdict()).reason();
        assertTrue(reason.contains("truncated"), "Unknown reason should mention truncation: " + reason);
    }

    // === NU-053: Route A coloured quiescence (EXTENDED + colour-aware deadlock) ===
    // When Route B truncates on a bounded quiescence ν-net, the proof defers to the
    // scalable Route A coloured IC3/PDR encoder. Forced here via nuMaxClasses(1).

    /**
     * A single-turn co-mint→join net: {@code fork} consumes {@code source} + {@code budget}
     * and co-mints one fresh name into join inputs {@code a} and {@code b}; {@code join}
     * correlates them into {@code merged} and refunds {@code budget}. The only quiescent
     * marking holds just the sinks {merged, budget}, so it is deadlock-free.
     */
    private static PetriNet nu053NoStallNet() {
        var source = Place.of("source", Integer.class);
        var budget = Place.of("budget", Integer.class);
        var a = Place.of("a", String.class);
        var b = Place.of("b", String.class);
        var merged = Place.of("merged", String.class);

        var fork = Transition.builder("fork")
            .inputs(In.one(source), In.one(budget))
            .outputs(Out.and(a, b))
            .build();
        var join = Transition.builder("join")
            .inputs(In.one(a), In.one(b))
            .match(MatchSpec.builder()
                .key(a, (String s) -> NameId.of(s))
                .key(b, (String s) -> NameId.of(s))
                .build())
            .outputs(Out.and(merged, budget))
            .build();
        return PetriNet.builder("nu053NoStall").transitions(fork, join).build();
    }

    /**
     * The no-stall net plus an EXTENDED drain that steals {@code a} into a dead-letter,
     * stranding {@code b}: an unprioritised schedule can reach a quiescent marking where
     * the non-sink {@code b} still holds a token, so it is NOT deadlock-free.
     */
    private static PetriNet nu053StealNet() {
        var source = Place.of("source", Integer.class);
        var budget = Place.of("budget", Integer.class);
        var a = Place.of("a", String.class);
        var b = Place.of("b", String.class);
        var merged = Place.of("merged", String.class);
        var deadletter = Place.of("deadletter", String.class);

        var fork = Transition.builder("fork")
            .inputs(In.one(source), In.one(budget))
            .outputs(Out.and(a, b))
            .build();
        var join = Transition.builder("join")
            .inputs(In.one(a), In.one(b))
            .match(MatchSpec.builder()
                .key(a, (String s) -> NameId.of(s))
                .key(b, (String s) -> NameId.of(s))
                .build())
            .outputs(Out.and(merged, budget))
            .build();
        var drain = Transition.builder("drain")
            .inputs(In.one(a))
            .outputs(Out.place(deadletter))
            .build();
        return PetriNet.builder("nu053Steal").transitions(fork, join, drain).build();
    }

    private static final Place<Integer> NU053_SOURCE = Place.of("source", Integer.class);
    private static final Place<Integer> NU053_BUDGET = Place.of("budget", Integer.class);
    private static final Place<String> NU053_MERGED = Place.of("merged", String.class);
    private static final Place<String> NU053_DEADLETTER = Place.of("deadletter", String.class);

    @Test
    @EnabledIf("z3Available")
    void nu053RouteAProvesDeadlockFreeWhenRouteBTruncates() {
        // nuMaxClasses = 1 forces Route B to truncate, so the bounded quiescence proof
        // defers to the Route A coloured IC3/PDR encoder (NU-053).
        var result = SmtVerifier.forNet(StructureOnly.bind(nu053NoStallNet()))
            .initialMarking(m -> { m.tokens(NU053_SOURCE, 1); m.tokens(NU053_BUDGET, 1); })
            .property(SmtProperty.deadlockFree())
            .sinkPlaces(NU053_MERGED, NU053_BUDGET)
            .budgetPlaces(NU053_BUDGET)
            .nuMaxClasses(1)
            // 60s (not 15s): the sound P-semiflow colour bound makes k larger, so the
            // coloured encoding is heavier and in-process JNI Z3 (Spacer) is slower here.
            // Rust's z3 binary and TS's WASM Z3 solve the same net fast — this is JNI-only.
            .timeout(Duration.ofSeconds(60))
            .verify();
        assertTrue(result.report().contains("Route A"),
            "expected the proof to defer to Route A\n" + result.report());
        assertTrue(result.isProven(),
            "Route A must prove the co-mint→join net deadlock-free\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void nu053RouteADetectsStrandingDeadlock() {
        // The EXTENDED drain can steal `a` and strand `b` under an unprioritised schedule
        // — a genuine reachable deadlock the coloured encoding must catch.
        var result = SmtVerifier.forNet(StructureOnly.bind(nu053StealNet()))
            .initialMarking(m -> { m.tokens(NU053_SOURCE, 1); m.tokens(NU053_BUDGET, 1); })
            .property(SmtProperty.deadlockFree())
            .sinkPlaces(NU053_MERGED, NU053_BUDGET, NU053_DEADLETTER)
            .budgetPlaces(NU053_BUDGET)
            .fragmentMode(FragmentMode.EXTENDED)
            .nuMaxClasses(1)
            .timeout(Duration.ofSeconds(15))
            .verify();
        assertTrue(result.isViolated(),
            "Route A must detect the drain-steal stranding as a deadlock\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void nu053RouteAAgreesWithRouteBOnNoStall() {
        // Differential: Route B (exact SCG, default class bound) and Route A (forced via a
        // tiny class bound) must agree that the net is deadlock-free.
        var net = nu053NoStallNet();
        java.util.function.IntFunction<SmtVerificationResult> build = maxClasses ->
            SmtVerifier.forNet(StructureOnly.bind(net))
                .initialMarking(m -> { m.tokens(NU053_SOURCE, 1); m.tokens(NU053_BUDGET, 1); })
                .property(SmtProperty.deadlockFree())
                .sinkPlaces(NU053_MERGED, NU053_BUDGET)
                .budgetPlaces(NU053_BUDGET)
                .nuMaxClasses(maxClasses)
                // 60s (not 15s): the sound P-semiflow colour bound makes k larger, so the
                // coloured encoding is heavier and in-process JNI Z3 (Spacer) is slower here.
                // Rust's z3 binary and TS's WASM Z3 solve the same net fast — this is JNI-only.
                .timeout(Duration.ofSeconds(60))
                .verify();
        var routeB = build.apply(100_000);
        var routeA = build.apply(1);
        assertTrue(routeB.isProven(), "Route B must prove no-stall\n" + routeB.report());
        assertTrue(routeA.isProven(), "Route A must prove no-stall\n" + routeA.report());
    }

    @Test
    @EnabledIf("z3Available")
    void poisonedInvariant_droppedByExactValidationAndReported() {
        // Chain A -(65539)-> B -(65537)-> C: the genuine conservation law carries a
        // weight of 65539*65537 = 4295229443 > Integer.MAX_VALUE, so the row cannot be
        // narrowed to the int weight vector at all. It must be dropped at extraction
        // (a wrapped invariant in the transition-rule body removes reachable successors
        // -> false PROVEN) and the report must say so.
        var pA = Place.of("A", String.class);
        var pB = Place.of("B", String.class);
        var pC = Place.of("C", String.class);
        var t1 = Transition.builder("T1")
            .inputs(In.exactly(65539, pA)).outputs(Out.place(pB)).build();
        var t2 = Transition.builder("T2")
            .inputs(In.exactly(65537, pB)).outputs(Out.place(pC)).build();
        var net = PetriNet.builder("Poisoned").transitions(t1, t2).build();

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
            .initialMarking(m -> m.tokens(pA, 1))
            .property(SmtProperty.deadlockFree())
            .timeout(Duration.ofSeconds(30))
            .verify();

        assertTrue(result.report().contains(
            "Dropped invariant: weight overflow at place 'C' "
            + "(exact value outside this implementation's integer extraction range)"),
            "Report should list the dropped invariant with the overflow reason\n" + result.report());
        assertTrue(result.report().contains("failed exact re-validation"),
            "Report should include the drop count line\n" + result.report());
        assertTrue(result.invariants().isEmpty(),
            "The corrupted invariant must not reach the encoder or the result\n" + result.report());
        // T1 needs 65539 tokens but M0(A) = 1: the net deadlocks immediately, so a
        // correct (unpoisoned) encoding must not certify deadlock-freedom.
        assertFalse(result.isProven(),
            "A false PROVEN here would mean the wrong invariant reached the encoder\n" + result.report());
    }

    // === IC3 certificate check (C1): verdict plumbing and end-to-end wiring ===

    // --- No Z3 needed: the downgrade mapping is pure ---

    @Test
    void certificateDowngradeReason_passed_returnsNull() {
        assertNull(SmtVerifier.certificateDowngradeReason(
            new CertificateChecker.Result.Passed()));
    }

    @Test
    void certificateDowngradeReason_failed_namesTheVc() {
        var reason = SmtVerifier.certificateDowngradeReason(
            new CertificateChecker.Result.Failed(
                CertificateChecker.Vc.CONSECUTION, "solver returned SATISFIABLE"));
        assertNotNull(reason);
        assertTrue(reason.contains("consecution (VC2)"), reason);
        assertTrue(reason.contains("unstrengthened"), reason);
        assertTrue(reason.contains("solver returned SATISFIABLE"), reason);
    }

    @Test
    void certificateDowngradeReason_eachVcHasDistinctLabel() {
        var initReason = SmtVerifier.certificateDowngradeReason(
            new CertificateChecker.Result.Failed(
                CertificateChecker.Vc.INIT, "solver returned SATISFIABLE"));
        var safetyReason = SmtVerifier.certificateDowngradeReason(
            new CertificateChecker.Result.Failed(
                CertificateChecker.Vc.SAFETY, "solver returned UNKNOWN"));
        assertTrue(initReason.contains("initiation (VC1)"), initReason);
        assertTrue(safetyReason.contains("safety (VC3)"), safetyReason);
    }

    @Test
    void certificateDowngradeReason_detailClauseIsUnconditional() {
        // The " - <detail>" clause is never conditional: a Java-only shape that
        // drops it would be a reason string no sibling implementation can emit.
        // The separator is an ASCII hyphen-minus, so the four reports diff
        // byte-for-byte.
        assertEquals(
            "certificate check failed: consecution (VC2) was not UNSAT"
            + " - solver returned SATISFIABLE (witness: A=1, B=1)"
            + "; the IC3 certificate could not be independently re-validated "
            + "against the unstrengthened step relation, so PROVEN is withheld",
            SmtVerifier.certificateDowngradeReason(
                new CertificateChecker.Result.Failed(
                    CertificateChecker.Vc.CONSECUTION,
                    "solver returned SATISFIABLE (witness: A=1, B=1)")));
    }

    @Test
    void certificateDowngradeReason_unavailable_returnsReason() {
        var reason = SmtVerifier.certificateDowngradeReason(
            new CertificateChecker.Result.Unavailable("Spacer produced no certificate"));
        assertNotNull(reason);
        assertTrue(reason.contains("Spacer produced no certificate"), reason);
    }

    // --- Z3-gated: end-to-end wiring through the verifier ---

    /** Single-token circular net: A <-> B, proven mutual exclusion via flat IC3. */
    private static PetriNet mutexNet(Place<String> p1, Place<String> p2) {
        var t1 = Transition.builder("AtoB")
            .inputs(In.one(p1))
            .outputs(Out.place(p2))
            .build();
        var t2 = Transition.builder("BtoA")
            .inputs(In.one(p2))
            .outputs(Out.place(p1))
            .build();
        return PetriNet.builder("MutualExclusion").transitions(t1, t2).build();
    }

    @Test
    @EnabledIf("z3Available")
    void corruptCertificate_injectedThroughSeam_downgradesToUnknown() {
        // The seam replaces the checker with one that reports a failing safety VC,
        // as a corrupted/invalid Spacer certificate would. The PROVEN verdict must
        // NOT survive: the verifier downgrades to Unknown naming the VC.
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);

        var result = SmtVerifier.forNet(StructureOnly.bind(mutexNet(p1, p2)))
            .initialMarking(m -> m.tokens(p1, 1))
            .property(SmtProperty.mutualExclusion(p1, p2))
            .timeout(Duration.ofSeconds(10))
            .certificateChecker((_, _, _, _, _, _, _, _, _) ->
                new CertificateChecker.Result.Failed(
                    CertificateChecker.Vc.SAFETY, "injected corrupt certificate"))
            .verify();

        assertFalse(result.isProven(),
            "A failing certificate must downgrade the proven verdict\n" + result.report());
        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(),
            "Downgrade target is the inconclusive verdict\n" + result.report());
        assertTrue(unknown.reason().contains("safety (VC3)"),
            "The reason must name the failing VC: " + unknown.reason());
        assertTrue(result.report().contains("Certificate check: FAILED"), result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void throwingCertificateChecker_downgradesToUnknown_neverPropagates() {
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);

        var result = SmtVerifier.forNet(StructureOnly.bind(mutexNet(p1, p2)))
            .initialMarking(m -> m.tokens(p1, 1))
            .property(SmtProperty.mutualExclusion(p1, p2))
            .timeout(Duration.ofSeconds(10))
            .certificateChecker((_, _, _, _, _, _, _, _, _) -> {
                throw new com.microsoft.z3.Z3Exception("simulated Z3 failure");
            })
            .verify();

        assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(),
            "A throwing checker must yield Unknown, not an exception\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void certificateCheckOptOut_skipsCheckAndKeepsProven() {
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);

        var result = SmtVerifier.forNet(StructureOnly.bind(mutexNet(p1, p2)))
            .initialMarking(m -> m.tokens(p1, 1))
            .property(SmtProperty.mutualExclusion(p1, p2))
            .timeout(Duration.ofSeconds(10))
            .certificateCheck(false)
            .verify();

        assertTrue(result.isProven(), "Opt-out must keep the proven verdict\n" + result.report());
        assertTrue(result.report().contains("  Certificate check: not applicable (disabled)"),
            "Opt-out must say the check did not run\n" + result.report());
        assertFalse(result.report().contains("Certificate check: PASSED"),
            "Opt-out must skip the check entirely\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void certificateCheckOptOut_alsoSkipsWithCorruptSeam() {
        // The opt-out must win over the seam: with the check disabled the injected
        // failing checker is never invoked.
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);

        var result = SmtVerifier.forNet(StructureOnly.bind(mutexNet(p1, p2)))
            .initialMarking(m -> m.tokens(p1, 1))
            .property(SmtProperty.mutualExclusion(p1, p2))
            .timeout(Duration.ofSeconds(10))
            .certificateCheck(false)
            .certificateChecker((_, _, _, _, _, _, _, _, _) -> {
                throw new AssertionError("checker must not run when opted out");
            })
            .verify();

        assertTrue(result.isProven(), result.report());
    }

    // === H1 linearity guard (lean/Libpetri/Strengthening.lean) ===

    @Test
    @EnabledIf("z3Available")
    void h1Guard_consumeAllWitness_placeBoundViolatedNotProven() {
        // End-to-end run of the Lean witness (`consume_all_hypothesis_is_necessary`):
        // T: all(P0) -> P1 with M0 = (2, 0). The linearized incidence column (-1, +1)
        // admits y = P0 + P1 = 2, which passes the numeric y*C = 0 gate; conjoined into
        // the CHC rule bodies it would prune the genuine successor (0, 1) — a real
        // firing drains BOTH tokens, y*M drops 2 -> 1 — and falsely prove
        // placeBound(P1, 0). With the H1 guard active the candidate is dropped, P1
        // genuinely reaches 1, and the verdict must be VIOLATED, never Proven. The
        // certificate checker (R' = I AND validated invariants) simply sees fewer
        // invariants folded in — the correct interaction, nothing special-cased.
        var p0 = Place.of("P0", String.class);
        var p1 = Place.of("P1", String.class);
        var t = Transition.builder("T").inputs(In.all(p0)).outputs(Out.place(p1)).build();
        var net = PetriNet.builder("h1-witness").transitions(t).build();

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
            .initialMarking(m -> m.tokens(p0, 2))
            .property(SmtProperty.placeBound(p1, 0))
            .timeout(Duration.ofSeconds(15))
            .verify();

        assertFalse(result.isProven(),
            "false Proven is the exact failure shape the H1 guard closes\n" + result.report());
        assertTrue(result.isViolated(),
            "P1 = 1 is genuinely reachable once the bogus invariant is dropped\n" + result.report());
        assertTrue(result.report().contains("Strengthening.lean H1"),
            "The existing drop-report plumbing should carry the H1 reason\n" + result.report());
    }

    // === Counterexample replay (C3): verdict plumbing and end-to-end wiring ===

    // --- No Z3 needed: the assessment mapping is pure (AbstractReplayer is JNI-free) ---

    private static final Place<String> RP0 = Place.of("p0", String.class);
    private static final Place<String> RP1 = Place.of("p1", String.class);
    private static final Place<String> RP2 = Place.of("p2", String.class);

    /** p0(1) -> t01 -> p1 -> t12 -> p2, then stuck: the dead-end chain, flattened. */
    private static org.libpetri.smt.encoding.FlatNet deadEndChainFlat() {
        var t01 = Transition.builder("t01").inputs(In.one(RP0)).outputs(Out.place(RP1)).build();
        var t12 = Transition.builder("t12").inputs(In.one(RP1)).outputs(Out.place(RP2)).build();
        var net = PetriNet.builder("dead-end").transitions(t01, t12).build();
        return org.libpetri.smt.encoding.NetFlattener.flatten(
            net, java.util.Set.of(), EnvironmentAnalysisMode.ignore());
    }

    private static org.libpetri.analysis.MarkingState mk(Place<?> place, int count) {
        return org.libpetri.analysis.MarkingState.builder().tokens(place, count).build();
    }

    @Test
    void assessCounterexample_nothingDecoded_keepsViolatedUnconfirmed() {
        // Nothing decoded is NOT a downgrade: the verdict stands, unconfirmed.
        var decoded = new CounterexampleDecoder.DecodedStates(
            java.util.List.of(), java.util.Set.of(), java.util.List.of(), "answer was null");

        var assessment = SmtVerifier.assessCounterexample(
            deadEndChainFlat(), mk(RP0, 1), decoded, SmtProperty.deadlockFree(), java.util.Set.of());

        var unconfirmed = assertInstanceOf(SmtVerifier.ReplayAssessment.Unconfirmed.class, assessment);
        assertTrue(unconfirmed.note().contains("unconfirmed"), unconfirmed.note());
    }

    @Test
    void assessCounterexample_chainableSet_confirmsWithReplayOrderedTrace() {
        var decoded = new CounterexampleDecoder.DecodedStates(
            java.util.List.of(mk(RP2, 1), mk(RP0, 1), mk(RP1, 1)),
            java.util.Set.of(mk(RP2, 1), mk(RP0, 1), mk(RP1, 1)), java.util.List.of(), null);

        var assessment = SmtVerifier.assessCounterexample(
            deadEndChainFlat(), mk(RP0, 1), decoded, SmtProperty.deadlockFree(), java.util.Set.of());

        var confirmed = assertInstanceOf(SmtVerifier.ReplayAssessment.Confirmed.class, assessment);
        assertEquals(java.util.List.of(mk(RP0, 1), mk(RP1, 1), mk(RP2, 1)), confirmed.trace(),
            "the replay must order the unordered decoded set into the actual run");
        assertEquals(java.util.List.of("t01", "t12"), confirmed.firings());
    }

    @Test
    void assessCounterexample_unchainableSet_downgradesAsSpuriousOrMismatch() {
        // The stub mimics a decoder mismatch: a garbage state no abstract run
        // reaches, under a property the net never violates. The mapping must
        // produce the downgrade, mirroring certificateDowngradeReason's design.
        var garbage = org.libpetri.analysis.MarkingState.builder()
            .tokens(RP0, 7).tokens(RP1, 7).tokens(RP2, 7).build();
        var decoded = new CounterexampleDecoder.DecodedStates(
            java.util.List.of(mk(RP0, 1), garbage),
            java.util.Set.of(mk(RP0, 1), garbage), java.util.List.of(), null);

        var assessment = SmtVerifier.assessCounterexample(
            deadEndChainFlat(), mk(RP0, 1), decoded,
            SmtProperty.placeBound(RP2, 5), java.util.Set.of());

        var downgraded = assertInstanceOf(SmtVerifier.ReplayAssessment.Downgraded.class, assessment);
        assertEquals(
            "counterexample replay found no firing chain to the violation under the "
            + "abstract semantics, so VIOLATED is withheld",
            downgraded.reason());
    }

    // --- Z3-gated: end-to-end wiring through the verifier ---

    @Test
    @EnabledIf("z3Available")
    void violatedVerdict_confirmedByAbstractReplay() {
        // Same net as deadlockNet_findsViolation: replay must confirm the genuine
        // deadlock and report the replay-ordered trace, starting at M0.
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);
        var p3 = Place.of("C", String.class);
        var t1 = Transition.builder("T1").inputs(In.one(p1)).outputs(Out.place(p2)).build();
        var t2 = Transition.builder("T2").inputs(In.one(p2), In.one(p3)).outputs(Out.place(p1)).build();
        var net = PetriNet.builder("DeadlockNet").transitions(t1, t2).build();

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
            .initialMarking(m -> m.tokens(p1, 1))
            .property(SmtProperty.deadlockFree())
            .timeout(Duration.ofSeconds(10))
            .verify();

        assertInstanceOf(SmtVerificationResult.Verdict.Violated.class, result.verdict(),
            "the genuine deadlock must stay VIOLATED with replay default-on\n" + result.report());
        assertEquals(Boolean.TRUE, result.counterexampleConfirmed(),
            "the replay must confirm the decoded counterexample\n" + result.report());
        assertTrue(result.report().contains("Counterexample replay: CONFIRMED"), result.report());
        assertFalse(result.counterexampleTrace().isEmpty(), result.report());
        assertEquals(mk(p1, 1), result.counterexampleTrace().getFirst(),
            "the replay-ordered trace starts at the initial marking\n" + result.report());
        assertEquals(mk(p2, 1), result.counterexampleTrace().getLast(),
            "the replay-ordered trace ends at the deadlocked marking\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void counterexampleReplayOptOut_keepsViolatedUnconfirmed() {
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);
        var p3 = Place.of("C", String.class);
        var t1 = Transition.builder("T1").inputs(In.one(p1)).outputs(Out.place(p2)).build();
        var t2 = Transition.builder("T2").inputs(In.one(p2), In.one(p3)).outputs(Out.place(p1)).build();
        var net = PetriNet.builder("DeadlockNet").transitions(t1, t2).build();

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
            .initialMarking(m -> m.tokens(p1, 1))
            .property(SmtProperty.deadlockFree())
            .timeout(Duration.ofSeconds(10))
            .counterexampleReplay(false)
            .verify();

        assertInstanceOf(SmtVerificationResult.Verdict.Violated.class, result.verdict(),
            result.report());
        assertNull(result.counterexampleConfirmed(),
            "opting out means replay did not apply, not that it failed\n" + result.report());
        assertTrue(result.report().contains("Counterexample replay: disabled"), result.report());
    }

    // --- C4: a replay that could not decide is an ABSENCE of evidence ---
    //
    // Only a search that covers the space and finds no chain may withdraw a
    // verdict. Every other outcome leaves VIOLATED standing with the tri-state
    // at FALSE (the replay applied and did not confirm), never at null.
    // Mirrors rust/libpetri-verification/src/smt_verifier.rs and
    // typescript/tests/verification/replay-downgrade.test.ts.

    /** p0 -> p1 -> ... -> p5, one token: the violation is five steps from M0. */
    private static PetriNet longChainNet(java.util.List<Place<String>> places) {
        var transitions = new java.util.ArrayList<Transition>();
        for (int i = 0; i + 1 < places.size(); i++) {
            transitions.add(Transition.builder("T" + i)
                .inputs(In.one(places.get(i)))
                .outputs(Out.place(places.get(i + 1)))
                .build());
        }
        return PetriNet.builder("LongChain").transitions(transitions.toArray(Transition[]::new)).build();
    }

    private static java.util.List<Place<String>> chainPlaces(int n) {
        var places = new java.util.ArrayList<Place<String>>();
        for (int i = 0; i < n; i++) {
            places.add(Place.of("p" + i, String.class));
        }
        return java.util.List.copyOf(places);
    }

    @Test
    @EnabledIf("z3Available")
    void segmentBudgetExhaustion_keepsViolatedUnconfirmed() {
        // The seam anchors the search on M0 alone; the violation is five steps away,
        // twice the segment budget. The search is cut short, which says nothing about
        // the net — the verdict must survive it.
        var places = chainPlaces(6);
        var result = SmtVerifier.forNet(StructureOnly.bind(longChainNet(places)))
            .initialMarking(m -> m.tokens(places.getFirst(), 1))
            .property(SmtProperty.placeBound(places.getLast(), 0))
            .replayStateSetOverride(java.util.Set.of(mk(places.getFirst(), 1)))
            .timeout(Duration.ofSeconds(20))
            .verify();

        assertInstanceOf(SmtVerificationResult.Verdict.Violated.class, result.verdict(),
            "a cut-short search must not withdraw the verdict\n" + result.report());
        assertEquals(Boolean.FALSE, result.counterexampleConfirmed(),
            "the replay applied and did not confirm: FALSE, not null\n" + result.report());
        assertTrue(result.report().contains("segment budget"),
            "the report must name the exhausted budget\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void nodeBudgetExhaustion_keepsViolatedUnconfirmed() {
        // Budget 1 is spent by the root node, so not one successor is admitted.
        var places = chainPlaces(4);
        var result = SmtVerifier.forNet(StructureOnly.bind(longChainNet(places)))
            .initialMarking(m -> m.tokens(places.getFirst(), 1))
            .property(SmtProperty.placeBound(places.getLast(), 0))
            .replayNodeBudget(1)
            .timeout(Duration.ofSeconds(20))
            .verify();

        assertInstanceOf(SmtVerificationResult.Verdict.Violated.class, result.verdict(),
            result.report());
        assertEquals(Boolean.FALSE, result.counterexampleConfirmed(), result.report());
        assertTrue(result.report().contains("replay budget exhausted (1 nodes admitted)"),
            "the report must name the exhausted budget\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void decodedSetWithoutInitialMarking_keepsViolatedUnconfirmed() {
        // Nothing to anchor on is a property of the proof text, not of the net.
        var places = chainPlaces(4);
        var result = SmtVerifier.forNet(StructureOnly.bind(longChainNet(places)))
            .initialMarking(m -> m.tokens(places.getFirst(), 1))
            .property(SmtProperty.placeBound(places.getLast(), 0))
            .replayStateSetOverride(java.util.Set.of(mk(places.get(1), 1), mk(places.get(2), 1)))
            .timeout(Duration.ofSeconds(20))
            .verify();

        assertInstanceOf(SmtVerificationResult.Verdict.Violated.class, result.verdict(),
            result.report());
        assertEquals(Boolean.FALSE, result.counterexampleConfirmed(), result.report());
        assertTrue(result.report().contains("is not among the"),
            "the report must say the anchor was missing\n" + result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void emptyDecode_keepsViolatedUnconfirmed() {
        // Decoding nothing is not a downgrade; mass-downgrading real verdicts on a
        // decoder that degraded gracefully would be the worse failure.
        var places = chainPlaces(4);
        var result = SmtVerifier.forNet(StructureOnly.bind(longChainNet(places)))
            .initialMarking(m -> m.tokens(places.getFirst(), 1))
            .property(SmtProperty.placeBound(places.getLast(), 0))
            .replayStateSetOverride(java.util.Set.of())
            .timeout(Duration.ofSeconds(20))
            .verify();

        assertInstanceOf(SmtVerificationResult.Verdict.Violated.class, result.verdict(),
            result.report());
        assertEquals(Boolean.FALSE, result.counterexampleConfirmed(), result.report());
        assertTrue(result.report().contains("no counterexample states could be decoded"),
            result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void noChainDowngrade_reportsUnknownWithConfirmedFalse() {
        // The one outcome that WITHDRAWS a verdict, end to end and without a seam:
        // an Unreachable property whose places are all outside the flat net. The
        // encoder's violation conjunction is then over nothing — i.e. TRUE, so Bad
        // holds everywhere and Spacer answers SAT at M0 — while the replay's
        // non-empty guard (AbstractReplayer.violates) refuses to call any marking
        // Bad. The search covers the two-state space, finds no chain, and the
        // verifier withholds VIOLATED rather than report a violation it cannot
        // reproduce.
        var pA = Place.of("A", String.class);
        var pB = Place.of("B", String.class);
        var ghost = Place.of("Ghost", String.class); // never declared by a transition
        var t = Transition.builder("T").inputs(In.one(pA)).outputs(Out.place(pB)).build();
        var net = PetriNet.builder("tiny").transitions(t).build();

        var result = SmtVerifier.forNet(StructureOnly.bind(net))
            .initialMarking(m -> m.tokens(pA, 1))
            .property(SmtProperty.unreachable(java.util.Set.of(ghost)))
            .timeout(Duration.ofSeconds(20))
            .verify();

        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(),
            "a refuted counterexample downgrades, it does not stand\n" + result.report());
        assertEquals(
            "counterexample replay found no firing chain to the violation under the "
            + "abstract semantics, so VIOLATED is withheld",
            unknown.reason());
        // D1: the replay APPLIED and refuted the trace. That is strictly more
        // informative than "did not apply", so the tri-state is FALSE, never null.
        assertEquals(Boolean.FALSE, result.counterexampleConfirmed(),
            "a refutation reports FALSE, not the null that means 'replay did not apply'\n"
            + result.report());
        assertTrue(result.report().contains("Counterexample replay: FAILED"), result.report());
        assertTrue(result.counterexampleTrace().isEmpty(), result.report());
    }
}
