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
            var result = SmtVerifier.forNet(net)
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

        var bounded1 = SmtVerifier.forNet(build.get())
            .environmentPlaces(in)
            .environmentMode(EnvironmentAnalysisMode.bounded(1))
            .property(SmtProperty.placeBound(out, 0))
            .timeout(Duration.ofSeconds(15))
            .verify();
        assertTrue(bounded1.isProven(),
            "bounded(1) starves a 2-token env input -> OUT stays 0\n" + bounded1.report());

        var always = SmtVerifier.forNet(build.get())
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

        var result = SmtVerifier.forNet(net)
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
        var result = SmtVerifier.forNet(net)
            .initialMarking(m -> { m.tokens(pA, 1); m.tokens(pB, 5); })
            .property(SmtProperty.placeBound(pB, 5))
            .timeout(Duration.ofSeconds(10))
            .verify();

        assertFalse(result.isViolated(),
            "B with reset arc should never exceed initial value\n" + result.report());
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
    void nuBranchBudgetBound_provenWithDeclaredBudget() {
        // NU-040 #1: with the budget declared, the live correlation pool is
        // bounded — BranchPlaceBound(budget, k) is proven by conservation.
        var result = SmtVerifier.forNet(nuScatterGatherNet())
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
        var result = SmtVerifier.forNet(nuScatterGatherNet())
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
    }

    @Test
    void nuStructurallyBounded_withoutDeclaredBudget_decidedByRouteB() {
        // NU-050 Route B: without a DECLARED budget place the SMT/Route-A path
        // returns Unknown, but the name-aware SCG name-partition quotient discovers
        // the structural bound (the budget token caps live groups) and proves the
        // bound exactly — the beyond-bounded win. Pure SCG, so no Z3 binary needed.
        var result = SmtVerifier.forNet(nuScatterGatherNet())
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
        var result = SmtVerifier.forNet(nuScatterGatherNet())
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
        var result = SmtVerifier.forNet(nuScatterGatherNet())
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

        var result = SmtVerifier.forNet(net)
            .initialMarking(m -> m.tokens(start, 1))
            .property(SmtProperty.joinedOrDeadLettered(pending))
            .timeout(Duration.ofSeconds(15))
            .verify();
        assertTrue(result.isProven(),
            "every group joins/dead-letters before quiescence -> Proven\n" + result.report());
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

        var result = SmtVerifier.forNet(net)
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
        var result = SmtVerifier.forNet(nuDistinctMintsNet())
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
        var result = SmtVerifier.forNet(nuScatterGatherNet())
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
        var result = SmtVerifier.forNet(nuDistinctMintsNoBudgetNet())
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
        var result = SmtVerifier.forNet(nuUnboundedMintNet())
            .initialMarking(m -> m.tokens(NU_SOURCE, 1))
            .property(SmtProperty.unreachable(Set.of(NU_MERGED)))
            .nuMaxClasses(40)
            .verify();
        assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(),
            "an unbounded ν-mint must truncate to Unknown\n" + result.report());
        var reason = ((SmtVerificationResult.Verdict.Unknown) result.verdict()).reason();
        assertTrue(reason.contains("truncated"), "Unknown reason should mention truncation: " + reason);
    }
}
