package org.libpetri.smt;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.fixtures.VerificationNets;
import org.libpetri.smt.z3.CertificateChecker;
import org.libpetri.smt.z3.StateEquationNets;
import org.libpetri.smt.z3.StateEquationNets.JoinWithSkip;
import org.libpetri.smt.z3.StateEquationNets.QueueAndBundle;
import org.libpetri.smt.z3.Z3Solver;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.*;

/**
 * [VER-018] and [VER-019] through {@link SmtVerifier}: where the phases run, what they decide, and
 * the report lines they print. Mirrors the end-to-end cases of
 * {@code typescript/tests/verification/state-equation-phase.test.ts} and the verifier-level phase
 * tests of the Rust port. The pinned report blocks were diffed byte-identical against the
 * TypeScript verifier's reports for the same nets when this port landed.
 */
@EnabledIf("z3Available")
class StateEquationPhaseVerifierTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static SmtVerifier joinVerifier(JoinWithSkip join) {
        return SmtVerifier.forNet(StructureOnly.bind(join.net()))
            // Explicit opt-out, not an oversight: [VER-017]'s enumeration route closes these small
            // untimed nets and would decide them with no solver at all, before either phase ran.
            .enumerationMaxClasses(0)
            .initialMarking(join.m0())
            .property(SmtProperty.deadlockFree())
            .sinkPlaces(join.done(), join.skipped())
            .timeout(Duration.ofSeconds(30));
    }

    private static SmtVerifier queueVerifier(QueueAndBundle queue, boolean cancellable) {
        return SmtVerifier.forNet(StructureOnly.bind(queue.net()))
            .enumerationMaxClasses(0)
            .initialMarking(queue.m0())
            .property(SmtProperty.deadlockFree())
            .sinkPlaces(queue.sinks(cancellable).toArray(new Place<?>[0]))
            .timeout(Duration.ofSeconds(30));
    }

    private static String method(SmtVerificationResult result) {
        return result.verdict() instanceof SmtVerificationResult.Verdict.Proven proven ? proven.method() : null;
    }

    /** {@code T: IN → OUT} with {@code IN} an environment place in {@code mode}. */
    private static SmtVerifier envSource(EnvironmentAnalysisMode mode) {
        var in = EnvironmentPlace.of(Place.of("IN", String.class));
        var out = Place.of("OUT", String.class);
        var net = PetriNet.builder("envNet")
            .transitions(Transition.builder("T").inputs(In.one(in.place())).outputs(Out.place(out)).build()).build();
        return SmtVerifier.forNet(StructureOnly.bind(net)).enumerationMaxClasses(0)
            .environmentPlaces(in).environmentMode(mode)
            .property(SmtProperty.placeBound(out, 0)).timeout(Duration.ofSeconds(30));
    }

    /**
     * [VER-018] AC1/AC2: the join proves with the inequality the inhibitor makes inductive,
     * certified, and the discovered invariants are the refinements as printed.
     */
    @Test
    void provesTheJoinWithTheInequalityTheInhibitorMakesInductive_certified() {
        var result = joinVerifier(StateEquationNets.joinWithSkip()).verify();
        assertTrue(result.isProven(), result.report());
        assertEquals("state-equation", method(result), result.report());
        assertEquals(SmtVerificationResult.Route.SMT, result.route());
        assertTrue(result.report().contains("""
              State-equation phase (VER-018):
                Refinement (inductive): hasdata <= ready0 + ready1
                Queries: 3
                Status: no marking the equation admits violates the property
              Certificate check: PASSED (init, consecution, safety)

            === RESULT ===

            PROVEN (state equation): Deadlock-freedom (sinks: done, skipped)
              Every reachable marking satisfies the marking equation over 8 firing counters \
            and the refinements above, and none of those markings violates the property (VER-018).
              NOTE: Verification ignores timing constraints.
            """), result.report());
        assertEquals(List.of("hasdata <= ready0 + ready1"), result.discoveredInvariants());
        var proven = (SmtVerificationResult.Verdict.Proven) result.verdict();
        assertTrue(proven.inductiveInvariant().contains("(<= (+ x!5 (- x!6) (- x!7)) 0)"), proven.inductiveInvariant());
        assertFalse(result.report().contains("Phase 5"), result.report());
    }

    /** [VER-018] AC5 and [VER-019] AC5: with both phases off, the fixpoint query decides. */
    @Test
    void keepsTheVerdictTheFixpointQueryReachesWhenBothPhasesAreOff() {
        var result = joinVerifier(StateEquationNets.joinWithSkip())
            .stateEquationPhase(false).firingBound(false).verify();
        assertTrue(result.isProven(), result.report());
        assertEquals("IC3/PDR", method(result), result.report());
        assertFalse(result.report().contains("VER-018"), result.report());
        assertFalse(result.report().contains("VER-019"), result.report());
    }

    /** The queue is empty at every quiescence once the signal came, which holds only relative to the equation. */
    @Test
    void provesTheQueueWithARelativeRefinement() {
        var result = queueVerifier(StateEquationNets.queueAndBundle(3, false), false).verify();
        assertTrue(result.isProven(), result.report());
        assertEquals("state-equation", method(result), result.report());
        assertTrue(result.report().contains("    Refinement (relative): 3*out + q <= 3\n"), result.report());
        assertTrue(result.report().contains("  Certificate check: PASSED (init, consecution, safety)\n"), result.report());
        // The refinements before it depend on the models z3 returns (4.11 also adds `out + q <= 3`).
        assertTrue(result.discoveredInvariants().contains("3*out + q <= 3"), result.report());
    }

    /** [VER-018] AC3: a candidate a run within its counts realises is violated, with that run, confirmed. */
    @Test
    void reportsTheRunThatStrandsTheCancelledQueue() {
        var queue = StateEquationNets.queueAndBundle(3, true);
        var result = queueVerifier(queue, true).verify();
        assertTrue(result.isViolated(), result.report());
        assertEquals(Boolean.TRUE, result.counterexampleConfirmed(), result.report());
        assertEquals(List.of("produce", "produce", "produce", "cancel"), result.counterexampleTransitions());
        assertTrue(result.counterexampleTrace().getLast().tokens(queue.q()) > 0, result.report());
        assertTrue(result.report().contains("""
                Status: a run within the candidate's firing counts reaches a violation

            === RESULT ===

            VIOLATED: Deadlock-freedom (sinks: out, budget, cancelled)
              Counterexample trace (replay order, 5 states):
                0: {budget:3, src:1}
                1: {budget:2, q:1, src:1}
                2: {budget:1, q:2, src:1}
                3: {q:3, src:1}
                4: {cancelled:1, q:3}
              Firing sequence: produce -> produce -> produce -> cancel

              WARNING: This counterexample is in UNTIMED semantics.
              It may be spurious if timing constraints prevent this sequence.
            """), result.report());
    }

    /** [VER-018] AC6: every query is dumped under its own phase name ([VER-013]). */
    @Test
    void dumpsEachOfItsQueriesUnderItsOwnPhaseName(@TempDir Path dump) throws Exception {
        var result = joinVerifier(StateEquationNets.joinWithSkip())
            .solver(Z3Solver.resolve().withDumpDir(dump))
            .verify();
        assertTrue(result.isProven(), result.report());
        // The candidate, the inequality excluding it, the unsat, and the certificate check. The
        // counter is process-wide, so the numbers give the order and the names the phases.
        try (Stream<Path> files = Files.list(dump)) {
            var scripts = files.map(p -> p.getFileName().toString())
                .filter(n -> n.endsWith(".smt2"))
                .sorted()
                .map(n -> n.substring(n.indexOf('-') + 1))
                .toList();
            assertEquals(List.of("state-equation.smt2", "invariant.smt2", "state-equation.smt2", "certificate.smt2"),
                scripts);
        }
    }

    /** [VER-018] AC7: encodeScripts() exposes the phase's first query exactly where verify() would send it. */
    @Test
    void reportsTheFirstQueryThroughEncodeScriptsExactlyWhereThePhaseRuns() throws IOException {
        var join = StateEquationNets.joinWithSkip();
        String query = joinVerifier(join).encodeScripts().stateEquation();
        assertNotNull(query);
        assertTrue(query.startsWith("; State-equation phase (VER-018)"), query);
        assertFalse(query.contains("(<= (+ m"), "the first query carries no refinement: " + query);
        assertNull(joinVerifier(join).stateEquationPhase(false).encodeScripts().stateEquation());
        // The firing bound does not gate it.
        assertNotNull(joinVerifier(join).firingBound(false).encodeScripts().stateEquation());

        assertNull(envSource(EnvironmentAnalysisMode.ignore()).encodeScripts().stateEquation());
        assertNotNull(envSource(EnvironmentAnalysisMode.alwaysAvailable()).encodeScripts().stateEquation());

        var nu = VerificationNets.nuScatterGather();
        var budget = Place.of("budget", String.class);
        var coloured = SmtVerifier.forNet(nu.net()).initialMarking(nu.initialMarking())
            .property(SmtProperty.branchPlaceBound(budget, 2)).budgetPlaces(budget).encodeScripts();
        assertTrue(coloured.coloured());
        assertNull(coloured.stateEquation());
    }

    /**
     * [VER-018] AC4: the phase's proof is withheld unless its certificate check passes. The
     * failure stays in the report, nested under the phase, and the pipeline continues: here the
     * firing bound decides instead, and with it off the fixpoint query does.
     */
    @Test
    void withholdsThePhasesProofWhenItsCertificateFailsAndContinues() {
        // The phase's check is the only one that forces the counter-augmented step relation.
        SmtVerifier.CertificateCheck failingPhase = (cert, flat, m0, property, sinks, invariants, z3, timeout,
                conditional, stateEquation) -> stateEquation
            ? new CertificateChecker.Result.Failed(CertificateChecker.Vc.SAFETY, "injected")
            : CertificateChecker.check(cert, flat, m0, property, sinks, invariants, z3, timeout, conditional, false);
        var join = StateEquationNets.joinWithSkip();

        var bounded = joinVerifier(join).certificateChecker(failingPhase).verify();
        assertTrue(bounded.report().contains("    Status: no marking the equation admits violates the property\n"
            + "    Certificate check: FAILED (certificate check failed: safety (VC3) was not UNSAT - injected; "
            + "the IC3 certificate could not be independently re-validated against the unstrengthened step "
            + "relation, so PROVEN is withheld)\n"
            + "  Firing bound (VER-019):\n"), bounded.report());
        assertFalse(bounded.report().contains("PROVEN (state equation)"), bounded.report());
        assertEquals("bounded-model-check", method(bounded), bounded.report());

        var fixpoint = joinVerifier(join).certificateChecker(failingPhase).firingBound(false).verify();
        assertEquals("IC3/PDR", method(fixpoint), fixpoint.report());
        assertTrue(fixpoint.report().contains("  Certificate check: PASSED (init, consecution, safety)"),
            fixpoint.report());
    }

    /** [VER-019] AC1/AC3: with the state-equation phase off, the queue is proven by a bounded model check. */
    @Test
    void provesTheQueueByABoundedModelCheckToItsFiringBound() {
        var queue = StateEquationNets.queueAndBundle(3, false);
        var result = queueVerifier(queue, false).stateEquationPhase(false).verify();
        assertTrue(result.isProven(), result.report());
        assertEquals("bounded-model-check", method(result), result.report());
        assertTrue(result.report().contains("""
              Firing bound (VER-019):
                Bound: 5 firings (budget + s + 2*src drops on every firing)
                Depths: 5 none
                Status: no run of at most the bound reaches a violation, and no run is longer
              Certificate check: not applicable (bounded model check to the firing bound)

            === RESULT ===

            PROVEN (bounded model check): Deadlock-freedom (sinks: out, budget)
              No run has more than 5 firings, and none of at most that many reaches a violation (VER-019).
              NOTE: Verification ignores timing constraints.
            """), result.report());
        assertTrue(result.discoveredInvariants().isEmpty());
        assertNull(((SmtVerificationResult.Verdict.Proven) result.verdict()).inductiveInvariant());

        // A declared environment place that no arc touches still turns the phase off, as it does
        // in TypeScript, whose gate reads the declared injection rather than the resolved one.
        var ghost = EnvironmentPlace.of(Place.of("ghost", String.class));
        var declared = queueVerifier(queue, false).stateEquationPhase(false)
            .environmentPlaces(ghost).environmentMode(EnvironmentAnalysisMode.bounded(1)).verify();
        assertTrue(declared.report().contains("""
              Firing bound (VER-019):
                Status: inconclusive (environment injection has no firing bound)
            """), declared.report());
        assertNotEquals("bounded-model-check", method(declared), declared.report());
    }

    /** [VER-019] AC2: a violating bounded run is replayed and reported, confirmed. */
    @Test
    void findsTheCancelledQueueByABoundedRunAndReplaysIt() {
        var queue = StateEquationNets.queueAndBundle(3, true);
        var result = queueVerifier(queue, true).stateEquationPhase(false).verify();
        assertTrue(result.isViolated(), result.report());
        assertEquals(Boolean.TRUE, result.counterexampleConfirmed(), result.report());
        assertTrue(result.report().contains(
            "    Depths: 5 violation\n    Status: a bounded run reaches a violation (replayed)\n"), result.report());
        assertTrue(result.counterexampleTrace().getLast().tokens(queue.q()) > 0, result.report());
    }

    /** [VER-019] AC4: a ring has no ranking; the report names what repeats, and the fixpoint query proves the bound. */
    @Test
    void namesTheTransitionsAnUnboundedNetRepeatsAndLeavesItToTheFixpointQuery() {
        var p0 = Place.of("p0", String.class);
        var p1 = Place.of("p1", String.class);
        var p2 = Place.of("p2", String.class);
        var net = PetriNet.builder("ring").transitions(
            Transition.builder("t0").inputs(In.one(p0)).outputs(Out.place(p1)).build(),
            Transition.builder("t1").inputs(In.one(p1)).outputs(Out.place(p2)).build(),
            Transition.builder("t2").inputs(In.one(p2)).outputs(Out.place(p0)).build()).build();
        var result = SmtVerifier.forNet(StructureOnly.bind(net)).enumerationMaxClasses(0)
            .initialMarking(MarkingState.builder().tokens(p0, 1).build())
            .property(SmtProperty.placeBound(p0, 1))
            .linearBound(false).stateEquationPhase(false)
            .timeout(Duration.ofSeconds(30)).verify();
        assertTrue(result.isProven(), result.report());
        assertTrue(result.report().contains(
            "    Status: no firing bound — the marking equation lets t0, t1, t2 repeat; not attempted\n"), result.report());
        assertEquals("IC3/PDR", method(result), result.report());
    }

    /**
     * Where the phases do not run: under Ignore with environment places ([VER-006]), where every
     * Proven is refused anyway, and on a ν-net's exact routes. A phase that stepped aside on a net
     * with injection says why, and the fixpoint query still decides.
     */
    @Test
    void thePhasesStepAsideWhereTheyCannotDecide() {
        var ignored = envSource(EnvironmentAnalysisMode.ignore()).verify();
        assertFalse(ignored.report().contains("VER-018"), ignored.report());
        assertFalse(ignored.report().contains("VER-019"), ignored.report());

        var nu = VerificationNets.nuScatterGather();
        var budget = Place.of("budget", String.class);
        var coloured = SmtVerifier.forNet(nu.net()).initialMarking(nu.initialMarking())
            .property(SmtProperty.branchPlaceBound(budget, 2)).budgetPlaces(budget)
            .timeout(Duration.ofSeconds(30)).verify();
        assertTrue(coloured.isProven(), coloured.report());
        assertFalse(coloured.report().contains("VER-018"), coloured.report());

        var injected = envSource(EnvironmentAnalysisMode.alwaysAvailable()).verify();
        assertTrue(injected.isViolated(), injected.report());
        assertTrue(injected.report().contains("""
                Status: inconclusive (no trap and no inductive inequality with weights within ±8 excludes the candidate)
                Unsettled candidate: OUT=1 after T x1
              Firing bound (VER-019):
                Status: inconclusive (environment injection has no firing bound)
            """), injected.report());
        assertEquals(Boolean.TRUE, injected.counterexampleConfirmed(), injected.report());
    }
}
