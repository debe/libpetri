package org.libpetri.smt;

import java.time.Duration;
import java.util.List;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.fixtures.VerificationNets;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [VER-025] the bounded witness phase through {@link SmtVerifier}: where it runs, what it
 * reports, and that it only ever adds a {@code Violated}. The encoder, the replay, the trim and
 * the driver's outcomes are {@code org.libpetri.smt.z3.WitnessPhaseTest}'s.
 *
 * <p>The ν-net: {@code accept: E → source}, {@code fork: source + budget → branchA + branchB}
 * (the mint), {@code join: branchA + branchB → merged} matched by name,
 * {@code finish: 2 merged → done}. {@code E} is an environment place under {@code bounded(2)},
 * so the name-coloured encoding declines and the name-blind flat encoding decides: the case no
 * earlier phase searches for a counterexample.
 */
@EnabledIf("z3Available")
class WitnessPhaseVerifierTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final String HEADER = "  Bounded witness phase (VER-025):\n";
    private static final String NO_RUN =
        "    Status: no run of at most 8 steps reaches a violation (not a proof)\n";
    private static final String NU_NOTE = "a 'Violated' counterexample may be spurious";

    private static final Place<Object> E = Place.of("E", Object.class);
    private static final Place<Object> SOURCE = Place.of("source", Object.class);
    private static final Place<Object> BUDGET = Place.of("budget", Object.class);
    private static final Place<String> BRANCH_A = Place.of("branchA", String.class);
    private static final Place<String> BRANCH_B = Place.of("branchB", String.class);
    private static final Place<String> MERGED = Place.of("merged", String.class);
    private static final Place<String> DONE = Place.of("done", String.class);

    private static PetriNet nuNet() {
        var match = MatchSpec.builder()
            .key(BRANCH_A, (String v) -> NameId.of(v))
            .key(BRANCH_B, (String v) -> NameId.of(v))
            .build();
        return StructureOnly.bind(PetriNet.builder("witness-nu").transitions(
            Transition.builder("accept").inputs(In.one(E)).outputs(Out.place(SOURCE)).build(),
            Transition.builder("fork").inputs(In.one(SOURCE), In.one(BUDGET))
                .outputs(Out.and(Out.place(BRANCH_A), Out.place(BRANCH_B))).build(),
            Transition.builder("join").inputs(In.one(BRANCH_A), In.one(BRANCH_B)).match(match)
                .outputs(Out.place(MERGED)).build(),
            Transition.builder("finish").inputs(In.exactly(2, MERGED)).outputs(Out.place(DONE)).build()
        ).build());
    }

    /** The ν-net with {@code budget} tokens of budget, the budget declared. */
    private static SmtVerifier nu(SmtProperty property, int budget) {
        return SmtVerifier.forNet(nuNet())
            .initialMarking(MarkingState.builder().tokens(BUDGET, budget).build())
            .environmentPlaces(EnvironmentPlace.of(E))
            .environmentMode(EnvironmentAnalysisMode.bounded(2))
            .budgetPlaces(BUDGET)
            .mintTransitions("fork")
            .property(property)
            .timeout(Duration.ofSeconds(60));
    }

    private static SmtVerifier fixture(String net, SmtProperty property) {
        var named = VerificationNets.build(net);
        return SmtVerifier.forNet(named.net())
            .initialMarking(named.initialMarking())
            .environmentPlaces(named.environmentPlaces().toArray(EnvironmentPlace<?>[]::new))
            .environmentMode(named.environmentMode())
            .property(property)
            .timeout(Duration.ofSeconds(60));
    }

    private static Place<?> p(String net, String name) {
        return VerificationNets.build(net).net().places().stream()
            .filter(place -> place.name().equals(name)).findFirst().orElseThrow();
    }

    // ==================== what it finds ====================

    /** The gap the phase closes: a ν-net, name-blind, with injection — two tokens need eight steps. */
    @Test
    void findsARunThatNeedsInjectionsOnANameBlindNuNet() {
        var r = nu(SmtProperty.placeBound(MERGED, 1), 3).verify();
        assertTrue(r.isViolated(), r.report());
        assertTrue(r.report().contains(
            HEADER + "    Status: a run of 8 steps reaches a violation (replayed; depth 8)\n"), r.report());
        assertEquals(Boolean.TRUE, r.counterexampleConfirmed(), r.report());
        assertEquals(SmtVerificationResult.Route.SMT, r.route(), r.report());
        assertEquals(8, r.counterexampleTransitions().size(), r.report());
        assertEquals(2, r.counterexampleTransitions().stream().filter("inject(E)"::equals).count(), r.report());
        assertEquals(9, r.counterexampleTrace().size(), r.report());
        // The run is one of the name-blind abstraction: it carries the ν guard's note.
        assertTrue(r.report().contains(NU_NOTE), r.report());
        // No fixpoint query was needed.
        assertFalse(r.report().contains("Status: SAT (counterexample found)"), r.report());
    }

    /** {@code done} needs nine steps: past the default depth, within a raised one. */
    @Test
    void aRunPastTheDepthFallsThroughAndARaisedDepthFindsIt() {
        var byDefault = nu(SmtProperty.placeBound(DONE, 0), 3).verify();
        assertTrue(byDefault.isViolated(), byDefault.report());
        assertTrue(byDefault.report().contains(HEADER + NO_RUN), byDefault.report());
        assertTrue(byDefault.report().contains("Status: SAT (counterexample found)"), byDefault.report());

        var raised = nu(SmtProperty.placeBound(DONE, 0), 3).witnessDepth(12).verify();
        assertTrue(raised.isViolated(), raised.report());
        // Trimmed: the solver pads to twelve steps, the run needs nine.
        assertTrue(raised.report().contains(
            HEADER + "    Status: a run of 9 steps reaches a violation (replayed; depth 12)\n"), raised.report());
        assertEquals(9, raised.counterexampleTransitions().size(), raised.report());
        assertEquals("finish", raised.counterexampleTransitions().getLast(), raised.report());
    }

    /** The shared fixtures of [VER-025]: four steps with two injections, and ten steps. */
    @Test
    void theSharedFixturesAreDecidedAsTheirDescriptionsSay() {
        var shallow = fixture("envBoundedPair", SmtProperty.placeBound(p("envBoundedPair", "p1"), 1)).verify();
        assertTrue(shallow.isViolated(), shallow.report());
        assertTrue(shallow.report().contains(
            HEADER + "    Status: a run of 4 steps reaches a violation (replayed; depth 8)\n"), shallow.report());
        assertEquals(List.of("inject(e)", "t", "inject(e)", "t").stream().sorted().toList(),
            shallow.counterexampleTransitions().stream().sorted().toList(), shallow.report());

        var deep = fixture("envBoundedPair", SmtProperty.placeBound(p("envBoundedPair", "p1"), 4)).verify();
        assertTrue(deep.isViolated(), deep.report());
        assertTrue(deep.report().contains(HEADER + NO_RUN), deep.report());
        assertTrue(deep.report().contains("Status: SAT (counterexample found)"), deep.report());
    }

    /** {@code M0} violates: the run has no step, as the fixpoint path reports it. */
    @Test
    void anInitialViolationIsTheEmptyRun() {
        var r = nu(SmtProperty.placeBound(BUDGET, 2), 3).verify();
        assertTrue(r.isViolated(), r.report());
        assertTrue(r.report().contains(
            HEADER + "    Status: a run of 0 steps reaches a violation (replayed; depth 8)\n"), r.report());
        assertEquals(1, r.counterexampleTrace().size(), r.report());
        assertTrue(r.counterexampleTransitions().isEmpty(), r.report());
        assertEquals(Boolean.TRUE, r.counterexampleConfirmed(), r.report());
    }

    /** {@code counterexampleReplay} governs the replay after the fixpoint query, not this one. */
    @Test
    void theReplayOptOutDoesNotSwitchThePhaseOff() {
        var r = nu(SmtProperty.placeBound(MERGED, 1), 3).counterexampleReplay(false).verify();
        assertTrue(r.isViolated(), r.report());
        assertTrue(r.report().contains(HEADER), r.report());
        assertEquals(Boolean.TRUE, r.counterexampleConfirmed(), r.report());
    }

    /**
     * Under {@code Ignore} the flat net has no injection step, so only runs that inject nothing
     * are found; such a run is real, as a fixpoint {@code Violated} is there.
     */
    @Test
    void underIgnoreItFindsOnlyRunsWithoutInjection() {
        var needsInjection = fixture("envBoundedPair", SmtProperty.placeBound(p("envBoundedPair", "p1"), 1))
            .environmentMode(EnvironmentAnalysisMode.ignore())
            .verify();
        assertFalse(needsInjection.isViolated(), needsInjection.report());
        assertTrue(needsInjection.report().contains(HEADER + NO_RUN), needsInjection.report());

        var e = Place.of("e", Object.class);
        var a = Place.of("a", Object.class);
        var b = Place.of("b", Object.class);
        var net = StructureOnly.bind(PetriNet.builder("ignore-closed-part").transitions(
            Transition.builder("t").inputs(In.one(e)).outputs(Out.place(a)).build(),
            Transition.builder("u").inputs(In.one(a)).outputs(Out.place(b)).build()
        ).build());
        var closedRun = SmtVerifier.forNet(net)
            .initialMarking(MarkingState.builder().tokens(a, 1).build())
            .environmentPlaces(EnvironmentPlace.of(e))
            .environmentMode(EnvironmentAnalysisMode.ignore())
            .property(SmtProperty.placeBound(b, 0))
            .timeout(Duration.ofSeconds(60))
            .verify();
        assertTrue(closedRun.isViolated(), closedRun.report());
        assertTrue(closedRun.report().contains(
            HEADER + "    Status: a run of 1 steps reaches a violation (replayed; depth 8)\n"), closedRun.report());
        assertEquals(List.of("u"), closedRun.counterexampleTransitions(), closedRun.report());
    }

    // ==================== what it never changes ====================

    /**
     * A property the fixpoint query proves: the phase finds no run, says it is no proof, and the
     * verdict, its method and the rest of the report are those of the pipeline without it.
     */
    @Test
    void aProvenQueryKeepsItsVerdictAndReportApartFromThePhaseLines() {
        // The linear bound would prove this structurally before either path is reached.
        var on = nu(SmtProperty.placeBound(MERGED, 1), 1).linearBound(false).verify();
        var off = nu(SmtProperty.placeBound(MERGED, 1), 1).linearBound(false).witnessDepth(0).verify();
        assertTrue(on.isProven(), on.report());
        assertTrue(off.isProven(), off.report());
        assertEquals(off.verdict(), on.verdict());
        assertEquals(off.route(), on.route());
        assertTrue(on.report().contains(HEADER + NO_RUN), on.report());
        assertEquals(off.report(), on.report().replace(HEADER + NO_RUN, ""));
    }

    @Test
    void depthZeroDisablesThePhase() {
        var r = nu(SmtProperty.placeBound(MERGED, 1), 3).witnessDepth(0).verify();
        // The fixpoint query still finds the violation; no line of the phase is in the report.
        assertTrue(r.isViolated(), r.report());
        assertFalse(r.report().contains("Bounded witness phase"), r.report());
        assertTrue(r.report().contains("Status: SAT (counterexample found)"), r.report());
        assertNull(nu(SmtProperty.placeBound(MERGED, 1), 3).witnessDepth(0).encodeScripts().witness());
    }

    @Test
    void aNegativeDepthIsRejected() {
        var e = assertThrows(IllegalArgumentException.class,
            () -> SmtVerifier.forNet(nuNet()).witnessDepth(-1));
        assertEquals("witnessDepth must be non-negative, got -1", e.getMessage());
    }

    // ==================== where it does not run ====================

    /**
     * The script is reported exactly when {@code verify()} would send it: on the flat encoding,
     * at the configured depth, and not on a ν-net whose verdict the guard turns into Unknown.
     */
    @Test
    void theEncodedScriptFollowsTheGates() {
        String byDefault = nu(SmtProperty.placeBound(MERGED, 1), 3).encodeScripts().witness();
        assertNotNull(byDefault);
        assertTrue(byDefault.startsWith("; Bounded run (VER-019): 8 steps"), byDefault);
        // Four transitions and one injection: idle is 5.
        assertTrue(byDefault.contains("(assert (and (>= s0 0) (<= s0 5)))"), byDefault);
        assertTrue(nu(SmtProperty.placeBound(MERGED, 1), 3).witnessDepth(3).encodeScripts().witness()
            .startsWith("; Bounded run (VER-019): 3 steps"));

        // A quiescence property on a ν-net: the guard would answer Unknown whatever is found.
        assertNull(nu(SmtProperty.deadlockFree(), 3).encodeScripts().witness());
        // No declared budget: unbounded fresh names, Unknown as well.
        var unbudgeted = SmtVerifier.forNet(nuNet())
            .initialMarking(MarkingState.builder().tokens(BUDGET, 3).build())
            .environmentPlaces(EnvironmentPlace.of(E))
            .environmentMode(EnvironmentAnalysisMode.bounded(2))
            .mintTransitions("fork")
            .property(SmtProperty.placeBound(MERGED, 1));
        assertNull(unbudgeted.encodeScripts().witness());
        // Without match transitions neither condition applies: a quiescence property is searched.
        assertNotNull(fixture("envBoundedPair", SmtProperty.deadlockFree()).encodeScripts().witness());
    }

    /** The name-coloured encoding is exact: a name-blind run must not pre-empt it. */
    @Test
    void theNameColouredEncodingNeverEntersThePhase() {
        var named = VerificationNets.build("nuScatterGather");
        var budget = p("nuScatterGather", "budget");
        var verifier = SmtVerifier.forNet(named.net())
            .initialMarking(named.initialMarking())
            .budgetPlaces(budget)
            // A bound the net exceeds, so a run exists for the phase to find if it were asked.
            .property(SmtProperty.placeBound(budget, 1))
            .timeout(Duration.ofSeconds(60));
        var scripts = verifier.encodeScripts();
        assertTrue(scripts.coloured());
        assertNull(scripts.witness());
        var r = verifier.verify();
        assertInstanceOf(SmtVerificationResult.Verdict.Violated.class, r.verdict(), r.report());
        assertTrue(r.report().contains("ν-encoding: name-coloured"), r.report());
        assertFalse(r.report().contains("Bounded witness phase"), r.report());
    }
}
