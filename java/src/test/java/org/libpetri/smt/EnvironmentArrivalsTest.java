package org.libpetri.smt;

import java.time.Duration;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.StateClassGraph;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [VER-006] {@code arrivals(k)}: at most {@code k} tokens injected into each environment place in
 * total, by a net rewrite that reuses the [VER-022] closure (AC9), and the ν routes' refusal to
 * read an arrival into a coloured place as a mint (AC10).
 */
class EnvironmentArrivalsTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final Place<Object> IN = Place.of("IN", Object.class);
    private static final Place<Object> OUT = Place.of("OUT", Object.class);

    /** {@code env IN -> T -> OUT}. */
    private static SmtVerifier forward(EnvironmentAnalysisMode mode, SmtProperty property) {
        var net = StructureOnly.bind(PetriNet.builder("forward")
            .transition(Transition.builder("T").inputs(In.one(IN)).outputs(Out.place(OUT)).build())
            .build());
        return SmtVerifier.forNet(net)
            .environmentPlaces(EnvironmentPlace.of(IN))
            .environmentMode(mode)
            .property(property)
            .timeout(Duration.ofSeconds(15));
    }

    @Test
    void arrivalsBoundsTheTotal_placeBoundAtKIsProven_atKMinusOneViolatedWithKArrivals() {
        int k = 2;
        var proven = forward(EnvironmentAnalysisMode.arrivals(k), SmtProperty.placeBound(OUT, k)).verify();
        assertTrue(proven.isProven(), proven.report());
        assertTrue(proven.report().contains("Environment: arrivals(2) — net closed before any route: "
            + "env:arrive?[0]:IN from env:optional[0] (at most 2) (VER-006)"), proven.report());

        var violated = forward(EnvironmentAnalysisMode.arrivals(k), SmtProperty.placeBound(OUT, k - 1)).verify();
        assertTrue(violated.isViolated(), violated.report());
        var trace = violated.counterexampleTransitions();
        assertEquals(k, Collections.frequency(trace, "env:arrive?[0]:IN"), trace.toString());
        assertEquals(k, Collections.frequency(trace, "T"), trace.toString());
        assertEquals(2 * k, trace.size(), trace.toString());
    }

    @Test
    @EnabledIf("z3Available")
    void boundedIsResident_bothBoundsAreViolated() {
        int k = 2;
        for (int bound : new int[] {k, k - 1}) {
            var r = forward(EnvironmentAnalysisMode.bounded(k), SmtProperty.placeBound(OUT, bound)).verify();
            assertTrue(r.isViolated(), "bounded(2), placeBound(OUT, " + bound + "):\n" + r.report());
        }
    }

    @Test
    void deadlockFreeWithASink_isDecidedWithoutTheVacuityNote() {
        var r = forward(EnvironmentAnalysisMode.arrivals(3), SmtProperty.deadlockFree())
            .sinkPlaces(OUT)
            .verify();
        assertTrue(r.isProven(), r.report());
        assertFalse(r.report().contains(SmtVerifier.QUIESCENCE_VACUITY_NOTE), r.report());

        var stranded = forward(EnvironmentAnalysisMode.arrivals(3), SmtProperty.deadlockFree()).verify();
        assertTrue(stranded.isViolated(), "OUT is not a sink, so the tokens rest there:\n" + stranded.report());
    }

    @Test
    void arrivalsIsAtMost_forQuiescenceToo_aRunMayDeclineEveryArrival() {
        // Exactly k arrivals would put a token on OUT in every quiescent marking; at most k lets a
        // run decline them all and rest with no sink marked.
        var r = forward(EnvironmentAnalysisMode.arrivals(2), SmtProperty.terminatesAtSink())
            .sinkPlaces(OUT)
            .verify();
        assertTrue(r.isViolated(), r.report());
        assertEquals(List.of("env:decline[0]", "env:decline[0]"), r.counterexampleTransitions());
    }

    @Test
    void arrivalsIsAtMost_aQuiescentCountOfExactlyKIsViolatedByADecline() {
        var r = forward(EnvironmentAnalysisMode.arrivals(2),
                SmtProperty.quiescentCount(List.of(OUT), 2, java.util.OptionalInt.of(2)))
            .verify();
        assertTrue(r.isViolated(), r.report());
        assertTrue(r.counterexampleTransitions().contains("env:decline[0]"), r.counterexampleTransitions().toString());
    }

    @Test
    void arrivalsExact_aQuiescentCountOfExactlyKIsProven() {
        var r = forward(EnvironmentAnalysisMode.arrivals(2, 2),
                SmtProperty.quiescentCount(List.of(OUT), 2, java.util.OptionalInt.of(2)))
            .sinkPlaces(OUT)
            .verify();
        assertTrue(r.isProven(), r.report());
        assertTrue(r.report().contains("Environment: arrivals(2..2) — net closed before any route: "
            + "env:arrive[0]:IN from env:arrivals[0] (exactly 2) (VER-006)"), r.report());
    }

    @Test
    void arrivalsBetween_reportsBothSources_andTheMandatoryPartCannotBeDeclined() {
        var r = forward(EnvironmentAnalysisMode.arrivals(1, 3),
                SmtProperty.quiescentCount(List.of(OUT), 1, java.util.OptionalInt.of(3)))
            .sinkPlaces(OUT)
            .verify();
        assertTrue(r.isProven(), r.report());
        assertTrue(r.report().contains("Environment: arrivals(1..3) — net closed before any route: "
            + "env:arrive[0]:IN from env:arrivals[0] (exactly 1), "
            + "env:arrive?[0]:IN from env:optional[0] (at most 2) (VER-006)"), r.report());
    }

    @Test
    void arrivalsBounds_areValidated_andOneArgumentIsZeroToK() {
        assertThrows(IllegalArgumentException.class, () -> EnvironmentAnalysisMode.arrivals(-1, 2));
        assertThrows(IllegalArgumentException.class, () -> EnvironmentAnalysisMode.arrivals(3, 2));
        assertEquals(EnvironmentAnalysisMode.arrivals(0, 2), EnvironmentAnalysisMode.arrivals(2));
    }

    @Test
    void arrivalsZero_injectsNothing() {
        var r = forward(EnvironmentAnalysisMode.arrivals(0), SmtProperty.unreachable(Set.of(OUT))).verify();
        assertTrue(r.isProven(), r.report());
        assertTrue(r.report().contains("Environment: arrivals(0) — nothing is injected"), r.report());
    }

    @Test
    void theGraphBuilderRefusesArrivalsOnANetThatStillHasEnvironmentPlaces() {
        var net = PetriNet.builder("forward")
            .transition(Transition.builder("T").inputs(In.one(IN)).outputs(Out.place(OUT)).build())
            .build();
        var error = assertThrows(IllegalArgumentException.class, () -> StateClassGraph.build(
            net, MarkingState.empty(), 100, Set.of(EnvironmentPlace.of(IN)),
            EnvironmentAnalysisMode.arrivals(1)));
        assertTrue(error.getMessage().contains("net rewrite applied by SmtVerifier"), error.getMessage());
    }

    // ---- AC10: an arrival into a coloured place is not a mint ----------------------------------

    private static final Place<String> SLOT = Place.of("slot", String.class);
    private static final Place<String> A = Place.of("A", String.class);
    private static final Place<String> KEY_IN = Place.of("IN", String.class);
    private static final Place<String> ACCEPTED = Place.of("accepted", String.class);

    /** {@code fork: slot -> A} (a mint), {@code join: A, IN (matched) -> accepted}, IN an environment place. */
    private static SmtVerifier colouredEnvironment(SmtProperty property) {
        var match = MatchSpec.builder()
            .key(A, (String v) -> NameId.of(v))
            .key(KEY_IN, (String v) -> NameId.of(v))
            .build();
        var net = StructureOnly.bind(PetriNet.builder("coloured-arrivals").transitions(
            Transition.builder("fork").inputs(In.one(SLOT)).outputs(Out.place(A)).build(),
            Transition.builder("join").inputs(In.one(A), In.one(KEY_IN)).match(match)
                .outputs(Out.place(ACCEPTED)).build()).build());
        return SmtVerifier.forNet(net)
            .environmentPlaces(EnvironmentPlace.of(KEY_IN))
            .environmentMode(EnvironmentAnalysisMode.arrivals(2))
            .initialMarking(m -> m.tokens(SLOT, 1))
            .property(property)
            .timeout(Duration.ofSeconds(15));
    }

    @Test
    void anArrivalIntoAColouredPlace_routeBDeclinesNamingThePlace() {
        // Read as a mint, the arrival carries a fresh name, the join never matches, and
        // unreachable(accepted) would be Proven — although an arrival may carry the forked name.
        var r = colouredEnvironment(SmtProperty.unreachable(Set.of(ACCEPTED))).verify();
        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, r.verdict(), r.report());
        assertEquals(SmtVerificationResult.Route.NU_SCG, r.route(), r.report());
        assertEquals("environment place 'IN' carries ν-names (a match key or carrier place) and is fed by "
            + "arrivals(k): an injected token's name is unknown, so an arrival is not a fresh mint; refusing to "
            + "decide it by name (VER-006)", unknown.reason());
    }

    @Test
    void anArrivalIntoAColouredPlace_quiescenceDeclinesToo() {
        var r = colouredEnvironment(SmtProperty.deadlockFree()).verify();
        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, r.verdict(), r.report());
        assertTrue(unknown.reason().startsWith("environment place 'IN' carries ν-names"), unknown.reason());
        assertEquals(List.of(), r.counterexampleTransitions());
    }

    @Test
    @EnabledIf("z3Available")
    void anArrivalIntoAColouredPlace_routeADeclinesToTheFlatEncoding_namingThePlace() {
        // Budgeted reachability-safety is Route A's (coloured IC3). Read as a mint, the arrival
        // would carry a fresh colour and the join would never match: an unsound Proven. The guard
        // refuses before the plan is built; the report line is what AC10 and AC7 require.
        var r = colouredEnvironment(SmtProperty.unreachable(Set.of(ACCEPTED)))
            .budgetPlaces(SLOT)
            .verify();
        assertFalse(r.isProven(), r.report());
        assertTrue(r.report().contains("  ν-encoding: name-blind over-approximation (environment place 'IN' carries "
            + "ν-names (a match key or carrier place) and is fed by arrivals(k)"), r.report());
    }

    /**
     * A verifier reused after a change of the environment mode redoes the arrivals closure from
     * the caller's net and marking, and scripts what a fresh verifier with that mode scripts. It
     * used to close the net once and keep that closure (or its absence) for good.
     */
    @Test
    void aReusedVerifierFollowsTheEnvironmentMode() {
        var property = SmtProperty.placeBound(OUT, 1);
        var modes = List.of(EnvironmentAnalysisMode.arrivals(2), EnvironmentAnalysisMode.alwaysAvailable(),
            EnvironmentAnalysisMode.arrivals(1), EnvironmentAnalysisMode.arrivals(1, 2),
            EnvironmentAnalysisMode.arrivals(2));
        var reused = forward(modes.getFirst(), property);
        for (var mode : modes) {
            assertEquals(forward(mode, property).encodeScripts(), reused.environmentMode(mode).encodeScripts(),
                mode.toString());
        }
    }
}
