package org.libpetri.smt;

import java.time.Duration;
import java.util.List;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [VER-017] "Verdicts from a truncated graph", for Route B ([VER-012] AC3), the enumeration route
 * ([VER-017] AC11, including a cached truncation, AC8) and the timed check ([VER-023] AC4): the
 * shared predicate reads the explored prefix — every stored class for a safety property, only
 * expanded classes without successors for a quiescence property — and a prefix never proves.
 */
class TruncatedPrefixTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final Place<String> CLERK = Place.of("clerk", String.class);
    private static final Place<String> ORDER = Place.of("order", String.class);
    private static final Place<String> ORDER_CLERK = Place.of("order_clerk", String.class);
    private static final Place<String> SEND_DONE = Place.of("send_done", String.class);

    /**
     * PNID Fig. 11(b) (research/net-metrics/validation/pnid, {@code res11b}): {@code create_order}
     * reads a clerk and mints an order onto {@code order} and {@code order_clerk};
     * {@code send_order} joins the two by name. Clerks are only read, so orders mint without
     * bound and the name-partition graph never closes.
     */
    static PetriNet fig11b() {
        var match = MatchSpec.builder()
            .key(ORDER, (String v) -> NameId.of(v))
            .key(ORDER_CLERK, (String v) -> NameId.of(v))
            .build();
        return StructureOnly.bind(PetriNet.builder("P-Fig11b-not-exclusive").transitions(
            Transition.builder("create_order").read(CLERK).outputs(Out.and(ORDER, ORDER_CLERK)).build(),
            Transition.builder("send_order").inputs(In.one(ORDER), In.one(ORDER_CLERK)).match(match)
                .outputs(Out.place(SEND_DONE)).build()).build());
    }

    static MarkingState twoClerks() {
        return MarkingState.builder().tokens(CLERK, 2).build();
    }

    @Test
    void routeB_fig11b_safetyViolatedBeforeTheCap_withTheDepthThreeTrace() {
        var r = SmtVerifier.forNet(fig11b()).initialMarking(twoClerks())
            .property(SmtProperty.placeBound(ORDER_CLERK, 2))
            .nuMaxClasses(50)
            .verify();
        assertTrue(r.isViolated(), r.report());
        assertEquals(SmtVerificationResult.Route.NU_SCG, r.route(), r.report());
        assertEquals(List.of("create_order", "create_order", "create_order"), r.counterexampleTransitions());
        assertEquals(3, r.counterexampleTrace().getLast().tokens(ORDER_CLERK));
        // The build stops at the first violating class ([VER-012]), long before the cap.
        assertTrue(r.report().contains("Note: Route B stopped at the first violating class after "), r.report());
    }

    @Test
    void routeB_fig11b_aBoundTheGraphNeverReaches_staysUnknown() {
        var r = SmtVerifier.forNet(fig11b()).initialMarking(twoClerks())
            .property(SmtProperty.placeBound(ORDER_CLERK, 1_000))
            .nuMaxClasses(50)
            .verify();
        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, r.verdict(), r.report());
        assertTrue(unknown.reason().startsWith("ν name-aware state-class graph truncated at 50 classes"),
            unknown.reason());
    }

    @Test
    void routeB_aFrontierClassIsNeverQuiescent() {
        // gen: G -> G, A, B mints forever; the only successor-free classes of the prefix are
        // unexpanded frontier classes, each still holding G — read as dead, they would "strand" it.
        var g = Place.of("G", String.class);
        var a = Place.of("A", String.class);
        var b = Place.of("B", String.class);
        var done = Place.of("DONE", String.class);
        var match = MatchSpec.builder().key(a, (String v) -> NameId.of(v)).key(b, (String v) -> NameId.of(v)).build();
        var net = StructureOnly.bind(PetriNet.builder("ever-minting").transitions(
            Transition.builder("gen").inputs(In.one(g)).outputs(Out.and(g, a, b)).build(),
            Transition.builder("join").inputs(In.one(a), In.one(b)).match(match).outputs(Out.place(done)).build())
            .build());
        var r = SmtVerifier.forNet(net).initialMarking(m -> m.tokens(g, 1))
            .property(SmtProperty.deadlockFree())
            .nuMaxClasses(50)
            .verify();
        assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, r.verdict(), r.report());
        assertEquals(SmtVerificationResult.Route.NU_SCG, r.route(), r.report());
    }

    private static final Place<Object> G = Place.of("G", Object.class);
    private static final Place<Object> A = Place.of("A", Object.class);

    /** {@code gen: G -> G, A}: an unbounded producer, one token on {@code G}. */
    private static PetriNet producer(Timing timing) {
        return StructureOnly.bind(PetriNet.builder("producer").transitions(
            Transition.builder("gen").inputs(In.one(G)).outputs(Out.and(G, A)).timing(timing).build()).build());
    }

    private static final PetriNet UNTIMED_PRODUCER = producer(Timing.immediate());

    private static SmtVerifier untimedProducer(SmtProperty property) {
        return SmtVerifier.forNet(UNTIMED_PRODUCER)
            .initialMarking(m -> m.tokens(G, 1))
            .property(property)
            .enumerationMaxClasses(50)
            .timeout(Duration.ofSeconds(15));
    }

    @Test
    void enumeration_truncatedPrefixViolatesASafetyProperty() {
        var r = untimedProducer(SmtProperty.placeBound(A, 2)).verify();
        assertTrue(r.isViolated(), r.report());
        assertEquals(SmtVerificationResult.Route.ENUMERATION, r.route(), r.report());
        assertEquals(List.of("gen", "gen", "gen"), r.counterexampleTransitions());
        assertEquals(Boolean.TRUE, r.counterexampleConfirmed());
        assertTrue(r.report().contains("Note: the state-class graph was truncated at 50 classes; "
            + "the violation was found in the explored prefix."), r.report());
    }

    @Test
    void enumeration_truncatedPrefixNeverReadsAFrontierClassAsDead_andFallsThrough() {
        var r = untimedProducer(SmtProperty.deadlockFree()).verify();
        assertTrue(r.report().contains(
            "Bounded state-space enumeration truncated at 50 classes (VER-017); verifying via the SMT pipeline."),
            r.report());
        assertFalse(r.isViolated(), r.report());
        assertTrue(r.route() != SmtVerificationResult.Route.ENUMERATION, r.report());
    }

    @Test
    void enumeration_aCachedTruncationIsReadAsAPrefix_withoutBuilding() {
        var cache = new StateSpaceCache();
        var first = untimedProducer(SmtProperty.placeBound(A, 1_000)).stateSpaceCache(cache).verify();
        assertTrue(first.report().contains("verifying via the SMT pipeline"), first.report());
        assertEquals(1, cache.buildsForTesting());

        var second = untimedProducer(SmtProperty.placeBound(A, 2)).stateSpaceCache(cache).verify();
        assertEquals(1, cache.buildsForTesting(), "the remembered truncation answers without a build");
        assertTrue(second.isViolated(), second.report());
        assertEquals(SmtVerificationResult.Route.ENUMERATION, second.route(), second.report());
        assertEquals(List.of("gen", "gen", "gen"), second.counterexampleTransitions());
        assertTrue(second.report().contains("Bounded state-space enumeration: cached truncation at 50 classes "
            + "(VER-017); its explored prefix (50 classes) was read."), second.report());
    }

    @Test
    @EnabledIf("z3Available")
    void timedCheck_aTruncatedTimedGraphWhosePrefixViolates_isTimedConfirmed() {
        var r = SmtVerifier.forNet(producer(Timing.delayed(Duration.ofMillis(1))))
            .initialMarking(m -> m.tokens(G, 1))
            .property(SmtProperty.placeBound(A, 2))
            .enumerationMaxClasses(50)
            .timedCounterexampleCheck(true)
            .timeout(Duration.ofSeconds(30))
            .verify();
        assertTrue(r.isViolated(), r.report());
        assertEquals(SmtVerificationResult.CounterexampleTiming.TIMED_CONFIRMED, r.counterexampleTiming(), r.report());
        assertEquals(List.of("gen", "gen", "gen"), r.counterexampleTransitions());
        assertTrue(r.report().contains("  CONFIRMED: the timed state-class graph, truncated at 50 classes "
            + "(enumerationMaxClasses), reaches a violating class in its explored prefix."), r.report());
    }
}
