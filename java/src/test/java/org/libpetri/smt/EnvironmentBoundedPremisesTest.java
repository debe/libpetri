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

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [VER-006] AC3: the {@code bounded(k)} premises. Every route models a bounded environment place
 * as a source holding at most k: the flat encoding caps each successor there at k, the state-class
 * graphs enable an environment input exactly when it demands at most k, and the quiescence clause
 * calls a demand above k permanently disabled. That is the executor only when no transition
 * deposits into an environment place and the initial marking holds at most k on each one. Outside
 * those premises the verifier answers Unknown, naming the place, on every route.
 */
@EnabledIf("z3Available")
class EnvironmentBoundedPremisesTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final Place<Object> A = Place.of("a", Object.class);
    private static final Place<Object> B = Place.of("b", Object.class);
    private static final Place<Object> C = Place.of("c", Object.class);
    private static final Place<Object> D = Place.of("d", Object.class);
    private static final Place<Object> E = Place.of("E", Object.class);
    private static final Place<Object> OUT = Place.of("out", Object.class);
    private static final Place<Object> SOURCE = Place.of("source", Object.class);
    private static final Place<String> BRANCH_A = Place.of("branchA", String.class);
    private static final Place<String> BRANCH_B = Place.of("branchB", String.class);
    private static final Place<String> MERGED = Place.of("merged", String.class);

    private static Transition arc(String name, In in, Place<?> to) {
        return Transition.builder(name).inputs(in).outputs(Out.place(to)).build();
    }

    /** A same-mint ν-join beside the net, so the query runs on Route B. */
    private static List<Transition> join() {
        var match = MatchSpec.builder()
            .key(BRANCH_A, (String v) -> NameId.of(v))
            .key(BRANCH_B, (String v) -> NameId.of(v))
            .build();
        return List.of(
            Transition.builder("fork").inputs(In.one(SOURCE))
                .outputs(Out.and(Out.place(BRANCH_A), Out.place(BRANCH_B))).build(),
            Transition.builder("join").inputs(In.one(BRANCH_A), In.one(BRANCH_B)).match(match)
                .outputs(Out.place(MERGED)).build());
    }

    private static PetriNet net(String name, boolean withJoin, Transition... transitions) {
        var builder = PetriNet.builder(name).transitions(transitions);
        if (withJoin) {
            join().forEach(builder::transition);
        }
        return StructureOnly.bind(builder.build());
    }

    private static SmtVerificationResult verify(
            PetriNet net, MarkingState m0, SmtProperty property, int budget) {
        var verifier = SmtVerifier.forNet(net)
            .initialMarking(m0)
            .environmentPlaces(EnvironmentPlace.of(E))
            .environmentMode(EnvironmentAnalysisMode.bounded(1))
            .property(property)
            .enumerationMaxClasses(budget)
            .timeout(Duration.ofSeconds(15));
        if (net.transitions().stream().anyMatch(t -> t.name().equals("fork"))) {
            verifier.mintTransitions("fork");
        }
        return verifier.verify();
    }

    private static void assertRefused(SmtVerificationResult r, String cause) {
        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, r.verdict(), r.report());
        assertTrue(unknown.reason().startsWith(
            "environment place 'E' is outside the Bounded(1) premises (VER-006 AC3): " + cause + ". "),
            unknown.reason());
    }

    /** (A) M0(E) = 2 > k = 1: the post-cap froze every transition, so b looked unreachable. */
    @Test
    void anInitialMarkingAboveKIsRefused() {
        var net = net("capA", false,
            arc("t", In.one(A), B),
            Transition.builder("u").inputs(In.one(E), In.one(D)).outputs(Out.place(C)).build());
        var m0 = MarkingState.builder().tokens(A, 1).tokens(E, 2).build();
        for (int budget : new int[] {0, 50_000}) {
            assertRefused(verify(net, m0, SmtProperty.placeBound(B, 0), budget),
                "the initial marking holds 2 tokens there, more than 1");
        }
    }

    /** (B) t deposits into E: the executor marks E with 2, the cap kept it at 1. */
    @Test
    void aDepositIntoAnEnvironmentPlaceIsRefused() {
        var net = net("capB", false, arc("t", In.one(A), E));
        var m0 = MarkingState.builder().tokens(A, 2).build();
        assertRefused(verify(net, m0, SmtProperty.placeBound(E, 1), 50_000),
            "transition 't' deposits into it");
    }

    /** exactly(2, E) is met by two deposits; the graphs read it as never enabled. */
    @Test
    void aDemandAboveKMetByADepositIsRefusedOnEveryRoute() {
        var m0 = MarkingState.builder().tokens(A, 2).tokens(SOURCE, 1).build();
        for (boolean withJoin : new boolean[] {true, false}) {
            var net = net("supplied", withJoin, arc("t0", In.one(A), E), arc("t1", In.exactly(2, E), OUT));
            assertRefused(verify(net, m0, SmtProperty.placeBound(OUT, 0), 50_000),
                "transition 't0' deposits into it");
        }
    }

    /** The quiescence clause read tQ1 as permanently disabled: a spurious deadlock at M0. */
    @Test
    void aSpuriousDeadlockFromAnInitialMarkingAboveKIsRefused() {
        var m0 = MarkingState.builder().tokens(E, 2).build();
        for (boolean withJoin : new boolean[] {true, false}) {
            var net = net("quiescent", withJoin, arc("tQ1", In.exactly(2, E), OUT), arc("tQ2", In.one(OUT), OUT));
            assertRefused(verify(net, m0, SmtProperty.deadlockFree(), 50_000),
                "the initial marking holds 2 tokens there, more than 1");
        }
    }

    /** Within the premises the verdict stands. */
    @Test
    void withinThePremisesTheVerdictStands() {
        var net = net("within", false, arc("t", In.one(A), B), arc("u", In.one(E), OUT));
        var m0 = MarkingState.builder().tokens(A, 1).tokens(E, 1).build();
        var violated = verify(net, m0, SmtProperty.placeBound(B, 0), 0);
        assertTrue(violated.isViolated(), violated.report());
        var proven = verify(net, m0, SmtProperty.placeBound(B, 1), 0);
        assertTrue(proven.isProven(), proven.report());
        assertNotEquals(SmtVerificationResult.Route.UNAVAILABLE, proven.route(), proven.report());
    }

    /**
     * A split transition deposits through its completion step ([VER-004]). The premise names the
     * transition, not {@code complete:t}.
     */
    @Test
    void aDepositByASplitTransitionIsRefusedNamingIt() {
        var q = Place.of("q", Object.class);
        var r = Place.of("r", Object.class);
        var net = net("capSplit", false,
            arc("t", In.one(A), E),
            Transition.builder("u").inputs(In.one(q)).inhibitors(E).outputs(Out.place(r)).build());
        var m0 = MarkingState.builder().tokens(A, 1).tokens(q, 1).build();
        for (int budget : new int[] {0, 50_000}) {
            var result = verify(net, m0, SmtProperty.placeBound(E, 1), budget);
            assertRefused(result, "transition 't' deposits into it");
            assertTrue(!result.report().contains("'complete:"), result.report());
        }
    }
}
