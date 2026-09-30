package org.libpetri.smt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [IO-014]: a timeout {@code ForwardInput(from, to)} deposits one token in {@code to} per token
 * the firing consumed from {@code from}. On {@code t: exactly(2, a) -> xor(c, timeout(50,
 * forwardInput(a, b)))} from {@code a = 2} the executor ends at {@code b = 2}; every route used
 * to prove {@code placeBound(b, 1)} while the analyses deposited one token per forward.
 */
class ForwardDepositTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final Place<Object> A = Place.of("a", Object.class);
    private static final Place<Object> B = Place.of("b", Object.class);
    private static final Place<Object> C = Place.of("c", Object.class);

    private static PetriNet net(In input) {
        return StructureOnly.bind(PetriNet.builder("forward")
            .transition(Transition.builder("t")
                .inputs(input)
                .outputs(Out.xor(Out.place(C), Out.timeout(Duration.ofMillis(50), Out.forwardInput(A, B))))
                .build())
            .build());
    }

    private static SmtVerificationResult verify(In input, int budget, boolean linearBound) {
        return verify(input, budget, linearBound, true);
    }

    private static SmtVerificationResult verify(In input, int budget, boolean linearBound, boolean phases) {
        return SmtVerifier.forNet(net(input))
            .initialMarking(MarkingState.builder().tokens(A, 2).build())
            .property(SmtProperty.placeBound(B, 1))
            .enumerationMaxClasses(budget)
            .linearBound(linearBound)
            .stateEquationPhase(phases)
            .firingBound(phases)
            .verify();
    }

    /**
     * Each route finds the timeout outcome and a one-step trace to it: the linear bound
     * (budget 0), the state-equation phase ([VER-018], linear bound off), the CHC/IC3 fixpoint
     * alone (every phase off) and the enumeration ([VER-017]). Before the fix each proved it.
     */
    @Test
    @EnabledIf("z3Available")
    void aForwardOfTwoConsumedTokensViolatesABoundOfOneOnEveryRoute() {
        record Case(int budget, boolean linearBound, boolean phases, SmtVerificationResult.Route route) {}
        for (var c : new Case[] {
            new Case(0, true, true, SmtVerificationResult.Route.SMT),
            new Case(0, false, true, SmtVerificationResult.Route.SMT),
            new Case(0, false, false, SmtVerificationResult.Route.SMT),
            new Case(50_000, true, true, SmtVerificationResult.Route.ENUMERATION),
        }) {
            var r = verify(In.exactly(2, A), c.budget(), c.linearBound(), c.phases());
            var tag = "budget " + c.budget() + ", linear bound " + c.linearBound() + ", phases "
                + c.phases() + ":\n" + r.report();
            assertTrue(r.isViolated(), tag);
            assertEquals(c.route(), r.route(), tag);
            assertEquals(1, r.counterexampleTransitions().size(), tag);
            var last = r.counterexampleTrace().getLast();
            assertEquals(0, last.tokens(A), tag);
            assertEquals(2, last.tokens(B), tag);
        }
    }

    private static SmtVerificationResult verifyBound(In input, int bound, int budget) {
        return SmtVerifier.forNet(net(input))
            .initialMarking(MarkingState.builder().tokens(A, 2).build())
            .property(SmtProperty.placeBound(B, bound))
            .enumerationMaxClasses(budget)
            .verify();
    }

    /**
     * The deposit of a drained batch is marking-dependent: no flat encoding can hold it, so the
     * linear routes refuse the net ([VER-003] AC5), while the enumeration ([VER-017]) counts the
     * drained batch exactly as the executor does ([IO-014]) and decides it: {@code b} reaches 2
     * (the timeout forwards both drained tokens), never 3.
     */
    @Test
    void aForwardOfADrainedInputIsDecidedByTheGraphAndRefusedByTheLinearRoutes() {
        for (var input : new In[] {In.all(A), In.atLeast(1, A)}) {
            // Enumeration off: only the linear routes are left, and each refuses.
            var refused = verifyBound(input, 1, 0);
            var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, refused.verdict(), refused.report());
            assertTrue(unknown.reason().contains("forwards its All/AtLeast input 'a' to 'b'"), unknown.reason());
            assertTrue(unknown.reason().contains("refusing to certify on the linear routes"), unknown.reason());
            assertEquals(SmtVerificationResult.Route.UNAVAILABLE, refused.route());

            // The enumeration decides both directions.
            var violated = verifyBound(input, 1, 50_000);
            assertTrue(violated.isViolated(), violated.report());
            assertEquals(SmtVerificationResult.Route.ENUMERATION, violated.route());
            assertEquals(1, violated.counterexampleTransitions().size(), violated.report());
            var last = violated.counterexampleTrace().getLast();
            assertEquals(0, last.tokens(A), violated.report());
            assertEquals(2, last.tokens(B), violated.report());

            var proven = verifyBound(input, 2, 50_000);
            assertTrue(proven.isProven(), proven.report());
            assertEquals(SmtVerificationResult.Route.ENUMERATION, proven.route());
        }
    }
}
