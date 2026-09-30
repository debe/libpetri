package org.libpetri.smt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The &nu; mint and relay contracts (NU-010, NU-051) on both &nu; routes of NU-050. Each net has a
 * run the executor takes and the routes used to rule out, because they read a coloured write as
 * a fresh name when it was not one. The Rust twin, {@code rust/libpetri/tests/nu_mint_contract.rs},
 * runs the executor to that run.
 */
class NuMintContractTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static Place<String> p(String name) {
        return Place.of(name, String.class);
    }

    private static Transition join(String name, Place<String> a, Place<String> b, Place<String> out) {
        return Transition.builder(name).inputs(In.one(a), In.one(b))
            .match(MatchSpec.builder().key(a, (String s) -> NameId.of(s)).key(b, (String s) -> NameId.of(s)).build())
            .outputs(Out.place(out)).build();
    }

    private static void notProven(SmtVerificationResult r, String what) {
        assertFalse(r.isProven(), what + ": the executor reaches the bad marking\n" + r.report());
    }

    // ---- copying producers (NU-010) -----------------------------------------------------------

    /** {@code mA: S1 -> A}, {@code mB: S2 -> B} (the built-in fork copies), {@code J: A, B -> DONE}. */
    private static PetriNet copyingMints() {
        return StructureOnly.bind(PetriNet.builder("copying_mints").transitions(
            Transition.builder("mA").inputs(In.one(p("S1"))).outputs(Out.place(p("A"))).build(),
            Transition.builder("mB").inputs(In.one(p("S2"))).outputs(Out.place(p("B"))).build(),
            join("J", p("A"), p("B"), p("DONE"))).build());
    }

    @Test
    void aCopyingProducerIsNotReadAsAMintUnlessDeclared() {
        var net = copyingMints();
        var r = SmtVerifier.forNet(net)
            .initialMarking(m -> m.tokens(p("S1"), 1).tokens(p("S2"), 1))
            .property(SmtProperty.placeBound(p("DONE"), 0))
            .verify();
        notProven(r, "undeclared copying producers");
        assertNotEquals(SmtVerificationResult.Route.NU_SCG, r.route(), r.report());

        var declared = SmtVerifier.forNet(net)
            .initialMarking(m -> m.tokens(p("S1"), 1).tokens(p("S2"), 1))
            .property(SmtProperty.placeBound(p("DONE"), 0))
            .mintTransitions("mA", "mB")
            .verify();
        assertTrue(declared.isProven(), declared.report());
        assertEquals(SmtVerificationResult.Route.NU_SCG, declared.route());
        assertTrue(declared.report().contains(
            "Mint contract (NU-010) assumed for mA, mB: each writes a freshly minted name into every "
                + "coloured place it writes."), declared.report());
    }

    @Test
    void aDeclaredMintThatIsNotInTheNetIsRejected() {
        var e = assertThrows(IllegalArgumentException.class,
            () -> SmtVerifier.forNet(copyingMints()).mintTransitions("mA", "mC"));
        assertEquals("declared mint transition 'mC' not in the net (NU-010)", e.getMessage());
    }

    // ---- timeout forwards (IO-014) ------------------------------------------------------------

    /**
     * {@code t1: budget, reqA -> xor(okA, timeout(20, forward(reqA, a)))}, its twin {@code t2}
     * into {@code b}, {@code join: a, b -> done}. Both timeouts forward the request token itself.
     */
    private static PetriNet forwardMints() {
        var budget = p("budget");
        return StructureOnly.bind(PetriNet.builder("forward_mints").transitions(
            Transition.builder("t1").inputs(In.one(budget), In.one(p("reqA")))
                .outputs(Out.xor(Out.place(p("okA")),
                    Out.timeout(Duration.ofMillis(20), Out.forwardInput(p("reqA"), p("a"))))).build(),
            Transition.builder("t2").inputs(In.one(budget), In.one(p("reqB")))
                .outputs(Out.xor(Out.place(p("okB")),
                    Out.timeout(Duration.ofMillis(20), Out.forwardInput(p("reqB"), p("b"))))).build(),
            join("join", p("a"), p("b"), p("done"))).build());
    }

    @Test
    void aTimeoutForwardIntoAMatchKeyIsNeverAMint_routeB() {
        var r = SmtVerifier.forNet(forwardMints())
            .initialMarking(m -> m.tokens(p("budget"), 2).tokens(p("reqA"), 1).tokens(p("reqB"), 1))
            .property(SmtProperty.placeBound(p("done"), 0))
            .mintTransitions("t1", "t2")
            .verify();
        notProven(r, "Route B");
        assertNotEquals(SmtVerificationResult.Route.NU_SCG, r.route(), r.report());
    }

    @Test
    @EnabledIf("z3Available")
    void aTimeoutForwardIntoAMatchKeyIsNeverAMint_routeA() {
        var r = SmtVerifier.forNet(forwardMints())
            .initialMarking(m -> m.tokens(p("budget"), 2).tokens(p("reqA"), 1).tokens(p("reqB"), 1))
            .property(SmtProperty.placeBound(p("done"), 0))
            .budgetPlaces(p("budget"))
            .verify();
        notProven(r, "Route A");
        assertFalse(r.report().contains("ν-encoding: name-coloured"), r.report());
    }

    // ---- EXTENDED coloured consumers (NU-051) -------------------------------------------------

    /**
     * {@code m1: budget -> A1}, {@code m2: budget -> A2} mint (carriers {@code A1}, {@code A2});
     * {@code r1: A1, reqA -> xor(okA, timeout(20, forward(reqA, KA)))} and its twin {@code r2} into
     * {@code KB} forward the request, not the name they consumed; {@code join: KA, KB -> done}.
     */
    private static PetriNet forwardingConsumers() {
        var budget = p("budget");
        return StructureOnly.bind(PetriNet.builder("forwarding_consumers").transitions(
            Transition.builder("m1").inputs(In.one(budget)).outputs(Out.place(p("A1"))).build(),
            Transition.builder("m2").inputs(In.one(budget)).outputs(Out.place(p("A2"))).build(),
            Transition.builder("r1").inputs(In.one(p("A1")), In.one(p("reqA")))
                .outputs(Out.xor(Out.place(p("okA")),
                    Out.timeout(Duration.ofMillis(20), Out.forwardInput(p("reqA"), p("KA"))))).build(),
            Transition.builder("r2").inputs(In.one(p("A2")), In.one(p("reqB")))
                .outputs(Out.xor(Out.place(p("okB")),
                    Out.timeout(Duration.ofMillis(20), Out.forwardInput(p("reqB"), p("KB"))))).build(),
            join("join", p("KA"), p("KB"), p("done"))).build());
    }

    private static SmtVerifier consumerVerifier() {
        return SmtVerifier.forNet(forwardingConsumers())
            .initialMarking(m -> m.tokens(p("budget"), 2).tokens(p("reqA"), 1).tokens(p("reqB"), 1))
            .property(SmtProperty.placeBound(p("done"), 0))
            .fragmentMode(FragmentMode.EXTENDED)
            .carrierPlaces(p("A1"), p("A2"));
    }

    @Test
    void aConsumerTimeoutForwardingAnotherInputIsNotARelay_routeB() {
        var r = consumerVerifier().mintTransitions("m1", "m2").verify();
        notProven(r, "Route B");
        assertNotEquals(SmtVerificationResult.Route.NU_SCG, r.route(), r.report());
    }

    @Test
    @EnabledIf("z3Available")
    void aConsumerTimeoutForwardingAnotherInputIsNotARelay_routeA() {
        var r = consumerVerifier().budgetPlaces(p("budget")).verify();
        notProven(r, "Route A");
        assertFalse(r.report().contains("ν-encoding: name-coloured"), r.report());
    }

    // ---- a consumer relaying into its own input (Route A) --------------------------------------

    /**
     * {@code mint: budget -> a, b} (one fresh name in both); {@code spin: a, tick -> a, tock}
     * relays it back into {@code a}; {@code join: a, b -> done}. {@code spin} can fire.
     */
    @Test
    @EnabledIf("z3Available")
    void aConsumerRelayingIntoItsOwnInputKeepsTheColourThere() {
        var net = StructureOnly.bind(PetriNet.builder("self_loop").transitions(
            Transition.builder("mint").inputs(In.one(p("budget"))).outputs(Out.and(p("a"), p("b"))).build(),
            Transition.builder("spin").inputs(In.one(p("a")), In.one(p("tick"))).outputs(Out.and(p("a"), p("tock"))).build(),
            join("join", p("a"), p("b"), p("done"))).build());
        var r = SmtVerifier.forNet(net)
            .initialMarking(m -> m.tokens(p("budget"), 1).tokens(p("tick"), 1))
            .property(SmtProperty.placeBound(p("tock"), 0))
            .budgetPlaces(p("budget"))
            .fragmentMode(FragmentMode.EXTENDED)
            .verify();
        assertTrue(r.report().contains("ν-encoding: name-coloured"), r.report());
        assertTrue(r.isViolated(), r.report());
        assertTrue(r.report().contains(
            "Relay contract (NU-051) assumed for spin: each writes the name it consumed into every "
                + "coloured place it writes."), r.report());
    }
}
