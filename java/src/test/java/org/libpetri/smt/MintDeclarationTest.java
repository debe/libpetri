package org.libpetri.smt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.opennet.OpenNetContract;
import org.libpetri.smt.opennet.OpenNetOptions;
import org.libpetri.smt.opennet.OpenNetVerifier;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The &nu; mint declaration ([NU-010]) and the carrier declaration ([NU-051]) at every entry
 * point: a mint name that is not a transition of the net is rejected where it is declared, with
 * the reason every implementation gives, and so before either route of {@code verifyOpenNet}
 * runs; a Route B decline caused by an undeclared mint names the transition and the
 * declaration; and the open-net route splits its closed net with the carrier places a
 * {@code configureSmt} hook declares, as {@link SmtVerifier} does. Mirrors
 * {@code rust/libpetri-verification/tests/mint_declarations.rs}.
 */
class MintDeclarationTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final Place<Object> SOURCE = Place.of("source", Object.class);
    private static final Place<String> BRANCH_A = Place.of("branchA", String.class);
    private static final Place<String> BRANCH_B = Place.of("branchB", String.class);
    private static final Place<String> MERGED = Place.of("merged", String.class);

    private static final String TYPO = "declared mint transition 'frok' not in the net (NU-010)";

    /** {@code fork: source -> branchA, branchB} and {@code join} joining the two by name into {@code merged}. */
    private static PetriNet forkJoin() {
        return StructureOnly.bind(PetriNet.builder("fork-join").transitions(
            Transition.builder("fork").inputs(In.one(SOURCE))
                .outputs(Out.and(Out.place(BRANCH_A), Out.place(BRANCH_B))).build(),
            Transition.builder("join").inputs(In.one(BRANCH_A), In.one(BRANCH_B))
                .match(MatchSpec.builder().key(BRANCH_A, NameId::of).key(BRANCH_B, NameId::of).build())
                .outputs(Out.place(MERGED)).build()).build());
    }

    private static SmtVerifier verifier(PetriNet net) {
        return SmtVerifier.forNet(net)
            .initialMarking(MarkingState.builder().tokens(SOURCE, 1).build())
            .property(SmtProperty.deadlockFree())
            .sinkPlaces(MERGED)
            .timeout(Duration.ofSeconds(30));
    }

    /** The declaration throws with the reason Rust's verify() answers Unknown with; verify() and encodeScripts() never see it. */
    @Test
    void aMintNameNotInTheNetIsRejectedWhereItIsDeclared() {
        var e = assertThrows(IllegalArgumentException.class, () -> verifier(forkJoin()).mintTransitions("frok"));
        assertEquals(TYPO, e.getMessage());
        var two = assertThrows(IllegalArgumentException.class,
            () -> verifier(forkJoin()).mintTransitions("zz", "frok", "fork", "frok"));
        assertEquals("declared mint transitions 'frok', 'zz' not in the net (NU-010)", two.getMessage());
    }

    /**
     * {@code verifyOpenNet} used to answer per route: the graph route decided without ever applying
     * the hook, so a typo'd declaration went unnoticed. The hook now runs on a probe verifier
     * before either route, and the declaration is rejected there.
     */
    @Test
    void verifyOpenNetRejectsAMintNameNotInTheNetBeforeEitherRoute() {
        var a = Place.of("a", Object.class);
        var b = Place.of("b", Object.class);
        var net = StructureOnly.bind(PetriNet.builder("plain").transitions(
            Transition.builder("t").inputs(In.one(a)).outputs(Out.place(b)).build()).build());
        var contract = OpenNetContract.builder().initialMarking(m -> m.tokens(a, 1)).rest(b).build();
        var decided = OpenNetVerifier.verifyOpenNet(net, contract, OpenNetOptions.DEFAULT);
        assertTrue(decided.isProven(), decided.report());
        var e = assertThrows(IllegalArgumentException.class, () -> OpenNetVerifier.verifyOpenNet(net, contract,
            OpenNetOptions.DEFAULT.withConfigureSmt(v -> v.mintTransitions("frok"))));
        assertEquals(TYPO, e.getMessage());
    }

    /** Route B declines a net whose only obstacle is an undeclared mint, and says which transition to declare with what. */
    @Test
    @EnabledIf("z3Available")
    void aRouteBDeclineForAnUndeclaredMintPointsAtMintTransitions() {
        String pointer = "'fork' writes a coloured place without consuming one and is not declared to mint "
            + "(NU-010); if the action writes a name minted with freshName(), declare it with mintTransitions";
        var result = verifier(forkJoin()).verify();
        assertTrue(result.report().contains("ν-net Route B declined: " + pointer + "."), result.report());
        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(), result.report());
        assertTrue(unknown.reason().endsWith("; " + pointer), unknown.reason());
        var declared = verifier(forkJoin()).mintTransitions("fork").verify();
        assertTrue(declared.isProven(), declared.report());
        assertFalse(declared.report().contains("Route B declined"), declared.report());
    }

    /**
     * {@code t: a -> and(c, d)} writes the carrier {@code c}, and {@code u} tests {@code d} with an
     * inhibitor, so the split needs {@code t} and cannot express it ([VER-004]). The open-net route
     * used to split it anyway, blind to the carrier its hook declares; {@link SmtVerifier} refuses it.
     */
    @Test
    void verifyOpenNetSplitsWithTheCarriersItsHookDeclares() {
        var a = Place.of("a", Object.class);
        var c = Place.of("c", String.class);
        var d = Place.of("d", Object.class);
        var q = Place.of("q", Object.class);
        var r = Place.of("r", Object.class);
        var net = StructureOnly.bind(PetriNet.builder("carrier-split").transitions(
            Transition.builder("t").inputs(In.one(a)).outputs(Out.and(Out.place(c), Out.place(d))).build(),
            Transition.builder("u").inputs(In.one(q)).inhibitors(d).outputs(Out.place(r)).build()).build());
        String refusal = "it writes the coloured place 'c', whose tokens carry a ν name";

        var direct = SmtVerifier.forNet(net)
            .initialMarking(MarkingState.builder().tokens(a, 1).tokens(q, 1).build())
            .property(SmtProperty.placeBound(r, 1))
            .carrierPlaces(c)
            .verify();
        var directUnknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, direct.verdict(), direct.report());
        assertTrue(directUnknown.reason().contains(refusal), directUnknown.reason());

        var contract = OpenNetContract.builder().initialMarking(m -> m.tokens(a, 1).tokens(q, 1)).rest(c, d, r).build();
        var result = OpenNetVerifier.verifyOpenNet(net, contract,
            OpenNetOptions.DEFAULT.withConfigureSmt(v -> v.carrierPlaces(c)));
        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, result.verdict(), result.report());
        assertTrue(unknown.reason().contains(refusal), unknown.reason());
    }

    /**
     * {@code buildPlan} solves the colour-slot program only after every structural refusal, and
     * writes its report line right after the re-check. With {@code copy: extra -> branchA}
     * writing a coloured place as an undeclared mint, the classification refuses the plan, so the
     * simplex never runs and the line never appears. Without {@code copy} the plan is built and
     * the line is there, which is what makes its absence mean something. Neither run enumerates a
     * semiflow: the slot bound is not a semiflow search.
     */
    @Test
    @EnabledIf("z3Available")
    void anUndeclaredMintRefusesTheColouredPlanBeforeTheSlotBoundIsSolved() {
        final String slotBound = "Colour-slot bound: ";
        var extra = Place.of("extra", Object.class);
        java.util.function.Function<PetriNet, SmtVerificationResult> run = net -> SmtVerifier.forNet(net)
            .initialMarking(MarkingState.builder().tokens(SOURCE, 1).tokens(extra, 1).build())
            .property(SmtProperty.placeBound(MERGED, 5))
            .budgetPlaces(SOURCE)
            .linearBound(false)
            .enumerationMaxClasses(0)
            .timeout(Duration.ofSeconds(30))
            .verify();

        var declared = run.apply(forkJoin());
        assertTrue(declared.report().contains("ν-encoding: name-coloured (colour-slot bound k=2;"), declared.report());
        // `source` weighs at least both keys: optimum 2 over source, branchA and branchB, and the
        // fork, the one row producing into them.
        assertTrue(declared.report().contains("  Colour-slot bound: LP optimum 2 over 3 places and 1 transitions, "
            + "so k=2 (re-checked in exact arithmetic)\n"), declared.report());
        assertEquals(1, declared.report().split(slotBound, -1).length - 1, declared.report());

        var copy = Transition.builder("copy").inputs(In.one(extra)).outputs(Out.place(BRANCH_A)).build();
        var net = StructureOnly.bind(PetriNet.builder("fork-join-copy")
            .transitions(forkJoin().transitions().toArray(Transition[]::new))
            .transition(copy).build());
        var undeclared = run.apply(net);
        assertFalse(undeclared.report().contains("ν-encoding: name-coloured"), undeclared.report());
        assertFalse(undeclared.report().contains(slotBound), undeclared.report());
        for (var report : java.util.List.of(declared.report(), undeclared.report())) {
            assertFalse(report.contains("semiflow"), report);
        }
    }
}
