package org.libpetri.smt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * VER-007 — {@link SmtVerifier#semiflowInvariants(boolean)}: the validated P-semiflows
 * reach the encoder as extra invariants, and only when asked for.
 *
 * <p>The net is a budgeted work loop with one reset arc on a side place — the shape that
 * makes the null-space basis fold the reset place into the loop's conservation law and lose
 * it. The semiflow enumeration still finds {@code Budget + Work + Done = 1} with zero weight
 * on the reset place.
 */
class SemiflowInvariantsTest {

    static boolean z3Available() {
        return org.libpetri.smt.SmtVerifier.z3Available();
    }

    private static final Place<String> BUDGET = Place.of("Budget", String.class);
    private static final Place<String> WORK = Place.of("Work", String.class);
    private static final Place<String> DONE = Place.of("Done", String.class);
    private static final Place<String> STAMP = Place.of("Stamp", String.class);
    private static final Place<String> SINK = Place.of("Sink", String.class);

    private static PetriNet loop() {
        var open = Transition.builder("Open")
            .inputs(In.one(BUDGET))
            .resets(STAMP)
            .outputs(Out.and(WORK, STAMP))
            .build();
        var step = Transition.builder("Step").inputs(In.one(WORK)).outputs(Out.place(DONE)).build();
        var close = Transition.builder("Close")
            .inputs(In.one(DONE))
            .outputs(Out.and(BUDGET, SINK))
            .build();
        return StructureOnly.bind(PetriNet.builder("loop").transitions(open, step, close).build());
    }

    @Test
    @EnabledIf("z3Available")
    void semiflowsAreEncodedOnlyWhenEnabled() {
        var off = SmtVerifier.forNet(loop())
            .initialMarking(m -> m.tokens(BUDGET, 1))
            .property(SmtProperty.placeBound(WORK, 1))
            .timeout(Duration.ofSeconds(30))
            .verify();
        assertFalse(off.report().contains("Semiflows encoded as invariants"), off.report());

        var on = SmtVerifier.forNet(loop())
            .initialMarking(m -> m.tokens(BUDGET, 1))
            .property(SmtProperty.placeBound(WORK, 1))
            .semiflowInvariants(true)
            .timeout(Duration.ofSeconds(30))
            .verify();
        assertTrue(on.isProven(), on.report());
        assertTrue(on.report().contains("Semiflows encoded as invariants: "), on.report());
        assertTrue(on.report().contains("Budget + Done + Work = 1")
                || on.report().contains("Work + Done + Budget = 1")
                || on.report().lines().anyMatch(l -> l.contains("Budget") && l.contains("Work")
                        && l.contains("Done") && l.contains("= 1") && !l.contains("Dropped")),
            "the loop's conservation law must survive the reset arc on Stamp\n" + on.report());
    }

    @Test
    @EnabledIf("z3Available")
    void strengtheningNeverHidesACounterexample() {
        // Sink accumulates one token per loop iteration: the bound 1 is genuinely violated.
        var result = SmtVerifier.forNet(loop())
            .initialMarking(m -> m.tokens(BUDGET, 1))
            .property(SmtProperty.placeBound(SINK, 1))
            .semiflowInvariants(true)
            .timeout(Duration.ofSeconds(30))
            .verify();
        assertTrue(result.isViolated(), result.report());
    }

    // ==================== coloured (ν) path ====================

    private static final Place<Integer> NU_SOURCE = Place.of("source", Integer.class);
    private static final Place<Integer> NU_BUDGET = Place.of("budget", Integer.class);
    private static final Place<Integer> NU_PENDING = Place.of("pending", Integer.class);
    private static final Place<String> NU_A = Place.of("branchA", String.class);
    private static final Place<String> NU_B = Place.of("branchB", String.class);
    private static final Place<String> NU_MERGED = Place.of("merged", String.class);

    /**
     * The scatter-gather ν-net (which puts the verifier on the name-coloured encoder)
     * alongside the reset-bearing work loop above (which is what makes the null-space
     * basis deficient). The two halves share no places; the loop is there purely so the
     * semiflow enumeration has a law to contribute.
     *
     * <p>The reset arc has to sit on the uncoloured half. {@code NameColouredEncoder}
     * rejects any transition whose reset or consume-all set touches a coloured place, and
     * {@code buildPlan} then returns null and the verifier falls back silently to the flat
     * encoding — which would make these tests pass for the wrong reason. That is what the
     * {@code coloured()} assertions below are guarding.
     */
    /** Distinct from the ν budget below: "Budget" and "budget" differ only by case. */
    private static final Place<String> LOOP_BUDGET = Place.of("loopBudget", String.class);

    private static PetriNet colouredLoop() {
        var fork = Transition.builder("fork")
            .inputs(In.one(NU_SOURCE), In.one(NU_BUDGET))
            .outputs(Out.and(NU_A, NU_B, NU_PENDING))
            .build();
        var join = Transition.builder("join")
            .inputs(In.one(NU_A), In.one(NU_B), In.one(NU_PENDING))
            .match(MatchSpec.builder()
                .key(NU_A, (String s) -> NameId.of(s))
                .key(NU_B, (String s) -> NameId.of(s))
                .build())
            .outputs(Out.and(NU_MERGED, NU_BUDGET))
            .build();
        var open = Transition.builder("Open")
            .inputs(In.one(LOOP_BUDGET))
            .resets(STAMP)
            .outputs(Out.and(WORK, STAMP))
            .build();
        var step = Transition.builder("Step").inputs(In.one(WORK)).outputs(Out.place(DONE)).build();
        var close = Transition.builder("Close")
            .inputs(In.one(DONE))
            .outputs(Out.and(LOOP_BUDGET, SINK))
            .build();
        return StructureOnly.bind(PetriNet.builder("colouredLoop")
            .transitions(fork, join, open, step, close)
            .build());
    }

    private static SmtVerifier colouredVerifier(boolean semiflows) {
        return SmtVerifier.forNet(colouredLoop())
            .initialMarking(m -> {
                m.tokens(NU_SOURCE, 3);
                m.tokens(NU_BUDGET, 2);
                m.tokens(LOOP_BUDGET, 1);
            })
            .property(SmtProperty.branchPlaceBound(NU_PENDING, 2))
            .budgetPlaces(NU_BUDGET)
            .semiflowInvariants(semiflows);
    }

    /**
     * The strengthened invariant list reaches the <em>name-coloured</em> encoder, not only
     * the flat one. Solver-free: {@code encodeScripts()} returns the script the verifier
     * would send, so this needs no z3.
     *
     * <p>This is the case that would survive the encoder being handed {@code semiflows}
     * where it wants {@code invariants} — the two are passed a line apart in
     * {@code SmtVerifier} and every other test is blind to the swap. Under it both scripts
     * below would carry the same list and the inequality would fail.
     */
    @Test
    void semiflowsReachTheColouredEncoder() {
        var off = colouredVerifier(false).encodeScripts();
        var on = colouredVerifier(true).encodeScripts();

        assertTrue(off.coloured(), "fixture must take the name-coloured path, not fall back to flat");
        assertTrue(on.coloured(), "fixture must take the name-coloured path, not fall back to flat");
        assertNotEquals(off.horn(), on.horn(),
            "the semiflows must change the coloured HORN script when the option is on");
    }

    /** The report says so too, on the coloured path. */
    @Test
    @EnabledIf("z3Available")
    void colouredReportCountsTheSemiflows() {
        var result = colouredVerifier(true)
            .timeout(Duration.ofSeconds(30))
            .verify();

        assertTrue(result.report().contains("name-coloured"),
            "fixture must take the name-coloured path: " + result.report());
        assertTrue(result.report().contains("  Semiflows encoded as invariants: "),
            result.report());
        assertFalse(result.report().contains("  Semiflows encoded as invariants: 0\n"),
            "the loop half must contribute at least one law: " + result.report());
    }
}
