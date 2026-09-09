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

import static org.junit.jupiter.api.Assertions.assertEquals;
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

    // ==================== computed only when read (VER-007 AC2) ====================

    private static final Place<String> CYCLE_A = Place.of("cycleA", String.class);
    private static final Place<String> CYCLE_C = Place.of("cycleC", String.class);

    /**
     * A conservation cycle that runs THROUGH a consume-all place: {@code cycleA + cycleC}
     * is a genuine semiflow, and the H1 guard drops it because {@code cycleC} is drained
     * by {@code all()}. That drop is the observable — it appears in the report only if the
     * Farkas enumeration actually ran.
     */
    private static PetriNet drainCycle() {
        var fill = Transition.builder("fill").inputs(In.one(CYCLE_A)).outputs(Out.place(CYCLE_C)).build();
        var drain = Transition.builder("drain").inputs(In.all(CYCLE_C)).outputs(Out.place(CYCLE_A)).build();
        return StructureOnly.bind(PetriNet.builder("drainCycle").transitions(fill, drain).build());
    }

    private static SmtVerificationResult drainCycleUnder(SmtVerifier.SemiflowMode mode) {
        // Explicit opt-out, not an oversight: [VER-017]'s enumeration route would decide
        // this net before Phase 3 prints anything about semiflows.
        return SmtVerifier.forNet(drainCycle())
            .enumerationMaxClasses(0)
            .initialMarking(m -> m.tokens(CYCLE_A, 1))
            .property(SmtProperty.placeBound(CYCLE_C, 1))
            .semiflowInvariants(mode)
            .timeout(Duration.ofSeconds(30))
            .verify();
    }

    @Test
    @EnabledIf("z3Available")
    void semiflowsAreNotEvenComputedWhenNothingWillReadThem() {
        // The enumeration is worst-case exponential and, on a wide net, uncatchable — the
        // heap it exhausts kills the process rather than returning a verdict. So the
        // default must not run it at all, not merely discard the answer.
        var off = drainCycleUnder(SmtVerifier.SemiflowMode.OFF);
        assertFalse(off.report().contains("Dropped semiflow:"), off.report());
        assertFalse(off.report().contains("Semiflows encoded as invariants"), off.report());

        // Same net, same drop, reported — so the OFF report above is silence about a phase
        // that did not run, not silence about one that ran and found nothing.
        var on = drainCycleUnder(SmtVerifier.SemiflowMode.ON);
        // The rendered support order is not pinned here (Set.copyOf iteration is salted per
        // JVM run); the presence of the line is what this test is about.
        assertTrue(on.report().lines().anyMatch(l -> l.startsWith("  Dropped semiflow: ")
            && l.contains("cycleA") && l.contains("cycleC")
            && l.contains("consume-all/reset place 'cycleC'")), on.report());
    }

    // ==================== AUTO (VER-007) ====================
    //
    // `AUTO` computes the semiflows exactly when the basis LOST a law to the H1 guard,
    // which is the condition the option exists for. One pass — the drops are known before
    // the decision is made.

    private static final Place<String> AUTO_BUDGET = Place.of("autoBudget", String.class);
    private static final Place<String> AUTO_QUEUE = Place.of("autoQueue", String.class);
    private static final Place<String> AUTO_WORK = Place.of("autoWork", String.class);
    private static final Place<String> AUTO_SINK = Place.of("autoSink", String.class);

    /** A draining {@code all()} arc on a busy place: the H1 guard drops laws touching it. */
    private static PetriNet drainingLoop() {
        var take = Transition.builder("take")
            .inputs(In.one(AUTO_BUDGET), In.all(AUTO_QUEUE))
            .outputs(Out.place(AUTO_WORK))
            .build();
        var done = Transition.builder("done")
            .inputs(In.one(AUTO_WORK))
            .outputs(Out.and(AUTO_BUDGET, AUTO_SINK))
            .build();
        return StructureOnly.bind(PetriNet.builder("drain").transitions(take, done).build());
    }

    private static final Place<String> CLEAN_A = Place.of("cleanA", String.class);
    private static final Place<String> CLEAN_B = Place.of("cleanB", String.class);
    private static final Place<String> CLEAN_C = Place.of("cleanC", String.class);

    /** A clean pipeline: nothing is dropped, so the union would add only cost. */
    private static PetriNet cleanChain() {
        var t1 = Transition.builder("c1").inputs(In.one(CLEAN_A)).outputs(Out.place(CLEAN_B)).build();
        var t2 = Transition.builder("c2").inputs(In.one(CLEAN_B)).outputs(Out.place(CLEAN_C)).build();
        return StructureOnly.bind(PetriNet.builder("clean").transitions(t1, t2).build());
    }

    @Test
    @EnabledIf("z3Available")
    void auto_turnsTheUnionOnWhenTheBasisLostALaw_andSaysWhy() {
        // Explicit opt-out, not an oversight: [VER-017]'s enumeration route would decide
        // this before Phase 3 ever printed the semiflow decision under test.
        var r = SmtVerifier.forNet(drainingLoop())
            .enumerationMaxClasses(0)
            .initialMarking(m -> {
                m.tokens(AUTO_BUDGET, 1);
                m.tokens(AUTO_QUEUE, 2);
            })
            .property(SmtProperty.placeBound(AUTO_SINK, 2))
            .semiflowInvariants(SmtVerifier.SemiflowMode.AUTO)
            .timeout(Duration.ofSeconds(30))
            .verify();
        assertTrue(r.report().contains("Strengthening.lean H1"), r.report());
        assertTrue(r.report().contains(
            "  Semiflow union: ON (auto — the basis lost a law to the H1 guard)"), r.report());
        assertTrue(r.report().contains("  Semiflows encoded as invariants: "), r.report());
    }

    @Test
    @EnabledIf("z3Available")
    void auto_leavesTheUnionOffWhenTheBasisIsComplete_andSaysWhy() {
        // Explicit opt-out, not an oversight: see the sibling test above.
        var r = SmtVerifier.forNet(cleanChain())
            .enumerationMaxClasses(0)
            .initialMarking(m -> m.tokens(CLEAN_A, 1))
            .property(SmtProperty.placeBound(CLEAN_C, 1))
            .semiflowInvariants(SmtVerifier.SemiflowMode.AUTO)
            .timeout(Duration.ofSeconds(30))
            .verify();
        assertFalse(r.report().contains("Strengthening.lean H1"), r.report());
        assertTrue(r.report().contains(
            "  Semiflow union: off (auto — the basis is complete, so the semiflows would add no "
            + "constraint the encoding does not already have; they may still differ in FORM)"),
            r.report());
        assertFalse(r.report().contains("Semiflows encoded as invariants:"), r.report());
    }

    // A discriminating AUTO fixture: the draining loop again (so the H1 guard drops a
    // basis law and AUTO unions) alongside a two-client mutex whose minimal conservation
    // law `mutex + crit1 + crit2 = 1` is NOT a row of the eliminated basis (so the union
    // actually ADDS one). Both halves are needed: on a net where the union adds nothing,
    // ON and OFF emit the same script and no test could tell AUTO-honoured from
    // AUTO-read-as-OFF. Places are indexed in code-point order of their names ([VER-013]),
    // which is what fixes the elimination's pivot order — hence the premise assertion.
    private static final Place<String> MX_BUDGET = Place.of("budget", String.class);
    private static final Place<String> MX_QUEUE = Place.of("queue", String.class);
    private static final Place<String> MX_WORK = Place.of("work", String.class);
    private static final Place<String> MX_SINK = Place.of("sink", String.class);
    private static final Place<String> MX_MUTEX = Place.of("mutex", String.class);
    private static final Place<String> MX_IDLE_1 = Place.of("idle1", String.class);
    private static final Place<String> MX_IDLE_2 = Place.of("idle2", String.class);
    private static final Place<String> MX_CRIT_1 = Place.of("crit1", String.class);
    private static final Place<String> MX_CRIT_2 = Place.of("crit2", String.class);

    private static PetriNet drainingLoopWithMutex() {
        var take = Transition.builder("take")
            .inputs(In.one(MX_BUDGET), In.all(MX_QUEUE))
            .outputs(Out.place(MX_WORK))
            .build();
        var done = Transition.builder("done")
            .inputs(In.one(MX_WORK))
            .outputs(Out.and(MX_BUDGET, MX_SINK))
            .build();
        var enter1 = Transition.builder("enter1")
            .inputs(In.one(MX_IDLE_1), In.one(MX_MUTEX)).outputs(Out.place(MX_CRIT_1)).build();
        var exit1 = Transition.builder("exit1")
            .inputs(In.one(MX_CRIT_1)).outputs(Out.and(MX_IDLE_1, MX_MUTEX)).build();
        var enter2 = Transition.builder("enter2")
            .inputs(In.one(MX_IDLE_2), In.one(MX_MUTEX)).outputs(Out.place(MX_CRIT_2)).build();
        var exit2 = Transition.builder("exit2")
            .inputs(In.one(MX_CRIT_2)).outputs(Out.and(MX_IDLE_2, MX_MUTEX)).build();
        return StructureOnly.bind(PetriNet.builder("drain-mutex")
            .transitions(take, done, enter1, exit1, enter2, exit2).build());
    }

    private static void mutexMarking(org.libpetri.analysis.MarkingState.Builder m) {
        m.tokens(MX_BUDGET, 1);
        m.tokens(MX_QUEUE, 2);
        m.tokens(MX_MUTEX, 1);
        m.tokens(MX_IDLE_1, 1);
        m.tokens(MX_IDLE_2, 1);
    }

    private static SmtVerifier.EncodedScripts mutexScripts(SmtVerifier.SemiflowMode mode) {
        return SmtVerifier.forNet(drainingLoopWithMutex())
            .initialMarking(SemiflowInvariantsTest::mutexMarking)
            .property(SmtProperty.placeBound(MX_SINK, 2))
            .semiflowInvariants(mode)
            .encodeScripts();
    }

    @Test
    void auto_isHonouredByEncodeScripts_soTheGoldensPinWhatThePipelineSends() {
        // encodeScripts() is what the cross-language goldens are diffed against, so it must
        // report the script verify() would SEND. It applied the union only for an explicit
        // ON, so on a net where AUTO unions the goldens pinned a script the pipeline never
        // emits. Solver-free.
        var on = mutexScripts(SmtVerifier.SemiflowMode.ON);
        var off = mutexScripts(SmtVerifier.SemiflowMode.OFF);
        var auto = mutexScripts(SmtVerifier.SemiflowMode.AUTO);
        // The premise: on THIS net the union changes the script.
        assertNotEquals(off.horn(), on.horn(),
            "fixture no longer discriminates: the union adds no law here");
        assertEquals(on.horn(), auto.horn(),
            "AUTO unions on this net, so it must emit the script ON emits");
        assertEquals(on.certificate(), auto.certificate());

        // A complete basis: AUTO declines, so the script matches the OFF case.
        var cleanAuto = SmtVerifier.forNet(cleanChain()).initialMarking(m -> m.tokens(CLEAN_A, 1))
            .property(SmtProperty.placeBound(CLEAN_C, 1))
            .semiflowInvariants(SmtVerifier.SemiflowMode.AUTO).encodeScripts();
        var cleanOff = SmtVerifier.forNet(cleanChain()).initialMarking(m -> m.tokens(CLEAN_A, 1))
            .property(SmtProperty.placeBound(CLEAN_C, 1))
            .semiflowInvariants(SmtVerifier.SemiflowMode.OFF).encodeScripts();
        assertEquals(cleanOff.horn(), cleanAuto.horn());
        assertEquals(cleanOff.certificate(), cleanAuto.certificate());
    }

    @Test
    @EnabledIf("z3Available")
    void auto_theReportedScriptIsTheOneVerifySends() {
        // The other half of the same claim: verify() takes the union on this net, and says
        // how many laws it added — the count encodeScripts() now also carries.
        var r = SmtVerifier.forNet(drainingLoopWithMutex())
            .enumerationMaxClasses(0)
            .initialMarking(SemiflowInvariantsTest::mutexMarking)
            .property(SmtProperty.placeBound(MX_SINK, 2))
            .semiflowInvariants(SmtVerifier.SemiflowMode.AUTO)
            .timeout(Duration.ofSeconds(30))
            .verify();
        assertTrue(r.report().contains(
            "  Semiflow union: ON (auto — the basis lost a law to the H1 guard)"), r.report());
        assertTrue(r.report().contains("  Semiflows encoded as invariants: 1"), r.report());
    }

    @Test
    @EnabledIf("z3Available")
    void auto_neverWeakensAVerdictAgainstTheExplicitSettings() {
        record Case(PetriNet net, java.util.function.Consumer<org.libpetri.analysis.MarkingState.Builder> m0,
                    Place<String> target) {}
        var cases = java.util.List.of(
            new Case(drainingLoop(), m -> {
                m.tokens(AUTO_BUDGET, 1);
                m.tokens(AUTO_QUEUE, 2);
            }, AUTO_SINK),
            new Case(cleanChain(), m -> m.tokens(CLEAN_A, 1), CLEAN_C));
        for (var c : cases) {
            var verdicts = new java.util.LinkedHashSet<String>();
            for (var mode : SmtVerifier.SemiflowMode.values()) {
                var r = SmtVerifier.forNet(c.net())
                    // Explicit opt-out: the point is that the three MODES agree, which only
                    // means something on the route the modes affect.
                    .enumerationMaxClasses(0)
                    .initialMarking(c.m0()::accept)
                    .property(SmtProperty.placeBound(c.target(), 2))
                    .semiflowInvariants(mode)
                    .timeout(Duration.ofSeconds(30))
                    .verify();
                verdicts.add(r.verdict().getClass().getSimpleName());
            }
            assertEquals(1, verdicts.size(), "verdicts differed across modes: " + verdicts);
        }
    }
}
