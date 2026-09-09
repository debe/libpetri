package org.libpetri.smt;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.z3.LinearBound;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

import java.math.BigInteger;
import java.time.Duration;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.*;

/**
 * [VER-015] linear state-equation bound.
 *
 * <p>A fork that may halt instead: {@code p0(1) → f → AND(a, b) | halt; a → ga → ra;
 * b → gb → rb}; join {@code ra + rb → done}. {@code {ra, rb, halt}} is unreachable — a halt
 * consumes the token that would have fed both arms — and no EQUALITY law says so (the halt
 * branch turns 2 units into 1), so the null-space basis cannot exclude it. The decreasing
 * law {@code 2·p0 + a + b + ra + rb + halt + 2·done <= 2} does: the target needs 3. Mirrors
 * {@code typescript/tests/verification/linear-bound.test.ts}.
 */
class LinearBoundTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final Place<String> P0 = Place.of("p0", String.class);
    private static final Place<String> A = Place.of("a", String.class);
    private static final Place<String> B = Place.of("b", String.class);
    private static final Place<String> RA = Place.of("ra", String.class);
    private static final Place<String> RB = Place.of("rb", String.class);
    private static final Place<String> HALT = Place.of("halt", String.class);
    private static final Place<String> DONE = Place.of("done", String.class);

    static PetriNet forkOrHalt() {
        var f = Transition.builder("f").inputs(In.one(P0)).outputs(Out.xor(Out.and(A, B), Out.place(HALT))).build();
        var ga = Transition.builder("ga").inputs(In.one(A)).outputs(Out.place(RA)).build();
        var gb = Transition.builder("gb").inputs(In.one(B)).outputs(Out.place(RB)).build();
        var join = Transition.builder("join").inputs(In.one(RA), In.one(RB)).outputs(Out.place(DONE)).build();
        return StructureOnly.bind(PetriNet.builder("forkOrHalt").transitions(f, ga, gb, join).build());
    }

    static MarkingState m0() {
        return MarkingState.builder().tokens(P0, 1).build();
    }

    static FlatNet flat(PetriNet net) {
        return NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.alwaysAvailable());
    }

    private static SmtProperty target() {
        return SmtProperty.unreachable(Set.of(RA, RB, HALT));
    }

    // === Encoding ===

    @Test
    void hasNoDemandForTheQuiescenceProperties() {
        var flat = flat(forkOrHalt());
        assertNull(LinearBound.violationDemand(flat, SmtProperty.deadlockFree()));
        assertNull(LinearBound.encode(flat, m0(), SmtProperty.deadlockFree()));
    }

    @Test
    void encodesNonNegativeWeights_oneRowPerFlatTransition_andTheDemandAgainstInitPlusOne() {
        var flat = flat(forkOrHalt());
        String script = LinearBound.encode(flat, m0(), target());
        assertNotNull(script);
        assertTrue(script.contains("(set-logic QF_LIA)"));
        for (int p = 0; p < flat.placeCount(); p++) {
            assertTrue(script.contains("(declare-const y" + p + " Int)"));
            assertTrue(script.contains("(assert (>= y" + p + " 0))"));
        }
        // f's halt branch: -p0 + halt, places in flat-index order
        int p0 = flat.indexOf(P0);
        int halt = flat.indexOf(HALT);
        int[] row = {halt, p0};
        Arrays.sort(row);
        String haltRow = (row[0] == p0 ? "(- y" + row[0] + ")" : "y" + row[0]) + " "
            + (row[1] == p0 ? "(- y" + row[1] + ")" : "y" + row[1]);
        assertTrue(script.contains("(assert (<= (+ " + haltRow + ") 0))"), script);
        // Demand: ra + rb + halt >= 1 + p0
        int[] d = {flat.indexOf(RA), flat.indexOf(RB), halt};
        Arrays.sort(d);
        assertTrue(script.contains("(assert (>= (+ y" + d[0] + " y" + d[1] + " y" + d[2] + ") (+ 1 y" + p0 + ")))"),
            script);
        assertTrue(script.endsWith("(check-sat)\n(get-model)"));
    }

    @Test
    void pinsConsumeAllPlacesToZeroWeight() {
        var q = Place.of("q", String.class);
        var r = Place.of("r", String.class);
        var t = Transition.builder("t").inputs(In.all(q)).outputs(Out.place(r)).build();
        var flat = flat(StructureOnly.bind(PetriNet.builder("drain").transitions(t).build()));
        var m0 = MarkingState.builder().tokens(q, 2).build();
        String script = LinearBound.encode(flat, m0, SmtProperty.placeBound(r, 1));
        assertNotNull(script);
        assertTrue(script.contains("(assert (= y" + flat.indexOf(q) + " 0))"), script);
        // A weighting that leans on the drained place is rejected by the exact check.
        var y = new BigInteger[flat.placeCount()];
        Arrays.fill(y, BigInteger.ZERO);
        y[flat.indexOf(q)] = BigInteger.ONE;
        y[flat.indexOf(r)] = BigInteger.ONE;
        assertNull(LinearBound.checkExact(flat, m0, SmtProperty.placeBound(r, 1), y));
    }

    @Test
    void decodesAModelAndReChecksItExactly() {
        var flat = flat(forkOrHalt());
        String model = String.join("\n",
            "sat", "(",
            "  (define-fun y" + flat.indexOf(P0) + " () Int\n    2)",
            "  (define-fun y" + flat.indexOf(A) + " () Int 1)",
            "  (define-fun y" + flat.indexOf(B) + " () Int 1)",
            "  (define-fun y" + flat.indexOf(RA) + " () Int 1)",
            "  (define-fun y" + flat.indexOf(RB) + " () Int 1)",
            "  (define-fun y" + flat.indexOf(HALT) + " () Int 1)",
            "  (define-fun y" + flat.indexOf(DONE) + " () Int 2)",
            ")");
        BigInteger[] y = LinearBound.decode(model, flat.placeCount());
        assertNotNull(y);
        assertEquals(BigInteger.TWO, y[flat.indexOf(P0)]);
        var bound = LinearBound.checkExact(flat, m0(), target(), y);
        assertNotNull(bound);
        assertEquals(BigInteger.TWO, bound.constant());
        assertEquals(BigInteger.valueOf(3), bound.demandValue());
        assertEquals("a + b + 2*done + halt + 2*p0 + ra + rb <= 2", LinearBound.formatBound(flat, bound));
        assertEquals("halt + ra + rb >= 3", LinearBound.formatDemand(flat, target(), bound));
        // A weighting that is not decreasing under the fork is rejected.
        var bad = y.clone();
        bad[flat.indexOf(P0)] = BigInteger.ONE;
        assertNull(LinearBound.checkExact(flat, m0(), target(), bad));
        // A weighting whose demand does not exceed the constant is rejected.
        assertNull(LinearBound.checkExact(flat, m0(), SmtProperty.unreachable(Set.of(RA, HALT)), y));
        // Negative literals decode.
        BigInteger[] neg = LinearBound.decode("sat\n(\n  (define-fun y0 () Int\n    (- 3))\n)", 1);
        assertNotNull(neg);
        assertEquals(BigInteger.valueOf(-3), neg[0]);
        assertNull(LinearBound.decode("sat\n(\n)", 1));
    }

    // === End to end ===

    @Test
    @EnabledIf("z3Available")
    void provesAnUnreachableMarkingStructurally_whenNoEqualityLawExcludesIt() {
        // Explicit opt-out, not an oversight: [VER-017]'s enumeration route closes this
        // small untimed net and would answer "proven by enumeration" before the linear
        // bound this test exists to exercise ever runs.
        var result = SmtVerifier.forNet(forkOrHalt()).initialMarking(m0())
            .enumerationMaxClasses(0)
            .property(target()).timeout(Duration.ofSeconds(30)).verify();
        assertTrue(result.isProven(), result.report());
        var proven = assertInstanceOf(SmtVerificationResult.Verdict.Proven.class, result.verdict());
        assertEquals("structural", proven.method());
        // The solver is free to pick any separating weighting; the report names it and
        // the exact re-check vouched for it.
        assertTrue(Pattern.compile("Linear state-equation bound: .* <= \\d+; violation needs .* >= \\d+")
            .matcher(result.report()).find(), result.report());
        assertTrue(result.report().contains(
            "Status: bound excludes every violating marking (re-checked in exact integer arithmetic)"), result.report());
        assertTrue(result.report().contains("PROVEN (structural)"), result.report());
        assertFalse(result.report().contains("Phase 5"), result.report());
        // [VER-003] AC4: a structural proof names its route, and still carries the
        // invariants the pipeline computed before it — a NON-empty list is real on
        // every route.
        assertEquals(SmtVerificationResult.Route.STRUCTURAL, result.route(), result.report());
    }

    @Test
    @EnabledIf("z3Available")
    void handsOverToTheFixpointQuery_whenNoBoundSeparatesAReachableTarget() {
        // Explicit opt-out, not an oversight: the enumeration route ([VER-017]) would
        // decide this net without ever asking the bound query, and the hand-over to the
        // fixpoint search is exactly what is under test.
        var result = SmtVerifier.forNet(forkOrHalt()).initialMarking(m0())
            .enumerationMaxClasses(0)
            .property(SmtProperty.mutualExclusion(RA, RB)).timeout(Duration.ofSeconds(30)).verify();
        assertTrue(result.isViolated(), result.report());
        assertTrue(result.report().contains("Linear state-equation bound: none separates the violation"),
            result.report());
        assertEquals(Boolean.TRUE, result.counterexampleConfirmed(), result.report());
    }

    @Test
    void encodeScripts_reportsTheBoundQueryForReachabilitySafetyAndNullOtherwise() {
        var scripts = SmtVerifier.forNet(forkOrHalt()).initialMarking(m0()).property(target()).encodeScripts();
        assertNotNull(scripts.bound());
        assertTrue(scripts.bound().contains("(set-logic QF_LIA)"));
        var none = SmtVerifier.forNet(forkOrHalt()).initialMarking(m0()).property(SmtProperty.deadlockFree())
            .encodeScripts();
        assertNull(none.bound());
        // Disabled: verify() would not send it, so encodeScripts() reports none.
        var off = SmtVerifier.forNet(forkOrHalt()).initialMarking(m0()).property(target())
            .linearBound(false).encodeScripts();
        assertNull(off.bound());
    }
}
