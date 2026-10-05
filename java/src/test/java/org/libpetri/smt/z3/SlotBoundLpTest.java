package org.libpetri.smt.z3;

import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.internal.VerificationDeadline;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.z3.SlotBoundLp.CheckedCover;
import org.libpetri.smt.z3.SlotBoundLp.CoverCheck;
import org.libpetri.smt.z3.SlotBoundLp.CoverRefused;
import org.libpetri.smt.z3.SlotBoundLp.LpAnswer;
import org.libpetri.smt.z3.SlotBoundLp.Outcome;
import org.libpetri.smt.z3.SlotBoundLp.Rule;
import org.libpetri.smt.z3.SlotBoundLp.ScaledCover;
import org.libpetri.smt.z3.SlotBoundLp.SlotBound;
import org.libpetri.smt.z3.SlotBoundLp.Tableau;
import org.libpetri.smt.z3.SlotLpFixtures.Row;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.OptionalInt;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;
import static org.libpetri.smt.z3.SlotLpFixtures.flat;
import static org.libpetri.smt.z3.SlotLpFixtures.marking;

/**
 * The colour-slot linear program of [NU-053] ({@link SlotBoundLp}): the simplex core on Beale's
 * cycling example, the presolve, exact arithmetic on large counts, the limits, every refusal of
 * the exact re-check, and the shared parity cases of
 * {@code spec/verification-fixtures/slot-bound-lp.json}, whose expectations Rust writes. Mirrors
 * the unit tests of {@code rust/libpetri-verification/src/slot_bound_lp.rs}.
 */
class SlotBoundLpTest {

    private static Rational q(long n, long d) {
        return Rational.of(n, d);
    }

    /**
     * Beale's example (1955) in its original rational data: maximise
     * {@code 3/4 x4 - 20 x5 + 1/2 x6 - 6 x7} subject to
     * {@code 1/4 x4 - 8 x5 - x6 + 9 x7 <= 0}, {@code 1/2 x4 - 12 x5 - 1/2 x6 + 3 x7 <= 0},
     * {@code x6 <= 1}.
     */
    private static Tableau beale() {
        Rational[][] a = {
            {q(1, 4), q(-8, 1), q(-1, 1), q(9, 1)},
            {q(1, 2), q(-12, 1), q(-1, 2), q(3, 1)},
            {q(0, 1), q(0, 1), q(1, 1), q(0, 1)},
        };
        Rational[] b = {q(0, 1), q(0, 1), q(1, 1)};
        Rational[] c = {q(3, 4), q(-20, 1), q(1, 2), q(-6, 1)};
        return Tableau.standard(a, b, c);
    }

    @Test
    void blandSolvesBealesCyclingExample() {
        var t = beale();
        assertEquals(Outcome.OPTIMAL, t.run(Rule.BLAND, 1000, () -> false));
        assertEquals(q(5, 4), t.objValue);
        assertEquals(6, t.pivots);
    }

    /**
     * The largest-coefficient rule with lowest-row ties revisits a basis on the same data, so it
     * never terminates. This is what Bland's rule is there for.
     */
    @Test
    void theLargestCoefficientRuleCyclesOnBealesExample() {
        var t = beale();
        var seen = new ArrayList<List<Integer>>();
        seen.add(sortedBasis(t));
        Integer revisited = null;
        for (int step = 1; step <= 50; step++) {
            int e = t.entering(Rule.LARGEST);
            assertTrue(e >= 0, "not optimal yet");
            int r = t.leaving(Rule.LARGEST, e);
            assertTrue(r >= 0, "bounded");
            t.pivot(r, e);
            var basis = sortedBasis(t);
            if (seen.contains(basis)) {
                revisited = step;
                break;
            }
            seen.add(basis);
        }
        assertEquals(6, revisited, "the largest-coefficient rule must cycle after 6 pivots");
        assertEquals(q(0, 1), t.objValue);
    }

    private static List<Integer> sortedBasis(Tableau t) {
        return Arrays.stream(t.basis).sorted().boxed().toList();
    }

    /**
     * Bland's leaving rule breaks a ratio tie by the smallest basic column, not by the lowest
     * row. Here rows 0 and 1 tie at ratio 1 for column 0, and row 1 holds the smaller basic
     * column (2 against 3), so Bland leaves row 1. The largest-coefficient rule's lowest-row tie
     * leaves row 0.
     */
    @Test
    void blandBreaksARatioTieByTheSmallestBasicColumn() {
        var rows = new SlotBoundLp.SparseRow[] {
            new SlotBoundLp.SparseRow(new int[] {0, 3}, new Rational[] {q(1, 1), q(1, 1)}, 2),
            new SlotBoundLp.SparseRow(new int[] {0, 2}, new Rational[] {q(2, 1), q(1, 1)}, 2),
        };
        var obj = new SlotBoundLp.SparseRow(new int[] {0}, new Rational[] {q(-1, 1)}, 1);
        var t = new Tableau(rows, new Rational[] {q(1, 1), q(2, 1)}, obj, Rational.ZERO, new int[] {3, 2});
        assertEquals(0, t.entering(Rule.BLAND));
        assertEquals(1, t.leaving(Rule.BLAND, 0));
        assertEquals(0, t.leaving(Rule.LARGEST, 0));
    }

    @Test
    void thePivotLimitAndTheStopArePolledBeforeAPivot() {
        var t = beale();
        assertEquals(Outcome.PIVOT_LIMIT, t.run(Rule.BLAND, 3, () -> false));
        assertEquals(3, t.pivots);
        var u = beale();
        assertEquals(Outcome.STOPPED, u.run(Rule.BLAND, 1000, () -> true));
        assertEquals(0, u.pivots);
    }

    private static SlotBound bound(FlatNet net, MarkingState m0, int[] coloured) {
        return SlotBoundLp.checked(net, m0, coloured, SlotBoundLp.solve(net, m0, coloured));
    }

    private static Map<String, Integer> counts(Object... pairs) {
        var m = new LinkedHashMap<String, Integer>();
        for (int i = 0; i < pairs.length; i += 2) {
            m.put((String) pairs[i], (Integer) pairs[i + 1]);
        }
        return m;
    }

    private static Row row(String name, Map<String, Integer> pre, Map<String, Integer> post) {
        return new Row(name, pre, post);
    }

    /**
     * An {@code exactly(3)} fork into the keys {@code a}, {@code b} and a join that refunds one
     * budget token: optimum {@code 14/3} at budget 7, {@code 2/3} at budget 1.
     */
    private static FlatNet fractionalFork() {
        return flat(List.of("a", "b", "budget"), List.of(
            row("mint", counts("budget", 3), counts("a", 1, "b", 1)),
            row("join", counts("a", 1, "b", 1), counts("budget", 1))));
    }

    private static int[] ab() {
        return new int[] {0, 1};
    }

    @Test
    void aFractionalOptimumIsFlooredAfterTheReCheck() {
        var net = fractionalFork();
        var m0 = marking(net, counts("budget", 7));
        var answer = SlotBoundLp.solve(net, m0, ab());
        var opt = assertInstanceOf(LpAnswer.Optimal.class, answer);
        assertEquals(3, opt.places());
        assertEquals(2, opt.rows());
        assertEquals(BigInteger.valueOf(3), opt.cover().denominator());
        assertEquals(bigs(3, 3, 2), opt.cover().weights());
        var b = SlotBoundLp.checked(net, m0, ab(), answer);
        assertEquals(new SlotBound.Bound(4, q(14, 3), 3, 2), b);
        assertEquals("  Colour-slot bound: LP optimum 14/3 over 3 places and 2 transitions, so k=4 "
            + "(re-checked in exact arithmetic)", b.reportLine());
        // One budget token: below one coloured token, so the exact zero-slot plan.
        assertEquals(OptionalInt.of(0), bound(net, marking(net, counts("budget", 1)), ab()).bound());
    }

    @Test
    void noBudgetTokenGivesKZeroAndAnInflatingJoinIsInfeasible() {
        var conserving = flat(List.of("a", "b", "budget"), List.of(
            row("mint", counts("budget", 1), counts("a", 1, "b", 1)),
            row("join", counts("a", 1, "b", 1), counts("budget", 1))));
        assertEquals(OptionalInt.of(0), bound(conserving, marking(conserving, counts()), ab()).bound());
        assertEquals(OptionalInt.of(6), bound(conserving, marking(conserving, counts("budget", 3)), ab()).bound());
        // The join refunds two tokens, one to each budget place: the colours multiply.
        var inflating = flat(List.of("a", "b", "budget1", "budget2"), List.of(
            row("mint1", counts("budget1", 1), counts("a", 1, "b", 1)),
            row("mint2", counts("budget2", 1), counts("a", 1, "b", 1)),
            row("join", counts("a", 1, "b", 1), counts("budget1", 1, "budget2", 1))));
        var b = bound(inflating, marking(inflating, counts("budget1", 1)), ab());
        assertEquals(new SlotBound.Infeasible(4, 3), b);
        assertEquals("  Colour-slot bound: none (LP infeasible over 4 places and 3 transitions: no "
            + "weighting bounds the coloured tokens)", b.reportLine());
    }

    /**
     * The presolve keeps the upstream cone: a row producing into it with an entry outside it, a
     * duplicate restricted row, a consume-only row and an unrelated cycle.
     */
    @Test
    void thePresolveKeepsTheUpstreamConeAndDropsDuplicates() {
        var net = flat(List.of("a", "budget", "log", "x", "y"), List.of(
            row("mint", counts("budget", 1), counts("a", 1, "log", 1)),
            row("mint_again", counts("budget", 1), counts("a", 1)),
            row("consume", counts("a", 1), counts()),
            row("cycle", counts("x", 1), counts("y", 1)),
            row("back", counts("y", 1), counts("x", 1))));
        var m0 = marking(net, counts("budget", 2, "x", 1));
        var p = SlotBoundLp.presolve(net, new boolean[] {true, false, false, false, false});
        assertEquals(List.of(0, 1), Arrays.stream(p.places()).boxed().toList());
        assertEquals(List.of(new SlotBoundLp.RestrictedRow(new int[] {0, 1}, new long[] {1, -1})), p.rows());
        assertEquals(new SlotBound.Bound(2, q(2, 1), 2, 1), bound(net, m0, new int[] {0}));
        // m' = 0: nothing produces into the coloured place.
        var empty = flat(List.of("a", "b"), List.of(row("t", counts("a", 1), counts("b", 1))));
        assertEquals(0, SlotBoundLp.presolve(empty, new boolean[] {true, false}).rows().size());
        assertEquals(OptionalInt.of(0), bound(empty, marking(empty, counts("b", 4)), new int[] {0}).bound());
    }

    /**
     * Large counts keep the arithmetic exact. A mint that turns {@code 2^30} budget tokens into
     * {@code 2^30 - 1} keys, from {@code 2^30 - 1} budget tokens, has the optimum
     * {@code (2^30 - 1)^2 / 2^30}, whose numerator is outside an {@code int} and whose tableau
     * products reach {@code 2^60}.
     */
    @Test
    void bigCountsAndDenominatorsStayExact() {
        int big = 1 << 30;
        var net = flat(List.of("a", "budget"), List.of(
            row("mint", counts("budget", big), counts("a", big - 1)),
            row("join", counts("a", 1), counts("budget", 1))));
        var m0 = marking(net, counts("budget", big - 1));
        var answer = SlotBoundLp.solve(net, m0, new int[] {0});
        var opt = assertInstanceOf(LpAnswer.Optimal.class, answer);
        assertEquals(BigInteger.valueOf(big), opt.cover().denominator());
        assertEquals(bigs(big, big - 1), opt.cover().weights());
        var b = assertInstanceOf(SlotBound.Bound.class, SlotBoundLp.checked(net, m0, new int[] {0}, answer));
        var expected = Rational.of(BigInteger.valueOf(big - 1).pow(2), BigInteger.valueOf(big));
        assertEquals("1152921502459363329/1073741824", expected.toString());
        assertEquals(expected, b.value());
        assertEquals(big - 2, b.k());
    }

    /** One row consuming from 4096 places into the coloured one puts all 4097 in the cone. */
    @Test
    void theSizeLimitIsDecidedBeforeAnyPivot() {
        int n = SlotBoundLp.MAX_PLACES + 1;
        var names = new ArrayList<String>();
        var pre = new LinkedHashMap<String, Integer>();
        for (int i = 0; i < n; i++) {
            String name = String.format("p%05d", i);
            names.add(name);
            if (i > 0) {
                pre.put(name, 1);
            }
        }
        var net = flat(names, List.of(row("gather", pre, counts("p00000", 1))));
        var empty = marking(net, counts());
        var solved = SlotBoundLp.solveCounted(net, empty, new int[] {0});
        assertEquals(new LpAnswer.TooLarge(n, 1), solved.answer());
        assertEquals(0, solved.pivots());
        assertEquals("  Colour-slot bound: none (LP over 4097 places and 1 transitions exceeds the limit "
            + "of 4096 places and 16384 transitions)",
            SlotBoundLp.checked(net, empty, new int[] {0}, solved.answer()).reportLine());
    }

    /**
     * [VER-013]: the solve calls the verification's checkpoint before every pivot. Under a
     * cancelled {@code verify()} (an interrupted thread with a deadline bound) a program that
     * needs a pivot stops with {@code Cancelled}; one that needs none still answers, because the
     * poll comes only before a pivot.
     */
    @Test
    void theSolveHonoursTheVerificationCheckpointBeforeEveryPivot() throws Exception {
        var net = fractionalFork();
        var m0 = marking(net, counts("budget", 7));
        var empty = flat(List.of("a", "b"), List.of(row("t", counts("a", 1), counts("b", 1))));
        var deadline = VerificationDeadline.unlimited("colour-slot bound");
        Thread.currentThread().interrupt();
        try {
            var stopped = assertThrows(VerificationDeadline.Cancelled.class, () ->
                ScopedValue.where(VerificationDeadline.carrier(), deadline)
                    .call(() -> SlotBoundLp.solve(net, m0, ab())));
            assertEquals("verification cancelled during colour-slot bound", stopped.reason());
            var answered = ScopedValue.where(VerificationDeadline.carrier(), deadline)
                .call(() -> SlotBoundLp.solve(empty, marking(empty, counts()), new int[] {0}));
            assertInstanceOf(LpAnswer.Optimal.class, answered);
        } finally {
            Thread.interrupted();
        }
        // Outside a verify() call the checkpoint does nothing, as in encodeScripts().
        assertInstanceOf(LpAnswer.Optimal.class, SlotBoundLp.solve(net, m0, ab()));
    }

    // ---- the checker, one refusal per clause, in order ----

    private static List<BigInteger> bigs(long... values) {
        return Arrays.stream(values).mapToObj(BigInteger::valueOf).toList();
    }

    private static ScaledCover cover(long d, long... weights) {
        return new ScaledCover(bigs(weights), BigInteger.valueOf(d));
    }

    private static String refusal(CoverCheck check) {
        return assertInstanceOf(CoverRefused.class, check).reason();
    }

    @Test
    void theCheckerRefusesEachClauseWithItsReason() {
        var net = fractionalFork();
        var m0 = marking(net, counts("budget", 7));
        java.util.function.Function<ScaledCover, CoverCheck> check = c -> SlotBoundLp.checkCover(net, m0, ab(), c);
        assertEquals(new CheckedCover(4, q(14, 3)), check.apply(cover(3, 3, 3, 2)));
        assertEquals("weighting has 2 entries for 3 places", refusal(check.apply(cover(3, 3, 3))));
        assertEquals("denominator 0 is not positive", refusal(check.apply(cover(0, 3, 3, 2))));
        assertEquals("denominator -3 is not positive", refusal(check.apply(cover(-3, -3, -3, -2))));
        assertEquals("place 'budget' has negative weight -2", refusal(check.apply(cover(3, 3, 3, -2))));
        assertEquals("coloured place 'b' has weight 2 below the denominator 3",
            refusal(check.apply(cover(3, 3, 2, 2))));
        // Keys at 1 and the budget at 0: the mint raises the weighted sum by 2.
        assertEquals("transition 'mint' increases the weighted sum by 2", refusal(check.apply(cover(1, 1, 1, 0))));
        // Feasible and above the cap: k = 7·2^31 / 3 > 2147483647.
        long w = 1L << 31;
        assertEquals("k=" + (7 * w / 3) + " exceeds 2147483647",
            refusal(check.apply(cover(3, w * 3 / 2, w * 3 / 2, w))));
        // A feasible weighting that is not optimal is accepted, with its larger k.
        assertEquals(7, assertInstanceOf(CheckedCover.class, check.apply(cover(1, 1, 1, 1))).k());
    }

    /**
     * The checker reads every flat row, including one the presolve drops: here a row that only
     * consumes from the cone has no positive entry in it and never reaches the simplex, but a
     * weighting that is positive on its output must still fail.
     */
    @Test
    void theCheckerSeesRowsThePresolveDropped() {
        var net = flat(List.of("a", "budget", "z"), List.of(
            row("mint", counts("budget", 1), counts("a", 1)),
            row("join", counts("a", 1), counts("budget", 1)),
            row("spill", counts("a", 1), counts("z", 2))));
        var m0 = marking(net, counts("budget", 1));
        assertEquals(2, SlotBoundLp.presolve(net, new boolean[] {true, false, false}).rows().size());
        // z = 1: spill raises the sum by 2·1 - 1 = 1.
        assertEquals("transition 'spill' increases the weighted sum by 1",
            refusal(SlotBoundLp.checkCover(net, m0, new int[] {0}, cover(1, 1, 1, 1))));
        assertEquals(OptionalInt.of(1), bound(net, m0, new int[] {0}).bound());
    }

    @Test
    void everyAnswerWithoutAWeightingIsNoBound() {
        var net = fractionalFork();
        var m0 = marking(net, counts());
        var limited = SlotBoundLp.checked(net, m0, ab(), new LpAnswer.PivotLimit(250));
        assertEquals(OptionalInt.empty(), limited.bound());
        assertEquals("  Colour-slot bound: none (no LP optimum within the pivot limit of 250)", limited.reportLine());
        var stopped = SlotBoundLp.checked(net, m0, ab(), new LpAnswer.Stopped());
        assertEquals(OptionalInt.empty(), stopped.bound());
        assertNull(stopped.reportLine());
        var failed = SlotBoundLp.checked(net, m0, ab(), new LpAnswer.Optimal(cover(1, 1, 1), 3, 2));
        assertEquals("  Colour-slot bound: none (LP weighting failed the exact re-check: weighting has 2 "
            + "entries for 3 places)", failed.reportLine());
    }

    // ---- the shared parity cases ----

    /**
     * Every case of {@code slot-bound-lp.json}: the status, the presolved sizes, the pivot count,
     * the optimum, {@code k} and the scaled weighting Rust's simplex gives, exactly.
     */
    @TestFactory
    List<DynamicTest> theSharedParityCasesMatchRust() {
        var cases = SlotLpFixtures.parityCases();
        assertTrue(cases.size() >= 16, "slot-bound-lp.json lists " + cases.size() + " cases");
        return cases.stream().map(c -> DynamicTest.dynamicTest(c.id(), () -> {
            var solved = SlotBoundLp.solveCounted(c.flat(), c.initial(), c.coloured());
            var expected = c.expected();
            String status = switch (solved.answer()) {
                case LpAnswer.Optimal o -> "optimal";
                case LpAnswer.Infeasible i -> "infeasible";
                case LpAnswer.TooLarge t -> "too-large";
                case LpAnswer.PivotLimit l -> "pivot-limit";
                case LpAnswer.Stopped s -> "stopped";
            };
            assertEquals(expected.get("status").asText(), status, c.id());
            switch (solved.answer()) {
                case LpAnswer.Optimal o -> {
                    assertEquals(expected.get("places").asInt(), o.places(), c.id());
                    assertEquals(expected.get("rows").asInt(), o.rows(), c.id());
                }
                case LpAnswer.Infeasible i -> {
                    assertEquals(expected.get("places").asInt(), i.places(), c.id());
                    assertEquals(expected.get("rows").asInt(), i.rows(), c.id());
                }
                case LpAnswer.TooLarge t -> {
                    assertEquals(expected.get("places").asInt(), t.places(), c.id());
                    assertEquals(expected.get("rows").asInt(), t.rows(), c.id());
                }
                default -> { }
            }
            assertEquals(expected.get("pivots").asInt(), solved.pivots(), c.id() + " pivots");
            if (solved.answer() instanceof LpAnswer.Optimal o) {
                var b = SlotBoundLp.checked(c.flat(), c.initial(), c.coloured(), o);
                if (!(b instanceof SlotBound.Bound bound)) {
                    fail("[" + c.id() + "] the simplex's weighting failed the re-check: " + b);
                    return;
                }
                assertEquals(expected.get("optimum").asText(), bound.value().toString(), c.id());
                assertEquals(expected.get("k").asInt(), bound.k(), c.id());
                var weights = new LinkedHashMap<String, String>();
                for (int p = 0; p < c.flat().placeCount(); p++) {
                    var w = o.cover().weights().get(p);
                    if (w.signum() != 0) {
                        weights.put(c.flat().places().get(p).name(), w.toString());
                    }
                }
                var expectedWeights = new LinkedHashMap<String, String>();
                expected.get("weights").properties().forEach(e -> expectedWeights.put(e.getKey(), e.getValue().asText()));
                assertEquals(expectedWeights, weights, c.id());
                assertEquals(expected.get("denominator").asText(), o.cover().denominator().toString(), c.id());
            } else {
                assertNull(expected.get("optimum"), c.id());
            }
        })).toList();
    }

    /**
     * The seeded composed workflow of 255 places and 341 rows: optimum 6 (two budget tokens times
     * three keys), within twice as many pivots as the presolved program has places and rows.
     */
    @Test
    void theComposedWorkflowSolvesInFewPivots() {
        var c = SlotLpFixtures.parityCases().stream()
            .filter(x -> x.id().equals("composed-workflow-7")).findFirst().orElseThrow();
        assertEquals(255, c.flat().placeCount());
        assertEquals(341, c.flat().transitionCount());
        long start = System.nanoTime();
        var solved = SlotBoundLp.solveCounted(c.flat(), c.initial(), c.coloured());
        long micros = (System.nanoTime() - start) / 1000;
        var opt = assertInstanceOf(LpAnswer.Optimal.class, solved.answer());
        assertTrue(solved.pivots() <= 2 * (opt.places() + opt.rows()),
            solved.pivots() + " pivots over " + opt.places() + " places and " + opt.rows() + " rows");
        var b = SlotBoundLp.checked(c.flat(), c.initial(), c.coloured(), solved.answer());
        assertEquals(OptionalInt.of(6), b.bound(), String.valueOf(b));
        System.out.println("[slot-bound LP] composed workflow: " + solved.pivots() + " pivots in " + micros + " µs");
    }
}
