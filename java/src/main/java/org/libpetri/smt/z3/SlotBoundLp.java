package org.libpetri.smt.z3;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.internal.VerificationDeadline;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.FlatTransition;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.OptionalInt;
import java.util.Set;
import java.util.function.BooleanSupplier;

/**
 * The colour-slot bound {@code k} of the name-coloured encoding ([NU-053]), as a linear program
 * solved in exact rational arithmetic, with no solver ([VER-013] AC1).
 *
 * <p>{@code k} has to bound the number of names live at once. A name is live only while some
 * coloured place holds a token of it, so the live names never outnumber the tokens on the
 * coloured places. For any weighting {@code y} over the flat places with
 * <ul>
 *   <li>{@code y >= 0},</li>
 *   <li>{@code y_p >= 1} on every coloured place {@code p},</li>
 *   <li>{@code y·N_r <= 0} for every flat row {@code r}, where {@code N_r = post_r - pre_r} is
 *       the row's column of the incidence matrix (a timeout outcome counts its deposit),</li>
 * </ul>
 * every reachable marking has {@code Σ_{coloured} M <= y·M <= y·M0}. {@code k = ⌊opt⌋}, where
 * {@code opt} is the least {@code y·M0} over all such weightings. The optimum is unique, so every
 * implementation computes the same {@code k}. Equivalently (the dual), {@code opt} is the largest
 * coloured token count the state equation {@code M = M0 + N·σ >= 0}, {@code σ >= 0} admits over
 * the reals. The program is infeasible exactly when that count is unbounded: then nothing bounds
 * the coloured tokens structurally, and the plan is refused.
 *
 * <p><b>No H1.</b> A place a reset or consume-all arc clears keeps a free weight
 * {@code y_p >= 0}. At an enabled firing such a place ends at its deposit, which is at most
 * {@code m_p - pre_p + post_p} because enablement gives {@code pre_p <= m_p} (Lean
 * {@code fireAD_le_linear}, {@code Novel/LinearBound.lean}), and a non-negative weight keeps the
 * inequality. The [VER-015] check ({@link LinearBound}) still pins such places to weight zero
 * although its proof does not need it ({@code linear_bound_sound_noH1}); the slot bound follows
 * the proof. The difference is deliberate. Inhibitor and read arcs do not enter the column: they
 * only restrict enablement.
 *
 * <p><b>Trust.</b> {@link #solve} is untrusted: it is not modelled in Lean, so editing it needs
 * no Lean re-verification. Its answer is a weighting scaled to integers ({@link ScaledCover}).
 * The plan uses {@code k} only through {@link #checked}, which runs {@link #checkCover}: an exact
 * re-check of the weighting against every flat row, which computes {@code k = ⌊Y·M0 / D⌋}
 * itself. Only the checker is modelled ({@code checkCover}, {@code colourSlotBoundLP} in
 * {@code lean/Libpetri/Novel/RouteA/SlotBound.lean}) and proved sufficient for
 * {@code coloured_simulates} ({@code buildPlan_premisesS}, {@code Plan.lean}).
 *
 * <p><b>The algorithm</b> is normative in full, so every implementation performs the same pivots
 * and returns the same weighting:
 * <ol>
 *   <li><i>Presolve.</i> {@code U} is the least set of places containing the coloured ones such
 *       that a row producing into {@code U} ({@code N_r[q] > 0} for some {@code q} in {@code U})
 *       has every place it consumes from ({@code N_r[p] < 0}) in {@code U}. The kept rows are the
 *       rows producing into {@code U}, in flat order, restricted to {@code U}; a kept row equal to
 *       an earlier one after the restriction is dropped. {@code U} is ordered ascending. The
 *       presolve does not change the optimum, and a presolve bug cannot make {@code k} unsound
 *       because the checker sees every flat row.</li>
 *   <li><i>The dual, in standard form:</i> maximise {@code c·σ} subject to {@code A·σ + s = b},
 *       {@code σ, s >= 0}, with one constraint row per place {@code U[i]}
 *       ({@code A[i][j] = pre - post} of kept row {@code j} at {@code U[i]},
 *       {@code b_i = M0[U[i]] >= 0}) and {@code c_j} kept row {@code j}'s net production into the
 *       coloured places. Columns are the kept rows {@code 0..m'} in order, then the slacks
 *       {@code m'..m'+n'} in the order of {@code U}. The slacks are the initial basis, feasible
 *       because {@code M0 >= 0}: no Phase I, no artificial variables, no big-M.</li>
 *   <li><i>Bland's rule.</i> Entering: the smallest column with a negative objective-row entry.
 *       Leaving: the least ratio {@code rhs_i / a_ie} over rows with {@code a_ie > 0}, ties to the
 *       row whose basic column is smallest. No negative entry: optimal. No positive entry in the
 *       entering column: the dual is unbounded, so the program is infeasible.</li>
 *   <li><i>The weighting.</i> With {@code π_i} the objective-row entry of slack column
 *       {@code m' + i}, {@code y_p = π_i + [p coloured]} for {@code p = U[i]} and {@code y_p = 0}
 *       off {@code U}. {@code D} is the least common multiple of the denominators of the
 *       {@code y_p} in lowest terms and {@code Y = y·D}.</li>
 * </ol>
 *
 * <p>Limits, both functions of the presolved program and the pivot sequence, so every
 * implementation refuses the same nets: {@link LpAnswer.TooLarge} past {@link #MAX_PLACES}
 * places or {@link #MAX_ROWS} rows after the presolve, before any pivot;
 * {@link LpAnswer.PivotLimit} past {@link #PIVOTS_PER_SIZE}{@code · (n' + m')} pivots. The solve
 * calls {@link VerificationDeadline#checkpoint()} before every pivot ([VER-013]), which throws
 * when the verification must stop; outside a {@code verify()} call (as in
 * {@code encodeScripts()}) the checkpoint does nothing. Each round of the loop decides in this
 * order: no entering column, optimal; no leaving row, infeasible; the limit's pivots already
 * made, pivot limit; a stop, stopped; otherwise pivot. A solve that ends without needing another
 * pivot is therefore never refused by the limit.
 *
 * <p>This mirrors the Rust reference {@code slot_bound_lp.rs}: the same pivots, the same
 * weighting, the same report lines and refusal reasons.
 */
public final class SlotBoundLp {

    private SlotBoundLp() {}

    /**
     * The largest colour-slot bound a plan may carry: the limit of Java's {@code int}, applied by
     * every implementation so that all three refuse the same nets (Lean {@code slotCap}).
     */
    public static final long SLOT_CAP = 2_147_483_647L;

    /** The most places the presolved program may have. */
    public static final int MAX_PLACES = 4096;

    /** The most rows (transitions) the presolved program may have. */
    public static final int MAX_ROWS = 16384;

    /** The pivot limit is this many pivots per presolved place and row. */
    public static final int PIVOTS_PER_SIZE = 50;

    /**
     * A weighting scaled to integers: {@code y_p = weights[p] / denominator}, one entry per flat
     * place.
     */
    public record ScaledCover(List<BigInteger> weights, BigInteger denominator) {
        public ScaledCover {
            weights = List.copyOf(weights);
        }
    }

    /** What {@link #solve} answers. {@code places} and {@code rows} are the presolved sizes. */
    public sealed interface LpAnswer {
        /** An optimal weighting, still to be re-checked. */
        record Optimal(ScaledCover cover, int places, int rows) implements LpAnswer {}

        /** No weighting satisfies the constraints: the coloured tokens are not structurally bounded. */
        record Infeasible(int places, int rows) implements LpAnswer {}

        /** The presolved program exceeds {@link #MAX_PLACES} or {@link #MAX_ROWS}. */
        record TooLarge(int places, int rows) implements LpAnswer {}

        /** No optimum within {@code limit} pivots. */
        record PivotLimit(int limit) implements LpAnswer {}

        /**
         * The verification was stopped ([VER-013]). {@link #solve} itself never answers it: its
         * checkpoint throws instead. It exists for a caller's own {@code lp} function.
         */
        record Stopped() implements LpAnswer {}
    }

    /** What {@link #checkCover} decides. */
    public sealed interface CoverCheck permits CheckedCover, CoverRefused {}

    /**
     * A weighting {@link #checkCover} accepted: {@code k = ⌊Y·M0 / D⌋} and the value
     * {@code Y·M0 / D} in lowest terms.
     */
    public record CheckedCover(int k, Rational value) implements CoverCheck {}

    /** A weighting {@link #checkCover} refused, with the first failing clause. */
    public record CoverRefused(String reason) implements CoverCheck {}

    /** The colour-slot bound as {@code buildPlan} receives it: {@link #checked} of the simplex's answer. */
    public sealed interface SlotBound {
        /** A re-checked weighting: the bound {@code k}, the weighting's value, the presolved sizes. */
        record Bound(int k, Rational value, int places, int rows) implements SlotBound {}

        record Infeasible(int places, int rows) implements SlotBound {}

        record TooLarge(int places, int rows) implements SlotBound {}

        record PivotLimit(int limit) implements SlotBound {}

        /** The simplex's weighting failed the exact re-check (a simplex bug); no bound. */
        record CheckFailed(String reason) implements SlotBound {}

        record Stopped() implements SlotBound {}

        /** The bound {@code k}, when there is one. */
        default OptionalInt bound() {
            return this instanceof Bound b ? OptionalInt.of(b.k()) : OptionalInt.empty();
        }

        /**
         * The report line, with its two-space indent and no newline. {@code null} for a stop:
         * the budget machinery reports that.
         */
        default String reportLine() {
            return switch (this) {
                case Bound b -> "  Colour-slot bound: LP optimum " + b.value() + " over " + b.places()
                    + " places and " + b.rows() + " transitions, so k=" + b.k()
                    + " (re-checked in exact arithmetic)";
                case Infeasible i -> "  Colour-slot bound: none (LP infeasible over " + i.places()
                    + " places and " + i.rows() + " transitions: no weighting bounds the coloured tokens)";
                case TooLarge t -> "  Colour-slot bound: none (LP over " + t.places() + " places and "
                    + t.rows() + " transitions exceeds the limit of " + MAX_PLACES + " places and "
                    + MAX_ROWS + " transitions)";
                case PivotLimit l -> "  Colour-slot bound: none (no LP optimum within the pivot limit of "
                    + l.limit() + ")";
                case CheckFailed f -> "  Colour-slot bound: none (LP weighting failed the exact re-check: "
                    + f.reason() + ")";
                case Stopped s -> null;
            };
        }
    }

    /**
     * The bound of whatever the simplex answered (Lean {@code colourSlotBoundLP}). An optimal
     * answer goes through {@link #checkCover}; every other answer passes through as no bound.
     * {@code k} never comes from an unchecked weighting.
     */
    public static SlotBound checked(FlatNet flat, MarkingState initial, int[] coloured, LpAnswer answer) {
        return switch (answer) {
            case LpAnswer.Optimal o -> switch (checkCover(flat, initial, coloured, o.cover())) {
                case CheckedCover c -> new SlotBound.Bound(c.k(), c.value(), o.places(), o.rows());
                case CoverRefused r -> new SlotBound.CheckFailed(r.reason());
            };
            case LpAnswer.Infeasible i -> new SlotBound.Infeasible(i.places(), i.rows());
            case LpAnswer.TooLarge t -> new SlotBound.TooLarge(t.places(), t.rows());
            case LpAnswer.PivotLimit l -> new SlotBound.PivotLimit(l.limit());
            case LpAnswer.Stopped s -> new SlotBound.Stopped();
        };
    }

    /**
     * The exact re-check of a scaled weighting (Lean {@code checkCover}). Accepts {@code (Y, D)}
     * exactly when, in unbounded integer arithmetic,
     * <ol>
     *   <li>{@code Y} has one entry per flat place;</li>
     *   <li>{@code D >= 1};</li>
     *   <li>{@code Y_p >= 0} for every place, in index order;</li>
     *   <li>{@code Y_p >= D} for every coloured place, ascending;</li>
     *   <li>{@code Σ_p Y_p·(post_r[p] - pre_r[p]) <= 0} for every flat row {@code r} of
     *       {@code flat.transitions()}, in flat order: all of them, never the presolved or
     *       deduplicated ones;</li>
     *   <li>with {@code V = Σ_p Y_p·M0[p]} and {@code k = V div D}, {@code k <=} {@link #SLOT_CAP}.</li>
     * </ol>
     * and then returns {@code k} and {@code V / D}. The first failing check names the refusal. A
     * coloured index outside the net is refused too; {@code buildPlan} never passes one.
     *
     * <p>{@code pre_r[p]} is the summed required count of the inputs on {@code p}; [CORE-030] AC3
     * rejects two input specs on one place, so it is the one spec's count Lean {@code dotIncD}
     * reads.
     */
    public static CoverCheck checkCover(FlatNet flat, MarkingState initial, int[] coloured, ScaledCover cover) {
        int n = flat.placeCount();
        List<BigInteger> y = cover.weights();
        BigInteger d = cover.denominator();
        if (y.size() != n) {
            return new CoverRefused("weighting has " + y.size() + " entries for " + n + " places");
        }
        if (d.signum() <= 0) {
            return new CoverRefused("denominator " + d + " is not positive");
        }
        for (int p = 0; p < n; p++) {
            if (y.get(p).signum() < 0) {
                return new CoverRefused("place '" + flat.places().get(p).name() + "' has negative weight " + y.get(p));
            }
        }
        int[] ascending = coloured.clone();
        Arrays.sort(ascending);
        for (int p : ascending) {
            if (p < 0 || p >= n) {
                return new CoverRefused("coloured place index " + p + " is out of range for " + n + " places");
            }
            if (y.get(p).compareTo(d) < 0) {
                return new CoverRefused("coloured place '" + flat.places().get(p).name() + "' has weight "
                    + y.get(p) + " below the denominator " + d);
            }
        }
        for (FlatTransition row : flat.transitions()) {
            BigInteger delta = BigInteger.ZERO;
            for (int p = 0; p < n; p++) {
                long column = (long) row.postVector()[p] - row.preVector()[p];
                if (column != 0) {
                    delta = delta.add(y.get(p).multiply(BigInteger.valueOf(column)));
                }
            }
            if (delta.signum() > 0) {
                return new CoverRefused("transition '" + row.name() + "' increases the weighted sum by " + delta);
            }
        }
        BigInteger v = BigInteger.ZERO;
        for (int p = 0; p < n; p++) {
            int m0 = initial.tokens(flat.places().get(p));
            if (m0 != 0) {
                v = v.add(y.get(p).multiply(BigInteger.valueOf(m0)));
            }
        }
        BigInteger k = v.divide(d);
        if (k.compareTo(BigInteger.valueOf(SLOT_CAP)) > 0) {
            return new CoverRefused("k=" + k + " exceeds " + SLOT_CAP);
        }
        return new CheckedCover(k.intValueExact(), Rational.of(v, d));
    }

    /**
     * Solves the colour-slot program for the coloured places {@code coloured} (flat indices).
     * Untrusted: see the class documentation.
     */
    public static LpAnswer solve(FlatNet flat, MarkingState initial, int[] coloured) {
        return solveCounted(flat, initial, coloured).answer();
    }

    /** {@link #solve}'s answer and the number of pivots it performed. */
    public record Solved(LpAnswer answer, int pivots) {}

    /** {@link #solve}, with the number of pivots it performed. */
    public static Solved solveCounted(FlatNet flat, MarkingState initial, int[] coloured) {
        int n = flat.placeCount();
        boolean[] isColoured = new boolean[n];
        for (int p : coloured) {
            if (p >= 0 && p < n) {
                isColoured[p] = true;
            }
        }
        Presolved program = presolve(flat, isColoured);
        int places = program.places.length;
        int rows = program.rows.size();
        if (places > MAX_PLACES || rows > MAX_ROWS) {
            return new Solved(new LpAnswer.TooLarge(places, rows), 0);
        }

        // Constraint row i is place U[i]: A[i][j] = -N_j[U[i]] for kept row j, then its slack.
        // Kept rows are visited in order, so every sparse row stays sorted by column.
        int[] lengths = new int[places];
        for (RestrictedRow row : program.rows) {
            for (int i : row.pos) {
                lengths[i]++;
            }
        }
        int[][] cols = new int[places][];
        Rational[][] vals = new Rational[places][];
        for (int i = 0; i < places; i++) {
            cols[i] = new int[lengths[i] + 1];
            vals[i] = new Rational[lengths[i] + 1];
        }
        int[] filled = new int[places];
        for (int j = 0; j < rows; j++) {
            RestrictedRow row = program.rows.get(j);
            for (int e = 0; e < row.pos.length; e++) {
                int i = row.pos[e];
                cols[i][filled[i]] = j;
                vals[i][filled[i]++] = Rational.of(-row.val[e]);
            }
        }
        SparseRow[] a = new SparseRow[places];
        for (int i = 0; i < places; i++) {
            cols[i][lengths[i]] = rows + i;
            vals[i][lengths[i]] = Rational.ONE;
            a[i] = new SparseRow(cols[i], vals[i], lengths[i] + 1);
        }
        Rational[] b = new Rational[places];
        for (int i = 0; i < places; i++) {
            b[i] = Rational.of(initial.tokens(flat.places().get(program.places[i])));
        }
        // The objective row starts at -c_j on the structural columns.
        int[] objCols = new int[rows];
        Rational[] objVals = new Rational[rows];
        int objSize = 0;
        for (int j = 0; j < rows; j++) {
            RestrictedRow row = program.rows.get(j);
            long c = 0;
            for (int e = 0; e < row.pos.length; e++) {
                if (isColoured[program.places[row.pos[e]]]) {
                    c += row.val[e];
                }
            }
            if (c != 0) {
                objCols[objSize] = j;
                objVals[objSize] = Rational.of(-c);
                objSize++;
            }
        }
        int[] basis = new int[places];
        for (int i = 0; i < places; i++) {
            basis[i] = rows + i;
        }
        var tableau = new Tableau(a, b, new SparseRow(objCols, objVals, objSize), Rational.ZERO, basis);
        int limit = PIVOTS_PER_SIZE * (places + rows);
        Outcome outcome = tableau.run(Rule.BLAND, limit, () -> {
            VerificationDeadline.checkpoint();
            return false;
        });
        LpAnswer answer = switch (outcome) {
            case OPTIMAL -> {
                Rational[] y = new Rational[n];
                Arrays.fill(y, Rational.ZERO);
                for (int i = 0; i < places; i++) {
                    int p = program.places[i];
                    Rational pi = tableau.obj.get(rows + i);
                    if (pi == null) {
                        pi = Rational.ZERO;
                    }
                    y[p] = isColoured[p] ? pi.add(Rational.ONE) : pi;
                }
                BigInteger denominator = BigInteger.ONE;
                for (Rational v : y) {
                    BigInteger g = denominator.gcd(v.denominator());
                    denominator = denominator.divide(g).multiply(v.denominator());
                }
                var weights = new ArrayList<BigInteger>(n);
                for (Rational v : y) {
                    weights.add(v.numerator().multiply(denominator.divide(v.denominator())));
                }
                yield new LpAnswer.Optimal(new ScaledCover(weights, denominator), places, rows);
            }
            case UNBOUNDED -> new LpAnswer.Infeasible(places, rows);
            case PIVOT_LIMIT -> new LpAnswer.PivotLimit(limit);
            case STOPPED -> new LpAnswer.Stopped();
        };
        return new Solved(answer, tableau.pivots);
    }

    /** A kept row: positions in {@code U} ascending and the row's column {@code post - pre} there. */
    record RestrictedRow(int[] pos, long[] val) {
        @Override
        public boolean equals(Object o) {
            return o instanceof RestrictedRow r && Arrays.equals(pos, r.pos) && Arrays.equals(val, r.val);
        }

        @Override
        public int hashCode() {
            return 31 * Arrays.hashCode(pos) + Arrays.hashCode(val);
        }
    }

    /**
     * The presolved program: the places of {@code U} ascending, and the kept rows, each a sparse
     * vector over positions in {@code U} of the row's column {@code post - pre}.
     */
    record Presolved(int[] places, List<RestrictedRow> rows) {}

    static Presolved presolve(FlatNet flat, boolean[] isColoured) {
        int n = flat.placeCount();
        int t = flat.transitionCount();
        int[][] colPlaces = new int[t][];
        long[][] colValues = new long[t][];
        for (int r = 0; r < t; r++) {
            FlatTransition ft = flat.transitions().get(r);
            int count = 0;
            for (int p = 0; p < n; p++) {
                if (ft.postVector()[p] != ft.preVector()[p]) {
                    count++;
                }
            }
            int[] ps = new int[count];
            long[] vs = new long[count];
            int e = 0;
            for (int p = 0; p < n; p++) {
                long v = (long) ft.postVector()[p] - ft.preVector()[p];
                if (v != 0) {
                    ps[e] = p;
                    vs[e] = v;
                    e++;
                }
            }
            colPlaces[r] = ps;
            colValues[r] = vs;
        }

        // The upstream cone, to a fixpoint. It is a set, so the visiting order is irrelevant.
        boolean[] inU = isColoured.clone();
        boolean changed = true;
        while (changed) {
            changed = false;
            for (int r = 0; r < t; r++) {
                if (producesInto(colPlaces[r], colValues[r], inU)) {
                    for (int e = 0; e < colPlaces[r].length; e++) {
                        int p = colPlaces[r][e];
                        if (colValues[r][e] < 0 && !inU[p]) {
                            inU[p] = true;
                            changed = true;
                        }
                    }
                }
            }
        }
        int size = 0;
        for (boolean b : inU) {
            if (b) {
                size++;
            }
        }
        int[] places = new int[size];
        int[] position = new int[n];
        Arrays.fill(position, -1);
        int next = 0;
        for (int p = 0; p < n; p++) {
            if (inU[p]) {
                position[p] = next;
                places[next++] = p;
            }
        }

        Set<RestrictedRow> seen = new HashSet<>();
        List<RestrictedRow> rows = new ArrayList<>();
        for (int r = 0; r < t; r++) {
            if (!producesInto(colPlaces[r], colValues[r], inU)) {
                continue;
            }
            int count = 0;
            for (int p : colPlaces[r]) {
                if (inU[p]) {
                    count++;
                }
            }
            int[] pos = new int[count];
            long[] val = new long[count];
            int e = 0;
            for (int i = 0; i < colPlaces[r].length; i++) {
                int p = colPlaces[r][i];
                if (inU[p]) {
                    pos[e] = position[p];
                    val[e] = colValues[r][i];
                    e++;
                }
            }
            var restricted = new RestrictedRow(pos, val);
            if (seen.add(restricted)) {
                rows.add(restricted);
            }
        }
        return new Presolved(places, rows);
    }

    private static boolean producesInto(int[] ps, long[] vs, boolean[] inU) {
        for (int e = 0; e < ps.length; e++) {
            if (vs[e] > 0 && inU[ps[e]]) {
                return true;
            }
        }
        return false;
    }

    // ---- the simplex core ----

    /** A sparse row: {@code (column, value)} pairs sorted by column, no zero value. */
    static final class SparseRow {
        final int[] cols;
        final Rational[] vals;
        final int size;

        SparseRow(int[] cols, Rational[] vals, int size) {
            this.cols = cols;
            this.vals = vals;
            this.size = size;
        }

        /** The entry at {@code col}, or {@code null} when it is zero. */
        Rational get(int col) {
            int i = Arrays.binarySearch(cols, 0, size, col);
            return i >= 0 ? vals[i] : null;
        }

        /** {@code this - f·prow}, zeros dropped. */
        SparseRow subtractScaled(Rational f, SparseRow prow) {
            int[] outCols = new int[size + prow.size];
            Rational[] outVals = new Rational[size + prow.size];
            int out = 0;
            int i = 0;
            int j = 0;
            while (i < size || j < prow.size) {
                int ci = i < size ? cols[i] : Integer.MAX_VALUE;
                int cj = j < prow.size ? prow.cols[j] : Integer.MAX_VALUE;
                if (ci < cj) {
                    outCols[out] = ci;
                    outVals[out++] = vals[i++];
                } else if (cj < ci) {
                    outCols[out] = cj;
                    outVals[out++] = f.multiply(prow.vals[j++]).negate();
                } else {
                    Rational v = vals[i].subtract(f.multiply(prow.vals[j]));
                    if (!v.isZero()) {
                        outCols[out] = ci;
                        outVals[out++] = v;
                    }
                    i++;
                    j++;
                }
            }
            return new SparseRow(outCols, outVals, out);
        }

        /** Every entry divided by {@code a}. */
        SparseRow divide(Rational a) {
            Rational[] out = new Rational[size];
            for (int i = 0; i < size; i++) {
                out[i] = vals[i].divide(a);
            }
            return new SparseRow(Arrays.copyOf(cols, size), out, size);
        }
    }

    /** The pivot rule. Only {@link #BLAND} is used outside tests. */
    enum Rule {
        /** Smallest entering column; least ratio, ties to the smallest basic column. */
        BLAND,
        /**
         * The most negative objective entry (smallest column on ties); least ratio, ties to the
         * lowest row. It can cycle, which is what the tests show.
         */
        LARGEST
    }

    enum Outcome { OPTIMAL, UNBOUNDED, PIVOT_LIMIT, STOPPED }

    /**
     * A maximisation tableau {@code z + Σ obj_j·x_j = objValue}, {@code rows·x = rhs}, one basic
     * column per row.
     */
    static final class Tableau {
        final SparseRow[] rows;
        final Rational[] rhs;
        SparseRow obj;
        Rational objValue;
        final int[] basis;
        /** Pivots performed so far. */
        int pivots;

        Tableau(SparseRow[] rows, Rational[] rhs, SparseRow obj, Rational objValue, int[] basis) {
            this.rows = rows;
            this.rhs = rhs;
            this.obj = obj;
            this.objValue = objValue;
            this.basis = basis;
        }

        /**
         * The standard form {@code max c·x} subject to {@code A·x <= b}, {@code x >= 0}, with
         * {@code b >= 0} and the slacks as the initial basis (columns {@code 0..c.length}
         * structural, then one slack per row). For tests.
         */
        static Tableau standard(Rational[][] a, Rational[] b, Rational[] c) {
            int m = c.length;
            SparseRow[] rows = new SparseRow[a.length];
            for (int i = 0; i < a.length; i++) {
                int[] cols = new int[a[i].length + 1];
                Rational[] vals = new Rational[a[i].length + 1];
                int size = 0;
                for (int j = 0; j < a[i].length; j++) {
                    if (!a[i][j].isZero()) {
                        cols[size] = j;
                        vals[size++] = a[i][j];
                    }
                }
                cols[size] = m + i;
                vals[size++] = Rational.ONE;
                rows[i] = new SparseRow(cols, vals, size);
            }
            int[] objCols = new int[m];
            Rational[] objVals = new Rational[m];
            int objSize = 0;
            for (int j = 0; j < m; j++) {
                if (!c[j].isZero()) {
                    objCols[objSize] = j;
                    objVals[objSize++] = c[j].negate();
                }
            }
            int[] basis = new int[a.length];
            for (int i = 0; i < a.length; i++) {
                basis[i] = m + i;
            }
            return new Tableau(rows, b.clone(), new SparseRow(objCols, objVals, objSize), Rational.ZERO, basis);
        }

        /** The entering column, or {@code -1} when the tableau is optimal. */
        int entering(Rule rule) {
            if (rule == Rule.BLAND) {
                for (int i = 0; i < obj.size; i++) {
                    if (obj.vals[i].signum() < 0) {
                        return obj.cols[i];
                    }
                }
                return -1;
            }
            int best = -1;
            for (int i = 0; i < obj.size; i++) {
                if (obj.vals[i].signum() < 0 && (best < 0 || obj.vals[i].compareTo(obj.vals[best]) < 0)) {
                    best = i;
                }
            }
            return best < 0 ? -1 : obj.cols[best];
        }

        /** The leaving row for entering column {@code e}, or {@code -1} when it is unbounded. */
        int leaving(Rule rule, int e) {
            int best = -1;
            Rational bestRatio = null;
            for (int i = 0; i < rows.length; i++) {
                Rational a = rows[i].get(e);
                if (a == null || a.signum() <= 0) {
                    continue;
                }
                Rational ratio = rhs[i].divide(a);
                boolean better;
                if (best < 0) {
                    better = true;
                } else {
                    int cmp = ratio.compareTo(bestRatio);
                    better = cmp < 0 || (cmp == 0 && rule == Rule.BLAND && basis[i] < basis[best]);
                }
                if (better) {
                    best = i;
                    bestRatio = ratio;
                }
            }
            return best;
        }

        void pivot(int r, int e) {
            Rational a = rows[r].get(e);
            SparseRow prow = rows[r].divide(a);
            Rational prhs = rhs[r].divide(a);
            for (int i = 0; i < rows.length; i++) {
                if (i == r) {
                    continue;
                }
                Rational f = rows[i].get(e);
                if (f != null) {
                    rows[i] = rows[i].subtractScaled(f, prow);
                    rhs[i] = rhs[i].subtract(f.multiply(prhs));
                }
            }
            Rational f = obj.get(e);
            if (f != null) {
                obj = obj.subtractScaled(f, prow);
                objValue = objValue.subtract(f.multiply(prhs));
            }
            rows[r] = prow;
            rhs[r] = prhs;
            basis[r] = e;
        }

        /**
         * Pivots until optimal or unbounded, at most {@code limit} times in all, polling
         * {@code stop} before every pivot.
         */
        Outcome run(Rule rule, int limit, BooleanSupplier stop) {
            while (true) {
                int e = entering(rule);
                if (e < 0) {
                    return Outcome.OPTIMAL;
                }
                int r = leaving(rule, e);
                if (r < 0) {
                    return Outcome.UNBOUNDED;
                }
                if (pivots >= limit) {
                    return Outcome.PIVOT_LIMIT;
                }
                if (stop.getAsBoolean()) {
                    return Outcome.STOPPED;
                }
                pivot(r, e);
                pivots++;
            }
        }
    }
}
