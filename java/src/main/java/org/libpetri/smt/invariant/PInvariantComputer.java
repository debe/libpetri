package org.libpetri.smt.invariant;

import org.libpetri.analysis.MarkingState;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.IncidenceMatrix;

import java.util.*;

/**
 * Computes P-invariants of a Petri net via integer Gaussian elimination.
 *
 * <p>P-invariants are non-negative integer vectors y where y^T * C = 0.
 * They express conservation laws: the weighted token sum is constant
 * across all reachable markings.
 *
 * <p>Algorithm: compute the null space of C^T using integer row reduction
 * with an augmented identity matrix (Farkas' algorithm variant).
 */
public final class PInvariantComputer {

    private PInvariantComputer() {}

    /**
     * Computes P-invariants for a flat net.
     *
     * @param matrix  the incidence matrix
     * @param flatNet the flat net (for place info)
     * @param initialMarking the initial marking (for computing constants)
     * @return the null-space basis of conservation laws (signed, GCD-normalised)
     */
    public static List<PInvariant> compute(IncidenceMatrix matrix, FlatNet flatNet, MarkingState initialMarking) {
        return computeChecked(matrix, flatNet, initialMarking).valid();
    }

    /**
     * {@link #compute}, reporting the candidates it had to drop.
     *
     * <p>The elimination runs in {@code long} but {@link PInvariant#weights()} and
     * {@link PInvariant#constant()} are {@code int}: a row whose exact weight or
     * {@code y*M0} does not fit that range is DROPPED with a reason rather than
     * narrowed. Narrowing wraps, and a wrapped "invariant" conjoined into a CHC
     * transition-rule body removes reachable successors — the false-PROVEN shape.
     * {@link #validateExact} remains the backstop for rows the unchecked
     * elimination itself corrupted.
     *
     * @param matrix  the incidence matrix
     * @param flatNet the flat net (for place info and drop-reason place names)
     * @param initialMarking the initial marking (for computing constants)
     * @return the extracted P-invariants plus one reason per drop
     */
    public static Validation computeChecked(
            IncidenceMatrix matrix, FlatNet flatNet, MarkingState initialMarking) {
        int P = matrix.numPlaces();
        int T = matrix.numTransitions();

        if (P == 0 || T == 0) {
            return new Validation(List.of(), List.of());
        }

        // We want to find y such that y^T * C = 0, i.e., C^T * y = 0
        // Use the Farkas/integer elimination approach:
        // Start with augmented matrix [C^T | I_P]
        // Row-reduce C^T part to zero; the I_P part gives the invariant vectors.

        int[][] ct = matrix.transposedIncidence(); // P x T

        // Augmented matrix: P rows, T + P columns
        // [ct[0..P-1][0..T-1] | identity[0..P-1][0..P-1]]
        int cols = T + P;
        long[][] augmented = new long[P][cols];
        for (int i = 0; i < P; i++) {
            for (int j = 0; j < T; j++) {
                augmented[i][j] = ct[i][j];
            }
            augmented[i][T + i] = 1; // identity part
        }

        // Integer Gaussian elimination on the C^T part (columns 0..T-1)
        int pivotRow = 0;
        for (int col = 0; col < T && pivotRow < P; col++) {
            // Find pivot (non-zero entry in this column)
            int pivot = -1;
            for (int row = pivotRow; row < P; row++) {
                if (augmented[row][col] != 0) {
                    pivot = row;
                    break;
                }
            }
            if (pivot == -1) continue; // free variable

            // Swap pivot row
            if (pivot != pivotRow) {
                var tmp = augmented[pivotRow];
                augmented[pivotRow] = augmented[pivot];
                augmented[pivot] = tmp;
            }

            // Eliminate this column in all other rows
            for (int row = 0; row < P; row++) {
                if (row == pivotRow || augmented[row][col] == 0) continue;

                long a = augmented[pivotRow][col];
                long b = augmented[row][col];

                // row = a*row - b*pivotRow (keeps integers, eliminates col)
                for (int c = 0; c < cols; c++) {
                    augmented[row][c] = a * augmented[row][c] - b * augmented[pivotRow][c];
                }

                // Normalize by GCD to keep values small
                normalizeRow(augmented[row], cols);
            }

            pivotRow++;
        }

        // Extract invariants: rows where C^T part is all zeros
        var invariants = new ArrayList<PInvariant>();
        var dropped = new ArrayList<String>();
        for (int row = 0; row < P; row++) {
            boolean isZero = true;
            for (int col = 0; col < T; col++) {
                if (augmented[row][col] != 0) {
                    isZero = false;
                    break;
                }
            }
            if (!isZero) continue;

            // Extract the weight vector from the identity part, still in long.
            long[] weightsL = new long[P];
            boolean hasPositive = false;
            boolean hasNegative = false;
            for (int i = 0; i < P; i++) {
                weightsL[i] = augmented[row][T + i];
                if (weightsL[i] > 0) hasPositive = true;
                if (weightsL[i] < 0) hasNegative = true;
            }

            // A signed null-space basis, exactly as the Rust reference computes it
            // (VER-013 script parity): a mixed-sign row is a conservation law like any
            // other and passes the same exact gate; a semi-negative row is the same law
            // negated. Non-negativity is only required of the P-semiflows that bound
            // the colour slots (computePSemiflows), never of the strengthening laws.
            if (!hasPositive && !hasNegative) continue;
            if (!hasPositive) {
                for (int i = 0; i < P; i++) {
                    weightsL[i] = -weightsL[i];
                }
            }

            // No renormalisation here: every eliminated row was GCD-normalised over
            // all of its entries above, and an untouched identity row is a unit
            // vector. (A positives-only GCD would corrupt a signed row such as
            // (2, -3).)

            // Narrow to int and accumulate the constant with checked arithmetic; the
            // first out-of-range step names the offending place.
            int[] weights = new int[P];
            var support = new TreeSet<Integer>();
            long constant = 0;
            String overflow = null;
            for (int i = 0; i < P; i++) {
                long w = weightsL[i];
                if (w > Integer.MAX_VALUE || w < Integer.MIN_VALUE) {
                    overflow = overflowReason(flatNet, i);
                    break;
                }
                weights[i] = (int) w;
                if (w == 0) continue;
                support.add(i);
                try {
                    constant = Math.addExact(constant, Math.multiplyExact(
                        w, (long) initialMarking.tokens(flatNet.places().get(i))));
                } catch (ArithmeticException _) {
                    overflow = overflowReason(flatNet, i);
                    break;
                }
                if (constant > Integer.MAX_VALUE || constant < Integer.MIN_VALUE) {
                    overflow = overflowReason(flatNet, i);
                    break;
                }
            }
            if (overflow != null) {
                dropped.add(overflow);
                continue;
            }

            invariants.add(new PInvariant(weights, (int) constant, Set.copyOf(support)));
        }

        return new Validation(List.copyOf(invariants), List.copyOf(dropped));
    }

    /**
     * The one canonical overflow drop reason, shared by every stage that can detect
     * an overflow — {@link #computeChecked}'s narrowing and {@link #validateExact}'s
     * exact recheck alike — and byte-identical across the four implementations. It
     * names the place whose term could not be represented.
     */
    private static String overflowReason(FlatNet flatNet, int place) {
        return "weight overflow at place '" + flatNet.places().get(place).name()
            + "' (exact value outside this implementation's integer extraction range)";
    }

    /**
     * Computes the minimal <b>P-semiflows</b> — non-negative place weightings {@code y}
     * with {@code y^T·C = 0} — via the Colom&ndash;Silva / Farkas method. Unlike
     * {@link #compute} (a signed null-space basis), every returned
     * {@link PInvariant#weights()} is non-negative, a genuine P-semiflow, with
     * {@code constant = y·M0}. A non-negative conservation law soundly <b>bounds</b> the
     * token sum over its support: {@code sum_{support} M(p) <= y·M0}. Used to bound the
     * number of simultaneously-live colours in the name-coloured encoder.
     *
     * @param matrix         the incidence matrix
     * @param flatNet        the flat net (for place info)
     * @param initialMarking the initial marking (for computing constants)
     * @return list of non-negative P-semiflows
     */
    public static List<PInvariant> computePSemiflows(
            IncidenceMatrix matrix, FlatNet flatNet, MarkingState initialMarking) {
        int np = matrix.numPlaces();
        int nt = matrix.numTransitions();
        if (np == 0) {
            return List.of();
        }
        int[][] incidence = matrix.incidence(); // [t][p]

        // Each generator row = (signature over transitions, non-negative weight over
        // places). Start with one row per place: signature = that place's column of C,
        // weight = e_p. Eliminate one transition column at a time using only non-negative
        // combinations, so the accumulated weights stay non-negative.
        var rows = new ArrayList<Row>(np);
        for (int pl = 0; pl < np; pl++) {
            long[] sig = new long[nt];
            for (int t = 0; t < nt; t++) {
                sig[t] = incidence[t][pl];
            }
            long[] weight = new long[np];
            weight[pl] = 1;
            rows.add(new Row(sig, weight));
        }

        for (int t = 0; t < nt; t++) {
            var next = new ArrayList<Row>();
            var pos = new ArrayList<Row>();
            var neg = new ArrayList<Row>();
            for (Row r : rows) {
                if (r.sig[t] == 0) {
                    next.add(r);
                } else if (r.sig[t] > 0) {
                    pos.add(r);
                } else {
                    neg.add(r);
                }
            }
            for (Row rp : pos) {
                for (Row rn : neg) {
                    long cp = -rn.sig[t]; // > 0
                    long cn = rp.sig[t];  // > 0
                    // Checked combination: on long overflow DROP this generator rather
                    // than keep a wrapped (invalid) row. Dropping it can at worst lose a
                    // covering semiflow, so colourSlotBound falls back to the sound
                    // over-approximation — never an under-approximation.
                    long[] sig = combineRow(cp, rp.sig, cn, rn.sig);
                    long[] weight = combineRow(cp, rp.weight, cn, rn.weight);
                    if (sig == null || weight == null) {
                        continue;
                    }
                    reduceGcd(sig, weight);
                    next.add(new Row(sig, weight));
                }
            }
            rows = keepSupportMinimal(next);
            if (rows.size() > 8192) {
                rows.subList(8192, rows.size()).clear(); // safety backstop against blow-up
            }
        }

        var semiflows = new ArrayList<PInvariant>();
        for (Row r : rows) {
            boolean anyNonZero = false;
            for (long x : r.weight) {
                if (x != 0) {
                    anyNonZero = true;
                    break;
                }
            }
            if (!anyNonZero) {
                continue;
            }
            int[] weights = new int[np];
            var support = new TreeSet<Integer>();
            long constant = 0;
            boolean overflow = false;
            for (int pl = 0; pl < np; pl++) {
                long wl = r.weight[pl];
                if (wl > Integer.MAX_VALUE || wl < Integer.MIN_VALUE) {
                    overflow = true;
                    break;
                }
                weights[pl] = (int) wl;
                if (wl != 0) {
                    support.add(pl);
                    try {
                        long term = Math.multiplyExact(
                                wl, (long) initialMarking.tokens(flatNet.places().get(pl)));
                        constant = Math.addExact(constant, term);
                    } catch (ArithmeticException e) {
                        overflow = true;
                        break;
                    }
                }
            }
            // Drop a semiflow whose weight or `Σ weight·M0` does not fit int — fewer
            // covering semiflows just means colourSlotBound falls back soundly.
            if (overflow || constant > Integer.MAX_VALUE || constant < Integer.MIN_VALUE) {
                continue;
            }
            semiflows.add(new PInvariant(weights, (int) constant, Set.copyOf(support)));
        }
        return List.copyOf(semiflows);
    }

    /**
     * Outcome of {@link #validateExact}: the candidates that re-verified exactly, plus one
     * human-readable reason per dropped candidate.
     *
     * @param valid   invariants whose {@code y^T·C = 0} and {@code constant = y·M0} were
     *                re-established with overflow-checked arithmetic
     * @param dropped one reason string per rejected invariant (place names, not indices)
     */
    public record Validation(List<PInvariant> valid, List<String> dropped) {}

    /**
     * Exactly re-verifies each candidate invariant against the incidence matrix and the
     * initial marking, dropping any candidate that fails.
     *
     * <p>The elimination in {@link #compute} uses unchecked {@code long} arithmetic and
     * truncates the extracted weights to {@code int}; on adversarial nets (very large arc
     * weights) that can emit a numerically wrong "invariant". A wrong invariant conjoined
     * into the CHC transition-rule body removes reachable successors — it can certify a
     * false PROVEN — so every candidate is re-checked here before it may reach an encoder:
     *
     * <ul>
     *   <li><b>H1 linearity guard</b> ({@code lean/Libpetri/Strengthening.lean},
     *       {@code consume_all_hypothesis_is_necessary}): a candidate with nonzero weight
     *       on a place that any flat transition consume-all drains ({@code In.All} /
     *       {@code In.AtLeast} — both consume ALL available tokens per
     *       {@code Arc.In#consumptionCount} and IO-007) or resets is dropped outright.
     *       Those arms set {@code M'[p] = post[p]} in the encoder's fire relation; the
     *       linearized incidence column cannot express them, so {@code y·C = 0} is
     *       necessary but not sufficient on their support. Env-injectable places need no
     *       analogous treatment: the injector columns already force {@code y = 0} there
     *       via {@code y·C = 0} (Strengthening.lean H3&prime;).</li>
     *   <li>{@code y·C} is recomputed per transition column with
     *       {@link Math#multiplyExact(long, long)} / {@link Math#addExact(long, long)};
     *       every component must be exactly 0. Weights and incidence entries are
     *       {@code int}, so each product fits a {@code long} exactly — only the running
     *       sum can overflow, which {@code addExact} detects.</li>
     *   <li>{@code y·M0} is recomputed the same way and must equal
     *       {@link PInvariant#constant()}.</li>
     *   <li>Overflow ({@link ArithmeticException}) or any mismatch drops the candidate
     *       with a reason. Dropping only weakens the strengthening (resp. loses a
     *       covering semiflow, so the colour bound falls back soundly) — it never
     *       affects soundness.</li>
     * </ul>
     *
     * <p>The drop reasons are canonical strings: the Java, TypeScript, Rust and
     * Python verifiers emit them byte-identically, so keep the wording (here and in
     * {@link #computeChecked}) in sync when it changes. A dropped candidate renders
     * as {@code <description> - <reason>}, with an ASCII hyphen-minus separator —
     * never an em dash, which would break a byte-for-byte cross-language diff — and
     * an overflow at any stage uses the single {@link #overflowReason} wording.
     *
     * @param candidates     invariants to re-verify (from {@link #compute} or
     *                       {@link #computePSemiflows})
     * @param matrix         the incidence matrix the candidates were computed from
     * @param flatNet        the flat net (for place/transition names in drop reasons)
     * @param initialMarking the initial marking the constants were computed from
     * @return the exactly-validated invariants plus a drop reason per rejected one
     */
    public static Validation validateExact(
            List<PInvariant> candidates, IncidenceMatrix matrix,
            FlatNet flatNet, MarkingState initialMarking) {
        int[][] incidence = matrix.incidence(); // [t][p], includes env-injector columns
        int nt = matrix.numTransitions();
        int np = matrix.numPlaces();
        // The H1 place set depends only on the net, not on the candidate: walking every
        // flat transition once here instead of per candidate.
        boolean[] nonlinear = nonlinearPlaces(flatNet, np);
        var valid = new ArrayList<PInvariant>(candidates.size());
        var dropped = new ArrayList<String>();
        for (var inv : candidates) {
            String failure = recheckExact(inv, incidence, nt, np, nonlinear, flatNet, initialMarking);
            if (failure == null) {
                valid.add(inv);
            } else {
                // ASCII " - ", never an em dash: the four implementations' report
                // lines are diffed byte-for-byte.
                dropped.add(describe(inv, flatNet) + " - " + failure);
            }
        }
        return new Validation(List.copyOf(valid), List.copyOf(dropped));
    }

    /**
     * Re-verifies one invariant exactly; returns {@code null} on success or the reason to
     * drop it.
     */
    private static String recheckExact(
            PInvariant inv, int[][] incidence, int nt, int np, boolean[] nonlinear,
            FlatNet flatNet, MarkingState initialMarking) {
        int[] weights = inv.weights();
        if (weights.length != np) {
            return "weight vector has " + weights.length + " entries for " + np + " places";
        }
        // H1 linearity guard (lean/Libpetri/Strengthening.lean: `ZeroOnNonlinear`,
        // shown live by `consume_all_hypothesis_is_necessary`). The incidence column
        // linearizes consumption — pre[p] is Arc.In#requiredCount() and reset places
        // never enter it at all — but the encoder's fire relation (SmtEncoder, matching
        // the runtime) has two NON-linear arms that set M'[p] = post[p] outright:
        //   (a) consume-all inputs — In.All AND In.AtLeast. Both drain the place:
        //       Arc.In#consumptionCount(available) returns `available` for both
        //       (spec/02-input-output-specs.md, IO-007), and NetFlattener flags both
        //       in FlatTransition#consumeAll. Only In.One / In.Exactly consume exactly
        //       requiredCount and stay linear.
        //   (b) reset places (FlatTransition#resetPlaces), cleared before post.
        // The y*C = 0 recheck below is blind to both arms, so a candidate weighted on
        // such a place can pass the numeric gate yet be falsified by one real firing;
        // conjoined into a CHC rule body it would prune genuine successors — the
        // false-Proven shape. Drop it before it can reach an encoder.
        // Env-injectable places need NO analogous guard here: the injector columns that
        // IncidenceMatrix#from appends already force y[envPlace] = 0 through this same
        // y*C = 0 recheck (Strengthening.lean H3').
        for (int p = 0; p < np; p++) {
            if (weights[p] != 0 && nonlinear[p]) {
                return nonlinearReason(flatNet, p);
            }
        }
        for (int t = 0; t < nt; t++) {
            long component = 0;
            for (int p = 0; p < np; p++) {
                if (weights[p] == 0 || incidence[t][p] == 0) continue;
                try {
                    component = Math.addExact(component,
                        Math.multiplyExact((long) weights[p], (long) incidence[t][p]));
                } catch (ArithmeticException _) {
                    // One overflow reason for the whole pipeline, naming the place
                    // whose term could not be recomputed — same text as extraction.
                    return overflowReason(flatNet, p);
                }
            }
            if (component != 0) {
                return "y*C is " + component + " (not 0) at " + columnName(t, flatNet);
            }
        }
        long constant = 0;
        for (int p = 0; p < np; p++) {
            if (weights[p] == 0) continue;
            try {
                constant = Math.addExact(constant, Math.multiplyExact(
                    (long) weights[p], (long) initialMarking.tokens(flatNet.places().get(p))));
            } catch (ArithmeticException _) {
                return overflowReason(flatNet, p);
            }
        }
        if (constant != inv.constant()) {
            return "constant " + inv.constant() + " does not match exact y*M0 = " + constant;
        }
        return null;
    }

    /**
     * Places some flat transition consumes non-linearly: consume-all inputs
     * ({@code In.All} / {@code In.AtLeast}) and reset places — the H1 arms.
     */
    private static boolean[] nonlinearPlaces(FlatNet flatNet, int np) {
        var nonlinear = new boolean[np];
        for (var ft : flatNet.transitions()) {
            boolean[] consumeAll = ft.consumeAll();
            for (int p = 0; p < np && p < consumeAll.length; p++) {
                if (consumeAll[p]) {
                    nonlinear[p] = true;
                }
            }
            for (int rp : ft.resetPlaces()) {
                if (rp >= 0 && rp < np) {
                    nonlinear[rp] = true;
                }
            }
        }
        return nonlinear;
    }

    /** The H1 drop reason (canonical wording — see {@link #validateExact}). */
    private static String nonlinearReason(FlatNet flatNet, int place) {
        return "support intersects consume-all/reset place '" + flatNet.places().get(place).name()
            + "' (non-linear consumption; see Strengthening.lean H1)";
    }

    /** Names an incidence-matrix column: a flat transition or an env-injector column. */
    private static String columnName(int t, FlatNet flatNet) {
        return t < flatNet.transitionCount()
            ? "transition '" + flatNet.transitions().get(t).name() + "'"
            : "env-injector column " + (t - flatNet.transitionCount());
    }

    /**
     * Formats an invariant with place names, e.g. {@code 2*A + B = 3} — the report
     * rendering for both the kept invariants and the drop-reason lines.
     */
    public static String describe(PInvariant inv, FlatNet flatNet) {
        var sb = new StringBuilder();
        boolean first = true;
        for (int idx : inv.support()) {
            if (!first) sb.append(" + ");
            long w = idx < inv.weights().length ? inv.weights()[idx] : 0;
            if (w != 1) sb.append(w).append("*");
            sb.append(idx < flatNet.placeCount() ? flatNet.places().get(idx).name() : "p" + idx);
            first = false;
        }
        if (first) sb.append("0");
        return sb.append(" = ").append(inv.constant()).toString();
    }

    /** A generator row during Colom&ndash;Silva elimination: transition signature + place weight. */
    private record Row(long[] sig, long[] weight) {}

    /**
     * {@code cp*a + cn*b} componentwise, or {@code null} on long overflow (so the caller
     * drops the generator and the colour bound falls back soundly rather than using
     * wrapped values).
     */
    private static long[] combineRow(long cp, long[] a, long cn, long[] b) {
        long[] out = new long[a.length];
        try {
            for (int i = 0; i < a.length; i++) {
                out[i] = Math.addExact(Math.multiplyExact(cp, a[i]), Math.multiplyExact(cn, b[i]));
            }
        } catch (ArithmeticException e) {
            return null;
        }
        return out;
    }

    /**
     * Divides a (signature, weight) pair by the gcd of all its entries to keep the
     * integers small during elimination.
     */
    private static void reduceGcd(long[] sig, long[] weight) {
        long g = 0;
        for (long v : sig) {
            g = gcd(g, Math.abs(v));
        }
        for (long v : weight) {
            g = gcd(g, Math.abs(v));
        }
        if (g > 1) {
            for (int i = 0; i < sig.length; i++) {
                sig[i] /= g;
            }
            for (int i = 0; i < weight.length; i++) {
                weight[i] /= g;
            }
        }
    }

    /**
     * Drops any row whose weight-support is a strict superset of another's — a
     * non-minimal combination that only inflates the set (and can cause combinatorial
     * blow-up).
     */
    private static ArrayList<Row> keepSupportMinimal(ArrayList<Row> rows) {
        int n = rows.size();
        var supports = new ArrayList<Set<Integer>>(n);
        for (Row r : rows) {
            var s = new HashSet<Integer>();
            for (int i = 0; i < r.weight.length; i++) {
                if (r.weight[i] != 0) {
                    s.add(i);
                }
            }
            supports.add(s);
        }
        var keep = new boolean[n];
        Arrays.fill(keep, true);
        for (int i = 0; i < n; i++) {
            if (!keep[i]) {
                continue;
            }
            for (int j = 0; j < n; j++) {
                if (i == j || !keep[j]) {
                    continue;
                }
                if (supports.get(j).size() < supports.get(i).size()
                        && supports.get(i).containsAll(supports.get(j))) {
                    keep[i] = false;
                    break;
                }
            }
        }
        var out = new ArrayList<Row>();
        for (int i = 0; i < n; i++) {
            if (keep[i]) {
                out.add(rows.get(i));
            }
        }
        return out;
    }

    /**
     * Checks if every place is covered by at least one P-invariant.
     * If true, the net is structurally bounded.
     */
    public static boolean isCoveredByInvariants(List<PInvariant> invariants, int numPlaces) {
        var covered = new boolean[numPlaces];
        for (var inv : invariants) {
            // Only a non-negative law bounds its support; a mixed-sign law (which the
            // signed null-space basis now carries) says nothing about boundedness.
            boolean nonNegative = true;
            for (int w : inv.weights()) {
                if (w < 0) {
                    nonNegative = false;
                    break;
                }
            }
            if (!nonNegative) {
                continue;
            }
            for (int idx : inv.support()) {
                if (idx < numPlaces) {
                    covered[idx] = true;
                }
            }
        }
        for (boolean c : covered) {
            if (!c) return false;
        }
        return true;
    }

    private static void normalizeRow(long[] row, int cols) {
        long g = 0;
        for (int c = 0; c < cols; c++) {
            if (row[c] != 0) {
                g = gcd(g, Math.abs(row[c]));
            }
        }
        if (g > 1) {
            for (int c = 0; c < cols; c++) {
                row[c] /= g;
            }
        }
    }

    private static long gcd(long a, long b) {
        while (b != 0) {
            long t = b;
            b = a % b;
            a = t;
        }
        return a;
    }
}
