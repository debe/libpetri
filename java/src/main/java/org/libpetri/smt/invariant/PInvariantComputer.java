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
     * @return list of semi-positive P-invariants
     */
    public static List<PInvariant> compute(IncidenceMatrix matrix, FlatNet flatNet, MarkingState initialMarking) {
        int P = matrix.numPlaces();
        int T = matrix.numTransitions();

        if (P == 0 || T == 0) {
            return List.of();
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
        for (int row = 0; row < P; row++) {
            boolean isZero = true;
            for (int col = 0; col < T; col++) {
                if (augmented[row][col] != 0) {
                    isZero = false;
                    break;
                }
            }
            if (!isZero) continue;

            // Extract the weight vector from the identity part
            int[] weights = new int[P];
            boolean allNonNegative = true;
            boolean hasPositive = false;

            for (int i = 0; i < P; i++) {
                weights[i] = (int) augmented[row][T + i];
                if (weights[i] < 0) {
                    allNonNegative = false;
                    break;
                }
                if (weights[i] > 0) hasPositive = true;
            }

            // We want semi-positive invariants (all weights >= 0, at least one > 0)
            if (!allNonNegative) {
                // Try negating
                boolean allNonPositive = true;
                for (int i = 0; i < P; i++) {
                    if (augmented[row][T + i] > 0) {
                        allNonPositive = false;
                        break;
                    }
                }
                if (allNonPositive) {
                    for (int i = 0; i < P; i++) {
                        weights[i] = (int) -augmented[row][T + i];
                    }
                    hasPositive = true;
                    allNonNegative = true;
                }
            }

            if (!allNonNegative || !hasPositive) continue;

            // Normalize: divide by GCD of weights
            int gcd = 0;
            for (int w : weights) {
                if (w > 0) gcd = gcd(gcd, w);
            }
            if (gcd > 1) {
                for (int i = 0; i < P; i++) {
                    weights[i] /= gcd;
                }
            }

            // Compute support and constant
            var support = new TreeSet<Integer>();
            int constant = 0;
            for (int i = 0; i < P; i++) {
                if (weights[i] != 0) {
                    support.add(i);
                    var place = flatNet.places().get(i);
                    constant += weights[i] * initialMarking.tokens(place);
                }
            }

            invariants.add(new PInvariant(weights, constant, Set.copyOf(support)));
        }

        return List.copyOf(invariants);
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

    /** A generator row during Colom&ndash;Silva elimination: transition signature + place weight. */
    private record Row(long[] sig, long[] weight) {}

    /**
     * Divides a (signature, weight) pair by the gcd of all its entries to keep the
     * integers small during elimination.
     */
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

    private static int gcd(int a, int b) {
        while (b != 0) {
            int t = b;
            b = a % b;
            a = t;
        }
        return a;
    }
}
