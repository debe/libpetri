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
