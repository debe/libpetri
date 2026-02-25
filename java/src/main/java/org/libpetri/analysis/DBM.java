package org.libpetri.analysis;

import java.util.Arrays;
import java.util.List;

/**
 * Difference Bound Matrix (DBM) for Time Petri Net state class analysis.
 * <p>
 * Implements the Berthomieu-Diaz (1991) algorithm for computing firing domains
 * and their successors. This is the mathematically correct representation for
 * Time Petri Net verification.
 *
 * <h2>Mathematical Foundation</h2>
 * <p>
 * A firing domain D for enabled transitions {t₁, ..., tₙ} is a convex polyhedron:
 * <pre>
 *   D = { (θ₁, ..., θₙ) ∈ ℝⁿ | αᵢ ≤ θᵢ ≤ βᵢ  ∧  θᵢ - θⱼ ≤ cᵢⱼ }
 * </pre>
 * where θᵢ represents the time until transition tᵢ fires.
 *
 * <h2>DBM Representation</h2>
 * <p>
 * The domain is stored as a (n+1)×(n+1) matrix where:
 * <ul>
 *   <li>Index 0 = reference clock (always 0)</li>
 *   <li>Index i+1 = clock for transition i</li>
 *   <li>bounds[i][j] = upper bound on (xᵢ - xⱼ)</li>
 * </ul>
 * <p>
 * Encoding of interval constraints [α, β]:
 * <ul>
 *   <li>θᵢ ≥ α  ⟺  -θᵢ ≤ -α  ⟺  x₀ - xᵢ ≤ -α  ⟺  bounds[0][i+1] = -α</li>
 *   <li>θᵢ ≤ β  ⟺  xᵢ - x₀ ≤ β  ⟺  bounds[i+1][0] = β</li>
 * </ul>
 *
 * <h2>Key Operations (Berthomieu-Diaz 1991)</h2>
 * <ol>
 *   <li><b>Canonicalization</b>: Floyd-Warshall to derive tightest bounds</li>
 *   <li><b>Successor</b>: Fire transition, compute new domain via:
 *       intersection → substitution → elimination → add fresh clocks → canonicalize</li>
 * </ol>
 *
 * <h2>References</h2>
 * <ul>
 *   <li>Berthomieu, Diaz: "Modeling and verification of time dependent systems
 *       using Time Petri Nets", IEEE TSE 1991</li>
 *   <li>Gardey, Roux, Roux: "State Space Computation and Analysis of Time
 *       Petri Nets", STTT 2006</li>
 * </ul>
 */
public final class DBM {

    private static final double INF = Double.POSITIVE_INFINITY;
    private static final double EPSILON = 1e-9;

    /** DBM matrix: bounds[i][j] = upper bound on (xᵢ - xⱼ) */
    private final double[][] bounds;

    /** Ordered list of transition names (defines clock indices) */
    private final List<String> clockNames;

    /** Whether the zone is empty (unsatisfiable) */
    private final boolean empty;

    private DBM(double[][] bounds, List<String> clockNames, boolean empty) {
        this.bounds = bounds;
        this.clockNames = List.copyOf(clockNames);
        this.empty = empty;
    }

    /**
     * Creates an initial firing domain for enabled transitions.
     * <p>
     * For each transition tᵢ with interval [αᵢ, βᵢ]:
     * <ul>
     *   <li>θᵢ ≥ αᵢ (earliest firing time)</li>
     *   <li>θᵢ ≤ βᵢ (latest firing time / deadline)</li>
     * </ul>
     *
     * @param clockNames transition names
     * @param lowerBounds αᵢ values (in seconds)
     * @param upperBounds βᵢ values (in seconds)
     * @return canonicalized DBM
     */
    public static DBM create(List<String> clockNames, double[] lowerBounds, double[] upperBounds) {
        int n = clockNames.size();
        double[][] bounds = new double[n + 1][n + 1];

        // Initialize: no constraint between different clocks
        for (int i = 0; i <= n; i++) {
            Arrays.fill(bounds[i], INF);
            bounds[i][i] = 0;
        }

        // Set interval constraints
        for (int i = 0; i < n; i++) {
            bounds[0][i + 1] = -lowerBounds[i];  // θᵢ ≥ αᵢ
            bounds[i + 1][0] = upperBounds[i];   // θᵢ ≤ βᵢ
        }

        return new DBM(bounds, clockNames, false).canonicalize();
    }

    /**
     * Creates an empty (unsatisfiable) zone.
     */
    public static DBM empty(List<String> clockNames) {
        return new DBM(new double[1][1], clockNames, true);
    }

    public boolean isEmpty() {
        return empty;
    }

    public int clockCount() {
        return clockNames.size();
    }

    public List<String> clockNames() {
        return clockNames;
    }

    /**
     * Gets the lower bound (earliest firing time) for clock i.
     * θᵢ ≥ -bounds[0][i+1]
     */
    public double getLowerBound(int clockIndex) {
        if (empty || clockIndex < 0 || clockIndex >= clockNames.size()) return 0;
        return -bounds[0][clockIndex + 1];
    }

    /**
     * Gets the upper bound (latest firing time / deadline) for clock i.
     * θᵢ ≤ bounds[i+1][0]
     */
    public double getUpperBound(int clockIndex) {
        if (empty || clockIndex < 0 || clockIndex >= clockNames.size()) return INF;
        return bounds[clockIndex + 1][0];
    }

    /**
     * Checks if transition can fire now (lower bound ≤ 0 after time passage).
     */
    public boolean canFire(int clockIndex) {
        return !empty && getLowerBound(clockIndex) <= EPSILON;
    }

    /**
     * Computes the successor firing domain after firing transition t_f.
     * <p>
     * <b>Algorithm (Berthomieu-Diaz 1991, Theorem 1):</b>
     * <pre>
     * succ((M, D), t_f) = (M', D') where:
     *
     * 1. D₁ = D ∩ {θ_f ≤ θᵢ for all i ≠ f}    // t_f fires first
     * 2. D₂ = D₁ ∩ {θ_f ≥ 0}                  // t_f is fireable
     * 3. D₃ = substitute θᵢ' := θᵢ - θ_f      // shift time origin
     * 4. D₄ = eliminate θ_f from D₃           // Fourier-Motzkin
     * 5. D' = D₄ ∪ fresh intervals for newly enabled transitions
     * </pre>
     *
     * <h3>Detailed Derivation</h3>
     * <p>
     * After firing t_f at time θ_f, the remaining time for persistent transition tᵢ is:
     * <pre>
     *   θᵢ' = θᵢ - θ_f
     * </pre>
     * <p>
     * The constraints transform as:
     * <ul>
     *   <li>θᵢ' ≤ θⱼ' ⟺ θᵢ - θ_f ≤ θⱼ - θ_f ⟺ θᵢ ≤ θⱼ (unchanged!)</li>
     *   <li>θᵢ' ≥ 0 ⟺ θᵢ ≥ θ_f (must hold since t_f fires first among those with min deadline)</li>
     *   <li>θᵢ' ≤ β ⟺ θᵢ - θ_f ≤ β</li>
     * </ul>
     * <p>
     * From the constrained DBM (after intersection):
     * <ul>
     *   <li>θᵢ' upper = θᵢ - θ_f max = bounds[i+1][f+1] (from constraint θᵢ - θ_f ≤ bounds[i+1][f+1])</li>
     *   <li>θᵢ' lower = max(0, -bounds[f+1][i+1]) (since θ_f - θᵢ ≤ bounds[f+1][i+1])</li>
     * </ul>
     *
     * @param firedClock index of fired transition in current clock list
     * @param newClockNames names of newly enabled transitions
     * @param newLowerBounds α values for newly enabled transitions
     * @param newUpperBounds β values for newly enabled transitions
     * @param persistentClocks indices of transitions that remain enabled
     * @return the successor firing domain
     */
    public DBM fireTransition(
            int firedClock,
            List<String> newClockNames,
            double[] newLowerBounds,
            double[] newUpperBounds,
            int[] persistentClocks
    ) {
        if (empty) return this;

        int n = clockNames.size();
        if (firedClock < 0 || firedClock >= n) {
            throw new IllegalArgumentException("Invalid fired clock index: " + firedClock);
        }

        // ============================================================
        // STEP 1: Intersect with "t_f fires first" constraint
        // ============================================================
        // Add constraint: θ_f ≤ θᵢ for all enabled i ≠ f
        // In DBM: θ_f - θᵢ ≤ 0  ⟺  bounds[f+1][i+1] ≤ 0

        double[][] constrained = copyBounds();
        int f = firedClock + 1; // DBM index (0 is reference)

        for (int i = 0; i < n; i++) {
            if (i != firedClock) {
                int idx = i + 1;
                // θ_f ≤ θᵢ  ⟺  θ_f - θᵢ ≤ 0
                constrained[f][idx] = Math.min(constrained[f][idx], 0);
            }
        }

        // ============================================================
        // STEP 2: Canonicalize to derive tightest bounds
        // ============================================================
        if (!canonicalizeInPlace(constrained)) {
            return empty(List.of());
        }

        // ============================================================
        // STEP 3 & 4: Substitution and Elimination
        // ============================================================
        // After substitution θᵢ' = θᵢ - θ_f, the new bounds are:
        //
        // For persistent transition at old index i:
        //   θᵢ' = θᵢ - θ_f
        //   Upper bound: θᵢ' ≤ θᵢ - θ_f_min = constrained[i+1][f]
        //   Lower bound: θᵢ' ≥ θᵢ_min - θ_f_max = -constrained[f][i+1]
        //   But also θᵢ' ≥ 0 (can't be negative time), so lower = max(0, -constrained[f][i+1])
        //
        // Inter-clock constraints (between persistent transitions):
        //   θᵢ' - θⱼ' = (θᵢ - θ_f) - (θⱼ - θ_f) = θᵢ - θⱼ
        //   So: constrained[i+1][j+1] is preserved!

        int newN = persistentClocks.length + newClockNames.size();
        double[][] newBounds = new double[newN + 1][newN + 1];

        // Initialize
        for (int i = 0; i <= newN; i++) {
            Arrays.fill(newBounds[i], INF);
            newBounds[i][i] = 0;
        }

        // Copy persistent clocks with transformed bounds
        for (int pi = 0; pi < persistentClocks.length; pi++) {
            int oldIdx = persistentClocks[pi] + 1; // old DBM index
            int newIdx = pi + 1; // new DBM index

            // Upper bound: θᵢ' ≤ constrained[oldIdx][f]
            double upper = constrained[oldIdx][f];

            // Lower bound: θᵢ' ≥ max(0, -constrained[f][oldIdx])
            double lower = Math.max(0, -constrained[f][oldIdx]);

            newBounds[0][newIdx] = -lower;      // θᵢ' ≥ lower
            newBounds[newIdx][0] = upper;       // θᵢ' ≤ upper

            // Inter-clock constraints between persistent transitions (preserved!)
            for (int pj = 0; pj < persistentClocks.length; pj++) {
                int oldJ = persistentClocks[pj] + 1;
                int newJ = pj + 1;
                newBounds[newIdx][newJ] = constrained[oldIdx][oldJ];
            }
        }

        // ============================================================
        // STEP 5: Add fresh intervals for newly enabled transitions
        // ============================================================
        int offset = persistentClocks.length;
        for (int k = 0; k < newClockNames.size(); k++) {
            int idx = offset + k + 1;
            newBounds[0][idx] = -newLowerBounds[k];  // θ_new ≥ α
            newBounds[idx][0] = newUpperBounds[k];   // θ_new ≤ β
            // No inter-clock constraints with persistent (they're independent)
        }

        // Build new clock names
        var allNames = new java.util.ArrayList<String>();
        for (int idx : persistentClocks) {
            allNames.add(clockNames.get(idx));
        }
        allNames.addAll(newClockNames);

        // ============================================================
        // STEP 6: Final canonicalization
        // ============================================================
        return new DBM(newBounds, allNames, false).canonicalize();
    }

    /**
     * Lets time pass: all clocks decrease uniformly.
     * <p>
     * After time δ elapses, each θᵢ becomes θᵢ - δ.
     * The DBM operation: set all lower bounds to 0 (time can elapse until
     * transitions become fireable).
     * <p>
     * <b>Mathematical justification:</b>
     * If (θ₁, ..., θₙ) ∈ D, then for any δ ∈ [0, min(θᵢ)],
     * (θ₁ - δ, ..., θₙ - δ) is also reachable by letting time δ pass.
     * After letting maximum time pass, lower bounds become 0.
     */
    public DBM letTimePass() {
        if (empty) return this;

        double[][] newBounds = copyBounds();

        // Set all lower bounds to 0: transitions can fire immediately
        // (we've waited until earliest firing time)
        for (int i = 1; i < newBounds.length; i++) {
            newBounds[0][i] = 0; // θᵢ ≥ 0
        }

        return new DBM(newBounds, clockNames, false).canonicalize();
    }

    /**
     * Canonicalizes the DBM using Floyd-Warshall shortest paths.
     * <p>
     * After canonicalization:
     * <ul>
     *   <li>bounds[i][j] = tightest upper bound on (xᵢ - xⱼ)</li>
     *   <li>If bounds[i][i] < 0, the zone is empty (negative cycle)</li>
     * </ul>
     */
    private DBM canonicalize() {
        if (empty) return this;

        double[][] canon = copyBounds();
        if (!canonicalizeInPlace(canon)) {
            return empty(clockNames);
        }
        return new DBM(canon, clockNames, false);
    }

    /**
     * In-place canonicalization. Returns false if zone is empty.
     */
    private static boolean canonicalizeInPlace(double[][] dbm) {
        int n = dbm.length;

        // Floyd-Warshall
        for (int k = 0; k < n; k++) {
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    if (dbm[i][k] < INF && dbm[k][j] < INF) {
                        double via = dbm[i][k] + dbm[k][j];
                        if (via < dbm[i][j]) {
                            dbm[i][j] = via;
                        }
                    }
                }
            }
        }

        // Check for negative cycle (empty zone)
        for (int i = 0; i < n; i++) {
            if (dbm[i][i] < -EPSILON) {
                return false;
            }
        }
        return true;
    }

    private double[][] copyBounds() {
        double[][] copy = new double[bounds.length][];
        for (int i = 0; i < bounds.length; i++) {
            copy[i] = bounds[i].clone();
        }
        return copy;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof DBM other)) return false;
        if (empty && other.empty) return true;
        if (empty || other.empty) return false;
        if (!clockNames.equals(other.clockNames)) return false;
        return dbmEquals(bounds, other.bounds);
    }

    private static boolean dbmEquals(double[][] a, double[][] b) {
        if (a.length != b.length) return false;
        for (int i = 0; i < a.length; i++) {
            for (int j = 0; j < a[i].length; j++) {
                if (Math.abs(a[i][j] - b[i][j]) > EPSILON) return false;
            }
        }
        return true;
    }

    @Override
    public int hashCode() {
        if (empty) return 0;
        return java.util.Objects.hash(clockNames, Arrays.deepHashCode(bounds));
    }

    @Override
    public String toString() {
        if (empty) return "DBM[empty]";
        var sb = new StringBuilder("DBM{");
        for (int i = 0; i < clockNames.size(); i++) {
            if (i > 0) sb.append(", ");
            sb.append(clockNames.get(i)).append("∈[");
            sb.append(formatBound(getLowerBound(i))).append(",");
            sb.append(formatBound(getUpperBound(i))).append("]");
        }
        sb.append("}");
        return sb.toString();
    }

    private static String formatBound(double b) {
        if (b >= INF / 2) return "∞";
        if (b == (long) b) return String.valueOf((long) b);
        return String.format("%.3f", b);
    }
}
