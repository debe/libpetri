package org.libpetri.smt.z3;

import org.libpetri.analysis.MarkingState;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.IncidenceMatrix;
import org.libpetri.smt.invariant.PInvariant;
import org.libpetri.smt.invariant.PInvariantComputer;

import java.util.ArrayList;
import java.util.List;

/**
 * The colour-slot bound before the linear program ([NU-053]): the least {@code y·M0} over the
 * enumerated non-negative P-semiflows that weight every coloured place, else a summed fallback.
 * {@link #colourSlotBound} is a verbatim copy of the method {@code buildPlan} called until the LP
 * replaced it (Lean {@code colourSlotBound}, {@code Plan.lean}, kept there as history). The
 * differential tests use it to show the LP bound is never above it. Mirrors
 * {@code rust/libpetri-verification/tests/common/old_slot_bound.rs}.
 */
final class OldSlotBound {

    private OldSlotBound() {}

    /** The gate-validated semiflows the old bound read, computed as the verifier did. */
    static List<PInvariant> validatedSemiflows(FlatNet flat, MarkingState initial) {
        var matrix = IncidenceMatrix.from(flat);
        return PInvariantComputer.validateExact(
            PInvariantComputer.computePSemiflows(matrix, flat, initial), matrix, flat, initial).valid();
    }

    /** Verbatim copy of the old {@code NameColouredEncoder.colourSlotBound}. */
    static Integer colourSlotBound(int[] coloured, List<PInvariant> invariants) {
        // Tightest bound: a single non-negative P-semiflow weighting every coloured place.
        Integer single = null;
        for (PInvariant inv : invariants) {
            if (!isSemiflow(inv)) {
                continue;
            }
            boolean coversAll = true;
            for (int pid : coloured) {
                if (weightAt(inv, pid) < 1) {
                    coversAll = false;
                    break;
                }
            }
            if (coversAll) {
                single = (single == null) ? inv.constant() : Math.min(single, inv.constant());
            }
        }
        if (single != null) {
            return single;
        }

        // Otherwise sum non-negative semiflows that touch a coloured place — the sum is
        // itself a valid non-negative P-semiflow, so Σ y·M0 over any covering set is a
        // sound (looser) bound. Zero-constant semiflows cover their places for free, so
        // they go in first; a semiflow with a positive constant is added only if it
        // touches a coloured place the free ones left uncovered (decided against that
        // snapshot, so the result does not depend on enumeration order). If some
        // coloured place stays at weight 0 across all of them, no non-negative semiflow
        // covers it, so the coloured set is not structurally token-bounded → null
        // (sound over-approximation).
        boolean[] covered = new boolean[coloured.length];
        for (PInvariant inv : invariants) {
            if (!isSemiflow(inv) || inv.constant() != 0) {
                continue;
            }
            for (int i = 0; i < coloured.length; i++) {
                if (weightAt(inv, coloured[i]) >= 1) {
                    covered[i] = true;
                }
            }
        }
        boolean[] free = covered.clone();
        long sumConst = 0;
        for (PInvariant inv : invariants) {
            if (!isSemiflow(inv) || inv.constant() == 0) {
                continue;
            }
            boolean touchesUncovered = false;
            for (int i = 0; i < coloured.length; i++) {
                if (!free[i] && weightAt(inv, coloured[i]) >= 1) {
                    touchesUncovered = true;
                    break;
                }
            }
            if (!touchesUncovered) {
                continue;
            }
            for (int i = 0; i < coloured.length; i++) {
                if (weightAt(inv, coloured[i]) >= 1) {
                    covered[i] = true;
                }
            }
            sumConst += inv.constant();
        }
        boolean allCovered = true;
        for (boolean c : covered) {
            if (!c) {
                allCovered = false;
                break;
            }
        }
        return allCovered ? (int) sumConst : null;
    }

    /**
     * The weighting behind {@link #colourSlotBound}: the covering semiflow it picked (the first of
     * least constant), or the sum of the semiflows its fallback added. {@code y·M0} of it is the
     * old bound.
     */
    static long[] colourSlotWeighting(int n, int[] coloured, List<PInvariant> invariants) {
        var semiflows = new ArrayList<PInvariant>();
        for (PInvariant inv : invariants) {
            if (isSemiflow(inv)) {
                semiflows.add(inv);
            }
        }
        PInvariant best = null;
        for (PInvariant inv : semiflows) {
            boolean coversAll = true;
            for (int pid : coloured) {
                coversAll &= weightAt(inv, pid) >= 1;
            }
            if (coversAll && (best == null || inv.constant() < best.constant())) {
                best = inv;
            }
        }
        long[] out = new long[n];
        if (best != null) {
            for (int p = 0; p < n; p++) {
                out[p] = weightAt(best, p);
            }
            return out;
        }
        boolean[] free = new boolean[coloured.length];
        for (int i = 0; i < coloured.length; i++) {
            for (PInvariant inv : semiflows) {
                if (inv.constant() == 0 && weightAt(inv, coloured[i]) >= 1) {
                    free[i] = true;
                }
            }
        }
        boolean[] covered = free.clone();
        for (PInvariant inv : semiflows) {
            boolean take = false;
            for (int i = 0; i < coloured.length; i++) {
                if (weightAt(inv, coloured[i]) >= 1 && (inv.constant() == 0 || !free[i])) {
                    take = true;
                }
            }
            if (!take) {
                continue;
            }
            for (int i = 0; i < coloured.length; i++) {
                if (weightAt(inv, coloured[i]) >= 1) {
                    covered[i] = true;
                }
            }
            for (int p = 0; p < n; p++) {
                out[p] += weightAt(inv, p);
            }
        }
        for (boolean c : covered) {
            if (!c) {
                return null;
            }
        }
        return out;
    }

    private static int weightAt(PInvariant inv, int pid) {
        int[] w = inv.weights();
        return (pid >= 0 && pid < w.length) ? w[pid] : 0;
    }

    private static boolean isSemiflow(PInvariant inv) {
        for (int x : inv.weights()) {
            if (x < 0) {
                return false;
            }
        }
        return true;
    }
}
