package org.libpetri.smt.z3;

import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.FlatTransition;
import org.libpetri.smt.z3.StateEquationQuery.MarkingInequality;
import org.libpetri.smt.z3.StateEquationQuery.Origin;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.List;
import java.util.stream.IntStream;

/**
 * Trap refinement for the state-equation phase ([VER-018]), after Esparza, Ledesma-Garza,
 * Majumdar, Meyer and Niksic, "An SMT-based approach to coverability analysis" (CAV 2014).
 *
 * <p>A <b>trap</b> is a set of places {@code Q} such that every transition that removes a
 * token from {@code Q} also puts one into {@code Q}. A trap marked at {@code M0} stays
 * marked in every reachable marking, so a candidate that leaves an initially marked trap
 * empty is not reachable, and {@code Σ_{q∈Q} m_q >= 1} refutes it.
 *
 * <p>"Removes a token" is generalised to the arcs the ordinary definition does not know: a
 * consume-all input or a reset arc on a place of {@code Q} removes tokens from {@code Q}
 * whatever its weight, so that transition must also put one into {@code Q}. Without that, a
 * drain ({@code all(b) → c}) would leave {@code {a, b}} looking like a trap it is not, and
 * the refinement would exclude markings the net really reaches. Read and inhibitor arcs
 * remove nothing, and environment injection only adds tokens. No solver is involved.
 */
public final class TrapRefinement {

    private TrapRefinement() {}

    /**
     * An initially marked trap the candidate leaves empty, as the inequality
     * {@code Σ_{q∈Q} m_q >= 1}, or {@code null} when there is none. The trap is shrunk to a
     * locally minimal one: a smaller trap is a stronger constraint on the next candidate.
     *
     * @param initial   {@code M0}, one count per flat place ({@link AbstractReplayer#toVector})
     * @param candidate the candidate marking the trap must leave empty
     */
    public static MarkingInequality refutingTrap(FlatNet flatNet, int[] initial, long[] candidate) {
        int placeCount = flatNet.placeCount();
        var drains = new ArrayList<int[]>(flatNet.transitionCount());
        var feeds = new ArrayList<int[]>(flatNet.transitionCount());
        for (var ft : flatNet.transitions()) {
            drains.add(drainedPlaces(ft));
            feeds.add(fedPlaces(ft));
        }
        var empty = new BitSet(placeCount);
        for (int p = 0; p < Math.min(candidate.length, placeCount); p++) {
            if (candidate[p] == 0) {
                empty.set(p);
            }
        }
        var trap = maximalTrap(empty, drains, feeds);
        if (!markedIn(trap, initial)) {
            return null;
        }
        // Over a snapshot, ascending, while `trap` shrinks: a place an earlier round already
        // dropped is no longer a candidate for dropping.
        var snapshot = (BitSet) trap.clone();
        for (int p = snapshot.nextSetBit(0); p >= 0; p = snapshot.nextSetBit(p + 1)) {
            if (!trap.get(p)) {
                continue;
            }
            var without = (BitSet) trap.clone();
            without.clear(p);
            var smaller = maximalTrap(without, drains, feeds);
            if (markedIn(smaller, initial)) {
                trap = smaller;
            }
        }
        var weights = new BigInteger[placeCount];
        Arrays.fill(weights, BigInteger.ZERO);
        for (int p = trap.nextSetBit(0); p >= 0; p = trap.nextSetBit(p + 1)) {
            weights[p] = BigInteger.ONE.negate();
        }
        return new MarkingInequality(Arrays.asList(weights), BigInteger.ONE.negate(), Origin.TRAP);
    }

    /**
     * The largest trap inside {@code within} (possibly empty): repeatedly drop the places a
     * transition drains when it feeds nothing back into what is left. Traps are closed under
     * union, so the result contains every trap inside {@code within}.
     */
    private static BitSet maximalTrap(BitSet within, List<int[]> drains, List<int[]> feeds) {
        var trap = (BitSet) within.clone();
        boolean changed = true;
        while (changed) {
            changed = false;
            for (int t = 0; t < drains.size(); t++) {
                if (!anyIn(drains.get(t), trap) || anyIn(feeds.get(t), trap)) {
                    continue;
                }
                for (int p : drains.get(t)) {
                    if (trap.get(p)) {
                        trap.clear(p);
                        changed = true;
                    }
                }
            }
        }
        return trap;
    }

    /**
     * The places a firing of {@code ft} can take tokens from: its inputs, consume-all places
     * and reset places, ascending.
     */
    private static int[] drainedPlaces(FlatTransition ft) {
        var out = new BitSet(ft.preVector().length);
        for (int p : ft.resetPlaces()) {
            out.set(p);
        }
        for (int p = 0; p < ft.preVector().length; p++) {
            if (ft.preVector()[p] > 0 || ft.consumeAll()[p]) {
                out.set(p);
            }
        }
        return out.stream().toArray();
    }

    /** The places a firing of {@code ft} puts at least one token into, ascending. */
    private static int[] fedPlaces(FlatTransition ft) {
        int[] post = ft.postVector();
        return IntStream.range(0, post.length).filter(p -> post[p] > 0).toArray();
    }

    private static boolean anyIn(int[] places, BitSet set) {
        for (int p : places) {
            if (set.get(p)) {
                return true;
            }
        }
        return false;
    }

    private static boolean markedIn(BitSet places, int[] marking) {
        for (int p = places.nextSetBit(0); p >= 0 && p < marking.length; p = places.nextSetBit(p + 1)) {
            if (marking[p] > 0) {
                return true;
            }
        }
        return false;
    }
}
