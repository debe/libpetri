package org.libpetri.smt.invariant;

import org.libpetri.analysis.MarkingState;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.FlatTransition;

import java.util.*;

/**
 * Structural deadlock pre-check using siphon/trap analysis.
 *
 * <p>Commoner's theorem: a Petri net is deadlock-free if every siphon
 * contains a marked trap.
 *
 * <p>A <b>siphon</b> is a set of places S such that every transition with
 * an output in S also has an input in S. Once empty, a siphon stays empty.
 *
 * <p>A <b>trap</b> is a set of places S such that every transition with
 * an input in S also has an output in S. Once marked, a trap stays marked.
 *
 * <p>Checking every <em>minimal</em> siphon suffices, since a trap inside a minimal
 * siphon lies inside every siphon containing it. So {@code NoPotentialDeadlock} needs
 * the search to have found <b>every</b> minimal siphon, and each one's maximal trap to
 * hold a token in the initial marking. Deciding that is co-NP-complete, so the siphon
 * search runs under a budget and answers {@code Inconclusive} past it, leaving the
 * verdict to the SMT analysis.
 */
public final class StructuralCheck {

    private static final int MAX_PLACES_FOR_SIPHON_ANALYSIS = 50;

    /** Search budget for the siphon search, in search nodes. Identical in every implementation. */
    private static final int SIPHON_SEARCH_BUDGET = 10_000;

    private StructuralCheck() {}

    /**
     * Result of structural deadlock check.
     */
    public sealed interface Result {
        /** Every minimal siphon contains a trap marked in the initial marking. */
        record NoPotentialDeadlock() implements Result {}

        /** A siphon was found that does not contain a marked trap. */
        record PotentialDeadlock(Set<Integer> siphon) implements Result {}

        /** Analysis could not decide: the net has too many places, or the siphon search exceeded its node budget. */
        record Inconclusive(String reason) implements Result {}
    }

    /**
     * Checks for potential deadlocks using siphon/trap analysis.
     *
     * @param flatNet the flattened net
     * @param initialMarking the initial marking
     * @return the check result; {@code Inconclusive} when the net is too large or the siphon search exceeds its budget
     */
    public static Result check(FlatNet flatNet, MarkingState initialMarking) {
        int P = flatNet.placeCount();

        if (P == 0) {
            return new Result.NoPotentialDeadlock();
        }

        // For large nets, skip (too expensive for complete enumeration)
        if (P > MAX_PLACES_FOR_SIPHON_ANALYSIS) {
            return new Result.Inconclusive("Net has " + P + " places, siphon enumeration skipped");
        }

        var siphons = findMinimalSiphons(flatNet, SIPHON_SEARCH_BUDGET);
        if (siphons == null) {
            return new Result.Inconclusive("siphon search exceeded " + SIPHON_SEARCH_BUDGET + " nodes");
        }

        // For each siphon, check if it contains a marked trap
        for (var siphon : siphons) {
            // Find the maximal trap within this siphon
            var trap = findMaximalTrapIn(flatNet, siphon);

            // Check if the trap is initially marked
            if (trap.isEmpty() || !isMarked(trap, flatNet, initialMarking)) {
                return new Result.PotentialDeadlock(siphon);
            }
        }

        return new Result.NoPotentialDeadlock();
    }

    /**
     * Finds <b>all</b> minimal siphons, or {@code null} when the search exceeds
     * {@code budget} nodes.
     *
     * <p>A siphon is a place set S such that every transition with an output in S has
     * at least one input in S. The search grows S from each start place; where a
     * producer into S has no input in S, it branches on each of that producer's inputs.
     * Every minimal siphon containing the start place is reached by the branch that
     * always picks an input inside it, so the search is complete. Committing to one
     * input instead (the first, or all of them at once) is not: it can miss exactly
     * the unmarked siphon that makes the net dead.
     */
    static List<Set<Integer>> findMinimalSiphons(FlatNet flatNet, int budget) {
        var found = new ArrayList<Set<Integer>>();
        var nodes = new int[] {0};
        for (int start = 0; start < flatNet.placeCount(); start++) {
            if (!growSiphon(flatNet, Set.of(start), found, nodes, budget)) {
                return null;
            }
        }
        var minimal = new ArrayList<Set<Integer>>();
        for (int i = 0; i < found.size(); i++) {
            var s = found.get(i);
            boolean isMinimal = true;
            for (int j = 0; j < found.size(); j++) {
                var other = found.get(j);
                if (j != i && other.size() <= s.size() && s.containsAll(other)) {
                    isMinimal = false;
                    break;
                }
            }
            if (isMinimal) {
                minimal.add(s);
            }
        }
        return minimal;
    }

    /** One node of the siphon search. Returns {@code false} when the budget is exhausted. */
    private static boolean growSiphon(
            FlatNet flatNet, Set<Integer> siphon, List<Set<Integer>> found, int[] nodes, int budget) {
        if (++nodes[0] > budget) {
            return false;
        }
        // A superset of a siphon already found cannot lead to a new minimal one.
        for (var f : found) {
            if (f.size() <= siphon.size() && siphon.containsAll(f)) {
                return true;
            }
        }

        FlatTransition violating = null;
        for (var ft : flatNet.transitions()) {
            boolean outputsToSiphon = false;
            boolean hasInputInSiphon = false;
            for (int p : siphon) {
                if (ft.postVector()[p] > 0) outputsToSiphon = true;
                if (ft.preVector()[p] > 0) hasInputInSiphon = true;
            }
            if (outputsToSiphon && !hasInputInSiphon) {
                violating = ft;
                break;
            }
        }

        if (violating == null) {
            found.add(siphon);
            return true;
        }
        // A producer with no inputs keeps any set holding its output marked: no siphon
        // on this branch. Otherwise branch on each input.
        for (int q = 0; q < flatNet.placeCount(); q++) {
            if (violating.preVector()[q] > 0) {
                var next = new TreeSet<>(siphon);
                next.add(q);
                if (!growSiphon(flatNet, Collections.unmodifiableSortedSet(next), found, nodes, budget)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Finds the maximal trap within a given set of places.
     * Uses fixed-point: start with the full set and remove places that violate the trap condition.
     */
    static Set<Integer> findMaximalTrapIn(FlatNet flatNet, Set<Integer> places) {
        var trap = new TreeSet<>(places);

        boolean changed = true;
        while (changed) {
            changed = false;
            var toRemove = new ArrayList<Integer>();

            for (int p : trap) {
                // Check trap condition: every transition consuming from p must produce to some place in trap
                boolean satisfies = true;
                for (int t = 0; t < flatNet.transitionCount(); t++) {
                    var ft = flatNet.transitions().get(t);
                    if (ft.preVector()[p] > 0) {
                        // This transition consumes from p - check it outputs to some trap place
                        boolean outputsToTrap = false;
                        for (int q : trap) {
                            if (ft.postVector()[q] > 0) {
                                outputsToTrap = true;
                                break;
                            }
                        }
                        if (!outputsToTrap) {
                            satisfies = false;
                            break;
                        }
                    }
                }
                if (!satisfies) {
                    toRemove.add(p);
                }
            }

            if (!toRemove.isEmpty()) {
                trap.removeAll(toRemove);
                changed = true;
            }
        }

        return Set.copyOf(trap);
    }

    /**
     * Checks if a set of places has at least one token in the initial marking.
     */
    private static boolean isMarked(Set<Integer> placeIndices, FlatNet flatNet, MarkingState marking) {
        for (int idx : placeIndices) {
            var place = flatNet.places().get(idx);
            if (marking.tokens(place) > 0) {
                return true;
            }
        }
        return false;
    }
}
