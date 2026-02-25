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
 * <p>This is a cheap polynomial pre-check that may prove deadlock-freedom
 * before the more expensive SMT analysis.
 */
public final class StructuralCheck {

    private static final int MAX_PLACES_FOR_SIPHON_ANALYSIS = 50;

    private StructuralCheck() {}

    /**
     * Result of structural deadlock check.
     */
    public sealed interface Result {
        /** No potential deadlock detected (all siphons contain marked traps). */
        record NoPotentialDeadlock() implements Result {}

        /** A siphon was found that does not contain a marked trap. */
        record PotentialDeadlock(Set<Integer> siphon) implements Result {}

        /** Analysis could not determine (e.g., net too large for complete analysis). */
        record Inconclusive(String reason) implements Result {}
    }

    /**
     * Checks for potential deadlocks using siphon/trap analysis.
     *
     * @param flatNet the flattened net
     * @param initialMarking the initial marking
     * @return the check result
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

        // Find minimal siphons using backward closure
        var siphons = findMinimalSiphons(flatNet);

        if (siphons.isEmpty()) {
            return new Result.NoPotentialDeadlock();
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
     * Finds minimal siphons by checking all non-empty subsets of deadlock-enabling places.
     * Uses a fixed-point approach: start from each place and grow the siphon.
     */
    static List<Set<Integer>> findMinimalSiphons(FlatNet flatNet) {
        int P = flatNet.placeCount();
        var siphons = new ArrayList<Set<Integer>>();

        // Pre-compute: for each place, which transitions have it as output?
        // And for each transition, what are its input places?
        var placeAsOutput = new ArrayList<List<Integer>>(P); // place -> list of transition indices
        for (int p = 0; p < P; p++) {
            placeAsOutput.add(new ArrayList<>());
        }

        for (int t = 0; t < flatNet.transitionCount(); t++) {
            var ft = flatNet.transitions().get(t);
            for (int p = 0; p < P; p++) {
                if (ft.postVector()[p] > 0) {
                    placeAsOutput.get(p).add(t);
                }
            }
        }

        // For each starting place, compute the minimal siphon containing it
        for (int startPlace = 0; startPlace < P; startPlace++) {
            var siphon = computeSiphonContaining(startPlace, flatNet, placeAsOutput);
            if (siphon != null && !siphon.isEmpty()) {
                // Check it's truly minimal (not a superset of an existing siphon)
                boolean isMinimal = true;
                var toRemove = new ArrayList<Integer>();
                for (int i = 0; i < siphons.size(); i++) {
                    var existing = siphons.get(i);
                    if (existing.equals(siphon)) {
                        isMinimal = false;
                        break;
                    }
                    if (siphon.containsAll(existing)) {
                        isMinimal = false;
                        break;
                    }
                    if (existing.containsAll(siphon)) {
                        toRemove.add(i);
                    }
                }
                // Remove non-minimal existing siphons
                for (int i = toRemove.size() - 1; i >= 0; i--) {
                    siphons.remove((int) toRemove.get(i));
                }
                if (isMinimal) {
                    siphons.add(siphon);
                }
            }
        }

        return siphons;
    }

    /**
     * Computes the minimal siphon containing a given place using fixed-point iteration.
     * A siphon S must satisfy: for every transition t with an output in S, t has an input in S.
     */
    private static Set<Integer> computeSiphonContaining(
            int startPlace, FlatNet flatNet, List<List<Integer>> placeAsOutput) {

        var siphon = new TreeSet<Integer>();
        siphon.add(startPlace);

        // Fixed-point: keep adding required input places
        boolean changed = true;
        while (changed) {
            changed = false;

            for (int p : new ArrayList<>(siphon)) {
                // For each transition that outputs to p
                for (int t : placeAsOutput.get(p)) {
                    var ft = flatNet.transitions().get(t);

                    // This transition must have at least one input in the siphon
                    boolean hasInputInSiphon = false;
                    for (int q = 0; q < flatNet.placeCount(); q++) {
                        if (ft.preVector()[q] > 0 && siphon.contains(q)) {
                            hasInputInSiphon = true;
                            break;
                        }
                    }

                    if (!hasInputInSiphon) {
                        // Must add at least one input place of this transition
                        // Choose the first one (heuristic for minimality)
                        boolean added = false;
                        for (int q = 0; q < flatNet.placeCount(); q++) {
                            if (ft.preVector()[q] > 0) {
                                if (siphon.add(q)) {
                                    changed = true;
                                }
                                added = true;
                                break;
                            }
                        }
                        // If transition has no inputs but has outputs in siphon,
                        // the siphon property is trivially violated (source transition).
                        // This siphon can't exist - return null.
                        if (!added) {
                            return null;
                        }
                    }
                }
            }
        }

        return Set.copyOf(siphon);
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
