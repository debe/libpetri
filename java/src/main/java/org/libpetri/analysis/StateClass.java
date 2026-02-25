package org.libpetri.analysis;

import org.libpetri.core.Transition;

import java.util.List;
import java.util.Objects;

/**
 * A State Class in Time Petri Net analysis.
 * <p>
 * A state class is a pair (M, D) where:
 * <ul>
 *   <li>M is a marking (token distribution)</li>
 *   <li>D is a firing domain (DBM representing valid firing times)</li>
 * </ul>
 * <p>
 * State classes provide a finite abstraction of the infinite state space
 * of Time Petri Nets. Two configurations with the same marking and equivalent
 * firing domains are represented by the same state class.
 *
 * <h2>Mathematical Foundation (Berthomieu-Diaz 1991)</h2>
 * <p>
 * A Time Petri Net configuration is (M, ν) where:
 * <ul>
 *   <li>M is the current marking</li>
 *   <li>ν: enabled(M) → ℝ≥0 assigns a clock value to each enabled transition</li>
 * </ul>
 * <p>
 * A state class C = (M, D) represents all configurations (M, ν) where
 * the clock values ν satisfy the constraints in D.
 *
 * <h2>State Class Graph Properties</h2>
 * <ul>
 *   <li><b>Reachability preserving</b>: A marking M' is reachable iff there exists
 *       a state class (M', D') in the graph</li>
 *   <li><b>Finite</b>: For bounded TPNs, the state class graph is finite</li>
 *   <li><b>Trace equivalent</b>: Preserves firing sequences (linear time properties)</li>
 * </ul>
 *
 * @see DBM
 * @see StateClassGraph
 */
public final class StateClass {

    private final MarkingState marking;
    private final DBM firingDomain;
    private final List<Transition> enabledTransitions;

    /**
     * Creates a new state class.
     *
     * @param marking the marking (token distribution)
     * @param firingDomain the firing domain (timing constraints)
     * @param enabledTransitions transitions enabled in this marking
     */
    public StateClass(MarkingState marking, DBM firingDomain, List<Transition> enabledTransitions) {
        this.marking = Objects.requireNonNull(marking);
        this.firingDomain = Objects.requireNonNull(firingDomain);
        this.enabledTransitions = List.copyOf(enabledTransitions);
    }

    /**
     * Returns the marking of this state class.
     */
    public MarkingState marking() {
        return marking;
    }

    /**
     * Returns the firing domain (DBM) of this state class.
     */
    public DBM firingDomain() {
        return firingDomain;
    }

    /**
     * Returns the transitions enabled in this state class.
     */
    public List<Transition> enabledTransitions() {
        return enabledTransitions;
    }

    /**
     * Checks if this state class is empty (unreachable due to timing constraints).
     */
    public boolean isEmpty() {
        return firingDomain.isEmpty();
    }

    /**
     * Checks if a specific transition can fire from this state class.
     * A transition can fire if it's enabled and its earliest firing time has passed
     * (or can pass by letting time elapse).
     *
     * @param transition the transition to check
     * @return true if the transition can fire
     */
    public boolean canFire(Transition transition) {
        int idx = enabledTransitions.indexOf(transition);
        if (idx < 0) return false;
        // In a canonical DBM after time passage, any enabled transition can fire
        // if its upper bound hasn't been exceeded
        return firingDomain.getUpperBound(idx) >= 0;
    }

    /**
     * Returns the index of a transition in the enabled list.
     *
     * @param transition the transition
     * @return index or -1 if not enabled
     */
    public int transitionIndex(Transition transition) {
        return enabledTransitions.indexOf(transition);
    }

    /**
     * Two state classes are equal if they have the same marking AND
     * the same firing domain (zone equality).
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof StateClass other)) return false;
        return marking.equals(other.marking) && firingDomain.equals(other.firingDomain);
    }

    @Override
    public int hashCode() {
        return Objects.hash(marking, firingDomain);
    }

    @Override
    public String toString() {
        return "StateClass{" + marking + ", " + firingDomain + "}";
    }

    /**
     * Returns a compact string showing just the marking.
     */
    public String toShortString() {
        return marking.toString();
    }
}
