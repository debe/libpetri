package org.libpetri.smt.invariant;

import java.util.Arrays;
import java.util.Set;

/**
 * A P-invariant (place invariant) of a Petri net.
 *
 * <p>A P-invariant is a vector y such that y^T * C = 0, where C is the
 * incidence matrix. This means that for any reachable marking M:
 * {@code sum(y_i * M_i) = constant}, where constant = sum(y_i * M0_i).
 *
 * <p>P-invariants provide structural bounds on places and are used as
 * strengthening lemmas for the IC3/PDR engine.
 *
 * @param weights  weight vector (one entry per place index)
 * @param constant the invariant value sum(y_i * M0_i)
 * @param support  set of place indices where weight != 0
 */
public record PInvariant(int[] weights, int constant, Set<Integer> support) {

    @Override
    public String toString() {
        var sb = new StringBuilder("PInvariant[");
        boolean first = true;
        for (int i : support) {
            if (!first) sb.append(" + ");
            if (weights[i] != 1) sb.append(weights[i]).append("*");
            sb.append("p").append(i);
            first = false;
        }
        sb.append(" = ").append(constant).append("]");
        return sb.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof PInvariant other)) return false;
        return constant == other.constant
            && Arrays.equals(weights, other.weights)
            && support.equals(other.support);
    }

    @Override
    public int hashCode() {
        return 31 * Arrays.hashCode(weights) + constant;
    }
}
