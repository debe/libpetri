package org.libpetri.smt.encoding;

import org.libpetri.core.Transition;

import java.util.Arrays;

/**
 * A flattened transition with pre/post vectors for SMT encoding.
 *
 * <p>Each {@link Transition} with XOR outputs is expanded into multiple
 * FlatTransitions (one per branch). Non-XOR transitions map 1:1.
 *
 * @param name           display name (e.g. "Search_b0", "Search_b1")
 * @param source         the original transition
 * @param branchIndex    which XOR branch (-1 if no XOR)
 * @param preVector      tokens consumed per place (indexed by place index)
 * @param postVector     tokens produced per place (indexed by place index)
 * @param inhibitorPlaces place indices where inhibitor arcs block firing
 * @param readPlaces     place indices requiring a token without consuming
 * @param resetPlaces    place indices set to 0 on firing
 * @param consumeAll     true at index i means place i uses All/AtLeast semantics
 */
public record FlatTransition(
    String name,
    Transition source,
    int branchIndex,
    int[] preVector,
    int[] postVector,
    int[] inhibitorPlaces,
    int[] readPlaces,
    int[] resetPlaces,
    boolean[] consumeAll
) {
    @Override
    public String toString() {
        return "FlatTransition[" + name + "]";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof FlatTransition other)) return false;
        return branchIndex == other.branchIndex
            && name.equals(other.name)
            && source == other.source
            && Arrays.equals(preVector, other.preVector)
            && Arrays.equals(postVector, other.postVector)
            && Arrays.equals(inhibitorPlaces, other.inhibitorPlaces)
            && Arrays.equals(readPlaces, other.readPlaces)
            && Arrays.equals(resetPlaces, other.resetPlaces)
            && Arrays.equals(consumeAll, other.consumeAll);
    }

    @Override
    public int hashCode() {
        int h = name.hashCode();
        h = 31 * h + branchIndex;
        h = 31 * h + Arrays.hashCode(preVector);
        h = 31 * h + Arrays.hashCode(postVector);
        h = 31 * h + Arrays.hashCode(inhibitorPlaces);
        h = 31 * h + Arrays.hashCode(readPlaces);
        h = 31 * h + Arrays.hashCode(resetPlaces);
        h = 31 * h + Arrays.hashCode(consumeAll);
        return h;
    }
}
