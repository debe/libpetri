package org.libpetri.analysis;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import java.util.function.IntUnaryOperator;

import org.junit.jupiter.api.Test;

/**
 * [NU-055] AC5: the name-alignment predicate of a class gives the same answer on the class and on
 * the class with its name-symbols permuted, as the canonical key does.
 */
class NameMarkingAlignmentTest {

    private static NameMarking marking(IntUnaryOperator perm) {
        var nm = new NameMarking();
        nm.add("box", perm.applyAsInt(0), 1);
        nm.add("list", perm.applyAsInt(1), 1);
        nm.add("reply", perm.applyAsInt(0), 1);
        nm.add("reply", perm.applyAsInt(2), 1);
        nm.add("staged", perm.applyAsInt(2), 1);
        return nm;
    }

    @Test
    void nu055_ac5_thePredicateIsInvariantUnderNamePermutation() {
        var identity = marking(s -> s);
        var swapped = marking(s -> new int[] {7, 3, 5}[s]);
        var order = List.of("box", "list", "reply", "staged");
        assertEquals(identity.canonicalKey(order), swapped.canonicalKey(order));
        for (var p : order) {
            for (var q : order) {
                assertEquals(identity.aligned(p, q), swapped.aligned(p, q), p + ", " + q);
            }
        }
        assertFalse(identity.aligned("box", "list"));
        assertFalse(identity.aligned("box", "reply"));
        assertFalse(identity.aligned("reply", "staged"));
        assertTrue(identity.aligned("staged", "staged"));
        assertFalse(identity.aligned("reply", "reply"), "NameAligned(p, p): p never holds two names");
        assertTrue(identity.aligned("box", "inflightA"), "an empty place satisfies it");
    }
}
