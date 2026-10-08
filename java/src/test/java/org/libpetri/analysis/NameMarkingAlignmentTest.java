package org.libpetri.analysis;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.function.IntUnaryOperator;

import org.junit.jupiter.api.Test;

/**
 * [NU-055] AC5: the name-alignment predicate of a class gives the same answer on the class and on
 * the class with its name-symbols permuted, as the canonical key does, and on {@code S} reordered
 * or with a place repeated. AC7: it reads "one name across all" of {@code S}, self pairs included.
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
    void nu055_ac5_thePredicateIsInvariantUnderNamePermutationAndReorderingS() {
        var identity = marking(s -> s);
        var swapped = marking(s -> new int[] {7, 3, 5}[s]);
        var order = List.of("box", "list", "reply", "staged");
        assertEquals(identity.canonicalKey(order), swapped.canonicalKey(order));
        var lists = new ArrayList<List<String>>();
        for (var p : order) {
            lists.add(List.of(p));
            for (var q : order) {
                if (!q.equals(p)) lists.add(List.of(p, q));
            }
        }
        lists.add(order);
        for (var s : lists) {
            assertEquals(identity.aligned(s), swapped.aligned(s), s.toString());
            // Only membership counts: S reversed, or with a place repeated, reads the same.
            assertEquals(identity.aligned(s), identity.aligned(s.reversed()), s.toString());
            var repeated = new ArrayList<>(s);
            repeated.add(s.get(0));
            assertEquals(identity.aligned(s), identity.aligned(repeated), s.toString());
        }
        assertFalse(identity.aligned(List.of("box", "list")));
        assertFalse(identity.aligned(List.of("box", "reply")));
        assertFalse(identity.aligned(List.of("reply", "staged")));
        assertTrue(identity.aligned(List.of("staged")));
        assertFalse(identity.aligned(List.of("reply")));
        assertTrue(identity.aligned(List.of("box", "inflightA")), "an empty place imposes nothing");
    }

    @Test
    void nu055_ac7_theSingletonSaysItsPlaceNeverHoldsTwoNames() {
        var nm = new NameMarking();
        nm.add("reply", 0, 2);
        assertTrue(nm.aligned(List.of("reply")));
        nm.add("reply", 1, 1);
        assertFalse(nm.aligned(List.of("reply")));
    }

    @Test
    void nu055_ac7_oneNameAcrossAll_aPlaceHoldingTwoNamesViolatesSWhateverTheOthersHold() {
        // The pairwise reading of two places (every name in p equals every name in q) accepts this
        // marking, since `list` is empty; the list reading counts self pairs and does not.
        var nm = new NameMarking();
        nm.add("box", 0, 1);
        nm.add("box", 1, 1);
        assertFalse(nm.aligned(List.of("box", "list")));
        assertTrue(nm.aligned(List.of("list")));
        // Each place holding one name, but not the same one.
        var split = new NameMarking();
        split.add("box", 0, 1);
        split.add("staged", 0, 1);
        split.add("list", 1, 1);
        assertTrue(split.aligned(List.of("box", "staged")));
        assertFalse(split.aligned(List.of("box", "staged", "list")));
    }

    @Test
    void nu055_ac7_aPlaceEmptiedByRemovalImposesNothing() {
        var nm = new NameMarking();
        nm.add("box", 0, 1);
        nm.add("list", 1, 1);
        assertFalse(nm.aligned(List.of("box", "list")));
        assertTrue(nm.remove("list", 1, 1));
        assertTrue(nm.aligned(List.of("box", "list")));
    }
}
