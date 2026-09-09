package org.libpetri.analysis;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * [VER-011] AC4: the DBM exposes a dedup key over its full canonical matrix and a
 * permutation of its clocks that reorders the matrix with them. Mirrors the "DBM zone
 * identity" cases of {@code typescript/tests/verification/analysis/dbm.test.ts}.
 */
class DBMTest {

    @Test
    void permuted_reordersClocksWithoutChangingTheZone() {
        // f ∈ [0,1] fires first; u ∈ [2,4] and v ∈ [0,1] persist, w is newly enabled.
        var base = DBM.create(List.of("f", "u", "v"), new double[] {0, 2, 0}, new double[] {1, 4, 1});
        var a = base.fireTransition(0, List.of("w"), new double[] {0}, new double[] {1}, new int[] {1, 2})
            .letTimePass(); // clocks u, v, w
        var b = a.permuted(new int[] {2, 0, 1}); // clocks w, u, v
        assertEquals(List.of("w", "u", "v"), b.clockNames());
        assertEquals(a.getLowerBound(0), b.getLowerBound(1));
        assertEquals(a.getUpperBound(0), b.getUpperBound(1));
        assertEquals(a.getUpperBound(2), b.getUpperBound(0));
        // Permuting back restores the exact matrix.
        assertEquals(a, b.permuted(new int[] {1, 2, 0}));
        assertEquals(a.zoneKey(), b.permuted(new int[] {1, 2, 0}).zoneKey());
        // The projection string follows the clock order; the zone did not change.
        assertNotEquals(a.toString(), b.toString());
    }

    @Test
    void zoneKey_separatesZonesThatShareEveryPerClockProjection() {
        // Zone A: u − v ≥ 1 (u and v aged together under f), w fresh and unrelated.
        var a = DBM.create(List.of("f", "u", "v"), new double[] {0, 2, 0}, new double[] {1, 4, 1})
            .fireTransition(0, List.of("w"), new double[] {0}, new double[] {1}, new int[] {1, 2})
            .letTimePass();
        // Zone B: u − w ≥ 1, v fresh and unrelated — built with the roles of v and w
        // swapped, then permuted into the same clock order.
        var b = DBM.create(List.of("f", "u", "w"), new double[] {0, 2, 0}, new double[] {1, 4, 1})
            .fireTransition(0, List.of("v"), new double[] {0}, new double[] {1}, new int[] {1, 2})
            .letTimePass()
            .permuted(new int[] {0, 2, 1});
        assertEquals(List.of("u", "v", "w"), a.clockNames());
        assertEquals(List.of("u", "v", "w"), b.clockNames());
        // Identical projections: the old key would have merged these two classes.
        assertEquals(a.toString(), b.toString());
        // Different zones: the difference constraint sits between different clocks.
        assertNotEquals(a, b);
        assertNotEquals(a.zoneKey(), b.zoneKey());
    }

    @Test
    void zoneKey_ofAnEmptyZoneIsStable() {
        assertEquals("DBM[empty]", DBM.empty(List.of("t1")).zoneKey());
    }

    @Test
    void zoneKey_isTheClockNamesThenEveryMatrixEntryRowMajor() {
        // One clock in [1, 3]: reference row/column carry -lo and hi, diagonal is 0.
        var d = DBM.create(List.of("t"), new double[] {1}, new double[] {3});
        assertEquals("t|0|-1|3|0", d.zoneKey());
    }
}
