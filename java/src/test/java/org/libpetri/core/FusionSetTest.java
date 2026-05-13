package org.libpetri.core;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for {@link FusionSet} per <b>MOD-060</b> (fusion set declaration).
 *
 * <p>These tests exercise the construction and validation surface of the
 * carrier object only — the actual fusion-resolution semantics
 * (substitution at {@code build()} time) are covered by {@code FusionTest}.
 */
class FusionSetTest {

    // ============================================================
    //  Canonical-member convention
    // ============================================================

    @Test
    void fusionSet_firstMemberIsCanonical() {
        var a = Place.of("A", String.class);
        var b = Place.of("B", String.class);
        var c = Place.of("C", String.class);

        var set = FusionSet.builder("limiter")
            .member(a)
            .member(b)
            .member(c)
            .build();

        assertSame(a, set.canonical(),
            "first declared member must be canonical (MOD-060 convention)");
        assertEquals(3, set.members().size());
        assertEquals(a, set.members().get(0));
    }

    // ============================================================
    //  Type homogeneity (MOD-060)
    // ============================================================

    @Test
    void fusionSet_typeHomogeneity_enforced() {
        // Mixing Place<String> and Place<Integer> must fail at build().
        // We exercise the runtime check on the Builder which accepts Place<?>
        // members one at a time — the mix is created via the wildcard surface.
        var s1 = Place.of("S1", String.class);
        var s2 = Place.of("S2", String.class);
        var i1 = Place.of("I1", Integer.class);

        var builder = FusionSet.builder("mixed")
            .member(s1)
            .member(s2)
            .member(i1);

        var ex = assertThrows(IllegalArgumentException.class, builder::build);
        assertTrue(ex.getMessage().contains("I1"),
            "exception message must name the offending member. Got: " + ex.getMessage());
        assertTrue(ex.getMessage().contains("String"),
            "exception message must name the expected type. Got: " + ex.getMessage());
        assertTrue(ex.getMessage().contains("Integer"),
            "exception message must name the actual type. Got: " + ex.getMessage());
    }

    // ============================================================
    //  Empty-set rejection (MOD-060)
    // ============================================================

    @Test
    void fusionSet_emptySet_throws() {
        var ex = assertThrows(IllegalArgumentException.class,
            () -> FusionSet.builder("empty").build());
        assertTrue(ex.getMessage().contains("empty"),
            "exception message must name the empty set. Got: " + ex.getMessage());
    }

    // ============================================================
    //  Single-member set: degenerate but allowed (no-op fusion)
    // ============================================================

    @Test
    void fusionSet_singleMember_isValid() {
        var only = Place.of("only", String.class);

        var set = FusionSet.builder("solo").member(only).build();

        assertSame(only, set.canonical());
        assertEquals(1, set.members().size());
        assertTrue(set.nonCanonical().isEmpty(),
            "single-member fusion sets have no non-canonical members");
        assertEquals(String.class, set.tokenType());
    }

    // ============================================================
    //  Static of(...) factory convenience (MOD-060)
    // ============================================================

    @Test
    void fusionSet_of_factoryConvenience() {
        Place<String> a = Place.of("A", String.class);
        Place<String> b = Place.of("B", String.class);
        Place<String> c = Place.of("C", String.class);

        var set = FusionSet.of("rate", a, b, c);

        assertSame(a, set.canonical());
        assertEquals(3, set.members().size());
        assertEquals(2, set.nonCanonical().size());
        assertEquals(b, set.nonCanonical().get(0));
        assertEquals(c, set.nonCanonical().get(1));
        assertEquals(String.class, set.tokenType());
    }

    // ============================================================
    //  nonCanonical() returns all members except the first
    // ============================================================

    @Test
    void fusionSet_nonCanonical_returnsAllButFirst() {
        var a = Place.of("A", Integer.class);
        var b = Place.of("B", Integer.class);
        var c = Place.of("C", Integer.class);
        var d = Place.of("D", Integer.class);

        var set = FusionSet.builder("ints")
            .member(a)
            .member(b)
            .member(c)
            .member(d)
            .build();

        var nonCanonical = set.nonCanonical();
        assertEquals(3, nonCanonical.size());
        assertEquals(b, nonCanonical.get(0));
        assertEquals(c, nonCanonical.get(1));
        assertEquals(d, nonCanonical.get(2));
        // canonical not in non-canonical set
        assertFalse(nonCanonical.contains(a));

        // Verify nonCanonical is a list view, not modifiable.
        assertThrows(UnsupportedOperationException.class,
            () -> nonCanonical.add(a));
    }
}
