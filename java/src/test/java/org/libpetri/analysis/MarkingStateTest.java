package org.libpetri.analysis;

import org.libpetri.core.Place;
import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for {@link MarkingState}.
 */
class MarkingStateTest {

    record TestValue(String data) {}

    private final Place<TestValue> p1 = Place.of("P1", TestValue.class);
    private final Place<TestValue> p2 = Place.of("P2", TestValue.class);
    private final Place<TestValue> p3 = Place.of("P3", TestValue.class);

    @Test
    void empty_createsMarkingWithNoTokens() {
        var state = MarkingState.empty();

        assertTrue(state.isEmpty());
        assertEquals(0, state.totalTokens());
        assertTrue(state.placesWithTokens().isEmpty());
    }

    @Test
    void builder_createsMarkingWithTokens() {
        var state = MarkingState.builder()
            .tokens(p1, 2)
            .tokens(p2, 1)
            .build();

        assertEquals(2, state.tokens(p1));
        assertEquals(1, state.tokens(p2));
        assertEquals(0, state.tokens(p3));
    }

    @Test
    void hasTokens_withTokens_returnsTrue() {
        var state = MarkingState.builder()
            .tokens(p1, 1)
            .build();

        assertTrue(state.hasTokens(p1));
        assertFalse(state.hasTokens(p2));
    }

    @Test
    void hasTokensInAny_withSomeTokens_returnsTrue() {
        var state = MarkingState.builder()
            .tokens(p2, 1)
            .build();

        assertTrue(state.hasTokensInAny(Set.of(p1, p2)));
        assertFalse(state.hasTokensInAny(Set.of(p1, p3)));
    }

    @Test
    void placesWithTokens_returnsOnlyNonEmpty() {
        var state = MarkingState.builder()
            .tokens(p1, 2)
            .tokens(p2, 1)
            .build();

        var places = state.placesWithTokens();
        assertEquals(2, places.size());
        assertTrue(places.contains(p1));
        assertTrue(places.contains(p2));
        assertFalse(places.contains(p3));
    }

    @Test
    void totalTokens_sumsAllCounts() {
        var state = MarkingState.builder()
            .tokens(p1, 3)
            .tokens(p2, 2)
            .tokens(p3, 5)
            .build();

        assertEquals(10, state.totalTokens());
    }

    @Test
    void builder_zeroTokens_removesPlace() {
        var state = MarkingState.builder()
            .tokens(p1, 5)
            .tokens(p1, 0)
            .build();

        assertFalse(state.hasTokens(p1));
        assertTrue(state.isEmpty());
    }

    @Test
    void builder_negativeTokens_throwsException() {
        assertThrows(IllegalArgumentException.class, () ->
            MarkingState.builder().tokens(p1, -1)
        );
    }

    @Test
    void builder_addTokens_increments() {
        var state = MarkingState.builder()
            .tokens(p1, 2)
            .addTokens(p1, 3)
            .build();

        assertEquals(5, state.tokens(p1));
    }

    @Test
    void builder_removeTokens_decrements() {
        var state = MarkingState.builder()
            .tokens(p1, 5)
            .removeTokens(p1, 2)
            .build();

        assertEquals(3, state.tokens(p1));
    }

    @Test
    void builder_removeTokens_toZero_removesPlace() {
        var state = MarkingState.builder()
            .tokens(p1, 2)
            .removeTokens(p1, 2)
            .build();

        assertFalse(state.hasTokens(p1));
    }

    @Test
    void builder_removeTokens_insufficientTokens_throwsException() {
        assertThrows(IllegalStateException.class, () ->
            MarkingState.builder()
                .tokens(p1, 2)
                .removeTokens(p1, 5)
        );
    }

    @Test
    void builder_copyFrom_copiesAllTokens() {
        var original = MarkingState.builder()
            .tokens(p1, 2)
            .tokens(p2, 3)
            .build();

        var copy = MarkingState.builder()
            .copyFrom(original)
            .build();

        assertEquals(original, copy);
    }

    @Test
    void asMap_returnsTokenCounts() {
        var state = MarkingState.builder()
            .tokens(p1, 2)
            .tokens(p2, 1)
            .build();

        var map = state.asMap();
        assertEquals(2, map.get(p1));
        assertEquals(1, map.get(p2));
    }

    @Test
    void equality_sameTokenCounts_areEqual() {
        var s1 = MarkingState.builder()
            .tokens(p1, 2)
            .tokens(p2, 1)
            .build();

        var s2 = MarkingState.builder()
            .tokens(p1, 2)
            .tokens(p2, 1)
            .build();

        assertEquals(s1, s2);
        assertEquals(s1.hashCode(), s2.hashCode());
    }

    @Test
    void equality_differentTokenCounts_notEqual() {
        var s1 = MarkingState.builder()
            .tokens(p1, 2)
            .build();

        var s2 = MarkingState.builder()
            .tokens(p1, 3)
            .build();

        assertNotEquals(s1, s2);
    }

    @Test
    void equality_differentPlaces_notEqual() {
        var s1 = MarkingState.builder()
            .tokens(p1, 1)
            .build();

        var s2 = MarkingState.builder()
            .tokens(p2, 1)
            .build();

        assertNotEquals(s1, s2);
    }

    @Test
    void toString_emptyMarking_returnsEmptyBraces() {
        var state = MarkingState.empty();

        assertEquals("{}", state.toString());
    }

    @Test
    void toString_withTokens_showsSorted() {
        var pA = Place.of("A", TestValue.class);
        var pB = Place.of("B", TestValue.class);

        var state = MarkingState.builder()
            .tokens(pB, 2)
            .tokens(pA, 1)
            .build();

        assertEquals("{A:1, B:2}", state.toString());
    }

    @Test
    void immutability_mapIsUnmodifiable() {
        var state = MarkingState.builder()
            .tokens(p1, 1)
            .build();

        assertThrows(UnsupportedOperationException.class, () ->
            state.asMap().put(p2, 1)
        );
    }

    @Test
    void immutability_placesSetIsUnmodifiable() {
        var state = MarkingState.builder()
            .tokens(p1, 1)
            .build();

        assertThrows(UnsupportedOperationException.class, () ->
            state.placesWithTokens().add(p2)
        );
    }
}
