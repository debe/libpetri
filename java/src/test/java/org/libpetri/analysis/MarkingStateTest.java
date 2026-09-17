package org.libpetri.analysis;

import org.libpetri.core.Place;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
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
    void placesWithTokens_listsPlacesInInsertionOrder() {
        // A place set again keeps its position; one removed and set again moves to the end.
        var state = MarkingState.builder()
            .tokens(p3, 1)
            .tokens(p1, 1)
            .tokens(p2, 1)
            .addTokens(p3, 2)
            .tokens(p1, 0)
            .tokens(p1, 4)
            .build();

        assertEquals(List.of(p3, p2, p1), List.copyOf(state.placesWithTokens()));
        assertEquals(List.of(p3, p2, p1),
            List.copyOf(MarkingState.builder().copyFrom(state).build().placesWithTokens()));
        assertEquals(MarkingState.builder().tokens(p1, 4).tokens(p2, 1).tokens(p3, 3).build(), state);
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

    /**
     * The builder against the ordered map it replaced, on random operations: every marking it
     * builds holds the same counts, lists its places in the same order, and equals and hashes
     * like the map. The pool mixes a few places with many, and equal places that are distinct
     * instances, so the source index, the scan of appended places and re-indexing all run.
     */
    @Test
    void builder_behavesLikeAnInsertionOrderedMap_onRandomOperations() {
        var random = new Random(20260917);
        var pool = new ArrayList<Place<?>>();
        for (int i = 0; i < 60; i++) {
            pool.add(Place.of("p" + i, TestValue.class));
        }
        var built = new ArrayList<MarkingState>();
        built.add(MarkingState.empty());
        for (int round = 0; round < 3000; round++) {
            var builder = MarkingState.builder();
            var model = new LinkedHashMap<Place<?>, Integer>();
            if (random.nextBoolean()) {
                var from = built.get(random.nextInt(built.size()));
                builder.copyFrom(from);
                for (var place : from.placesWithTokens()) {
                    model.put(place, from.tokens(place));
                }
            }
            int width = random.nextBoolean() ? 4 : pool.size();
            int operations = random.nextInt(random.nextBoolean() ? 6 : 80);
            for (int op = 0; op < operations; op++) {
                var named = pool.get(random.nextInt(width));
                // An equal place that is another instance.
                Place<?> place = random.nextInt(4) == 0 ? Place.of(named.name(), TestValue.class) : named;
                int count = random.nextInt(4);
                switch (random.nextInt(4)) {
                    case 0 -> {
                        builder.tokens(place, count);
                        if (count > 0) model.put(place, count); else model.remove(place);
                    }
                    case 1 -> {
                        builder.addTokens(place, count);
                        if (count > 0) model.merge(place, count, Integer::sum);
                    }
                    case 2 -> {
                        int have = model.getOrDefault(place, 0);
                        if (count > have) {
                            assertThrows(IllegalStateException.class, () -> builder.removeTokens(place, count));
                        } else {
                            builder.removeTokens(place, count);
                            if (have - count == 0) model.remove(place); else model.put(place, have - count);
                        }
                    }
                    default -> {
                        var from = built.get(random.nextInt(built.size()));
                        builder.copyFrom(from);
                        for (var p : from.placesWithTokens()) {
                            model.put(p, from.tokens(p));
                        }
                    }
                }
            }
            var marking = builder.build();
            assertEquals(List.copyOf(model.keySet()).stream().map(Place::name).toList(),
                marking.placesWithTokens().stream().map(Place::name).toList(), "insertion order");
            assertEquals(model, marking.asMap());
            assertEquals(model.hashCode(), marking.hashCode());
            assertEquals(new HashMap<>(model), new HashMap<>(marking.asMap()));
            for (var place : pool) {
                assertEquals(model.getOrDefault(place, 0), marking.tokens(place), place.name());
                assertEquals(model.containsKey(place), marking.placesWithTokens().contains(place));
            }
            var shuffled = new ArrayList<>(model.entrySet());
            java.util.Collections.shuffle(shuffled, random);
            var reordered = MarkingState.builder();
            for (var e : shuffled) {
                reordered.tokens(e.getKey(), e.getValue());
            }
            assertEquals(marking, reordered.build(), "equality ignores order");
            assertEquals(marking.hashCode(), reordered.build().hashCode());
            built.add(marking);
        }
    }

    /** Markings of 200 and 70,000 places index them in wider tables; lookups and order still hold. */
    @Test
    void largeMarkings_findEveryPlace_andKeepTheirOrder() {
        for (int n : new int[] {1, 2, 127, 128, 200, 65_534, 65_535, 70_000}) {
            var places = new ArrayList<Place<TestValue>>();
            var builder = MarkingState.builder();
            for (int i = n - 1; i >= 0; i--) {
                var place = Place.of("q" + i, TestValue.class);
                places.add(place);
                builder.tokens(place, i % 5 + 1);
            }
            var marking = builder.build();
            assertEquals(n, marking.placesWithTokens().size());
            assertEquals(places, List.copyOf(marking.placesWithTokens()));
            for (int i = 0; i < n; i++) {
                assertEquals((n - 1 - i) % 5 + 1, marking.tokens(Place.of("q" + (n - 1 - i), TestValue.class)));
            }
            assertEquals(0, marking.tokens(Place.of("q" + n, TestValue.class)));
            var derived = MarkingState.builder().copyFrom(marking).removeTokens(places.getFirst(), 1).build();
            assertEquals(marking.tokens(places.getFirst()) - 1, derived.tokens(places.getFirst()));
        }
    }

    @Test
    void derivedMarking_keepsItsSourcesOrder_movesARefilledPlaceToTheEnd() {
        var source = MarkingState.builder().tokens(p3, 1).tokens(p1, 2).tokens(p2, 1).build();
        var moved = MarkingState.builder().copyFrom(source).removeTokens(p3, 1).addTokens(p3, 1).build();
        assertEquals(List.of(p1, p2, p3), List.copyOf(moved.placesWithTokens()));
        assertEquals(source, moved);
        var counted = MarkingState.builder().copyFrom(source).removeTokens(p1, 1).addTokens(p2, 3).build();
        assertEquals(List.of(p3, p1, p2), List.copyOf(counted.placesWithTokens()));
        assertEquals(Map.of(p3, 1, p1, 1, p2, 4), counted.asMap());
        assertTrue(MarkingState.builder().copyFrom(source).tokens(p1, 0).tokens(p2, 0).tokens(p3, 0).build().isEmpty());
    }
}
