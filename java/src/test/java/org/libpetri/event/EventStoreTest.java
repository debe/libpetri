package org.libpetri.event;

import org.junit.jupiter.api.Test;
import org.libpetri.core.Token;

import java.time.Duration;
import java.time.Instant;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.*;

class EventStoreTest {

    /**
     * EVT-030 (every helper is total) and EVT-013 AC4: an engine diagnostic no transition is
     * responsible for carries no transition name, and both executors emit one on an interrupted
     * run. Filtering by transition must skip it, not throw.
     */
    @Test
    void transitionEventsSkipsAnEventWithNoTransitionName_EVT030_AC2() {
        var store = EventStore.inMemory();
        var first = new NetEvent.TransitionStarted(Instant.EPOCH, "t", List.of());
        var nameless = new NetEvent.LogMessage(Instant.EPOCH, null, "libpetri.runtime", "WARN", "x", null, null);
        var namelessEnabled = new NetEvent.TransitionEnabled(Instant.EPOCH, null);
        var second = new NetEvent.TransitionStarted(Instant.EPOCH, "t", List.of());
        store.append(first);
        store.append(nameless);
        store.append(namelessEnabled);
        store.append(second);

        assertEquals(List.of(first, second), store.transitionEvents("t"));
    }

    private static final NetEvent STARTED = new NetEvent.ExecutionStarted(Instant.EPOCH, "net", "run");
    private static final NetEvent ADD_A1 = new NetEvent.TokenAdded(Instant.ofEpochMilli(1), "A", Token.of("a1"));
    private static final NetEvent T_STARTED = new NetEvent.TransitionStarted(Instant.EPOCH, "t", List.of());
    private static final NetEvent REMOVE_A = new NetEvent.TokenRemoved(Instant.ofEpochMilli(3), "A", Token.of("a1"));
    private static final NetEvent ADD_B = new NetEvent.TokenAdded(Instant.ofEpochMilli(4), "B", Token.of("b"));
    private static final NetEvent ADD_A2 = new NetEvent.TokenAdded(Instant.ofEpochMilli(5), "A", Token.of("a2"));
    private static final NetEvent ADD_C = new NetEvent.TokenAdded(Instant.ofEpochMilli(6), "C", Token.of("c"));
    private static final NetEvent T_COMPLETED =
        new NetEvent.TransitionCompleted(Instant.EPOCH, "t", List.of(), Duration.ZERO);

    private static EventStore mixedStore() {
        var store = EventStore.inMemory();
        for (var e : List.of(STARTED, ADD_A1, T_STARTED, REMOVE_A, ADD_B, ADD_A2, ADD_C, T_COMPLETED)) {
            store.append(e);
        }
        return store;
    }

    /** [EVT-030] AC3: the place filter returns only the token events of the named places, in store order. */
    @Test
    void placeEventsReturnsOnlyTokenEventsOfTheNamedPlaces_EVT030_AC3() {
        var store = mixedStore();

        assertEquals(List.of(ADD_A1, REMOVE_A, ADD_A2), store.placeEvents("A"));
        assertEquals(List.of(ADD_A1, REMOVE_A, ADD_B, ADD_A2), store.placeEvents("A", "B"));
        assertEquals(List.of(), store.placeEvents("missing"));
        assertEquals(List.of(), store.placeEvents());
    }

    /** [EVT-030] AC3: offset and limit page the filtered result, not the store. */
    @Test
    void offsetAndLimitPageTheFilteredResult_EVT030_AC3() {
        var store = mixedStore();
        Predicate<NetEvent> onA = store.placeEvents("A")::contains;

        assertEquals(List.of(REMOVE_A, ADD_A2), store.filter(onA, 1, 5));
        assertEquals(List.of(ADD_A1), store.filter(onA, 0, 1));
        assertEquals(List.of(REMOVE_A), store.filter(onA, 1, 1));
        assertEquals(List.of(), store.filter(onA, 3, 5));
        assertEquals(List.of(), store.filter(onA, 0, 0));
        assertEquals(store.filter(onA), store.filter(onA, 0, Integer.MAX_VALUE));
        assertThrows(IllegalArgumentException.class, () -> store.filter(onA, -1, 1));
        assertThrows(IllegalArgumentException.class, () -> store.filter(onA, 0, -1));
    }

    /** [EVT-030] AC5: counters() names each occurring type once, sorted, and sums to the event count. */
    @Test
    void countersIsAnEventTypeHistogramSummingToTheEventCount_EVT030_AC5() {
        var store = mixedStore();

        var counters = store.counters();

        assertEquals(Map.of(
            "ExecutionStarted", 1,
            "TokenAdded", 4,
            "TokenRemoved", 1,
            "TransitionCompleted", 1,
            "TransitionStarted", 1), counters);
        assertEquals(List.of("ExecutionStarted", "TokenAdded", "TokenRemoved",
            "TransitionCompleted", "TransitionStarted"), List.copyOf(counters.keySet()));
        assertEquals(store.size(), counters.values().stream().mapToInt(Integer::intValue).sum());
        assertThrows(UnsupportedOperationException.class, () -> counters.put("x", 1));
        assertEquals(Map.of(), EventStore.inMemory().counters());
    }
}
