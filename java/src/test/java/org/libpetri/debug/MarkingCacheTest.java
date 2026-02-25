package org.libpetri.debug;

import org.libpetri.core.Token;
import org.libpetri.event.NetEvent;
import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.*;

class MarkingCacheTest {

    @Test
    void emptyEventsShouldReturnEmptyState() {
        var cache = new MarkingCache();
        var state = cache.computeAt(List.of(), 0);

        assertTrue(state.marking().isEmpty());
        assertTrue(state.enabledTransitions().isEmpty());
        assertTrue(state.inFlightTransitions().isEmpty());
    }

    @Test
    void shouldMatchBruteForceForSmallEventList() {
        var events = generateEvents(50);
        var cache = new MarkingCache();

        for (int i = 0; i <= events.size(); i++) {
            var expected = DebugProtocolHandler.computeState(events.subList(0, i));
            var actual = cache.computeAt(events, i);
            assertEquals(expected.marking(), actual.marking(), "Marking mismatch at index " + i);
            assertEquals(expected.enabledTransitions(), actual.enabledTransitions(),
                "Enabled transitions mismatch at index " + i);
            assertEquals(expected.inFlightTransitions(), actual.inFlightTransitions(),
                "In-flight transitions mismatch at index " + i);
        }
    }

    @Test
    void shouldMatchBruteForceForLargeEventList() {
        var events = generateEvents(1000);
        var cache = new MarkingCache();
        var rng = new Random(42);

        // Test random indices
        for (int trial = 0; trial < 50; trial++) {
            int idx = rng.nextInt(events.size() + 1);
            var expected = DebugProtocolHandler.computeState(events.subList(0, idx));
            var actual = cache.computeAt(events, idx);
            assertEquals(expected.marking(), actual.marking(), "Marking mismatch at index " + idx);
            assertEquals(expected.enabledTransitions(), actual.enabledTransitions(),
                "Enabled transitions mismatch at index " + idx);
            assertEquals(expected.inFlightTransitions(), actual.inFlightTransitions(),
                "In-flight transitions mismatch at index " + idx);
        }
    }

    @Test
    void shouldMatchAtSnapshotBoundaries() {
        int interval = MarkingCache.SNAPSHOT_INTERVAL;
        var events = generateEvents(interval * 3 + 10);
        var cache = new MarkingCache();

        // Test at exact boundaries
        for (int boundary : List.of(interval, interval * 2, interval * 3)) {
            if (boundary <= events.size()) {
                var expected = DebugProtocolHandler.computeState(events.subList(0, boundary));
                var actual = cache.computeAt(events, boundary);
                assertEquals(expected.marking(), actual.marking(),
                    "Marking mismatch at boundary " + boundary);
                assertEquals(expected.enabledTransitions(), actual.enabledTransitions(),
                    "Enabled transitions mismatch at boundary " + boundary);
                assertEquals(expected.inFlightTransitions(), actual.inFlightTransitions(),
                    "In-flight transitions mismatch at boundary " + boundary);
            }
        }
    }

    @Test
    void shouldMatchJustBeforeAndAfterBoundaries() {
        int interval = MarkingCache.SNAPSHOT_INTERVAL;
        var events = generateEvents(interval * 2 + 10);
        var cache = new MarkingCache();

        for (int offset : List.of(interval - 1, interval + 1, interval * 2 - 1, interval * 2 + 1)) {
            if (offset <= events.size()) {
                var expected = DebugProtocolHandler.computeState(events.subList(0, offset));
                var actual = cache.computeAt(events, offset);
                assertEquals(expected.marking(), actual.marking(),
                    "Marking mismatch at offset " + offset);
            }
        }
    }

    @Test
    void invalidateShouldResetCache() {
        var events = generateEvents(500);
        var cache = new MarkingCache();

        // Build cache
        cache.computeAt(events, 400);

        // Invalidate and verify still works
        cache.invalidate();

        var expected = DebugProtocolHandler.computeState(events.subList(0, 300));
        var actual = cache.computeAt(events, 300);
        assertEquals(expected.marking(), actual.marking());
    }

    @Test
    void shouldHandleMarkingSnapshotEvents() {
        var events = new ArrayList<NetEvent>();
        var now = Instant.now();

        // Add some tokens
        events.add(new NetEvent.TokenAdded(now, "P1", Token.of("a")));
        events.add(new NetEvent.TokenAdded(now, "P1", Token.of("b")));

        // MarkingSnapshot resets everything
        events.add(new NetEvent.MarkingSnapshot(now, java.util.Map.of(
            "P2", List.of(Token.of("x"))
        )));

        // More events after snapshot
        events.add(new NetEvent.TokenAdded(now, "P2", Token.of("y")));

        var cache = new MarkingCache();
        for (int i = 0; i <= events.size(); i++) {
            var expected = DebugProtocolHandler.computeState(events.subList(0, i));
            var actual = cache.computeAt(events, i);
            assertEquals(expected.marking(), actual.marking(), "Marking mismatch at index " + i);
        }
    }

    /**
     * Generates a realistic event sequence with transitions and token movements.
     */
    private List<NetEvent> generateEvents(int count) {
        var events = new ArrayList<NetEvent>();
        var rng = new Random(12345);
        var transitions = List.of("T1", "T2", "T3", "T4");
        var places = List.of("P1", "P2", "P3", "P4");
        var now = Instant.now();

        for (int i = 0; i < count; i++) {
            now = now.plusMillis(1);
            int choice = rng.nextInt(6);
            switch (choice) {
                case 0 -> events.add(new NetEvent.TransitionEnabled(now, transitions.get(rng.nextInt(4))));
                case 1 -> events.add(new NetEvent.TransitionStarted(now, transitions.get(rng.nextInt(4)),
                    List.of(Token.of("input-" + i))));
                case 2 -> events.add(new NetEvent.TransitionCompleted(now, transitions.get(rng.nextInt(4)),
                    List.of(Token.of("output-" + i)), Duration.ofMillis(rng.nextInt(100))));
                case 3 -> events.add(new NetEvent.TokenAdded(now, places.get(rng.nextInt(4)),
                    Token.of("val-" + i)));
                case 4 -> events.add(new NetEvent.TokenRemoved(now, places.get(rng.nextInt(4)),
                    Token.of("val-" + i)));
                case 5 -> events.add(new NetEvent.TransitionFailed(now, transitions.get(rng.nextInt(4)),
                    "error", "RuntimeException"));
            }
        }
        return events;
    }
}
