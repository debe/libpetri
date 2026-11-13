package org.libpetri.event;

import org.junit.jupiter.api.Test;

import java.time.Instant;
import java.util.List;

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
}
