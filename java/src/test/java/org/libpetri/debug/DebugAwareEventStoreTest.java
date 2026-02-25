package org.libpetri.debug;

import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;
import org.junit.jupiter.api.Test;

import java.time.Instant;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class DebugAwareEventStoreTest {

    @Test
    void shouldDelegateAppendToBothStores() {
        var primary = EventStore.inMemory();
        var debug = new DebugEventStore("test");
        var store = new DebugAwareEventStore(primary, debug);

        var event = new NetEvent.TransitionEnabled(Instant.now(), "T1");
        store.append(event);

        assertEquals(1, primary.size());
        assertEquals(1, debug.size());
        assertEquals(List.of(event), primary.events());
        assertEquals(List.of(event), debug.events());
    }

    @Test
    void shouldReturnEventsAndSizeFromPrimaryOnly() {
        var primary = EventStore.inMemory();
        var debug = new DebugEventStore("test", 1); // Small capacity for eviction
        var store = new DebugAwareEventStore(primary, debug);

        for (int i = 0; i < 5; i++) {
            store.append(new NetEvent.TransitionEnabled(Instant.now(), "T" + i));
        }

        // Primary has all 5, debug may have evicted
        assertEquals(5, store.size());
        assertEquals(5, store.events().size());
        assertFalse(store.isEmpty());
    }

    @Test
    void shouldAlwaysBeEnabled() {
        var store = new DebugAwareEventStore(EventStore.noop(), new DebugEventStore("test"));
        assertTrue(store.isEnabled());
    }

    @Test
    void shouldNotBreakPrimaryWhenDebugStoreThrows() {
        var primary = EventStore.inMemory();
        // Create a debug store and close it to make it error-prone (broadcast executor shut down)
        var debug = new DebugEventStore("test") {
            @Override
            public void append(NetEvent event) {
                throw new RuntimeException("debug store failure");
            }
        };
        var store = new DebugAwareEventStore(primary, debug);

        var event = new NetEvent.TransitionEnabled(Instant.now(), "T1");
        assertDoesNotThrow(() -> store.append(event));
        assertEquals(1, primary.size());
    }

    @Test
    void shouldExposeDebugStore() {
        var debug = new DebugEventStore("my-session");
        var store = new DebugAwareEventStore(EventStore.inMemory(), debug);
        assertSame(debug, store.debugStore());
        assertEquals("my-session", store.debugStore().sessionId());
    }

    @Test
    void shouldReportEmptyCorrectly() {
        var store = new DebugAwareEventStore(EventStore.inMemory(), new DebugEventStore("test"));
        assertTrue(store.isEmpty());

        store.append(new NetEvent.TransitionEnabled(Instant.now(), "T1"));
        assertFalse(store.isEmpty());
    }
}
