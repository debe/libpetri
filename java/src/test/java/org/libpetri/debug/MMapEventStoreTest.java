package org.libpetri.debug;

import org.libpetri.event.NetEvent;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Instant;
import java.util.ArrayList;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.*;

class MMapEventStoreTest {

    @TempDir
    Path tempDir;

    @Test
    void shouldWriteAndReadEvents() {
        var store = MMapEventStore.open("test-session", tempDir);

        var event1 = new NetEvent.TransitionEnabled(Instant.now(), "T1");
        var event2 = new NetEvent.TransitionEnabled(Instant.now(), "T2");

        store.append(event1);
        store.append(event2);

        assertEquals(2, store.events().size());
        store.close();
    }

    @Test
    void shouldPersistAcrossCloseAndReopen() {
        // Write events
        var store1 = MMapEventStore.open("persist-test", tempDir);
        store1.append(new NetEvent.TransitionEnabled(Instant.now(), "T1"));
        store1.append(new NetEvent.TransitionEnabled(Instant.now(), "T2"));
        store1.append(new NetEvent.LogMessage(Instant.now(), "T1", "com.Foo", "INFO", "hello", null, null));
        store1.close();

        // Reopen and verify replay
        var store2 = MMapEventStore.open("persist-test", tempDir);
        var events = store2.events();
        assertEquals(3, events.size());
        assertInstanceOf(NetEvent.TransitionEnabled.class, events.get(0));
        assertEquals("T1", ((NetEvent.TransitionEnabled) events.get(0)).transitionName());
        assertInstanceOf(NetEvent.LogMessage.class, events.get(2));
        assertEquals("hello", ((NetEvent.LogMessage) events.get(2)).message());
        store2.close();
    }

    @Test
    void shouldCreateFileInDirectory() {
        var store = MMapEventStore.open("file-test", tempDir);
        assertTrue(Files.exists(tempDir.resolve("file-test.events")));
        assertEquals(tempDir.resolve("file-test.events"), store.filePath());
        store.close();
    }

    @Test
    void shouldGrowFileWhenNeeded() {
        var store = MMapEventStore.open("grow-test", tempDir);

        // Write enough events to exceed initial 4MB
        // Each event is ~100-200 bytes serialized, so ~30000 events should work
        // Note: DebugEventStore has DEFAULT_MAX_EVENTS=10000, so in-memory store evicts
        for (int i = 0; i < 30000; i++) {
            store.append(new NetEvent.TransitionEnabled(Instant.now(), "T" + i));
        }

        // eventCount() tracks total appended; events() returns only retained in memory
        assertEquals(30000, store.eventCount());
        assertTrue(store.events().size() <= DebugEventStore.DEFAULT_MAX_EVENTS);
        store.close();
    }

    @Test
    void shouldBroadcastToSubscribers() throws InterruptedException {
        var store = MMapEventStore.open("sub-test", tempDir);
        var received = new ArrayList<NetEvent>();
        var latch = new CountDownLatch(2);

        store.subscribe(event -> {
            received.add(event);
            latch.countDown();
        });

        store.append(new NetEvent.TransitionEnabled(Instant.now(), "T1"));
        store.append(new NetEvent.TransitionEnabled(Instant.now(), "T2"));

        assertTrue(latch.await(1, TimeUnit.SECONDS));
        assertEquals(2, received.size());
        store.close();
    }

    @Test
    void shouldContinueAppendingAfterReopen() {
        // Write initial events
        var store1 = MMapEventStore.open("continue-test", tempDir);
        store1.append(new NetEvent.TransitionEnabled(Instant.now(), "T1"));
        store1.close();

        // Reopen and append more
        var store2 = MMapEventStore.open("continue-test", tempDir);
        assertEquals(1, store2.events().size()); // replayed event
        store2.append(new NetEvent.TransitionEnabled(Instant.now(), "T2"));
        assertEquals(2, store2.events().size());
        store2.close();

        // Verify all events persist
        var store3 = MMapEventStore.open("continue-test", tempDir);
        assertEquals(2, store3.events().size());
        store3.close();
    }

    @Test
    void shouldReturnSessionId() {
        var store = MMapEventStore.open("my-session", tempDir);
        assertEquals("my-session", store.sessionId());
        store.close();
    }
}
