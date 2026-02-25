package org.libpetri.debug;

import org.libpetri.core.Token;
import org.libpetri.event.NetEvent;
import org.junit.jupiter.api.Test;

import java.time.Instant;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.*;

class DebugEventStoreTest {

    @Test
    void shouldStoreAndRetrieveEvents() {
        var store = new DebugEventStore("test-session");

        var event1 = new NetEvent.TransitionEnabled(Instant.now(), "T1");
        var event2 = new NetEvent.TransitionEnabled(Instant.now(), "T2");

        store.append(event1);
        store.append(event2);

        assertEquals(2, store.size());
        assertEquals(2, store.eventCount());
        assertEquals(List.of(event1, event2), store.events());
    }

    @Test
    void shouldBroadcastEventsToSubscribers() throws InterruptedException {
        var store = new DebugEventStore("test-session");
        var received = new CopyOnWriteArrayList<NetEvent>();
        var latch = new CountDownLatch(2);

        var subscription = store.subscribe(event -> {
            received.add(event);
            latch.countDown();
        });

        var event1 = new NetEvent.TransitionEnabled(Instant.now(), "T1");
        var event2 = new NetEvent.TransitionEnabled(Instant.now(), "T2");

        store.append(event1);
        store.append(event2);

        assertTrue(latch.await(1, TimeUnit.SECONDS));
        assertEquals(List.of(event1, event2), List.copyOf(received));
        assertTrue(subscription.isActive());
    }

    @Test
    void shouldStopBroadcastingAfterUnsubscribe() throws InterruptedException {
        var store = new DebugEventStore("test-session");
        var received = new CopyOnWriteArrayList<NetEvent>();
        var firstEventLatch = new CountDownLatch(1);

        var subscription = store.subscribe(event -> {
            received.add(event);
            firstEventLatch.countDown();
        });

        store.append(new NetEvent.TransitionEnabled(Instant.now(), "T1"));

        // Wait for async broadcast to deliver the first event
        assertTrue(firstEventLatch.await(1, TimeUnit.SECONDS));

        subscription.cancel();
        assertFalse(subscription.isActive());

        store.append(new NetEvent.TransitionEnabled(Instant.now(), "T2"));

        // Give the broadcast executor time to process (if it would)
        Thread.sleep(50);

        assertEquals(1, received.size());
    }

    @Test
    void shouldQueryEventsSinceTimestamp() throws InterruptedException {
        var store = new DebugEventStore("test-session");

        var event1 = new NetEvent.TransitionEnabled(Instant.now(), "T1");
        Thread.sleep(10);
        var midpoint = Instant.now();
        Thread.sleep(10);
        var event2 = new NetEvent.TransitionEnabled(Instant.now(), "T2");

        store.append(event1);
        store.append(event2);

        var eventsSince = store.eventsSince(midpoint);
        assertEquals(1, eventsSince.size());
        assertEquals("T2", ((NetEvent.TransitionEnabled) eventsSince.getFirst()).transitionName());
    }

    @Test
    void shouldQueryEventsBetweenTimestamps() throws InterruptedException {
        var store = new DebugEventStore("test-session");

        var event1 = new NetEvent.TransitionEnabled(Instant.now(), "T1");
        Thread.sleep(10);
        var from = Instant.now();
        Thread.sleep(10);
        var event2 = new NetEvent.TransitionEnabled(Instant.now(), "T2");
        Thread.sleep(10);
        var to = Instant.now();
        Thread.sleep(10);
        var event3 = new NetEvent.TransitionEnabled(Instant.now(), "T3");

        store.append(event1);
        store.append(event2);
        store.append(event3);

        var eventsBetween = store.eventsBetween(from, to);
        assertEquals(1, eventsBetween.size());
        assertEquals("T2", ((NetEvent.TransitionEnabled) eventsBetween.getFirst()).transitionName());
    }

    @Test
    void shouldQueryEventsFromIndex() {
        var store = new DebugEventStore("test-session");

        for (int i = 0; i < 5; i++) {
            store.append(new NetEvent.TransitionEnabled(Instant.now(), "T" + i));
        }

        var eventsFrom = store.eventsFrom(3);
        assertEquals(2, eventsFrom.size());
        assertEquals("T3", ((NetEvent.TransitionEnabled) eventsFrom.get(0)).transitionName());
        assertEquals("T4", ((NetEvent.TransitionEnabled) eventsFrom.get(1)).transitionName());
    }

    @Test
    void shouldSupportMultipleSubscribers() throws InterruptedException {
        var store = new DebugEventStore("test-session");
        var received1 = new CopyOnWriteArrayList<NetEvent>();
        var received2 = new CopyOnWriteArrayList<NetEvent>();
        var latch = new CountDownLatch(2);

        store.subscribe(event -> { received1.add(event); latch.countDown(); });
        store.subscribe(event -> { received2.add(event); latch.countDown(); });

        var event = new NetEvent.TransitionEnabled(Instant.now(), "T1");
        store.append(event);

        assertTrue(latch.await(1, TimeUnit.SECONDS));
        assertEquals(1, received1.size());
        assertEquals(1, received2.size());
        assertEquals(2, store.subscriberCount());
    }

    @Test
    void shouldReturnSessionId() {
        var store = new DebugEventStore("my-session-id");
        assertEquals("my-session-id", store.sessionId());
    }

    @Test
    void shouldReportEnabled() {
        var store = new DebugEventStore("test-session");
        assertTrue(store.isEnabled());
    }

    @Test
    void shouldEvictOldestEventsWhenCapacityExceeded() {
        var store = new DebugEventStore("test-session", 3);

        for (int i = 0; i < 5; i++) {
            store.append(new NetEvent.TransitionEnabled(Instant.now(), "T" + i));
        }

        // Should retain only the last 3 events
        assertEquals(3, store.events().size());
        assertEquals(5, store.eventCount());
        assertEquals(2, store.evictedCount());
        assertEquals(3, store.maxEvents());

        // Verify the retained events are T2, T3, T4
        var names = store.events().stream()
                .map(e -> ((NetEvent.TransitionEnabled) e).transitionName())
                .toList();
        assertEquals(List.of("T2", "T3", "T4"), names);
    }

    @Test
    void shouldAdjustEventsFromForEvictedEvents() {
        var store = new DebugEventStore("test-session", 5);

        for (int i = 0; i < 8; i++) {
            store.append(new NetEvent.TransitionEnabled(Instant.now(), "T" + i));
        }

        // 3 events evicted (T0, T1, T2), retained: T3, T4, T5, T6, T7
        assertEquals(3, store.evictedCount());

        // fromIndex=0 should return all retained events (evicted events are gone)
        assertEquals(5, store.eventsFrom(0).size());

        // fromIndex=3 should also return all retained (T3 is the first retained)
        assertEquals(5, store.eventsFrom(3).size());

        // fromIndex=5 should skip T3 and T4, returning T5, T6, T7
        var from5 = store.eventsFrom(5);
        assertEquals(3, from5.size());
        assertEquals("T5", ((NetEvent.TransitionEnabled) from5.get(0)).transitionName());

        // fromIndex=8 should return empty (past the end)
        assertEquals(0, store.eventsFrom(8).size());
    }

    @Test
    void shouldNotEvictWhenUnderCapacity() {
        var store = new DebugEventStore("test-session", 10);

        for (int i = 0; i < 5; i++) {
            store.append(new NetEvent.TransitionEnabled(Instant.now(), "T" + i));
        }

        assertEquals(5, store.events().size());
        assertEquals(5, store.eventCount());
        assertEquals(0, store.evictedCount());
    }

    @Test
    void shouldRejectNonPositiveMaxEvents() {
        assertThrows(IllegalArgumentException.class, () -> new DebugEventStore("test", 0));
        assertThrows(IllegalArgumentException.class, () -> new DebugEventStore("test", -1));
    }

    @Test
    void shouldUseDefaultMaxEvents() {
        var store = new DebugEventStore("test-session");
        assertEquals(DebugEventStore.DEFAULT_MAX_EVENTS, store.maxEvents());
    }

    @Test
    void sizeShouldEqualEventsListSizeAfterEviction() {
        var store = new DebugEventStore("test-session", 3);

        for (int i = 0; i < 10; i++) {
            store.append(new NetEvent.TransitionEnabled(Instant.now(), "T" + i));
        }

        assertEquals(store.events().size(), store.size());
        assertEquals(3, store.size());
    }

    @Test
    void shouldNotBreakWhenSubscriberThrows() throws InterruptedException {
        var store = new DebugEventStore("test-session");
        var received = new CopyOnWriteArrayList<NetEvent>();
        var latch = new CountDownLatch(1);

        // First subscriber throws
        store.subscribe(_ -> { throw new RuntimeException("boom"); });
        // Second subscriber should still receive events
        store.subscribe(event -> {
            received.add(event);
            latch.countDown();
        });

        store.append(new NetEvent.TransitionEnabled(Instant.now(), "T1"));

        assertTrue(latch.await(1, TimeUnit.SECONDS));
        assertEquals(1, received.size());
    }

    @Test
    void shouldStoreAndBroadcastLogMessageEvents() throws InterruptedException {
        var store = new DebugEventStore("test-session");
        var received = new CopyOnWriteArrayList<NetEvent>();
        var latch = new CountDownLatch(1);

        store.subscribe(event -> {
            received.add(event);
            latch.countDown();
        });

        var logEvent = new NetEvent.LogMessage(
            Instant.now(), "T1", "com.example.Foo", "INFO", "hello world", null, null
        );
        store.append(logEvent);

        assertTrue(latch.await(1, TimeUnit.SECONDS));
        assertEquals(1, store.events().size());
        assertEquals(1, received.size());
        assertInstanceOf(NetEvent.LogMessage.class, received.getFirst());
        assertEquals("hello world", ((NetEvent.LogMessage) received.getFirst()).message());
    }

    @Test
    void slowSubscriberShouldNotBlockAppend() throws InterruptedException {
        var store = new DebugEventStore("test-session");
        var slowSubscriberReceived = new CountDownLatch(1);

        // Subscriber that sleeps 200ms to simulate slow WebSocket write
        store.subscribe(_ -> {
            try { Thread.sleep(200); } catch (InterruptedException e) { Thread.currentThread().interrupt(); }
            slowSubscriberReceived.countDown();
        });

        long start = System.nanoTime();
        store.append(new NetEvent.TransitionEnabled(Instant.now(), "T1"));
        long elapsed = TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - start);

        // append() should return well before the 200ms subscriber sleep
        assertTrue(elapsed < 50, "append() took " + elapsed + "ms, expected <50ms (subscriber should not block)");

        // Verify the slow subscriber still eventually receives the event
        assertTrue(slowSubscriberReceived.await(1, TimeUnit.SECONDS));
    }

    @Test
    void shouldPreserveEventOrderingAcrossAsyncBroadcast() throws InterruptedException {
        var store = new DebugEventStore("test-session");
        int eventCount = 100;
        var received = new CopyOnWriteArrayList<NetEvent>();
        var latch = new CountDownLatch(eventCount);

        store.subscribe(event -> {
            received.add(event);
            latch.countDown();
        });

        var events = new ArrayList<NetEvent>();
        for (int i = 0; i < eventCount; i++) {
            events.add(new NetEvent.TransitionEnabled(Instant.now(), "T" + i));
        }

        for (var event : events) {
            store.append(event);
        }

        assertTrue(latch.await(2, TimeUnit.SECONDS));
        assertEquals(events, List.copyOf(received), "Events should be received in order");
    }

    @Test
    void closeShouldStopBroadcastExecutor() throws InterruptedException {
        var store = new DebugEventStore("test-session");
        var received = new CopyOnWriteArrayList<NetEvent>();
        var latch = new CountDownLatch(1);

        store.subscribe(event -> {
            received.add(event);
            latch.countDown();
        });

        store.append(new NetEvent.TransitionEnabled(Instant.now(), "T1"));
        assertTrue(latch.await(1, TimeUnit.SECONDS));

        store.close();

        // After close, new events are stored but not broadcast
        store.append(new NetEvent.TransitionEnabled(Instant.now(), "T2"));
        Thread.sleep(50);

        assertEquals(1, received.size(), "Broadcast should stop after close()");
        assertEquals(2, store.size(), "Events should still be stored after close()");
    }

    @Test
    void shutdownBroadcastShouldWaitForPendingBroadcasts() throws InterruptedException {
        var store = new DebugEventStore("test-session");
        var received = new CopyOnWriteArrayList<NetEvent>();
        var latch = new CountDownLatch(1);

        store.subscribe(event -> {
            try { Thread.sleep(100); } catch (InterruptedException e) { Thread.currentThread().interrupt(); }
            received.add(event);
            latch.countDown();
        });

        store.append(new NetEvent.TransitionEnabled(Instant.now(), "T1"));
        store.shutdownBroadcast();

        // After shutdown returns, the pending broadcast should have completed
        assertTrue(latch.await(1, TimeUnit.SECONDS), "Pending broadcast should complete before shutdown returns");
        assertEquals(1, received.size());
    }
}
