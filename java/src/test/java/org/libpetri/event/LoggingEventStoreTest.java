package org.libpetri.event;

import org.libpetri.core.Token;
import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.time.Instant;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

class LoggingEventStoreTest {

    @Test
    void shouldDelegateAppendToWrappedStore() {
        var inner = EventStore.inMemory();
        var logging = EventStore.logging(inner);

        var event = new NetEvent.TransitionEnabled(Instant.now(), "T1");
        logging.append(event);

        assertEquals(1, inner.size());
        assertEquals(List.of(event), logging.events());
    }

    @Test
    void shouldDelegateSizeAndIsEmptyToWrappedStore() {
        var inner = EventStore.inMemory();
        var logging = EventStore.logging(inner);

        assertTrue(logging.isEmpty());
        assertEquals(0, logging.size());

        logging.append(new NetEvent.TransitionEnabled(Instant.now(), "T1"));
        assertFalse(logging.isEmpty());
        assertEquals(1, logging.size());
    }

    @Test
    void shouldAlwaysBeEnabled() {
        var logging = EventStore.logging(EventStore.noop());
        assertTrue(logging.isEnabled());
    }

    @Test
    void shouldReturnEventsFromDelegate() {
        var inner = EventStore.inMemory();
        var logging = EventStore.logging(inner);

        var event1 = new NetEvent.TransitionEnabled(Instant.now(), "T1");
        var event2 = new NetEvent.TransitionEnabled(Instant.now(), "T2");
        logging.append(event1);
        logging.append(event2);

        assertEquals(List.of(event1, event2), logging.events());
    }

    @Test
    void shouldAppendAllThirteenEventTypesWithoutThrowing() {
        var logging = EventStore.logging(EventStore.inMemory());
        var now = Instant.now();
        var token = Token.of("test");

        assertDoesNotThrow(() -> {
            logging.append(new NetEvent.ExecutionStarted(now, "Net", "exec-1"));
            logging.append(new NetEvent.ExecutionCompleted(now, "Net", "exec-1", Duration.ofMillis(100)));
            logging.append(new NetEvent.TransitionEnabled(now, "T1"));
            logging.append(new NetEvent.TransitionClockRestarted(now, "T1"));
            logging.append(new NetEvent.TransitionStarted(now, "T1", List.of(token)));
            logging.append(new NetEvent.TransitionCompleted(now, "T1", List.of(token), Duration.ofMillis(50)));
            logging.append(new NetEvent.TransitionFailed(now, "T1", "error", "RuntimeException"));
            logging.append(new NetEvent.TransitionTimedOut(now, "T1", Duration.ofMillis(1000), Duration.ofMillis(1200)));
            logging.append(new NetEvent.ActionTimedOut(now, "T1", Duration.ofMillis(500)));
            logging.append(new NetEvent.TokenAdded(now, "P1", token));
            logging.append(new NetEvent.TokenRemoved(now, "P1", token));
            logging.append(new NetEvent.MarkingSnapshot(now, Map.of("P1", List.of(token))));
            logging.append(new NetEvent.LogMessage(now, "T1", "logger", "INFO", "msg", null, null));
        });

        assertEquals(13, logging.size());
    }
}
