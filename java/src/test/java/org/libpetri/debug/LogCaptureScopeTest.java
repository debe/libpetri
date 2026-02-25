package org.libpetri.debug;

import org.libpetri.event.NetEvent;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.time.Instant;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.*;

class LogCaptureScopeTest {

    @Test
    void currentShouldBeNullWhenUnbound() {
        assertNull(LogCaptureScope.current());
    }

    @Test
    void shouldBindSinkDuringRun() {
        var captured = new AtomicReference<LogCaptureScope.LogSink>();
        LogCaptureScope.run("T1", _ -> {}, () -> {
            captured.set(LogCaptureScope.current());
        });

        assertNotNull(captured.get());
        assertEquals("T1", captured.get().transitionName());
        // After run(), scope should be unbound again
        assertNull(LogCaptureScope.current());
    }

    @Test
    void shouldBindSinkDuringCall() throws Throwable {
        var result = LogCaptureScope.call("T1", _ -> {}, () -> {
            var sink = LogCaptureScope.current();
            assertNotNull(sink);
            return sink.transitionName();
        });

        assertEquals("T1", result);
        assertNull(LogCaptureScope.current());
    }

    @Test
    void shouldDeliverLogMessagesToSink() {
        var messages = new CopyOnWriteArrayList<NetEvent.LogMessage>();
        LogCaptureScope.run("T1", messages::add, () -> {
            var sink = LogCaptureScope.current();
            sink.accept(new NetEvent.LogMessage(Instant.now(), "T1", "logger", "INFO", "hello", null, null));
        });

        assertEquals(1, messages.size());
        assertEquals("hello", messages.getFirst().message());
    }

    @Test
    void wrapRunnableShouldPropagateScopeAcrossThreads() throws InterruptedException {
        var captured = new AtomicReference<LogCaptureScope.LogSink>();
        var latch = new CountDownLatch(1);

        LogCaptureScope.run("T1", _ -> {}, () -> {
            var wrapped = LogCaptureScope.wrapRunnable(() -> {
                captured.set(LogCaptureScope.current());
                latch.countDown();
            });

            try (var executor = Executors.newSingleThreadExecutor()) {
                executor.execute(wrapped);
            }
        });

        assertTrue(latch.await(1, TimeUnit.SECONDS));
        assertNotNull(captured.get());
        assertEquals("T1", captured.get().transitionName());
    }

    @Test
    void wrapCallableShouldPropagateScopeAcrossThreads() throws Exception {
        var result = LogCaptureScope.call("T1", _ -> {}, () -> {
            var wrapped = LogCaptureScope.wrapCallable(() -> {
                var sink = LogCaptureScope.current();
                return sink != null ? sink.transitionName() : "none";
            });

            try (var executor = Executors.newSingleThreadExecutor()) {
                return executor.submit(wrapped).get(1, TimeUnit.SECONDS);
            }
        });

        assertEquals("T1", result);
    }

    @Test
    void wrapRunnableShouldReturnSameInstanceWhenNoScope() {
        Runnable original = () -> {};
        Runnable wrapped = LogCaptureScope.wrapRunnable(original);
        assertSame(original, wrapped);
    }

    @Nested
    class LogSinkReentryGuard {

        @Test
        void tryEnterShouldPreventReentry() {
            var sink = new LogCaptureScope.LogSink("T1", _ -> {});

            assertTrue(sink.tryEnter());
            assertFalse(sink.tryEnter()); // Reentry blocked
            sink.exit();
            assertTrue(sink.tryEnter()); // After exit, can enter again
            sink.exit();
        }

        @Test
        void copyShouldCreateIndependentGuard() {
            var sink = new LogCaptureScope.LogSink("T1", _ -> {});
            assertTrue(sink.tryEnter()); // Original is now capturing

            var copy = sink.copy();
            assertEquals("T1", copy.transitionName());
            assertTrue(copy.tryEnter()); // Copy has independent guard

            copy.exit();
            sink.exit();
        }
    }
}
