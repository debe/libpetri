package org.libpetri.debug;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.*;

class LogCaptureScopeForwardingExecutorTest {

    private ExecutorService underlying;
    private ExecutorService wrapped;

    @BeforeEach
    void setUp() {
        underlying = Executors.newFixedThreadPool(2);
        wrapped = LogCaptureScopeForwardingExecutor.wrap(underlying);
    }

    @AfterEach
    void tearDown() {
        wrapped.shutdownNow();
    }

    @Test
    void shouldPropagateScopeViaExecute() throws InterruptedException {
        var captured = new AtomicReference<LogCaptureScope.LogSink>();
        var latch = new CountDownLatch(1);

        LogCaptureScope.run("T1", _ -> {}, () -> {
            wrapped.execute(() -> {
                captured.set(LogCaptureScope.current());
                latch.countDown();
            });
        });

        assertTrue(latch.await(1, TimeUnit.SECONDS));
        assertNotNull(captured.get());
        assertEquals("T1", captured.get().transitionName());
    }

    @Test
    void shouldPropagateScopeViaSubmitRunnable() throws Exception {
        var captured = new AtomicReference<LogCaptureScope.LogSink>();

        LogCaptureScope.run("T2", _ -> {}, () -> {
            var future = wrapped.submit(() -> {
                captured.set(LogCaptureScope.current());
            });
            try { future.get(1, TimeUnit.SECONDS); } catch (Exception e) { throw new RuntimeException(e); }
        });

        assertNotNull(captured.get());
        assertEquals("T2", captured.get().transitionName());
    }

    @Test
    void shouldPropagateScopeViaSubmitCallable() throws Exception {
        var result = LogCaptureScope.call("T3", _ -> {}, () -> {
            var future = wrapped.submit(() -> {
                var sink = LogCaptureScope.current();
                return sink != null ? sink.transitionName() : "none";
            });
            try {
                return future.get(1, TimeUnit.SECONDS);
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        });

        assertEquals("T3", result);
    }

    @Test
    void shouldPropagateScopeViaInvokeAll() throws Exception {
        var results = LogCaptureScope.call("T4", _ -> {}, () -> {
            Callable<String> task = () -> {
                var sink = LogCaptureScope.current();
                return sink != null ? sink.transitionName() : "none";
            };
            try {
                var futures = wrapped.invokeAll(List.of(task, task));
                return futures.stream()
                    .map(f -> { try { return f.get(); } catch (Exception e) { return "error"; } })
                    .toList();
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
        });

        assertEquals(List.of("T4", "T4"), results);
    }

    @Test
    void shouldDelegateLifecycleMethods() {
        assertFalse(wrapped.isShutdown());
        assertFalse(wrapped.isTerminated());

        wrapped.shutdown();
        assertTrue(wrapped.isShutdown());
    }
}
