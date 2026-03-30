package org.libpetri.runtime;

import static org.junit.jupiter.api.Assertions.*;

import java.time.Duration;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicInteger;

import org.libpetri.core.*;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.debug.LogCaptureScopeForwardingExecutor;
import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.RepeatedTest;

/**
 * Stress tests for BitmapNetExecutor with async actions that produce AND outputs
 * from a {@code finally} block via {@code CompletableFuture.runAsync} on virtual threads
 * wrapped with {@link LogCaptureScopeForwardingExecutor}.
 *
 * <p>Reproducer for the NudgeTurnComplete OutViolationException observed in production:
 * actions that produce both outputs unconditionally in a {@code finally} block occasionally
 * fail output validation (~13/day out of thousands of successful firings).
 *
 * <p>The test net mirrors NudgeTurnComplete's structure:
 * <pre>
 * ENV_INPUT → [AsyncAction] → OUTPUT_A + OUTPUT_B (AND output)
 *              ↑ reset(TIMER_PENDING)
 *              ↑ read(SHARED_CONTEXT)
 * </pre>
 *
 * @implNote The action executor chain matches production: virtual thread per task
 * wrapped with {@link LogCaptureScopeForwardingExecutor}. EventStore is enabled
 * to match the production code path where {@code LogCaptureScope.call()} wraps
 * the action invocation.
 */
class BitmapNetExecutorAsyncOutputTest {

    // ==================== Places ====================

    static final Place<String> ENV_INPUT = Place.of("EnvInput", String.class);
    static final Place<String> OUTPUT_A = Place.of("OutputA", String.class);
    static final Place<Void> OUTPUT_B = Place.of("OutputB", Void.class);
    static final Place<Void> TIMER_PENDING = Place.of("TimerPending", Void.class);
    static final Place<String> SHARED_CONTEXT = Place.of("SharedContext", String.class);

    static final EnvironmentPlace<String> ENV = EnvironmentPlace.of(ENV_INPUT);

    /**
     * Creates an action executor matching Marvin's production wrapping chain:
     * virtual thread per task + LogCaptureScopeForwardingExecutor.
     */
    private static ExecutorService createActionExecutor() {
        return LogCaptureScopeForwardingExecutor.wrap(
                Executors.newVirtualThreadPerTaskExecutor());
    }

    // ==================== Tests ====================

    @Test
    @DisplayName("Single async firing with AND output in finally block succeeds")
    void asyncAction_andOutput_producedInFinallyBlock() throws Exception {
        var actionExecutor = createActionExecutor();

        var transition = Transition.builder("AsyncAndOutput")
                .inputs(In.one(ENV_INPUT))
                .read(SHARED_CONTEXT)
                .reset(TIMER_PENDING)
                .outputs(Out.and(OUTPUT_A, OUTPUT_B))
                .action(ctx -> {
                    String input = ctx.input(ENV_INPUT);
                    return CompletableFuture.runAsync(() -> {
                        try {
                            // Simulate work
                            Thread.sleep(0, 100_000); // 100µs
                        } catch (InterruptedException e) {
                            Thread.currentThread().interrupt();
                        } finally {
                            ctx.output(OUTPUT_A, "processed-" + input);
                            ctx.output(OUTPUT_B, Token.unit());
                        }
                    }, actionExecutor);
                })
                .build();

        var net = PetriNet.builder("SingleAsyncTest").transitions(transition).build();

        // No environment places — single firing terminates naturally
        var store = EventStore.inMemory();
        try (var executor = BitmapNetExecutor.builder(net, Map.of(
                        ENV_INPUT, List.of(Token.of("test")),
                        SHARED_CONTEXT, List.of(Token.of("ctx")),
                        TIMER_PENDING, List.of(Token.unit())))
                .eventStore(store)
                .build()) {

            var marking = executor.run();

            assertTrue(marking.hasTokens(OUTPUT_A), "OUTPUT_A must have token");
            assertTrue(marking.hasTokens(OUTPUT_B), "OUTPUT_B must have token");
            assertEquals("processed-test", marking.peekFirst(OUTPUT_A).value());

            long failures = store.events().stream()
                    .filter(e -> e instanceof NetEvent.TransitionFailed)
                    .count();
            assertEquals(0, failures, "No transition failures expected");
        }
    }

    @RepeatedTest(10)
    @DisplayName("STRESS: 500 async firings with AND output in finally — zero OutViolationExceptions")
    void asyncAction_andOutput_stressTest() throws Exception {
        var actionExecutor = createActionExecutor();
        int iterations = 2000;
        var completed = new AtomicInteger(0);

        // Recycling transition: OUTPUT_A feeds back to ENV_INPUT-consuming transition
        // via a drainer that resets for next iteration
        var asyncTransition = Transition.builder("AsyncAndOutput")
                .inputs(In.one(ENV_INPUT))
                .read(SHARED_CONTEXT)
                .reset(TIMER_PENDING)
                .outputs(Out.and(OUTPUT_A, OUTPUT_B))
                .action(ctx -> {
                    String input = ctx.input(ENV_INPUT);
                    return CompletableFuture.runAsync(() -> {
                        try {
                            // no-op work — maximize firing rate to stress sync/async path
                        } finally {
                            ctx.output(OUTPUT_A, "done-" + input);
                            ctx.output(OUTPUT_B, Token.unit());
                            completed.incrementAndGet();
                        }
                    }, actionExecutor);
                })
                .build();

        // Drainer: consumes OUTPUT_A + OUTPUT_B, restores TIMER_PENDING for next cycle
        var drainer = Transition.builder("Drainer")
                .inputs(In.one(OUTPUT_A), In.one(OUTPUT_B))
                .outputs(Out.place(TIMER_PENDING))
                .action(ctx -> {
                    ctx.output(TIMER_PENDING, Token.unit());
                    return CompletableFuture.completedFuture(null);
                })
                .build();

        var net = PetriNet.builder("StressTest")
                .transitions(asyncTransition, drainer)
                .build();

        var store = EventStore.inMemory();
        try (var executor = BitmapNetExecutor.builder(net, Map.of(
                        SHARED_CONTEXT, List.of(Token.of("ctx")),
                        TIMER_PENDING, List.of(Token.unit())))
                .eventStore(store)
                .environmentPlaces(Set.of(ENV))
                .build()) {

            // Run executor in background
            var executorFuture = CompletableFuture.supplyAsync(
                    () -> executor.run(),
                    Executors.newVirtualThreadPerTaskExecutor());

            // Inject tokens rapidly
            for (int i = 0; i < iterations; i++) {
                executor.inject(ENV, "input-" + i);
            }

            // Wait for all firings to complete, then drain
            while (completed.get() < iterations) {
                Thread.sleep(10);
                if (completed.get() < iterations && executorFuture.isDone()) {
                    fail("Executor terminated before all iterations completed. Completed: " + completed.get());
                }
            }

            // Allow drainer to process remaining outputs
            Thread.sleep(100);
            executor.drain();
            executorFuture.get(10, TimeUnit.SECONDS);

            long failures = store.events().stream()
                    .filter(e -> e instanceof NetEvent.TransitionFailed f
                            && f.exceptionType().contains("OutViolationException"))
                    .count();

            assertEquals(0, failures,
                    "OutViolationException count (over " + iterations + " firings). " +
                    "Failures: " + store.events().stream()
                        .filter(e -> e instanceof NetEvent.TransitionFailed)
                        .map(e -> ((NetEvent.TransitionFailed) e).errorMessage())
                        .toList());
        }
    }

    @RepeatedTest(10)
    @DisplayName("STRESS: mixed sync/async — fast actions hit sync path, slow actions hit async path")
    void asyncAction_mixedSyncAsync_stressTest() throws Exception {
        var actionExecutor = createActionExecutor();
        int iterations = 2000;
        var completed = new AtomicInteger(0);

        var asyncTransition = Transition.builder("MixedAsyncAndOutput")
                .inputs(In.one(ENV_INPUT))
                .read(SHARED_CONTEXT)
                .reset(TIMER_PENDING)
                .outputs(Out.and(OUTPUT_A, OUTPUT_B))
                .action(ctx -> {
                    String input = ctx.input(ENV_INPUT);
                    return CompletableFuture.runAsync(() -> {
                        try {
                            // Alternate: even iterations sleep (→ async path),
                            // odd iterations are instant (→ sync path)
                            int idx = Integer.parseInt(input.split("-")[1]);
                            if (idx % 2 == 0) {
                                Thread.sleep(1); // force async path
                            }
                        } catch (Exception _) {
                            // ignore
                        } finally {
                            ctx.output(OUTPUT_A, "done-" + input);
                            ctx.output(OUTPUT_B, (Void) null);
                            completed.incrementAndGet();
                        }
                    }, actionExecutor);
                })
                .build();

        var drainer = Transition.builder("Drainer")
                .inputs(In.one(OUTPUT_A), In.one(OUTPUT_B))
                .outputs(Out.place(TIMER_PENDING))
                .action(ctx -> {
                    ctx.output(TIMER_PENDING, Token.unit());
                    return CompletableFuture.completedFuture(null);
                })
                .build();

        var net = PetriNet.builder("MixedStressTest")
                .transitions(asyncTransition, drainer)
                .build();

        var store = EventStore.inMemory();
        try (var executor = BitmapNetExecutor.builder(net, Map.of(
                        SHARED_CONTEXT, List.of(Token.of("ctx")),
                        TIMER_PENDING, List.of(Token.unit())))
                .eventStore(store)
                .environmentPlaces(Set.of(ENV))
                .build()) {

            var executorFuture = CompletableFuture.supplyAsync(
                    () -> executor.run(),
                    Executors.newVirtualThreadPerTaskExecutor());

            for (int i = 0; i < iterations; i++) {
                executor.inject(ENV, "input-" + i);
            }

            while (completed.get() < iterations) {
                Thread.sleep(10);
                if (completed.get() < iterations && executorFuture.isDone()) {
                    fail("Executor terminated early. Completed: " + completed.get());
                }
            }

            Thread.sleep(100);
            executor.drain();
            executorFuture.get(10, TimeUnit.SECONDS);

            long failures = store.events().stream()
                    .filter(e -> e instanceof NetEvent.TransitionFailed f
                            && f.exceptionType().contains("OutViolationException"))
                    .count();

            assertEquals(0, failures,
                    "OutViolationException in mixed sync/async test (" + iterations + " firings). " +
                    "Failures: " + store.events().stream()
                        .filter(e -> e instanceof NetEvent.TransitionFailed)
                        .map(e -> ((NetEvent.TransitionFailed) e).errorMessage())
                        .toList());
        }
    }
}
