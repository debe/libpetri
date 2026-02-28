package org.libpetri.runtime;

import org.libpetri.core.*;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.List;
import java.util.Map;
import java.util.concurrent.*;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for environment place support in NetExecutor.
 */
class EnvironmentPlaceTest {

    private final ExecutorService testExecutor = Executors.newVirtualThreadPerTaskExecutor();

    @Test
    @DisplayName("External token injection wakes orchestrator immediately")
    void injectWakesOrchestrator() throws Exception {
        var envPlace = EnvironmentPlace.of(Place.of("Input", String.class));
        var outputPlace = Place.of("Output", String.class);

        var transition = Transition.builder("Process")
            .inputs(In.one(envPlace.place()))
            .outputs(Out.and(outputPlace))
            .action(ctx -> {
                ctx.output(outputPlace, ctx.input(envPlace.place()));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var net = PetriNet.builder("Test").transitions(transition).build();

        try (var executor = NetExecutor.builder(net, Map.of())
                .environmentPlaces(envPlace)
                .longRunning(true)
                .build()) {

            // Start executor in background
            var resultFuture = CompletableFuture.supplyAsync(executor::run, testExecutor);

            // Wait for executor to be ready
            Thread.sleep(50);

            // Inject token
            long startTime = System.nanoTime();
            var injectResult = executor.inject(envPlace, Token.of("test"));
            injectResult.join();
            long elapsed = System.nanoTime() - startTime;

            // Should wake up quickly (within 100ms)
            assertTrue(elapsed < 100_000_000, "Should wake within 100ms, took " + elapsed / 1_000_000 + "ms");

            // Wait a bit for transition to fire
            Thread.sleep(100);

            // Close executor
            executor.close();
            var result = resultFuture.get(1, TimeUnit.SECONDS);

            assertTrue(result.hasTokens(outputPlace));
        }
    }

    @Test
    @DisplayName("Injection to non-environment place returns failed future")
    void injectToRegularPlaceReturnsFailed() {
        var regularPlace = Place.of("Regular", String.class);
        var net = PetriNet.builder("Test").places(regularPlace).build();

        try (var executor = NetExecutor.builder(net, Map.of())
                .build()) {

            var future = executor.inject(EnvironmentPlace.of(regularPlace), Token.of("test"));

            // Future should be completed exceptionally with IllegalArgumentException
            assertTrue(future.isCompletedExceptionally());
            var exception = assertThrows(ExecutionException.class, future::get);
            assertInstanceOf(IllegalArgumentException.class, exception.getCause());
        }
    }

    @Test
    @DisplayName("Long-running executor waits for external events")
    void longRunningWaitsForEvents() throws Exception {
        var envPlace = EnvironmentPlace.of(Place.of("Input", String.class));
        var net = PetriNet.builder("Test").places(envPlace.place()).build();

        try (var executor = NetExecutor.builder(net, Map.of())
                .environmentPlaces(envPlace)
                .longRunning(true)
                .build()) {

            var resultFuture = CompletableFuture.supplyAsync(executor::run, testExecutor);

            // Should not terminate immediately (unlike standard mode)
            Thread.sleep(200);
            assertFalse(resultFuture.isDone(), "Should not terminate without explicit close");

            executor.close();
            resultFuture.get(1, TimeUnit.SECONDS);
        }
    }

    @Test
    @DisplayName("Injection returns false after executor closes")
    void injectionAfterCloseReturnsFalse() {
        var envPlace = EnvironmentPlace.of(Place.of("Input", String.class));
        var net = PetriNet.builder("Test").places(envPlace.place()).build();

        var executor = NetExecutor.builder(net, Map.of())
            .environmentPlaces(envPlace)
            .build();
        executor.close();

        var result = executor.inject(envPlace, Token.of("test")).join();
        assertFalse(result);
    }

    @Test
    @DisplayName("Multiple tokens can be injected sequentially")
    void multipleTokensInjectedSequentially() throws Exception {
        var envPlace = EnvironmentPlace.of(Place.of("Input", Integer.class));
        var outputPlace = Place.of("Output", Integer.class);
        var counter = new java.util.concurrent.atomic.AtomicInteger(0);

        var transition = Transition.builder("Process")
            .inputs(In.one(envPlace.place()))
            .outputs(Out.and(outputPlace))
            .action(ctx -> {
                counter.incrementAndGet();
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var net = PetriNet.builder("Test").transitions(transition).build();

        try (var executor = NetExecutor.builder(net, Map.of())
                .environmentPlaces(envPlace)
                .longRunning(true)
                .build()) {

            var resultFuture = CompletableFuture.supplyAsync(executor::run, testExecutor);

            // Wait for executor to be ready
            Thread.sleep(50);

            // Inject multiple tokens
            int numTokens = 10;
            for (int i = 0; i < numTokens; i++) {
                executor.inject(envPlace, Token.of(i)).join();
                Thread.sleep(20); // Small delay between injections
            }

            // Wait for processing
            Thread.sleep(200);

            executor.close();
            resultFuture.get(1, TimeUnit.SECONDS);

            assertEquals(numTokens, counter.get(), "All tokens should be processed");
        }
    }

    @Test
    @DisplayName("Standard executor (non-long-running) terminates when quiescent")
    void standardExecutorTerminatesWhenQuiescent() throws Exception {
        var place = Place.of("Start", String.class);
        var net = PetriNet.builder("Test").places(place).build();

        // Standard executor with initial token but no transitions
        try (var executor = NetExecutor.create(net, Map.of(place, List.of(Token.of("initial"))))) {
            var result = executor.run();
            // Should terminate immediately since no transitions are enabled
            assertEquals(1, result.tokenCount(place));
        }
    }

    @Test
    @DisplayName("EnvironmentPlace wrapper preserves place properties")
    void environmentPlacePreservesProperties() {
        var place = Place.of("TestPlace", String.class);
        var envPlace = EnvironmentPlace.of(place);

        assertEquals("TestPlace", envPlace.name());
        assertEquals(String.class, envPlace.tokenType());
        assertEquals(place, envPlace.place());
        assertTrue(envPlace.accepts(Token.of("hello")));
    }
}
