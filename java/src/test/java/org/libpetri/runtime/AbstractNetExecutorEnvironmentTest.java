package org.libpetri.runtime;

import static org.junit.jupiter.api.Assertions.*;

import org.libpetri.core.Arc;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Token;
import org.libpetri.core.Transition;
import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;
import java.time.Duration;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicBoolean;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

/**
 * Abstract test suite for environment place executor behavior.
 *
 * <p>Subclasses provide executor creation via factory methods, allowing the same
 * tests to run against different executor implementations.
 */
abstract class AbstractNetExecutorEnvironmentTest {

    protected abstract PetriNetExecutor createExecutor(PetriNet net, Map<Place<?>, List<Token<?>>> initial);

    protected abstract PetriNetExecutor createWithEnvPlaces(PetriNet net, Map<Place<?>, List<Token<?>>> initial, Set<EnvironmentPlace<?>> envPlaces);

    protected abstract PetriNetExecutor createWithEnvPlacesAndStore(PetriNet net, Map<Place<?>, List<Token<?>>> initial, EventStore store, Set<EnvironmentPlace<?>> envPlaces);

    record StringValue(String data) {}

    private final ExecutorService testExecutor = Executors.newVirtualThreadPerTaskExecutor();

    @Nested
    class EnvironmentPlaceTests {

        @Test
        void executorWithEnvPlaces_wakesOnEnvironmentInjection()
            throws Exception {
            Place<StringValue> envPlace = Place.of(
                "ENV_INPUT",
                StringValue.class
            );
            EnvironmentPlace<StringValue> envInput = EnvironmentPlace.of(
                envPlace
            );
            Place<StringValue> processed = Place.of(
                "PROCESSED",
                StringValue.class
            );

            // Simple transition: whenever a token arrives in ENV_INPUT, move it to PROCESSED
            Transition process = Transition.builder("ProcessEnv")
                .inputs(Arc.In.one(envPlace))
                .outputs(Arc.Out.and(processed))
                .timing(Timing.deadline(Duration.ofMillis(1_000)))
                .action(ctx -> {
                    StringValue value = ctx.input(envPlace);
                    ctx.output(
                        processed,
                        new StringValue("processed-" + value.data())
                    );
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            PetriNet net = PetriNet.builder("ReactiveEnvNet")
                .transitions(process)
                .build();

            Map<Place<?>, List<Token<?>>> initial = Map.of(envPlace, List.of()); // starts idle

            try (
                PetriNetExecutor executor = createWithEnvPlaces(net, initial, Set.of(envInput))
            ) {
                // Run executor on a dedicated thread to simulate orchestrator with env places
                ExecutorService orchestrator =
                    Executors.newSingleThreadExecutor();
                Future<Marking> runFuture = orchestrator.submit(
                    (Callable<Marking>) executor::run
                );

                // Give orchestrator time to start and become idle
                Thread.sleep(50L);

                // Initially no tokens anywhere
                assertTrue(executor.marking().tokenCount(envPlace) == 0);
                assertTrue(executor.marking().tokenCount(processed) == 0);

                // Inject a token into the environment place
                CompletableFuture<Boolean> result = executor.inject(
                    envInput,
                    Token.of(new StringValue("hello"))
                );

                // Injection must be accepted and complete quickly
                assertTrue(result.get(1, TimeUnit.SECONDS));

                // Give executor some time to process
                Thread.sleep(100L);

                Marking marking = executor.marking();
                assertFalse(
                    marking.hasTokens(envPlace),
                    "Environment token should be consumed"
                );
                assertTrue(
                    marking.hasTokens(processed),
                    "Processed place should have token"
                );
                assertEquals(
                    "processed-hello",
                    marking.peekFirst(processed).value().data()
                );

                // Executor with env places should still be running until drain()
                assertFalse(
                    runFuture.isDone(),
                    "Executor with env places should not complete automatically"
                );

                executor.drain();

                // After drain, orchestrator should eventually terminate
                Marking finalMarking = runFuture.get(2, TimeUnit.SECONDS);
                assertSame(
                    marking,
                    finalMarking,
                    "Marking instance is shared live state"
                );

                orchestrator.shutdownNow();
            }
        }

        @Test
        void injectIntoNonEnvironmentPlace_failsImmediately() {
            Place<StringValue> regularInput = Place.of(
                "INPUT",
                StringValue.class
            );
            EnvironmentPlace<StringValue> fakeEnv = EnvironmentPlace.of(
                regularInput
            );
            Place<StringValue> output = Place.of("OUTPUT", StringValue.class);

            Transition t = Transition.builder("simple")
                .inputs(Arc.In.one(regularInput))
                .outputs(Arc.Out.and(output))
                .timing(Timing.deadline(Duration.ofMillis(1_000)))
                .action(ctx -> {
                    ctx.output(output, ctx.input(regularInput));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            PetriNet net = PetriNet.builder("NonEnvInjectNet")
                .transitions(t)
                .build();

            Map<Place<?>, List<Token<?>>> initial = Map.of(
                regularInput,
                List.of(Token.of(new StringValue("data")))
            );

            try (PetriNetExecutor executor = createExecutor(net, initial)) {
                // Attempt to treat a regular place as environment place

                CompletableFuture<Boolean> future = executor.inject(
                    fakeEnv,
                    Token.of(new StringValue("x"))
                );

                ExecutionException ex = assertThrows(
                    ExecutionException.class,
                    () -> future.get(1, TimeUnit.SECONDS),
                    "Expected ExecutionException when getting result of failed future"
                );
                assertNotNull(ex.getCause(), "ExecutionException should have a cause");
                assertTrue(ex.getCause() instanceof IllegalArgumentException,
                    "Cause should be IllegalArgumentException but was: " + ex.getCause().getClass().getName());
                String message = ex.getCause().getMessage();
                assertNotNull(message, "Exception message should not be null");
                assertTrue(
                    message.contains("not registered as an environment place"),
                    "Message should contain 'not registered as an environment place' but was: " + message
                );
            }
        }

       @Test
        void stateInspection_quiescentAndWaitingForCompletion()
            throws Exception {
            Place<StringValue> envPlace = Place.of(
                "ENV_INPUT",
                StringValue.class
            );
            EnvironmentPlace<StringValue> envInput = EnvironmentPlace.of(
                envPlace
            );
            Place<StringValue> slowOut = Place.of(
                "SLOW_OUT",
                StringValue.class
            );

            AtomicBoolean actionStarted = new AtomicBoolean(false);
            AtomicBoolean actionCanFinish = new AtomicBoolean(false);

            Transition slow = Transition.builder("slow")
                .inputs(Arc.In.one(envPlace))
                .outputs(Arc.Out.and(slowOut))
                .timing(Timing.deadline(Duration.ofMillis(5_000)))
                .action(ctx ->
                    CompletableFuture.runAsync(() -> {
                        actionStarted.set(true);
                        // Wait until test thread allows completion
                        while (!actionCanFinish.get()) {
                            try {
                                Thread.sleep(10L);
                            } catch (InterruptedException e) {
                                Thread.currentThread().interrupt();
                                break;
                            }
                        }
                        ctx.output(slowOut, new StringValue("done"));
                    }, testExecutor)
                )
                .build();

            PetriNet net = PetriNet.builder("StateInspectionNet")
                .transitions(slow)
                .build();

            Map<Place<?>, List<Token<?>>> initial = Map.of(envPlace, List.of());

            try (
                PetriNetExecutor executor = createWithEnvPlaces(net, initial, Set.of(envInput))
            ) {
                ExecutorService orchestrator =
                    Executors.newSingleThreadExecutor();
                Future<Marking> runFuture = orchestrator.submit(
                    (Callable<Marking>) executor::run
                );

                Thread.sleep(50L);

                // Initially quiescent: no enabled transitions and no in-flight
                assertTrue(executor.isQuiescent());
                assertEquals(0, executor.inFlightCount());
                assertEquals(0, executor.enabledCount());

                // Inject token to trigger slow transition
                CompletableFuture<Boolean> injectResult = executor.inject(
                    envInput,
                    Token.of(new StringValue("x"))
                );
                assertTrue(injectResult.get(1, TimeUnit.SECONDS));

                // Wait for the async action to start
                waitForTrue(actionStarted, 1_000);

                // While action is running:
                // - No newly-enabled transitions (strictly speaking none, since only one exists and is in-flight)
                // - One in-flight transition
                assertTrue(
                    executor.isWaitingForCompletion(),
                    "Should be waiting for completion"
                );
                assertEquals(1, executor.inFlightCount());
                // enabledAt contains no transitions that are not in-flight
                assertEquals(0, executor.enabledCount());

                // Allow action to complete
                actionCanFinish.set(true);

                // Wait for executor to process completion
                waitForMarkingHasToken(executor, slowOut, 2_000);

                // Now should be quiescent again
                assertTrue(executor.isQuiescent());
                assertEquals(0, executor.inFlightCount());
                assertEquals(0, executor.enabledCount());

                executor.drain();
                runFuture.get(2, TimeUnit.SECONDS);
                orchestrator.shutdownNow();
            }
        }

        /**
         * Ensures multiple quick injections correctly wake the executor with env places
         * and all tokens are processed.
         */
        @Test
        void multipleInjections_allProcessed() throws Exception {
            Place<StringValue> envPlace = Place.of(
                "ENV_INPUT",
                StringValue.class
            );
            EnvironmentPlace<StringValue> envInput = EnvironmentPlace.of(
                envPlace
            );
            Place<StringValue> sink = Place.of("SINK", StringValue.class);

            Transition consume = Transition.builder("consume")
                .inputs(Arc.In.one(envPlace))
                .outputs(Arc.Out.and(sink))
                .timing(Timing.deadline(Duration.ofMillis(1_000)))
                .action(ctx -> {
                    StringValue v = ctx.input(envPlace);
                    ctx.output(sink, new StringValue("seen-" + v.data()));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            PetriNet net = PetriNet.builder("MultiInjectNet")
                .transitions(consume)
                .build();

            Map<Place<?>, List<Token<?>>> initial = Map.of(envPlace, List.of());

            try (
                PetriNetExecutor executor = createWithEnvPlaces(net, initial, Set.of(envInput))
            ) {
                ExecutorService orchestrator =
                    Executors.newSingleThreadExecutor();
                Future<Marking> runFuture = orchestrator.submit(
                    (Callable<Marking>) executor::run
                );

                Thread.sleep(50L);

                int count = 10;
                CompletableFuture<Boolean>[] results =
                    new CompletableFuture[count];
                for (int i = 0; i < count; i++) {
                    results[i] = executor.inject(
                        envInput,
                        Token.of(new StringValue("v" + i))
                    );
                }

                for (CompletableFuture<Boolean> r : results) {
                    assertTrue(r.get(1, TimeUnit.SECONDS));
                }

                // Give some time for all transitions to fire
                Thread.sleep(500L);

                Marking marking = executor.marking();
                assertEquals(count, marking.tokenCount(sink));

                executor.drain();
                runFuture.get(2, TimeUnit.SECONDS);
                orchestrator.shutdownNow();
            }
        }

        /**
         * Verifies that a timed transition fires without requiring
         * external events to wake the executor. This is a regression test for the bug
         * where awaitExternalEvent() blocked indefinitely on wakeUpSignal.acquire().
         */
        @Test
        @DisplayName("Delayed transition fires autonomously with env places (regression test)")
        void delayedTransition_firesWithoutExternalEvent_withEnvPlaces() throws Exception {
            Place<StringValue> input = Place.of("Input", StringValue.class);
            EnvironmentPlace<StringValue> envInput = EnvironmentPlace.of(input);
            Place<StringValue> output = Place.of("Output", StringValue.class);

            // A transition with 100ms delay - should fire ~100ms after enabling
            Transition delayed = Transition.builder("Delayed100ms")
                .inputs(Arc.In.one(input))
                .outputs(Arc.Out.and(output))
                .timing(Timing.delayed(Duration.ofMillis(100)))
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            PetriNet net = PetriNet.builder("TimedTest").transitions(delayed).build();

            // Start with a token - transition becomes enabled immediately
            Map<Place<?>, List<Token<?>>> initial = Map.of(
                input, List.of(Token.of(new StringValue("test")))
            );

            try (PetriNetExecutor executor = createWithEnvPlaces(net, initial, Set.of(envInput))) {

                // Run executor on a dedicated thread
                ExecutorService orchestrator = Executors.newSingleThreadExecutor();
                Future<Marking> runFuture = orchestrator.submit((Callable<Marking>) executor::run);

                long start = System.currentTimeMillis();

                // Wait for the delayed transition to fire
                // Should happen around 100ms, we give it 300ms max
                waitForMarkingHasToken(executor, output, 300);

                long elapsed = System.currentTimeMillis() - start;

                // Verify timing - should fire after ~100ms delay, not immediately
                assertTrue(elapsed >= 90, "Should wait at least 90ms for the delay, but was " + elapsed + "ms");
                assertTrue(elapsed < 300, "Should fire before 300ms timeout, but took " + elapsed + "ms");

                // Verify transition fired correctly
                Marking marking = executor.marking();
                assertFalse(marking.hasTokens(input), "Input should be consumed");
                assertTrue(marking.hasTokens(output), "Output should have token");
                assertEquals("test", marking.peekFirst(output).value().data());

                // Executor should still be running (env places registered)
                assertFalse(runFuture.isDone(), "Executor with env places should not complete automatically");

                executor.drain();
                runFuture.get(2, TimeUnit.SECONDS);
                orchestrator.shutdownNow();
            }
        }

        private void waitForTrue(AtomicBoolean flag, long timeoutMillis)
            throws InterruptedException {
            long deadline = System.currentTimeMillis() + timeoutMillis;
            while (!flag.get() && System.currentTimeMillis() < deadline) {
                Thread.sleep(10L);
            }
            assertTrue(
                flag.get(),
                "Condition did not become true within timeout"
            );
        }

        private <T> void waitForMarkingHasToken(
            PetriNetExecutor executor,
            Place<T> place,
            long timeoutMillis
        ) throws InterruptedException {
            long deadline = System.currentTimeMillis() + timeoutMillis;
            while (
                !executor.marking().hasTokens(place) &&
                System.currentTimeMillis() < deadline
            ) {
                Thread.sleep(10L);
            }
            assertTrue(
                executor.marking().hasTokens(place),
                "Expected token at place " + place.name() + " within timeout"
            );
        }
    }

    @Nested
    class CloseBehaviorTests {

        @Test
        void close_drainsPendingExternalEvents() throws Exception {
            Place<StringValue> envPlace = Place.of("ENV_INPUT", StringValue.class);
            EnvironmentPlace<StringValue> envInput = EnvironmentPlace.of(envPlace);
            Place<StringValue> output = Place.of("OUTPUT", StringValue.class);

            AtomicBoolean actionStarted = new AtomicBoolean(false);

            // Transition that blocks long enough to queue a second inject while in-flight
            Transition slow = Transition.builder("slow")
                .inputs(Arc.In.one(envPlace))
                .outputs(Arc.Out.and(output))
                .timing(Timing.deadline(Duration.ofMillis(10_000)))
                .action(ctx -> CompletableFuture.runAsync(() -> {
                    actionStarted.set(true);
                    try { Thread.sleep(500); } catch (InterruptedException e) {
                        Thread.currentThread().interrupt();
                    }
                    ctx.output(output, new StringValue("done"));
                }, testExecutor))
                .build();

            PetriNet net = PetriNet.builder("DrainTest").transitions(slow).build();

            try (PetriNetExecutor executor = createWithEnvPlaces(net, Map.of(envPlace, List.of()), Set.of(envInput))) {
                ExecutorService orchestrator = Executors.newSingleThreadExecutor();
                Future<Marking> runFuture = orchestrator.submit((Callable<Marking>) executor::run);

                Thread.sleep(50L);

                // Inject a token to start the slow transition
                executor.inject(envInput, Token.of(new StringValue("first")));

                // Wait for action to start
                long deadline = System.currentTimeMillis() + 1_000;
                while (!actionStarted.get() && System.currentTimeMillis() < deadline) {
                    Thread.sleep(10L);
                }

                // Now inject another token while the first is still in-flight
                CompletableFuture<Boolean> pendingInject = executor.inject(
                    envInput, Token.of(new StringValue("pending")));

                // Close immediately - should drain pending events
                executor.close();

                // The runFuture should complete
                runFuture.get(3, TimeUnit.SECONDS);
                orchestrator.shutdownNow();

                // After close, pending inject should be discarded per ENV-013
                Boolean result = pendingInject.get(1, TimeUnit.SECONDS);
                assertFalse(result, "Pending inject should be discarded on close()");
            }
        }

        @Test
        void close_waitsForInFlightActions_ENV013() throws Exception {
            Place<StringValue> envPlace = Place.of("ENV_INPUT", StringValue.class);
            EnvironmentPlace<StringValue> envInput = EnvironmentPlace.of(envPlace);
            Place<StringValue> output = Place.of("OUTPUT", StringValue.class);

            AtomicBoolean actionStarted = new AtomicBoolean(false);

            Transition slow = Transition.builder("slow")
                .inputs(Arc.In.one(envPlace))
                .outputs(Arc.Out.and(output))
                .timing(Timing.deadline(Duration.ofMillis(10_000)))
                .action(ctx -> CompletableFuture.runAsync(() -> {
                    actionStarted.set(true);
                    try { Thread.sleep(200); } catch (InterruptedException e) {
                        Thread.currentThread().interrupt();
                    }
                    ctx.output(output, new StringValue("completed"));
                }, testExecutor))
                .build();

            PetriNet net = PetriNet.builder("CloseInFlightTest").transitions(slow).build();

            try (PetriNetExecutor executor = createWithEnvPlaces(net, Map.of(envPlace, List.of()), Set.of(envInput))) {
                ExecutorService orchestrator = Executors.newSingleThreadExecutor();
                Future<Marking> runFuture = orchestrator.submit((Callable<Marking>) executor::run);

                Thread.sleep(50L);

                // Inject a token to start the slow transition
                executor.inject(envInput, Token.of(new StringValue("go")));

                // Wait for action to start
                long deadline = System.currentTimeMillis() + 1_000;
                while (!actionStarted.get() && System.currentTimeMillis() < deadline) {
                    Thread.sleep(10L);
                }
                assertTrue(actionStarted.get(), "Action should have started");

                // Close while the action is in-flight — ENV-013 requires it to complete
                executor.close();

                Marking marking = runFuture.get(3, TimeUnit.SECONDS);
                orchestrator.shutdownNow();

                // The in-flight action should have completed and produced its output
                assertTrue(marking.hasTokens(output),
                    "In-flight action output should be in final marking per ENV-013");
            }
        }

        @Test
        void drainThenClose_escalatesToImmediateShutdown() throws Exception {
            Place<StringValue> envPlace = Place.of("ENV_INPUT", StringValue.class);
            EnvironmentPlace<StringValue> envInput = EnvironmentPlace.of(envPlace);
            Place<StringValue> output = Place.of("OUTPUT", StringValue.class);

            AtomicBoolean actionStarted = new AtomicBoolean(false);
            AtomicBoolean actionCanFinish = new AtomicBoolean(false);

            Transition slow = Transition.builder("slow")
                .inputs(Arc.In.one(envPlace))
                .outputs(Arc.Out.and(output))
                .timing(Timing.deadline(Duration.ofMillis(10_000)))
                .action(ctx -> CompletableFuture.runAsync(() -> {
                    actionStarted.set(true);
                    while (!actionCanFinish.get()) {
                        try { Thread.sleep(10); } catch (InterruptedException e) {
                            Thread.currentThread().interrupt();
                            break;
                        }
                    }
                    ctx.output(output, new StringValue("done"));
                }, testExecutor))
                .build();

            PetriNet net = PetriNet.builder("EscalateTest").transitions(slow).build();

            try (PetriNetExecutor executor = createWithEnvPlaces(net, Map.of(envPlace, List.of()), Set.of(envInput))) {
                ExecutorService orchestrator = Executors.newSingleThreadExecutor();
                Future<Marking> runFuture = orchestrator.submit((Callable<Marking>) executor::run);

                Thread.sleep(50L);

                // Inject a token and wait for in-flight action to start
                executor.inject(envInput, Token.of(new StringValue("go")));
                long deadline = System.currentTimeMillis() + 1_000;
                while (!actionStarted.get() && System.currentTimeMillis() < deadline) {
                    Thread.sleep(10L);
                }
                assertTrue(actionStarted.get(), "Action should have started");

                // Queue a second injection while first is in-flight
                CompletableFuture<Boolean> pendingInject = executor.inject(
                    envInput, Token.of(new StringValue("queued")));

                // Drain first — rejects new inject but processes queued events
                executor.drain();
                CompletableFuture<Boolean> postDrainInject = executor.inject(
                    envInput, Token.of(new StringValue("rejected")));
                assertFalse(postDrainInject.get(1, TimeUnit.SECONDS),
                    "Inject after drain should return false");

                // Escalate to close — should discard queued events
                executor.close();

                // Let the in-flight action finish
                actionCanFinish.set(true);

                Marking marking = runFuture.get(3, TimeUnit.SECONDS);
                orchestrator.shutdownNow();

                // In-flight action should have completed per ENV-013
                assertTrue(marking.hasTokens(output),
                    "In-flight action should complete even after close");
            }
        }

        @Test
        void inject_afterClose_returnsFalse() throws Exception {
            Place<StringValue> envPlace = Place.of("ENV_INPUT", StringValue.class);
            EnvironmentPlace<StringValue> envInput = EnvironmentPlace.of(envPlace);
            Place<StringValue> output = Place.of("OUTPUT", StringValue.class);

            Transition t = Transition.builder("t")
                .inputs(Arc.In.one(envPlace))
                .outputs(Arc.Out.and(output))
                .timing(Timing.deadline(Duration.ofMillis(1_000)))
                .action(ctx -> {
                    ctx.output(output, ctx.input(envPlace));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            PetriNet net = PetriNet.builder("InjectAfterClose").transitions(t).build();

            try (PetriNetExecutor executor = createWithEnvPlaces(net, Map.of(envPlace, List.of()), Set.of(envInput))) {
                ExecutorService orchestrator = Executors.newSingleThreadExecutor();
                Future<Marking> runFuture = orchestrator.submit((Callable<Marking>) executor::run);

                Thread.sleep(50L);

                // Close first
                executor.close();
                runFuture.get(2, TimeUnit.SECONDS);
                orchestrator.shutdownNow();

                // Then inject - should return false
                CompletableFuture<Boolean> result = executor.inject(
                    envInput, Token.of(new StringValue("too-late")));
                assertFalse(result.get(1, TimeUnit.SECONDS),
                    "Inject after close should return false");
            }
        }

        /**
         * Regression test for 1.5.0 CPU spin: close() with in-flight async actions
         * caused awaitCompletionOrEvent() to exit immediately (tight spin at 100% CPU).
         *
         * <p>Detects the spin by measuring orchestrator thread CPU time via ThreadMXBean.
         * Without the fix, the thread burns ~500ms of CPU. With the fix, it polls at
         * 50ms intervals and consumes &lt; 50ms of CPU.
         */
        @Test
        @DisplayName("close() with in-flight action does not spin CPU (regression)")
        void close_withInFlightAction_doesNotSpinCPU() throws Exception {
            Place<StringValue> envPlace = Place.of("ENV_INPUT", StringValue.class);
            EnvironmentPlace<StringValue> envInput = EnvironmentPlace.of(envPlace);
            Place<StringValue> output = Place.of("OUTPUT", StringValue.class);

            AtomicBoolean actionStarted = new AtomicBoolean(false);

            Transition slow = Transition.builder("slow500ms")
                .inputs(Arc.In.one(envPlace))
                .outputs(Arc.Out.and(output))
                .timing(Timing.deadline(Duration.ofMillis(10_000)))
                .action(ctx -> CompletableFuture.runAsync(() -> {
                    actionStarted.set(true);
                    try { Thread.sleep(500); } catch (InterruptedException e) {
                        Thread.currentThread().interrupt();
                    }
                    ctx.output(output, new StringValue("done"));
                }, testExecutor))
                .build();

            PetriNet net = PetriNet.builder("SpinTest").transitions(slow).build();

            try (PetriNetExecutor executor = createWithEnvPlaces(net, Map.of(envPlace, List.of()), Set.of(envInput))) {
                // Run executor on a named thread so we can measure its CPU time
                var threadMXBean = java.lang.management.ManagementFactory.getThreadMXBean();
                var threadRef = new java.util.concurrent.atomic.AtomicLong();

                ExecutorService orchestrator = Executors.newSingleThreadExecutor(r -> {
                    Thread t = new Thread(r, "spin-test-orchestrator");
                    threadRef.set(t.getId());
                    return t;
                });
                Future<Marking> runFuture = orchestrator.submit((Callable<Marking>) executor::run);

                Thread.sleep(50L);

                // Inject a token to start the slow 500ms action
                executor.inject(envInput, Token.of(new StringValue("go")));

                // Wait for action to start
                long deadline = System.currentTimeMillis() + 1_000;
                while (!actionStarted.get() && System.currentTimeMillis() < deadline) {
                    Thread.sleep(10L);
                }
                assertTrue(actionStarted.get(), "Action should have started");

                // Record CPU time, then close()
                long cpuBefore = threadMXBean.getThreadCpuTime(threadRef.get());
                executor.close();

                // Wait for executor to finish (action takes ~500ms)
                Marking marking = runFuture.get(3, TimeUnit.SECONDS);
                long cpuAfter = threadMXBean.getThreadCpuTime(threadRef.get());
                orchestrator.shutdownNow();

                long cpuDeltaMs = (cpuAfter - cpuBefore) / 1_000_000;

                // In-flight action should still complete per ENV-013
                assertTrue(marking.hasTokens(output),
                    "In-flight action output should be in marking");

                // CPU time should be well under 200ms during the ~500ms wait.
                // Without fix: ~500ms CPU (tight spin). With fix: ~5ms (50ms polling).
                assertTrue(cpuDeltaMs < 200,
                    "Orchestrator thread consumed " + cpuDeltaMs +
                    "ms of CPU during close() — suspected spin (threshold: 200ms)");
            }
        }
    }

    @Nested
    class EventStoreIntegrationTests {

        @Test
        void eventStore_recordsEnvironmentTokenAddedEvents() throws Exception {
            Place<StringValue> envPlace = Place.of(
                "ENV_INPUT",
                StringValue.class
            );
            EnvironmentPlace<StringValue> envInput = EnvironmentPlace.of(
                envPlace
            );
            Place<StringValue> out = Place.of("OUT", StringValue.class);

            EventStore store = EventStore.inMemory();

            Transition t = Transition.builder("fromEnv")
                .inputs(Arc.In.one(envPlace))
                .outputs(Arc.Out.and(out))
                .timing(Timing.deadline(Duration.ofMillis(1_000)))
                .action(ctx -> {
                    ctx.output(out, ctx.input(envPlace));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            PetriNet net = PetriNet.builder("EnvEventNet")
                .transitions(t)
                .build();

            Map<Place<?>, List<Token<?>>> initial = Map.of(envPlace, List.of());

            try (
                PetriNetExecutor executor = createWithEnvPlacesAndStore(net, initial, store, Set.of(envInput))
            ) {
                ExecutorService orchestrator =
                    Executors.newSingleThreadExecutor();
                Future<Marking> runFuture = orchestrator.submit(
                    (Callable<Marking>) executor::run
                );

                Thread.sleep(50L);

                CompletableFuture<Boolean> result = executor.inject(
                    envInput,
                    Token.of(new StringValue("env-data"))
                );
                assertTrue(result.get(1, TimeUnit.SECONDS));

                Thread.sleep(100L);

                executor.close();
                runFuture.get(2, TimeUnit.SECONDS);
                orchestrator.shutdownNow();
            }

            // Event store should contain at least one TokenAdded event for the environment place
            boolean hasTokenAddedFromEnv = store
                .events()
                .stream()
                .filter(e -> e instanceof NetEvent.TokenAdded)
                .map(NetEvent.TokenAdded.class::cast)
                .anyMatch(e -> "ENV_INPUT".equals(e.placeName()));

            assertTrue(
                hasTokenAddedFromEnv,
                "EventStore should record TokenAdded event for ENV_INPUT"
            );
        }
    }
}
