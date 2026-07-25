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
import java.util.concurrent.atomic.AtomicReference;
import org.junit.jupiter.api.Assumptions;
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
                // marking() read from another thread mid-run returns an independent
                // snapshot, not the live instance: rebuilding or reading the live marking
                // concurrently corrupts it rather than observing it. The snapshot must
                // still agree with the final marking, since nothing fired in between.
                Marking finalMarking = runFuture.get(2, TimeUnit.SECONDS);
                assertEquals(
                    marking.tokenCount(processed),
                    finalMarking.tokenCount(processed),
                    "the mid-run snapshot must agree with the final marking"
                );
                assertFalse(finalMarking.hasTokens(envPlace));

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

            // The transition completes immediately on the action thread. Determinism
            // comes from the event-store barrier below, NOT from timing.
            Transition slow = Transition.builder("slow")
                .inputs(Arc.In.one(envPlace))
                .outputs(Arc.Out.and(output))
                .timing(Timing.deadline(Duration.ofMillis(10_000)))
                .action(ctx -> CompletableFuture.runAsync(
                    () -> ctx.output(output, new StringValue("done")), testExecutor))
                .build();

            PetriNet net = PetriNet.builder("DrainTest").transitions(slow).build();

            // Synchronization barrier. The orchestrator thread synchronously emits
            // NetEvent.TransitionCompleted from processCompletedTransitions(), one
            // loop iteration BEFORE processExternalEvents(). Blocking append() there
            // pins the orchestrator at a known point, so we can queue a pending inject
            // and call close() while it is parked — removing the inject().wakeUp() vs
            // close() race that made this test flaky.
            CountDownLatch reachedBarrier = new CountDownLatch(1);
            CountDownLatch release = new CountDownLatch(1);
            EventStore gate = new EventStore() {
                @Override public void append(NetEvent event) {
                    if (event instanceof NetEvent.TransitionCompleted tc
                            && tc.transitionName().equals("slow")) {
                        reachedBarrier.countDown();
                        try {
                            release.await(10, TimeUnit.SECONDS);
                        } catch (InterruptedException e) {
                            Thread.currentThread().interrupt();
                        }
                    }
                }
                @Override public List<NetEvent> events() { return List.of(); }
            };

            try (PetriNetExecutor executor = createWithEnvPlacesAndStore(
                    net, Map.of(envPlace, List.of()), gate, Set.of(envInput))) {
                ExecutorService orchestrator = Executors.newSingleThreadExecutor();
                Future<Marking> runFuture = orchestrator.submit((Callable<Marking>) executor::run);

                // Inject the first token. The slow transition fires and completes; the
                // orchestrator parks at the barrier while emitting TransitionCompleted.
                executor.inject(envInput, Token.of(new StringValue("first")));
                assertTrue(reachedBarrier.await(10, TimeUnit.SECONDS),
                    "Orchestrator should reach the TransitionCompleted barrier");

                // Orchestrator is now provably blocked before processExternalEvents().
                // Queue a pending inject (its wakeUp() cannot be consumed yet) ...
                CompletableFuture<Boolean> pendingInject = executor.inject(
                    envInput, Token.of(new StringValue("pending")));
                // ... and close while the orchestrator is still parked at the barrier.
                executor.close();

                // Release it: at the top of the next processExternalEvents() it now
                // observes closed==true, leaves "pending" queued, and the post-loop
                // drainPendingExternalEvents() discards it per ENV-013.
                release.countDown();

                runFuture.get(10, TimeUnit.SECONDS);
                orchestrator.shutdownNow();

                Boolean result = pendingInject.get(5, TimeUnit.SECONDS);
                assertFalse(result, "Pending inject should be discarded on close()");
            }
        }

        @Test
        void injectAfterClose_returnsFalse() throws Exception {
            Place<StringValue> envPlace = Place.of("ENV_INPUT", StringValue.class);
            EnvironmentPlace<StringValue> envInput = EnvironmentPlace.of(envPlace);
            Place<StringValue> output = Place.of("OUTPUT", StringValue.class);

            Transition passthrough = Transition.builder("passthrough")
                .inputs(Arc.In.one(envPlace))
                .outputs(Arc.Out.and(output))
                .timing(Timing.deadline(Duration.ofMillis(10_000)))
                .action(ctx -> CompletableFuture.completedFuture(null))
                .build();

            PetriNet net = PetriNet.builder("InjectAfterCloseTest").transitions(passthrough).build();

            try (PetriNetExecutor executor = createWithEnvPlaces(net, Map.of(envPlace, List.of()), Set.of(envInput))) {
                ExecutorService orchestrator = Executors.newSingleThreadExecutor();
                Future<Marking> runFuture = orchestrator.submit((Callable<Marking>) executor::run);

                executor.close();
                runFuture.get(10, TimeUnit.SECONDS);
                orchestrator.shutdownNow();

                // ENV-013: an inject submitted at/after close() is rejected outright,
                // never queued — deterministically resolves false.
                CompletableFuture<Boolean> rejected = executor.inject(
                    envInput, Token.of(new StringValue("late")));
                assertFalse(rejected.get(5, TimeUnit.SECONDS),
                    "Inject after close() must return false");
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
            var threadMXBean = java.lang.management.ManagementFactory.getThreadMXBean();
            Assumptions.assumeTrue(threadMXBean.isThreadCpuTimeSupported(),
                "Thread CPU time not supported on this JVM");

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

        /**
         * Regression test: drain() with enabled timed transitions (nothing in-flight)
         * causes awaitWork() to fall through without blocking — tight spin at 100% CPU.
         *
         * <p>The bug is in awaitWork(): when draining=true, the {@code hasEnvironmentPlaces &&
         * !draining.get()} branch is skipped, and since inFlight is empty, no blocking occurs.
         * Meanwhile shouldTerminate() returns false because enabledTransitionCount > 0.
         *
         * <p>Detects the spin by measuring orchestrator thread CPU time via ThreadMXBean.
         * Without the fix, the thread burns ~500ms+ of CPU during the 600ms delayed transition wait.
         * With the fix, it polls at bounded intervals and consumes &lt; 50ms.
         */
        @Test
        @DisplayName("drain() with enabled timed transitions does not spin CPU (regression)")
        void drain_withEnabledTimedTransitions_doesNotSpinCPU() throws Exception {
            var threadMXBean = java.lang.management.ManagementFactory.getThreadMXBean();
            Assumptions.assumeTrue(threadMXBean.isThreadCpuTimeSupported(),
                "Thread CPU time not supported on this JVM");

            Place<StringValue> envPlace = Place.of("ENV_INPUT", StringValue.class);
            EnvironmentPlace<StringValue> envInput = EnvironmentPlace.of(envPlace);
            Place<StringValue> intermediate = Place.of("INTERMEDIATE", StringValue.class);
            Place<StringValue> output = Place.of("OUTPUT", StringValue.class);

            // T1: immediate sync transition — consumes env token, produces to intermediate
            Transition t1 = Transition.builder("immediate")
                .inputs(Arc.In.one(envPlace))
                .outputs(Arc.Out.and(intermediate))
                .action(ctx -> {
                    ctx.output(intermediate, ctx.input(envPlace));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            // T2: delayed 600ms — consumes intermediate, produces to output
            // After T1 fires synchronously, T2 is enabled but not ready (600ms delay).
            // Nothing is in-flight, so awaitWork() must wait on the timer, not spin.
            Transition t2 = Transition.builder("delayed600ms")
                .inputs(Arc.In.one(intermediate))
                .outputs(Arc.Out.and(output))
                .timing(Timing.delayed(Duration.ofMillis(600)))
                .action(ctx -> {
                    ctx.output(output, ctx.input(intermediate));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            PetriNet net = PetriNet.builder("DrainTimedSpinTest")
                .transitions(t1, t2)
                .build();

            try (PetriNetExecutor executor = createWithEnvPlaces(
                    net, Map.of(envPlace, List.of()), Set.of(envInput))) {

                var threadRef = new java.util.concurrent.atomic.AtomicLong();

                ExecutorService orchestrator = Executors.newSingleThreadExecutor(r -> {
                    Thread t = new Thread(r, "drain-timed-spin-test");
                    threadRef.set(t.getId());
                    return t;
                });
                Future<Marking> runFuture = orchestrator.submit((Callable<Marking>) executor::run);

                Thread.sleep(50L);

                // Inject a token — T1 fires immediately (sync), enabling T2 (delayed 600ms)
                executor.inject(envInput, Token.of(new StringValue("go")));

                // Give T1 time to fire and enable T2
                Thread.sleep(50L);

                // Record CPU time, then drain.
                // At this point: T2 is enabled but waiting 600ms, nothing in-flight.
                long cpuBefore = threadMXBean.getThreadCpuTime(threadRef.get());
                executor.drain();

                // Wait for executor to finish — T2 should fire after its delay
                Marking marking = runFuture.get(5, TimeUnit.SECONDS);
                long cpuAfter = threadMXBean.getThreadCpuTime(threadRef.get());
                orchestrator.shutdownNow();

                long cpuDeltaMs = (cpuAfter - cpuBefore) / 1_000_000;

                // T2 should have fired and produced output
                assertTrue(marking.hasTokens(output),
                    "Delayed transition should complete after drain");

                // CPU time should be well under 200ms during the ~600ms delay wait.
                // Without fix: ~600ms CPU (tight spin). With fix: ~5ms (timer-bounded polling).
                assertTrue(cpuDeltaMs < 200,
                    "Orchestrator thread consumed " + cpuDeltaMs +
                    "ms of CPU after drain() — suspected spin (threshold: 200ms)");
            }
        }

        /**
         * Stress test: 20 concurrent net instances with environment places and timed
         * transitions, all drained simultaneously. Detects aggregate CPU spin.
         *
         * <p>Uses per-thread CPU deltas (before/after drain) to isolate spin from
         * legitimate startup work.
         */
        @Test
        @DisplayName("20 concurrent nets with drain() do not saturate CPU (stress)")
        void manyConcurrentNets_drain_doesNotSaturateCPU() throws Exception {
            var threadMXBean = java.lang.management.ManagementFactory.getThreadMXBean();
            Assumptions.assumeTrue(threadMXBean.isThreadCpuTimeSupported(),
                "Thread CPU time not supported on this JVM");

            int netCount = 20;

            record NetInstance(PetriNetExecutor executor, Future<Marking> future,
                              java.util.concurrent.atomic.AtomicLong threadRef,
                              EnvironmentPlace<StringValue> envInput) {}

            var allStarted = new java.util.concurrent.CountDownLatch(netCount);
            ExecutorService orchestrators = Executors.newFixedThreadPool(netCount);
            List<NetInstance> instances = new java.util.ArrayList<>();

            try {
                for (int i = 0; i < netCount; i++) {
                    Place<StringValue> envPlace = Place.of("ENV_" + i, StringValue.class);
                    EnvironmentPlace<StringValue> envInput = EnvironmentPlace.of(envPlace);
                    Place<StringValue> mid = Place.of("MID_" + i, StringValue.class);
                    Place<StringValue> out = Place.of("OUT_" + i, StringValue.class);

                    Transition t1 = Transition.builder("imm_" + i)
                        .inputs(Arc.In.one(envPlace))
                        .outputs(Arc.Out.and(mid))
                        .action(ctx -> {
                            ctx.output(mid, ctx.input(envPlace));
                            return CompletableFuture.completedFuture(null);
                        })
                        .build();

                    Transition t2 = Transition.builder("delayed_" + i)
                        .inputs(Arc.In.one(mid))
                        .outputs(Arc.Out.and(out))
                        .timing(Timing.delayed(Duration.ofMillis(500)))
                        .action(ctx -> {
                            ctx.output(out, ctx.input(mid));
                            return CompletableFuture.completedFuture(null);
                        })
                        .build();

                    PetriNet net = PetriNet.builder("StressNet_" + i)
                        .transitions(t1, t2).build();

                    PetriNetExecutor executor = createWithEnvPlaces(
                        net, Map.of(envPlace, List.of()), Set.of(envInput));

                    var threadRef = new java.util.concurrent.atomic.AtomicLong();
                    Future<Marking> future = orchestrators.submit(() -> {
                        threadRef.set(Thread.currentThread().getId());
                        allStarted.countDown();
                        return executor.run();
                    });
                    instances.add(new NetInstance(executor, future, threadRef, envInput));
                }

                assertTrue(allStarted.await(2, TimeUnit.SECONDS),
                    "All orchestrator threads should start within 2s");

                // Inject a token into each net — T1 fires immediately, enabling T2
                for (var inst : instances) {
                    inst.executor().inject(inst.envInput(), Token.of(new StringValue("go")));
                }

                // Wait for T1 to fire in all nets
                Thread.sleep(100L);

                // Snapshot per-thread CPU before drain
                long[] cpuBefore = new long[netCount];
                for (int i = 0; i < netCount; i++) {
                    cpuBefore[i] = threadMXBean.getThreadCpuTime(instances.get(i).threadRef().get());
                }
                long wallBefore = System.nanoTime();

                for (var inst : instances) {
                    inst.executor().drain();
                }

                // Wait for all to finish
                for (var inst : instances) {
                    inst.future().get(5, TimeUnit.SECONDS);
                }

                long wallMs = (System.nanoTime() - wallBefore) / 1_000_000;

                // Measure per-thread CPU delta since drain
                long totalCpuDeltaMs = 0;
                for (int i = 0; i < netCount; i++) {
                    long after = threadMXBean.getThreadCpuTime(instances.get(i).threadRef().get());
                    totalCpuDeltaMs += Math.max(0, after - cpuBefore[i]) / 1_000_000;
                }

                // With 20 spinning threads on 4 cores for ~500ms, we'd see ~2000ms total CPU.
                // With fix: ~20 threads × ~5ms each ≈ ~100ms total CPU.
                // Use 500ms threshold (generous but catches the pathological case).
                assertTrue(totalCpuDeltaMs < 500,
                    "Total orchestrator CPU across " + netCount + " nets: " + totalCpuDeltaMs +
                    "ms (wall: " + wallMs + "ms) — suspected spin (threshold: 500ms)");

            } finally {
                for (var inst : instances) {
                    inst.executor().close();
                }
                orchestrators.shutdownNow();
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

    @Nested
    class LifecycleTests {

        private PetriNet envNet(Place<StringValue> envPlace, Place<StringValue> output) {
            return PetriNet.builder("LifecycleNet").transitions(
                Transition.builder("passthrough")
                    .inputs(Arc.In.one(envPlace))
                    .outputs(Arc.Out.and(output))
                    .timing(Timing.deadline(Duration.ofMillis(10_000)))
                    .action(ctx -> {
                        ctx.output(output, ctx.input(envPlace));
                        return CompletableFuture.completedFuture(null);
                    })
                    .build()
            ).build();
        }

        @Test
        void awaitTermination_returnsImmediatelyWhenNeverStarted() throws Exception {
            Place<StringValue> envPlace = Place.of("ENV", StringValue.class);
            Place<StringValue> output = Place.of("OUT", StringValue.class);
            var envInput = EnvironmentPlace.of(envPlace);

            try (PetriNetExecutor executor = createWithEnvPlaces(
                    envNet(envPlace, output), Map.of(envPlace, List.of()), Set.of(envInput))) {
                assertTrue(executor.awaitTermination(Duration.ofMillis(50)),
                    "an executor that never ran has nothing to wait for");
            }
        }

        @Test
        void awaitTermination_observesTheLoopStopping() throws Exception {
            Place<StringValue> envPlace = Place.of("ENV", StringValue.class);
            Place<StringValue> output = Place.of("OUT", StringValue.class);
            var envInput = EnvironmentPlace.of(envPlace);

            try (PetriNetExecutor executor = createWithEnvPlaces(
                    envNet(envPlace, output), Map.of(envPlace, List.of()), Set.of(envInput))) {
                ExecutorService orchestrator = Executors.newSingleThreadExecutor();
                orchestrator.submit((Callable<Marking>) executor::run);

                assertTrue(executor.inject(envInput, Token.of(new StringValue("x")))
                    .get(5, TimeUnit.SECONDS));

                // Still running: an env-place net does not terminate at quiescence.
                assertFalse(executor.awaitTermination(Duration.ofMillis(100)),
                    "a live env-place executor must not report termination");

                executor.close();
                assertTrue(executor.awaitTermination(Duration.ofSeconds(5)),
                    "close() must let the loop finish and awaitTermination observe it");
                orchestrator.shutdownNow();
            }
        }

        @Test
        void runWithClosePolicy_stopsTheLoop_whereAbandonLeavesItRunning() throws Exception {
            Place<StringValue> envPlace = Place.of("ENV", StringValue.class);
            Place<StringValue> output = Place.of("OUT", StringValue.class);
            var envInput = EnvironmentPlace.of(envPlace);

            try (PetriNetExecutor executor = createWithEnvPlaces(
                    envNet(envPlace, output), Map.of(envPlace, List.of()), Set.of(envInput))) {

                var timedOut = executor
                    .run(Duration.ofMillis(150), PetriNetExecutor.RunTimeoutPolicy.CLOSE)
                    .toCompletableFuture();

                var ex = assertThrows(ExecutionException.class,
                    () -> timedOut.get(5, TimeUnit.SECONDS),
                    "the caller's stage fails on timeout");
                assertInstanceOf(TimeoutException.class, ex.getCause(),
                    "the failure cause is the run timeout, not a hung get()");
                assertTrue(executor.awaitTermination(Duration.ofSeconds(5)),
                    "CLOSE must actually stop the orchestrator, not just fail the stage");
            }
        }

        @Test
        void runWithAbandonPolicy_leavesTheLoopRunning() throws Exception {
            Place<StringValue> envPlace = Place.of("ENV", StringValue.class);
            Place<StringValue> output = Place.of("OUT", StringValue.class);
            var envInput = EnvironmentPlace.of(envPlace);

            try (PetriNetExecutor executor = createWithEnvPlaces(
                    envNet(envPlace, output), Map.of(envPlace, List.of()), Set.of(envInput))) {

                var stage = executor
                    .run(Duration.ofMillis(150), PetriNetExecutor.RunTimeoutPolicy.ABANDON)
                    .toCompletableFuture();

                var ex = assertThrows(ExecutionException.class,
                    () -> stage.get(5, TimeUnit.SECONDS));
                assertInstanceOf(TimeoutException.class, ex.getCause());

                // The stage failed, but ABANDON leaves the loop alive: an injected token is still
                // processed, which it could not be if the orchestrator had stopped.
                assertTrue(executor.inject(envInput, Token.of(new StringValue("still-alive")))
                        .get(2, TimeUnit.SECONDS),
                    "ABANDON must leave the loop running to accept the injection");
                long deadline = System.currentTimeMillis() + 2_000;
                while (!executor.marking().hasTokens(output)
                        && System.currentTimeMillis() < deadline) {
                    Thread.sleep(10L);
                }
                assertTrue(executor.marking().hasTokens(output),
                    "the abandoned loop must still process the injected token");

                executor.terminateNow();
                assertTrue(executor.awaitTermination(Duration.ofSeconds(5)));
            }
        }

        @Test
        void terminateNow_stopsWithoutWaitingForInFlightActions() throws Exception {
            Place<StringValue> envPlace = Place.of("ENV", StringValue.class);
            Place<StringValue> output = Place.of("OUT", StringValue.class);
            var envInput = EnvironmentPlace.of(envPlace);
            var gateHeld = new CountDownLatch(1);       // never released while the loop runs
            var actionStarted = new CountDownLatch(1);

            Transition consume = Transition.builder("consume")
                .inputs(Arc.In.one(envPlace))
                .outputs(Arc.Out.and(output))
                .action(ctx -> {
                    actionStarted.countDown();
                    return CompletableFuture.runAsync(() -> {
                        try {
                            gateHeld.await(5, TimeUnit.SECONDS);
                        } catch (InterruptedException e) {
                            Thread.currentThread().interrupt();
                            return;
                        }
                        ctx.output(output, new StringValue("late"));
                    });
                })
                .build();
            PetriNet net = PetriNet.builder("TerminateNowNet").transitions(consume).build();
            Map<Place<?>, List<Token<?>>> initial = Map.of(envPlace, List.of());

            try (PetriNetExecutor executor = createWithEnvPlaces(net, initial, Set.of(envInput))) {
                ExecutorService orchestrator = Executors.newSingleThreadExecutor();
                orchestrator.submit((Callable<Marking>) executor::run);
                Thread.sleep(50L);

                executor.inject(envInput, Token.of(new StringValue("x")));
                assertTrue(actionStarted.await(2, TimeUnit.SECONDS),
                    "the action must be in-flight before terminateNow");

                executor.terminateNow();
                assertTrue(executor.awaitTermination(Duration.ofSeconds(5)),
                    "terminateNow must stop the loop without waiting for the gated in-flight action");
                assertFalse(executor.marking().hasTokens(output),
                    "the abandoned in-flight action's output must not be admitted to the marking");

                gateHeld.countDown(); // let the parked action thread unwind
                orchestrator.shutdownNow();
            }
        }

        @Test
        void marking_readConcurrentlyWhileFiring_neverThrowsAndStaysConsistent() throws Exception {
            Place<StringValue> envPlace = Place.of("ENV", StringValue.class);
            Place<StringValue> backlog = Place.of("BACKLOG", StringValue.class);
            var envInput = EnvironmentPlace.of(envPlace);

            // Injected tokens pile into a backlog place, driving it well past the default ring
            // capacity (16) so the Precompiled ring grows and reallocates while foreign threads read.
            Transition ingest = Transition.builder("ingest")
                .inputs(Arc.In.one(envPlace))
                .outputs(Arc.Out.and(backlog))
                .action(ctx -> {
                    ctx.output(backlog, ctx.input(envPlace));
                    return CompletableFuture.completedFuture(null);
                })
                .build();
            PetriNet net = PetriNet.builder("ConcurrentReadNet").transitions(ingest).build();
            Map<Place<?>, List<Token<?>>> initial = Map.of(envPlace, List.of());

            try (PetriNetExecutor executor = createWithEnvPlaces(net, initial, Set.of(envInput))) {
                ExecutorService orchestrator = Executors.newSingleThreadExecutor();
                orchestrator.submit((Callable<Marking>) executor::run);
                Thread.sleep(50L);

                var stop = new AtomicBoolean(false);
                var readerError = new AtomicReference<Throwable>();
                int readers = 4;
                var readerPool = Executors.newFixedThreadPool(readers);
                for (int r = 0; r < readers; r++) {
                    readerPool.submit(() -> {
                        try {
                            while (!stop.get()) {
                                Marking m = executor.marking();
                                // A read must never see a negative or corrupt count.
                                int count = m.tokenCount(backlog);
                                if (count < 0) throw new AssertionError("negative token count: " + count);
                            }
                        } catch (Throwable t) {
                            readerError.compareAndSet(null, t);
                        }
                    });
                }

                for (int i = 0; i < 200; i++) {
                    executor.inject(envInput, Token.of(new StringValue("v" + i)));
                }
                Thread.sleep(300L);
                stop.set(true);
                readerPool.shutdown();
                assertTrue(readerPool.awaitTermination(5, TimeUnit.SECONDS));

                assertNull(readerError.get(),
                    "a concurrent marking() read must never throw or observe corruption");

                executor.terminateNow();
                assertTrue(executor.awaitTermination(Duration.ofSeconds(5)));
                orchestrator.shutdownNow();
            }
        }
    }

    /**
     * A long-running net driven by {@code inject()} must survive a failing action.
     *
     * <p>This is the shape production agent nets use: one long-lived executor per session,
     * fed through environment places. Before the failure boundary existed, one unchecked
     * throw out of any action killed the orchestrator loop, and every later {@code inject()}
     * blocked its caller forever on a future nobody would ever complete.
     */
    @Nested
    class FailureBoundaryTests {

        @Test
        void actionThrowing_doesNotStrandLaterInjections() throws Exception {
            Place<StringValue> envPlace = Place.of("ENV_INPUT", StringValue.class);
            EnvironmentPlace<StringValue> envInput = EnvironmentPlace.of(envPlace);
            Place<StringValue> output = Place.of("OUTPUT", StringValue.class);

            CountDownLatch firstFired = new CountDownLatch(1);

            Transition throwing = Transition.builder("throwing")
                .inputs(Arc.In.one(envPlace))
                .outputs(Arc.Out.and(output))
                .timing(Timing.deadline(Duration.ofMillis(10_000)))
                .action(ctx -> {
                    firstFired.countDown();
                    throw new IllegalStateException("action blew up");
                })
                .build();

            PetriNet net = PetriNet.builder("InjectAfterFailureTest")
                .transitions(throwing)
                .build();

            try (PetriNetExecutor executor =
                     createWithEnvPlaces(net, Map.of(envPlace, List.of()), Set.of(envInput))) {
                ExecutorService orchestrator = Executors.newSingleThreadExecutor();
                Future<Marking> runFuture = orchestrator.submit((Callable<Marking>) executor::run);

                assertTrue(
                    executor.inject(envInput, Token.of(new StringValue("first")))
                        .get(5, TimeUnit.SECONDS),
                    "first injection is accepted"
                );
                assertTrue(firstFired.await(5, TimeUnit.SECONDS),
                    "the failing action must actually have run");

                // The decisive assertion: the loop survived the throw, so this injection is
                // still serviced. Without the failure boundary this future is never completed
                // and get() times out.
                assertTrue(
                    executor.inject(envInput, Token.of(new StringValue("second")))
                        .get(5, TimeUnit.SECONDS),
                    "an injection after a failed firing must still be serviced"
                );

                executor.close();
                runFuture.get(10, TimeUnit.SECONDS);
                orchestrator.shutdownNow();
            }
        }
    }
}
