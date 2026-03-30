package org.libpetri.runtime;

import static org.junit.jupiter.api.Assertions.*;

import java.time.Duration;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

import org.libpetri.core.*;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

class BitmapNetExecutorTest {

    private final ExecutorService testExecutor = Executors.newVirtualThreadPerTaskExecutor();

    record SimpleValue(String data) {}

    // ==================== Linear Chain ====================

    @Nested
    class LinearChainTests {

        @Test
        void singleTransition_producesToken() {
            var start = Place.of("start", SimpleValue.class);
            var end = Place.of("end", SimpleValue.class);

            var t = Transition.builder("t1")
                .inputs(In.one(start))
                .outputs(Out.place(end))
                .action(ctx -> {
                    ctx.output(end, new SimpleValue("result"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("Test").transitions(t).build();

            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(start, List.of(Token.of(new SimpleValue("input")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(end));
                assertFalse(result.hasTokens(start));
                assertEquals("result", result.peekFirst(end).value().data());
            }
        }

        @Test
        void threeTransitionChain_executesInOrder() {
            var p1 = Place.of("p1", SimpleValue.class);
            var p2 = Place.of("p2", SimpleValue.class);
            var p3 = Place.of("p3", SimpleValue.class);
            var p4 = Place.of("p4", SimpleValue.class);

            var order = new AtomicInteger(0);

            var t1 = Transition.builder("t1")
                .inputs(In.one(p1)).outputs(Out.place(p2))
                .action(ctx -> {
                    assertEquals(0, order.getAndIncrement());
                    ctx.output(p2, new SimpleValue("1"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var t2 = Transition.builder("t2")
                .inputs(In.one(p2)).outputs(Out.place(p3))
                .action(ctx -> {
                    assertEquals(1, order.getAndIncrement());
                    ctx.output(p3, new SimpleValue("2"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var t3 = Transition.builder("t3")
                .inputs(In.one(p3)).outputs(Out.place(p4))
                .action(ctx -> {
                    assertEquals(2, order.getAndIncrement());
                    ctx.output(p4, new SimpleValue("3"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("Chain").transitions(t1, t2, t3).build();

            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(p1, List.of(Token.of(new SimpleValue("start")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(p4));
                assertEquals(3, order.get());
            }
        }

        @Test
        void asyncTransition_executesOnVirtualThread() {
            var start = Place.of("start", SimpleValue.class);
            var end = Place.of("end", SimpleValue.class);
            var threadName = new AtomicReference<String>();

            var t = Transition.builder("async")
                .inputs(In.one(start)).outputs(Out.place(end))
                .action(ctx -> {
                    ctx.output(end, new SimpleValue("async"));
                    return CompletableFuture.supplyAsync(() -> {
                        threadName.set(Thread.currentThread().getName());
                        return null;
                    }, testExecutor);
                }).build();

            var net = PetriNet.builder("Async").transitions(t).build();

            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(start, List.of(Token.of(new SimpleValue("input")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(end));
                assertNotNull(threadName.get());
            }
        }
    }

    // ==================== Inhibitor Arcs ====================

    @Nested
    class InhibitorArcTests {

        @Test
        void inhibitor_blocksTransition() {
            var input = Place.of("input", SimpleValue.class);
            var blocker = Place.of("blocker", SimpleValue.class);
            var output = Place.of("output", SimpleValue.class);
            var fired = new AtomicBoolean(false);

            var t = Transition.builder("inhibited")
                .inputs(In.one(input)).outputs(Out.place(output))
                .inhibitor(blocker)
                .action(ctx -> {
                    fired.set(true);
                    ctx.output(output, new SimpleValue("out"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("Inhibitor").transitions(t).build();

            // Both input and blocker have tokens -> transition should NOT fire
            try (var executor = BitmapNetExecutor.create(net, Map.of(
                    input, List.of(Token.of(new SimpleValue("in"))),
                    blocker, List.of(Token.of(new SimpleValue("block")))))) {
                var result = executor.run();
                assertFalse(fired.get());
                assertTrue(result.hasTokens(input));
                assertTrue(result.hasTokens(blocker));
                assertFalse(result.hasTokens(output));
            }
        }

        @Test
        void inhibitor_enablesWhenBlockerRemoved() {
            var input = Place.of("input", SimpleValue.class);
            var blocker = Place.of("blocker", SimpleValue.class);
            var output = Place.of("output", SimpleValue.class);
            var unblock = Place.of("unblock", SimpleValue.class);

            // t_remove: consumes blocker
            var tRemove = Transition.builder("remove")
                .inputs(In.one(unblock)).outputs(Out.place(blocker))
                .action(ctx -> {
                    // Don't produce to blocker, just consume from unblock
                    return CompletableFuture.completedFuture(null);
                }).build();

            // Actually, let's use reset to clear the blocker
            var tRemoveBlocker = Transition.builder("removeBlocker")
                .inputs(In.one(blocker))
                .action(ctx -> CompletableFuture.completedFuture(null))
                .build();

            var tInhibited = Transition.builder("inhibited")
                .inputs(In.one(input)).outputs(Out.place(output))
                .inhibitor(blocker)
                .action(ctx -> {
                    ctx.output(output, new SimpleValue("done"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("Unblock")
                .transitions(tRemoveBlocker, tInhibited).build();

            try (var executor = BitmapNetExecutor.create(net, Map.of(
                    input, List.of(Token.of(new SimpleValue("in"))),
                    blocker, List.of(Token.of(new SimpleValue("b")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(output));
            }
        }
    }

    // ==================== Read Arcs ====================

    @Nested
    class ReadArcTests {

        @Test
        void readArc_doesNotConsumeToken() {
            var input = Place.of("input", SimpleValue.class);
            var config = Place.of("config", SimpleValue.class);
            var output = Place.of("output", SimpleValue.class);

            var t = Transition.builder("read")
                .inputs(In.one(input)).outputs(Out.place(output))
                .read(config)
                .action(ctx -> {
                    ctx.output(output, new SimpleValue("done"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("Read").transitions(t).build();

            try (var executor = BitmapNetExecutor.create(net, Map.of(
                    input, List.of(Token.of(new SimpleValue("in"))),
                    config, List.of(Token.of(new SimpleValue("cfg")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(output));
                assertTrue(result.hasTokens(config)); // still present
                assertFalse(result.hasTokens(input)); // consumed
            }
        }

        @Test
        void readArc_blocksWhenMissing() {
            var input = Place.of("input", SimpleValue.class);
            var config = Place.of("config", SimpleValue.class);
            var output = Place.of("output", SimpleValue.class);
            var fired = new AtomicBoolean(false);

            var t = Transition.builder("needsRead")
                .inputs(In.one(input)).outputs(Out.place(output))
                .read(config)
                .action(ctx -> {
                    fired.set(true);
                    ctx.output(output, new SimpleValue("done"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("NoRead").transitions(t).build();

            // No config token -> transition blocked
            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(input, List.of(Token.of(new SimpleValue("in")))))) {
                var result = executor.run();
                assertFalse(fired.get());
            }
        }
    }

    // ==================== Reset Arcs ====================

    @Nested
    class ResetArcTests {

        @Test
        void resetArc_removesAllTokens() {
            var input = Place.of("input", SimpleValue.class);
            var toReset = Place.of("toReset", SimpleValue.class);
            var output = Place.of("output", SimpleValue.class);

            var t = Transition.builder("resetter")
                .inputs(In.one(input)).outputs(Out.place(output))
                .reset(toReset)
                .action(ctx -> {
                    ctx.output(output, new SimpleValue("done"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("Reset").transitions(t).build();

            try (var executor = BitmapNetExecutor.create(net, Map.of(
                    input, List.of(Token.of(new SimpleValue("in"))),
                    toReset, List.of(
                        Token.of(new SimpleValue("a")),
                        Token.of(new SimpleValue("b")),
                        Token.of(new SimpleValue("c")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(output));
                assertFalse(result.hasTokens(toReset)); // all cleared
            }
        }

        @Test
        void resetArc_clockRestartOnNewTokens() {
            var input = Place.of("input", SimpleValue.class);
            var buffer = Place.of("buffer", SimpleValue.class);
            var output = Place.of("output", SimpleValue.class);
            var timedOutput = Place.of("timedOutput", SimpleValue.class);

            // t1: resets buffer and produces new token to it
            var t1 = Transition.builder("resetter")
                .inputs(In.one(input)).outputs(Out.and(output, buffer))
                .reset(buffer)
                .action(ctx -> {
                    ctx.output(output, new SimpleValue("done"));
                    ctx.output(buffer, new SimpleValue("new"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            // t2: timed transition consuming from buffer
            var t2 = Transition.builder("timed")
                .inputs(In.one(buffer)).outputs(Out.place(timedOutput))
                .timing(Timing.delayed(Duration.ofMillis(10)))
                .action(ctx -> {
                    ctx.output(timedOutput, new SimpleValue("timed"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("ResetClock").transitions(t1, t2).build();

            try (var executor = BitmapNetExecutor.create(net, Map.of(
                    input, List.of(Token.of(new SimpleValue("start"))),
                    buffer, List.of(Token.of(new SimpleValue("old")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(timedOutput));
            }
        }
    }

    // ==================== Priority ====================

    @Nested
    class PriorityTests {

        @Test
        void higherPriority_firesFirst() {
            var shared = Place.of("shared", SimpleValue.class);
            var lowOut = Place.of("lowOut", SimpleValue.class);
            var highOut = Place.of("highOut", SimpleValue.class);

            var low = Transition.builder("low")
                .inputs(In.one(shared)).outputs(Out.place(lowOut))
                .priority(1)
                .action(ctx -> {
                    ctx.output(lowOut, new SimpleValue("low"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var high = Transition.builder("high")
                .inputs(In.one(shared)).outputs(Out.place(highOut))
                .priority(10)
                .action(ctx -> {
                    ctx.output(highOut, new SimpleValue("high"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("Priority").transitions(low, high).build();

            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(shared, List.of(Token.of(new SimpleValue("token")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(highOut));
                assertFalse(result.hasTokens(lowOut));
            }
        }
    }

    // ==================== Timed Transitions ====================

    @Nested
    class TimedTransitionTests {

        @Test
        void delayedTransition_waitsBeforeFiring() {
            var start = Place.of("start", SimpleValue.class);
            var end = Place.of("end", SimpleValue.class);
            var fireTime = new AtomicReference<Long>();

            long beforeNanos = System.nanoTime();

            var t = Transition.builder("delayed")
                .inputs(In.one(start)).outputs(Out.place(end))
                .timing(Timing.delayed(Duration.ofMillis(50)))
                .action(ctx -> {
                    fireTime.set(System.nanoTime());
                    ctx.output(end, new SimpleValue("delayed"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("Delayed").transitions(t).build();

            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(start, List.of(Token.of(new SimpleValue("go")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(end));
                long elapsed = (fireTime.get() - beforeNanos) / 1_000_000;
                assertTrue(elapsed >= 40, "Should have waited ~50ms, got " + elapsed + "ms");
            }
        }

        @Test
        void windowTiming_respectsEarliest() {
            var start = Place.of("start", SimpleValue.class);
            var end = Place.of("end", SimpleValue.class);

            var t = Transition.builder("windowed")
                .inputs(In.one(start)).outputs(Out.place(end))
                .timing(Timing.window(Duration.ofMillis(30), Duration.ofMillis(200)))
                .action(ctx -> {
                    ctx.output(end, new SimpleValue("done"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("Window").transitions(t).build();

            long beforeNanos = System.nanoTime();
            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(start, List.of(Token.of(new SimpleValue("go")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(end));
                long elapsed = (System.nanoTime() - beforeNanos) / 1_000_000;
                assertTrue(elapsed >= 25, "Should have waited ~30ms, got " + elapsed + "ms");
            }
        }
    }

    // ==================== Cardinality ====================

    @Nested
    class CardinalityTests {

        @Test
        void exactlyN_consumesExactlyNTokens() {
            var input = Place.of("input", SimpleValue.class);
            var output = Place.of("output", SimpleValue.class);

            var t = Transition.builder("batch")
                .inputs(In.exactly(3, input))
                .outputs(Out.place(output))
                .action(ctx -> {
                    var items = ctx.inputs(input);
                    assertEquals(3, items.size());
                    ctx.output(output, new SimpleValue("batch:" + items.size()));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("Batch").transitions(t).build();

            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(input, List.of(
                        Token.of(new SimpleValue("a")),
                        Token.of(new SimpleValue("b")),
                        Token.of(new SimpleValue("c")),
                        Token.of(new SimpleValue("d")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(output));
                assertEquals(1, result.tokenCount(input)); // 4 - 3 = 1 remaining
            }
        }

        @Test
        void all_consumesAllTokens() {
            var input = Place.of("input", SimpleValue.class);
            var output = Place.of("output", SimpleValue.class);

            var t = Transition.builder("drain")
                .inputs(In.all(input))
                .outputs(Out.place(output))
                .action(ctx -> {
                    var items = ctx.inputs(input);
                    ctx.output(output, new SimpleValue("drained:" + items.size()));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("Drain").transitions(t).build();

            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(input, List.of(
                        Token.of(new SimpleValue("a")),
                        Token.of(new SimpleValue("b")),
                        Token.of(new SimpleValue("c")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(output));
                assertFalse(result.hasTokens(input));
                assertEquals("drained:3", result.peekFirst(output).value().data());
            }
        }

        @Test
        void atLeast_waitsForMinimum() {
            var input = Place.of("input", SimpleValue.class);
            var output = Place.of("output", SimpleValue.class);
            var fired = new AtomicBoolean(false);

            var t = Transition.builder("accumulate")
                .inputs(In.atLeast(5, input))
                .outputs(Out.place(output))
                .action(ctx -> {
                    fired.set(true);
                    ctx.output(output, new SimpleValue("accumulated"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("Accumulate").transitions(t).build();

            // Only 3 tokens, need 5 -> should not fire
            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(input, List.of(
                        Token.of(new SimpleValue("a")),
                        Token.of(new SimpleValue("b")),
                        Token.of(new SimpleValue("c")))))) {
                var result = executor.run();
                assertFalse(fired.get());
            }
        }
    }

    // ==================== XOR Output ====================

    @Nested
    class XorOutputTests {

        @Test
        void xorOutput_singleBranchProduced() {
            var input = Place.of("input", SimpleValue.class);
            var success = Place.of("success", SimpleValue.class);
            var error = Place.of("error", SimpleValue.class);

            var t = Transition.builder("xor")
                .inputs(In.one(input))
                .outputs(Out.xor(success, error))
                .action(ctx -> {
                    ctx.output(success, new SimpleValue("ok"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("XOR").transitions(t).build();

            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(input, List.of(Token.of(new SimpleValue("go")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(success));
                assertFalse(result.hasTokens(error));
            }
        }
    }

    // ==================== Environment Places ====================

    @Nested
    class EnvironmentPlaceTests {

        @Test
        void inject_addsTokenAndWakesExecutor() throws Exception {
            var envPlace = Place.of("env", SimpleValue.class);
            var env = EnvironmentPlace.of(envPlace);
            var output = Place.of("output", SimpleValue.class);

            var t = Transition.builder("react")
                .inputs(In.one(envPlace)).outputs(Out.place(output))
                .action(ctx -> {
                    ctx.output(output, new SimpleValue("reacted"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("Reactive").transitions(t).build();

            try (var executor = BitmapNetExecutor.builder(net, Map.of())
                    .environmentPlaces(env)
                    .build()) {

                var runFuture = CompletableFuture.supplyAsync(executor::run, testExecutor);

                // Give executor time to start
                Thread.sleep(50);

                // Inject token
                var injected = executor.inject(env, new SimpleValue("event"));
                assertTrue(injected.get(1, TimeUnit.SECONDS));

                // Give executor time to process
                Thread.sleep(100);

                // Drain to terminate
                executor.drain();
                var result = runFuture.get(2, TimeUnit.SECONDS);
                assertTrue(result.hasTokens(output));
            }
        }
    }

    // ==================== Concurrent Injection Stress ====================

    @Nested
    class ConcurrentInjectionTests {

        @Test
        void concurrentInjection_allTokensArriveAndProcess() throws Exception {
            var envPlace = Place.of("env", SimpleValue.class);
            var env = EnvironmentPlace.of(envPlace);
            var output = Place.of("output", SimpleValue.class);

            var processedCount = new AtomicInteger(0);

            var t = Transition.builder("consumer")
                .inputs(In.one(envPlace)).outputs(Out.place(output))
                .action(ctx -> {
                    processedCount.incrementAndGet();
                    ctx.output(output, ctx.input(envPlace));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("StressTest").transitions(t).build();

            int threadCount = 16;
            int injectionsPerThread = 10;
            int totalInjections = threadCount * injectionsPerThread;

            try (var executor = BitmapNetExecutor.builder(net, Map.of())
                    .environmentPlaces(env)
                    .build()) {

                var runFuture = CompletableFuture.supplyAsync(executor::run, testExecutor);

                // Wait for executor to start
                Thread.sleep(50);

                var latch = new java.util.concurrent.CountDownLatch(1);
                var futures = new ArrayList<CompletableFuture<Boolean>>();

                // Launch threads that all inject concurrently
                for (int thread = 0; thread < threadCount; thread++) {
                    int threadId = thread;
                    for (int i = 0; i < injectionsPerThread; i++) {
                        int injectionId = i;
                        var f = CompletableFuture.supplyAsync(() -> {
                            try {
                                latch.await();
                            } catch (InterruptedException e) {
                                Thread.currentThread().interrupt();
                            }
                            return executor.inject(env, new SimpleValue("t" + threadId + "_i" + injectionId));
                        }, testExecutor).thenCompose(inner -> inner);
                        futures.add(f);
                    }
                }

                // Release all threads simultaneously
                latch.countDown();

                // Wait for all injections to be accepted
                for (var f : futures) {
                    assertTrue(f.get(5, TimeUnit.SECONDS), "Injection should succeed");
                }

                // Give executor time to process all tokens
                long deadline = System.currentTimeMillis() + 5000;
                while (processedCount.get() < totalInjections && System.currentTimeMillis() < deadline) {
                    Thread.sleep(50);
                }

                executor.drain();
                runFuture.get(2, TimeUnit.SECONDS);

                assertEquals(totalInjections, processedCount.get(),
                    "All " + totalInjections + " injected tokens should be processed");
            }
        }
    }

    // ==================== Fork / AND Join ====================

    @Nested
    class ForkJoinTests {

        @Test
        void forkAndJoin_parallelPaths() {
            var input = Place.of("input", SimpleValue.class);
            var branch1 = Place.of("branch1", SimpleValue.class);
            var branch2 = Place.of("branch2", SimpleValue.class);
            var done1 = Place.of("done1", SimpleValue.class);
            var done2 = Place.of("done2", SimpleValue.class);
            var result = Place.of("result", SimpleValue.class);

            var fork = Transition.builder("fork")
                .inputs(In.one(input))
                .outputs(Out.and(branch1, branch2))
                .action(TransitionAction.fork())
                .build();

            var work1 = Transition.builder("work1")
                .inputs(In.one(branch1)).outputs(Out.place(done1))
                .action(ctx -> {
                    ctx.output(done1, new SimpleValue("w1"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var work2 = Transition.builder("work2")
                .inputs(In.one(branch2)).outputs(Out.place(done2))
                .action(ctx -> {
                    ctx.output(done2, new SimpleValue("w2"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var join = Transition.builder("join")
                .inputs(In.one(done1), In.one(done2))
                .outputs(Out.place(result))
                .action(ctx -> {
                    ctx.output(result, new SimpleValue("joined"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("ForkJoin")
                .transitions(fork, work1, work2, join).build();

            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(input, List.of(Token.of(new SimpleValue("start")))))) {
                var res = executor.run();
                assertTrue(res.hasTokens(result));
                assertEquals("joined", res.peekFirst(result).value().data());
            }
        }
    }

    // ==================== Complex Workflow (Integration Test) ====================

    @Nested
    class ComplexWorkflowTest {

        @Test
        void complexWorkflow_forkXorReadInhibitorPriorityAndJoin() {
            var v_input = Place.of("v_input", SimpleValue.class);
            var v_guardIn = Place.of("v_guardIn", SimpleValue.class);
            var v_intentIn = Place.of("v_intentIn", SimpleValue.class);
            var v_searchIn = Place.of("v_searchIn", SimpleValue.class);
            var v_topicIn = Place.of("v_topicIn", SimpleValue.class);
            var v_guardSafe = Place.of("v_guardSafe", SimpleValue.class);
            var v_guardViolation = Place.of("v_guardViolation", SimpleValue.class);
            var v_intentReady = Place.of("v_intentReady", SimpleValue.class);
            var v_topicReady = Place.of("v_topicReady", SimpleValue.class);
            var v_searchReady = Place.of("v_searchReady", SimpleValue.class);
            var v_response = Place.of("v_response", SimpleValue.class);

            // Fork: 1-to-4 fan-out
            var forkTrans = Transition.builder("Fork")
                .inputs(In.one(v_input))
                .outputs(Out.and(v_guardIn, v_intentIn, v_searchIn, v_topicIn))
                .action(TransitionAction.fork())
                .build();

            // Guard: XOR output (safe or violation)
            var guardTrans = Transition.builder("Guard")
                .inputs(In.one(v_guardIn))
                .outputs(Out.xor(v_guardSafe, v_guardViolation))
                .action(ctx -> {
                    ctx.output(v_guardSafe, new SimpleValue("safe"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            // Intent: produces intentReady (read by Search and TopicKnowledge)
            var intentTrans = Transition.builder("Intent")
                .inputs(In.one(v_intentIn))
                .outputs(Out.place(v_intentReady))
                .action(ctx -> {
                    ctx.output(v_intentReady, new SimpleValue("intent"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            // TopicKnowledge: reads intentReady (doesn't consume), uses own input from fork
            var topicTrans = Transition.builder("TopicKnowledge")
                .inputs(In.one(v_topicIn))
                .outputs(Out.place(v_topicReady))
                .read(v_intentReady)
                .action(ctx -> {
                    ctx.output(v_topicReady, new SimpleValue("topic"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            // Search: reads intentReady, inhibited by guardViolation, low priority
            var searchTrans = Transition.builder("Search")
                .inputs(In.one(v_searchIn))
                .outputs(Out.place(v_searchReady))
                .read(v_intentReady)
                .inhibitor(v_guardViolation)
                .priority(-5)
                .action(ctx -> {
                    ctx.output(v_searchReady, new SimpleValue("results"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            // Compose: AND-join of 3 parallel paths
            var composeTrans = Transition.builder("Compose")
                .inputs(In.one(v_guardSafe), In.one(v_searchReady), In.one(v_topicReady))
                .outputs(Out.place(v_response))
                .priority(10)
                .action(ctx -> {
                    ctx.output(v_response, new SimpleValue("composed"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("ComplexWorkflow")
                .transitions(forkTrans, guardTrans, intentTrans, topicTrans, searchTrans, composeTrans)
                .build();

            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(v_input, List.of(Token.of(new SimpleValue("hello")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(v_response));
                assertEquals("composed", result.peekFirst(v_response).value().data());
            }
        }
    }

    // ==================== Event Store Integration ====================

    @Nested
    class EventStoreTests {

        @Test
        void eventStore_recordsEvents() {
            var start = Place.of("start", SimpleValue.class);
            var end = Place.of("end", SimpleValue.class);

            var t = Transition.builder("tracked")
                .inputs(In.one(start)).outputs(Out.place(end))
                .action(ctx -> {
                    ctx.output(end, new SimpleValue("done"));
                    return CompletableFuture.completedFuture(null);
                }).build();

            var net = PetriNet.builder("Tracked").transitions(t).build();
            var store = EventStore.inMemory();

            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(start, List.of(Token.of(new SimpleValue("go")))),
                    store)) {
                executor.run();
            }

            assertTrue(store.stream().count() > 0);
            assertFalse(store.eventsOfType(NetEvent.ExecutionStarted.class).isEmpty());
            assertFalse(store.eventsOfType(NetEvent.TransitionStarted.class).isEmpty());
            assertFalse(store.eventsOfType(NetEvent.TransitionCompleted.class).isEmpty());
            assertFalse(store.eventsOfType(NetEvent.ExecutionCompleted.class).isEmpty());
        }
    }

    // ==================== CompiledNet Unit Tests ====================

    @Nested
    class CompiledNetTests {

        @Test
        void compile_assignsConsecutiveIds() {
            var p1 = Place.of("p1", SimpleValue.class);
            var p2 = Place.of("p2", SimpleValue.class);
            var p3 = Place.of("p3", SimpleValue.class);

            var t1 = Transition.builder("t1")
                .inputs(In.one(p1)).outputs(Out.place(p2))
                .action(TransitionAction.passthrough()).build();
            var t2 = Transition.builder("t2")
                .inputs(In.one(p2)).outputs(Out.place(p3))
                .action(TransitionAction.passthrough()).build();

            var net = PetriNet.builder("Test").transitions(t1, t2).build();
            var compiled = CompiledNet.compile(net);

            assertEquals(3, compiled.placeCount());
            assertEquals(2, compiled.transitionCount());
            assertEquals(1, compiled.wordCount()); // 3 places fit in 1 word

            // IDs should be valid
            int pid1 = compiled.placeId(p1);
            int pid2 = compiled.placeId(p2);
            int pid3 = compiled.placeId(p3);
            assertTrue(pid1 >= 0 && pid1 < 3);
            assertTrue(pid2 >= 0 && pid2 < 3);
            assertTrue(pid3 >= 0 && pid3 < 3);
            assertNotEquals(pid1, pid2);
            assertNotEquals(pid2, pid3);
        }

        @Test
        void needsMask_includesInputAndReadPlaces() {
            var input = Place.of("input", SimpleValue.class);
            var readP = Place.of("readP", SimpleValue.class);
            var output = Place.of("output", SimpleValue.class);

            var t = Transition.builder("t")
                .inputs(In.one(input)).outputs(Out.place(output))
                .read(readP)
                .action(TransitionAction.passthrough()).build();

            var net = PetriNet.builder("Test").transitions(t).build();
            var compiled = CompiledNet.compile(net);
            int tid = compiled.transitionId(t);

            var needs = compiled.needsMask(tid);
            assertTrue(needs.get(compiled.placeId(input)));
            assertTrue(needs.get(compiled.placeId(readP)));
            assertFalse(needs.get(compiled.placeId(output)));
        }

        @Test
        void inhibitorMask_tracksInhibitorPlaces() {
            var input = Place.of("input", SimpleValue.class);
            var blocker = Place.of("blocker", SimpleValue.class);
            var output = Place.of("output", SimpleValue.class);

            var t = Transition.builder("t")
                .inputs(In.one(input)).outputs(Out.place(output))
                .inhibitor(blocker)
                .action(TransitionAction.passthrough()).build();

            var net = PetriNet.builder("Test").transitions(t).build();
            var compiled = CompiledNet.compile(net);
            int tid = compiled.transitionId(t);

            var inhibitors = compiled.inhibitorMask(tid);
            assertTrue(inhibitors.get(compiled.placeId(blocker)));
            assertFalse(inhibitors.get(compiled.placeId(input)));
        }

        @Test
        void reverseIndex_mapsPlaceToAffectedTransitions() {
            var shared = Place.of("shared", SimpleValue.class);
            var out1 = Place.of("out1", SimpleValue.class);
            var out2 = Place.of("out2", SimpleValue.class);

            var t1 = Transition.builder("t1")
                .inputs(In.one(shared)).outputs(Out.place(out1))
                .action(TransitionAction.passthrough()).build();
            var t2 = Transition.builder("t2")
                .inputs(In.one(shared)).outputs(Out.place(out2))
                .action(TransitionAction.passthrough()).build();

            var net = PetriNet.builder("Test").transitions(t1, t2).build();
            var compiled = CompiledNet.compile(net);

            int pid = compiled.placeId(shared);
            int[] affected = compiled.affectedTransitions(pid);
            assertEquals(2, affected.length);
        }

        @Test
        void canEnableBitmap_checksPresenceAndInhibitors() {
            var input = Place.of("input", SimpleValue.class);
            var blocker = Place.of("blocker", SimpleValue.class);
            var output = Place.of("output", SimpleValue.class);

            var t = Transition.builder("t")
                .inputs(In.one(input)).outputs(Out.place(output))
                .inhibitor(blocker)
                .action(TransitionAction.passthrough()).build();

            var net = PetriNet.builder("Test").transitions(t).build();
            var compiled = CompiledNet.compile(net);
            int tid = compiled.transitionId(t);
            int pidInput = compiled.placeId(input);
            int pidBlocker = compiled.placeId(blocker);

            // No tokens -> not enabled
            assertFalse(compiled.canEnableBitmap(tid, new long[compiled.wordCount()]));

            // Input present, no blocker -> enabled
            long[] snap1 = new long[compiled.wordCount()];
            snap1[pidInput >>> 6] |= 1L << (pidInput & 63);
            assertTrue(compiled.canEnableBitmap(tid, snap1));

            // Input present + blocker present -> not enabled
            long[] snap2 = snap1.clone();
            snap2[pidBlocker >>> 6] |= 1L << (pidBlocker & 63);
            assertFalse(compiled.canEnableBitmap(tid, snap2));
        }
    }

    // ==================== Timeout ====================

    @Nested
    class TimeoutTests {

        @Test
        void actionTimeout_routesToTimeoutBranch() {
            var input = Place.of("input", SimpleValue.class);
            var success = Place.of("success", SimpleValue.class);
            var timeout = Place.of("timeout", SimpleValue.class);

            var t = Transition.builder("slow")
                .inputs(In.one(input))
                .outputs(Out.xor(
                    Out.place(success),
                    Out.timeout(Duration.ofMillis(50), timeout)))
                .action(ctx -> {
                    // Slow action - will timeout
                    return CompletableFuture.supplyAsync(() -> {
                        try { Thread.sleep(500); } catch (InterruptedException e) { Thread.currentThread().interrupt(); }
                        ctx.output(success, new SimpleValue("late"));
                        return null;
                    }, testExecutor);
                }).build();

            var net = PetriNet.builder("Timeout").transitions(t).build();

            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(input, List.of(Token.of(new SimpleValue("go")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(timeout));
                assertFalse(result.hasTokens(success));
            }
        }
    }

    // ==================== Error Handling ====================

    @Nested
    class ErrorHandlingTests {

        @Test
        void actionException_recordsFailure() {
            var input = Place.of("input", SimpleValue.class);
            var output = Place.of("output", SimpleValue.class);

            var t = Transition.builder("failing")
                .inputs(In.one(input)).outputs(Out.place(output))
                .action(ctx -> {
                    return CompletableFuture.failedFuture(new RuntimeException("boom"));
                }).build();

            var net = PetriNet.builder("Fail").transitions(t).build();
            var store = EventStore.inMemory();

            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(input, List.of(Token.of(new SimpleValue("go")))),
                    store)) {
                var result = executor.run();
                assertFalse(result.hasTokens(output));
            }

            assertFalse(store.failures().isEmpty());
        }
    }

    // ==================== CAS Bitmap Primitives ====================

    @Nested
    class CasBitmapTests {

        @Test
        void casSetBit_bit0() {
            var arr = new java.util.concurrent.atomic.AtomicLongArray(1);
            BitmapNetExecutor.casSetBit(arr, 0);
            assertEquals(1L, arr.get(0));
        }

        @Test
        void casSetBit_bit63_wordBoundary() {
            var arr = new java.util.concurrent.atomic.AtomicLongArray(1);
            BitmapNetExecutor.casSetBit(arr, 63);
            assertEquals(Long.MIN_VALUE, arr.get(0)); // 1L << 63 == Long.MIN_VALUE
        }

        @Test
        void casSetBit_bit64_secondWord() {
            var arr = new java.util.concurrent.atomic.AtomicLongArray(2);
            BitmapNetExecutor.casSetBit(arr, 64);
            assertEquals(0L, arr.get(0));
            assertEquals(1L, arr.get(1));
        }

        @Test
        void casSetBit_idempotent() {
            var arr = new java.util.concurrent.atomic.AtomicLongArray(1);
            BitmapNetExecutor.casSetBit(arr, 5);
            long after1 = arr.get(0);
            BitmapNetExecutor.casSetBit(arr, 5);
            assertEquals(after1, arr.get(0));
        }

        @Test
        void casClearBit_clearsSetBit() {
            var arr = new java.util.concurrent.atomic.AtomicLongArray(1);
            BitmapNetExecutor.casSetBit(arr, 10);
            assertTrue((arr.get(0) & (1L << 10)) != 0);
            BitmapNetExecutor.casClearBit(arr, 10);
            assertEquals(0L, arr.get(0));
        }

        @Test
        void casClearBit_idempotent() {
            var arr = new java.util.concurrent.atomic.AtomicLongArray(1);
            BitmapNetExecutor.casClearBit(arr, 10);
            assertEquals(0L, arr.get(0));
        }

        @Test
        void casClearBit_bit63() {
            var arr = new java.util.concurrent.atomic.AtomicLongArray(1);
            BitmapNetExecutor.casSetBit(arr, 63);
            BitmapNetExecutor.casClearBit(arr, 63);
            assertEquals(0L, arr.get(0));
        }

        @Test
        void casClearBit_preservesOtherBits() {
            var arr = new java.util.concurrent.atomic.AtomicLongArray(1);
            BitmapNetExecutor.casSetBit(arr, 3);
            BitmapNetExecutor.casSetBit(arr, 7);
            BitmapNetExecutor.casClearBit(arr, 3);
            assertEquals(1L << 7, arr.get(0));
        }

        @Test
        void snapshot_emptyArray() {
            var arr = new java.util.concurrent.atomic.AtomicLongArray(2);
            long[] snap = BitmapNetExecutor.snapshot(arr);
            assertEquals(2, snap.length);
            assertEquals(0L, snap[0]);
            assertEquals(0L, snap[1]);
        }

        @Test
        void snapshot_fullArray() {
            var arr = new java.util.concurrent.atomic.AtomicLongArray(2);
            arr.set(0, -1L);
            arr.set(1, -1L);
            long[] snap = BitmapNetExecutor.snapshot(arr);
            assertEquals(-1L, snap[0]);
            assertEquals(-1L, snap[1]);
        }

        @Test
        void snapshot_isIndependentCopy() {
            var arr = new java.util.concurrent.atomic.AtomicLongArray(1);
            BitmapNetExecutor.casSetBit(arr, 5);
            long[] snap = BitmapNetExecutor.snapshot(arr);
            BitmapNetExecutor.casSetBit(arr, 10);
            assertEquals(1L << 5, snap[0]); // snapshot unchanged
        }

        @Test
        void multiWordOperations() {
            var arr = new java.util.concurrent.atomic.AtomicLongArray(3);
            BitmapNetExecutor.casSetBit(arr, 0);    // word 0, bit 0
            BitmapNetExecutor.casSetBit(arr, 63);   // word 0, bit 63
            BitmapNetExecutor.casSetBit(arr, 64);   // word 1, bit 0
            BitmapNetExecutor.casSetBit(arr, 191);  // word 2, bit 63

            long[] snap = BitmapNetExecutor.snapshot(arr);
            assertEquals(1L | Long.MIN_VALUE, snap[0]);
            assertEquals(1L, snap[1]);
            assertEquals(Long.MIN_VALUE, snap[2]);

            BitmapNetExecutor.casClearBit(arr, 0);
            BitmapNetExecutor.casClearBit(arr, 191);
            snap = BitmapNetExecutor.snapshot(arr);
            assertEquals(Long.MIN_VALUE, snap[0]); // bit 63 remains
            assertEquals(1L, snap[1]);
            assertEquals(0L, snap[2]);
        }
    }

    // ==================== Large Chain Smoke Test ====================

    @Nested
    class ScaleTests {

        @Test
        void linearChain50_completesCorrectly() {
            int size = 50;
            var places = new ArrayList<Place<SimpleValue>>();
            for (int i = 0; i <= size; i++) {
                places.add(Place.of("p" + i, SimpleValue.class));
            }

            var builder = PetriNet.builder("Scale50");
            for (int i = 0; i < size; i++) {
                var from = places.get(i);
                var to = places.get(i + 1);
                builder.transition(
                    Transition.builder("t" + (i + 1))
                        .inputs(In.one(from)).outputs(Out.place(to))
                        .action(ctx -> {
                            ctx.output(to, new SimpleValue("v"));
                            return CompletableFuture.completedFuture(null);
                        }).build()
                );
            }

            var net = builder.build();

            try (var executor = BitmapNetExecutor.create(net,
                    Map.of(places.getFirst(), List.of(Token.of(new SimpleValue("start")))))) {
                var result = executor.run();
                assertTrue(result.hasTokens(places.getLast()));
                assertFalse(result.hasTokens(places.getFirst()));
            }
        }
    }
}
