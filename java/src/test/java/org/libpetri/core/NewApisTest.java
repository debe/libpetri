package org.libpetri.core;

import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;
import org.libpetri.runtime.NetExecutor;

import java.time.Duration;
import java.util.List;
import java.util.Map;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for new CTPN APIs:
 * - Timing sealed interface
 * - Out.Timeout action timeout
 * - Out.ForwardInput retry pattern
 * - In cardinality (Exactly, All, AtLeast)
 */
@Timeout(60)
class NewApisTest {

    private final ExecutorService testExecutor = Executors.newVirtualThreadPerTaskExecutor();

    // ==================== TEST TOKEN TYPES ====================

    record SimpleValue(String data) {}
    record SearchQuery(String query) {}
    record SearchResult(String result) {}
    record BatchItem(int id) {}

    // ==================== SECTION 1: TIMING TESTS ====================

    @Nested
    class TimingTests {

        @Test
        void immediate_firesWithoutDelay() {
            var timing = Timing.immediate();

            assertEquals(Duration.ZERO, timing.earliest());
            assertFalse(timing.hasDeadline());
            assertEquals(Timing.MAX_DURATION, timing.latest());
        }

        @Test
        void deadline_firesImmediatelyWithUpperBound() {
            var timing = Timing.deadline(Duration.ofSeconds(5));

            assertEquals(Duration.ZERO, timing.earliest());
            assertTrue(timing.hasDeadline());
            assertEquals(Duration.ofSeconds(5), timing.latest());
        }

        @Test
        void delayed_waitsBeforeFiring() {
            var timing = Timing.delayed(Duration.ofMillis(100));

            assertEquals(Duration.ofMillis(100), timing.earliest());
            assertFalse(timing.hasDeadline());
            assertEquals(Timing.MAX_DURATION, timing.latest());
        }

        @Test
        void window_hasEarliestAndLatest() {
            var timing = Timing.window(Duration.ofMillis(50), Duration.ofMillis(200));

            assertEquals(Duration.ofMillis(50), timing.earliest());
            assertTrue(timing.hasDeadline());
            assertEquals(Duration.ofMillis(200), timing.latest());
        }

        @Test
        void exact_firesAtPreciseTime() {
            var timing = Timing.exact(Duration.ofMillis(100));

            assertEquals(Duration.ofMillis(100), timing.earliest());
            assertTrue(timing.hasDeadline());
            assertEquals(Duration.ofMillis(100), timing.latest());
        }

        @Test
        void unconstrained_sameAsImmediate() {
            var timing = Timing.unconstrained();

            assertEquals(Duration.ZERO, timing.earliest());
            assertFalse(timing.hasDeadline());
            assertEquals(Timing.MAX_DURATION, timing.latest());
        }

        @Test
        void toInterval_convertsCorrectly() {
            var timing = Timing.window(Duration.ofMillis(50), Duration.ofMillis(200));
            var interval = timing.toInterval();

            assertEquals(Duration.ofMillis(50), interval.earliest());
            assertEquals(Duration.ofMillis(200), interval.latest());
        }

        @Test
        void delayed_enforcesMinimumWait() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("delayed")
                .inputs(In.one(input))
                .outputs(Out.place(output))
                .timing(Timing.delayed(Duration.ofMillis(100)))
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("DelayedTest").transitions(t).build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("test")))
            );

            long start = System.currentTimeMillis();
            try (var executor = NetExecutor.create(net, initial)) {
                var result = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();
                long elapsed = System.currentTimeMillis() - start;

                assertTrue(result.hasTokens(output), "Output should have token");
                assertTrue(elapsed >= 90, "Should wait at least ~100ms, took " + elapsed + "ms");
            }
        }
    }

    // ==================== SECTION 2: OUT.TIMEOUT TESTS ====================

    @Nested
    class OutTimeoutTests {

        @Test
        void timeout_producesNormalOutput_whenActionFast() throws Exception {
            var input = Place.of("Input", SearchQuery.class);
            var success = Place.of("Success", SearchResult.class);
            var timeout = Place.of("Timeout", Void.class);

            var t = Transition.builder("Search")
                .inputs(In.one(input))
                .outputs(Out.xor(
                    Out.place(success),
                    Out.timeout(Duration.ofMillis(500), timeout)
                ))
                .timing(Timing.immediate())
                .action(ctx -> {
                    // Fast action - completes immediately
                    ctx.output(success, new SearchResult("found"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("TimeoutTest").transitions(t).build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SearchQuery("test")))
            );

            try (var executor = NetExecutor.create(net, initial)) {
                var result = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

                assertTrue(result.hasTokens(success), "Success should have token");
                assertFalse(result.hasTokens(timeout), "Timeout should not have triggered");
            }
        }

        @Test
        void timeout_producesTimeoutToken_whenActionSlow() throws Exception {
            var input = Place.of("Input", SearchQuery.class);
            var success = Place.of("Success", SearchResult.class);
            var timeoutPlace = Place.of("Timeout", Void.class);

            var t = Transition.builder("SlowSearch")
                .inputs(In.one(input))
                .outputs(Out.xor(
                    Out.place(success),
                    Out.timeout(Duration.ofMillis(50), timeoutPlace)
                ))
                .timing(Timing.immediate())
                .action(ctx -> {
                    // Slow action - takes longer than timeout
                    return CompletableFuture.runAsync(() -> {
                        try {
                            Thread.sleep(200);
                            ctx.output(success, new SearchResult("found"));
                        } catch (InterruptedException e) {
                            Thread.currentThread().interrupt();
                        }
                    }, testExecutor);
                })
                .build();

            var net = PetriNet.builder("SlowTimeoutTest").transitions(t).build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SearchQuery("test")))
            );

            var eventStore = EventStore.inMemory();
            try (var executor = NetExecutor.builder(net, initial)
                    .eventStore(eventStore)
                    .build()) {
                var result = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

                assertTrue(result.hasTokens(timeoutPlace), "Timeout should have triggered");
                assertFalse(result.hasTokens(success), "Success should not have token");

                // Verify ActionTimedOut event was emitted
                var timeoutEvents = eventStore.eventsOfType(NetEvent.ActionTimedOut.class);
                assertEquals(1, timeoutEvents.size(), "Should have one timeout event");
                assertEquals("SlowSearch", timeoutEvents.get(0).transitionName());
            }
        }
    }

    // ==================== SECTION 3: OUT.FORWARDINPUT TESTS ====================

    @Nested
    class ForwardInputTests {

        @Test
        void forwardInput_forwardsConsumedToken_onTimeout() throws Exception {
            var query = Place.of("Query", SearchQuery.class);
            var result = Place.of("Result", SearchResult.class);
            var retry = Place.of("Retry", SearchQuery.class);

            var t = Transition.builder("SearchWithRetry")
                .inputs(In.one(query))
                .outputs(Out.xor(
                    Out.place(result),
                    Out.timeout(Duration.ofMillis(50),
                        Out.forwardInput(query, retry))
                ))
                .timing(Timing.immediate())
                .action(ctx -> {
                    // Slow action - triggers timeout
                    return CompletableFuture.runAsync(() -> {
                        try {
                            Thread.sleep(200);
                            ctx.output(result, new SearchResult("found"));
                        } catch (InterruptedException e) {
                            Thread.currentThread().interrupt();
                        }
                    }, testExecutor);
                })
                .build();

            var net = PetriNet.builder("ForwardInputTest").transitions(t).build();
            var originalQuery = new SearchQuery("original query");
            var initial = Map.<Place<?>, List<Token<?>>>of(
                query, List.of(Token.of(originalQuery))
            );

            try (var executor = NetExecutor.create(net, initial)) {
                var marking = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

                assertTrue(marking.hasTokens(retry), "Retry should have forwarded token");
                assertFalse(marking.hasTokens(result), "Result should be empty");

                // Verify the forwarded token has the original value
                var forwardedToken = marking.peekFirst(retry);
                assertEquals(originalQuery, forwardedToken.value(),
                    "Forwarded token should have original query value");
            }
        }

        @Test
        void forwardInput_validation_rejectsNonInputPlace() {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);
            var other = Place.of("Other", SimpleValue.class);

            // ForwardInput references 'other' which is NOT an input place
            var ex = assertThrows(IllegalArgumentException.class, () -> {
                Transition.builder("Invalid")
                    .inputs(In.one(input))
                    .outputs(Out.xor(
                        Out.place(output),
                        Out.timeout(Duration.ofMillis(100),
                            Out.forwardInput(other, output))  // 'other' is not an input
                    ))
                    .build();
            });

            assertTrue(ex.getMessage().contains("ForwardInput"),
                "Error should mention ForwardInput");
            assertTrue(ex.getMessage().contains("Other"),
                "Error should mention the invalid place name");
        }
    }

    // ==================== SECTION 4: IN CARDINALITY TESTS ====================

    @Nested
    class InCardinalityTests {

        @Test
        void inOne_consumesExactlyOneToken() throws Exception {
            var input = Place.of("Input", BatchItem.class);
            var output = Place.of("Output", BatchItem.class);

            var t = Transition.builder("OneAtATime")
                .inputs(In.one(input))
                .outputs(Out.place(output))
                .timing(Timing.immediate())
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("InOneTest").transitions(t).build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(
                    Token.of(new BatchItem(1)),
                    Token.of(new BatchItem(2)),
                    Token.of(new BatchItem(3))
                )
            );

            try (var executor = NetExecutor.create(net, initial)) {
                var result = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

                // All 3 should be processed one at a time
                assertEquals(3, result.peekTokens(output).size(),
                    "All 3 items should be in output");
                assertEquals(0, result.peekTokens(input).size(),
                    "Input should be empty");
            }
        }

        @Test
        void inExactly_consumesExactlyNTokens() throws Exception {
            var input = Place.of("Input", BatchItem.class);
            var output = Place.of("Output", BatchItem.class);
            var processed = new AtomicInteger(0);

            var t = Transition.builder("BatchOf3")
                .inputs(In.exactly(3, input))
                .outputs(Out.place(output))
                .timing(Timing.immediate())
                .action(ctx -> {
                    // Should receive exactly 3 tokens
                    var items = ctx.inputs(input);
                    processed.set(items.size());
                    for (var item : items) {
                        ctx.output(output, item);
                    }
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("InExactlyTest").transitions(t).build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(
                    Token.of(new BatchItem(1)),
                    Token.of(new BatchItem(2)),
                    Token.of(new BatchItem(3)),
                    Token.of(new BatchItem(4)),
                    Token.of(new BatchItem(5))
                )
            );

            try (var executor = NetExecutor.create(net, initial)) {
                var result = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

                assertEquals(3, processed.get(), "Should process exactly 3 tokens per firing");
                // Transition fires once (3 tokens), leaving 2 in input
                assertEquals(2, result.peekTokens(input).size(),
                    "2 tokens should remain in input (not enough for another batch)");
            }
        }

        @Test
        void inAll_consumesAllAvailableTokens() throws Exception {
            var input = Place.of("Input", BatchItem.class);
            var output = Place.of("Output", BatchItem.class);
            var consumed = new AtomicInteger(0);

            var t = Transition.builder("DrainAll")
                .inputs(In.all(input))
                .outputs(Out.place(output))
                .timing(Timing.immediate())
                .action(ctx -> {
                    var items = ctx.inputs(input);
                    consumed.set(items.size());
                    for (var item : items) {
                        ctx.output(output, item);
                    }
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("InAllTest").transitions(t).build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(
                    Token.of(new BatchItem(1)),
                    Token.of(new BatchItem(2)),
                    Token.of(new BatchItem(3)),
                    Token.of(new BatchItem(4)),
                    Token.of(new BatchItem(5))
                )
            );

            try (var executor = NetExecutor.create(net, initial)) {
                var result = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

                assertEquals(5, consumed.get(), "Should consume all 5 tokens at once");
                assertEquals(5, result.peekTokens(output).size(),
                    "All 5 should be in output");
                assertEquals(0, result.peekTokens(input).size(),
                    "Input should be empty");
            }
        }

        @Test
        void inAtLeast_waitsForMinimumThenConsumesAll() throws Exception {
            var input = Place.of("Input", BatchItem.class);
            var output = Place.of("Output", BatchItem.class);
            var consumed = new AtomicInteger(0);

            var t = Transition.builder("AtLeast3")
                .inputs(In.atLeast(3, input))
                .outputs(Out.place(output))
                .timing(Timing.immediate())
                .action(ctx -> {
                    var items = ctx.inputs(input);
                    consumed.set(items.size());
                    for (var item : items) {
                        ctx.output(output, item);
                    }
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("InAtLeastTest").transitions(t).build();

            // Test 1: Only 2 tokens - should not fire
            var initial2 = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(
                    Token.of(new BatchItem(1)),
                    Token.of(new BatchItem(2))
                )
            );

            try (var executor = NetExecutor.create(net, initial2)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertEquals(0, consumed.get(), "Should not fire with only 2 tokens");
                assertEquals(2, result.peekTokens(input).size(),
                    "Tokens should remain in input");
            }

            // Test 2: 5 tokens - should fire and consume all
            consumed.set(0);
            var initial5 = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(
                    Token.of(new BatchItem(1)),
                    Token.of(new BatchItem(2)),
                    Token.of(new BatchItem(3)),
                    Token.of(new BatchItem(4)),
                    Token.of(new BatchItem(5))
                )
            );

            try (var executor = NetExecutor.create(net, initial5)) {
                var result = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

                assertEquals(5, consumed.get(), "Should consume all 5 tokens");
                assertEquals(5, result.peekTokens(output).size(),
                    "All 5 should be in output");
            }
        }
    }
}
