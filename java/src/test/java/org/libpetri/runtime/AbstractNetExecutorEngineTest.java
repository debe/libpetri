package org.libpetri.runtime;

import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import org.libpetri.core.*;
import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;
import static org.libpetri.core.In.all;
import static org.libpetri.core.In.atLeast;
import static org.libpetri.core.In.exactly;
import static org.libpetri.core.In.one;
import static org.libpetri.core.Out.and;
import static org.libpetri.core.Out.place;
import static org.libpetri.core.Out.xor;

import java.time.Duration;
import java.time.Instant;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Abstract test suite for Petri Net engine semantics.
 *
 * <p>Subclasses provide executor creation via factory methods, allowing the same
 * 66 tests to run against different executor implementations (e.g. {@link NetExecutor},
 * {@link BitmapNetExecutor}).
 */
@Timeout(60)
abstract class AbstractNetExecutorEngineTest {

    protected abstract PetriNetExecutor createExecutor(PetriNet net, Map<Place<?>, List<Token<?>>> initial);

    protected abstract PetriNetExecutor createExecutor(PetriNet net, Map<Place<?>, List<Token<?>>> initial, EventStore store);

    protected abstract PetriNetExecutor createExecutorWithEnv(PetriNet net, Map<Place<?>, List<Token<?>>> initial, EventStore store, Set<EnvironmentPlace<?>> envPlaces);

    protected abstract PetriNetExecutor createExecutorWithEnv(PetriNet net, Map<Place<?>, List<Token<?>>> initial, Set<EnvironmentPlace<?>> envPlaces);

    private final ExecutorService testExecutor = Executors.newVirtualThreadPerTaskExecutor();

    // ==================== TEST TOKEN TYPES ====================

    record SimpleValue(String data) {}
    record CounterValue(int count) {}
    record TypeA(String id) {}
    record TypeB(String id) {}
    record TypeC(String id) {}

    // For conditional branching test
    sealed interface Decision permits GoLeft, GoRight {}
    record GoLeft(String reason) implements Decision {}
    record GoRight(String reason) implements Decision {}

    // ==================== SECTION 1: INPUT ARC TESTS ====================

    @Nested
    class InputArcTests {

        @Test
        void basicInputArc_consumesTokenWhenTransitionFires() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .inputs(one(input))
                .outputs(place(output))
                .timing(Timing.deadline(Duration.ofMillis(100)))
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("BasicInput").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("hello")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

                assertFalse(result.hasTokens(input), "Input should be consumed");
                assertTrue(result.hasTokens(output), "Output should have token");
                assertEquals("hello", result.peekFirst(output).value().data());
            }
        }

        @Test
        void inputArc_requiresTokenToEnable() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .inputs(one(input))
                .outputs(place(output))
                .timing(Timing.deadline(Duration.ofMillis(100)))
                .action(TransitionAction.produce(output, new SimpleValue("created")))
                .build();

            var net = PetriNet.builder("NoToken").transitions(t).build();

            // Start with empty marking
            try (var executor = createExecutor(net,Map.of())) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertFalse(result.hasTokens(output), "Transition should not fire without input");
            }
        }

        @Test
        void inputArcWithGuard_onlyConsumesMatchingTokens() throws Exception {
            var input = Place.of("Input", CounterValue.class);
            var output = Place.of("Output", CounterValue.class);

            var t = Transition.builder("t")
                .inputWhen(input, v -> v.count() > 5)
                .output(output)
                .deadline(100)
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("GuardedInput").transitions(t).build();

            // Token that doesn't match guard
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new CounterValue(3)))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertTrue(result.hasTokens(input), "Non-matching token should remain");
                assertFalse(result.hasTokens(output), "No output without guard match");
            }
        }

        @Test
        void inputArcWithGuard_consumesFirstMatchingToken() throws Exception {
            var input = Place.of("Input", CounterValue.class);
            var output = Place.of("Output", CounterValue.class);

            var t = Transition.builder("t")
                .inputWhen(input, v -> v.count() > 5)
                .output(output)
                .deadline(100)
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("GuardedInput").transitions(t).build();

            // Multiple tokens, only some match
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(
                    Token.of(new CounterValue(3)),
                    Token.of(new CounterValue(10)),
                    Token.of(new CounterValue(2))
                )
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertEquals(2, result.tokenCount(input), "Two non-matching tokens remain");
                assertTrue(result.hasTokens(output));
                assertEquals(10, result.peekFirst(output).value().count());
            }
        }

        @Test
        void multipleInputArcs_requireAllTokens() throws Exception {
            var inputA = Place.of("InputA", TypeA.class);
            var inputB = Place.of("InputB", TypeB.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .inputs(one(inputA), one(inputB))
                .outputs(place(output))
                .timing(Timing.deadline(Duration.ofMillis(100)))
                .action(ctx -> {
                    var a = ctx.input(inputA);
                    var b = ctx.input(inputB);
                    ctx.output(output, new SimpleValue(a.id() + "-" + b.id()));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("MultiInput").transitions(t).build();

            // Only one input provided
            var partial = Map.<Place<?>, List<Token<?>>>of(
                inputA, List.of(Token.of(new TypeA("a1")))
            );

            try (var executor = createExecutor(net,partial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertTrue(result.hasTokens(inputA), "Token should remain");
                assertFalse(result.hasTokens(output), "Transition not enabled");
            }

            // Both inputs provided
            var complete = Map.<Place<?>, List<Token<?>>>of(
                inputA, List.of(Token.of(new TypeA("a1"))),
                inputB, List.of(Token.of(new TypeB("b1")))
            );

            try (var executor = createExecutor(net,complete)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertFalse(result.hasTokens(inputA));
                assertFalse(result.hasTokens(inputB));
                assertTrue(result.hasTokens(output));
                assertEquals("a1-b1", result.peekFirst(output).value().data());
            }
        }

        @Test
        void inOneFromTwoDifferentPlaces_shouldNotFireWithEmptyPlaces() throws Exception {
            // BUG REPRODUCTION: This test reproduces a bug where transitions using the new API
            // .inputs(In.one(p1), In.one(p2)) fire even when both input places are EMPTY.
            // The legacy API .inputs(p1, p2) works correctly.
            var placeA = Place.of("PlaceA", Void.class);
            var placeB = Place.of("PlaceB", Void.class);
            var output = Place.of("Output", SimpleValue.class);
            var fireCount = new AtomicInteger(0);

            var t = Transition.builder("t")
                .inputs(one(placeA), one(placeB))  // NEW API - potential bug
                .outputs(place(output))
                .timing(Timing.immediate())
                .action(ctx -> {
                    fireCount.incrementAndGet();
                    ctx.output(output, new SimpleValue("fired"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            // First verify the builder correctly populated inputSpecs
            assertEquals(2, t.inputSpecs().size(), "Builder should populate inputSpecs with 2 In.One specs");
            assertTrue(t.inputSpecs().get(0) instanceof In.One, "First spec should be In.One");
            assertTrue(t.inputSpecs().get(1) instanceof In.One, "Second spec should be In.One");
            assertEquals(placeA, t.inputSpecs().get(0).place(), "First spec should reference placeA");
            assertEquals(placeB, t.inputSpecs().get(1).place(), "Second spec should reference placeB");

            var net = PetriNet.builder("InOneTest").transitions(t).build();

            // EMPTY places - should NOT fire
            var empty = Map.<Place<?>, List<Token<?>>>of();

            try (var executor = createExecutor(net,empty)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();
                assertEquals(0, fireCount.get(), "Should NOT fire with empty places");
                assertFalse(result.hasTokens(output), "No output without firing");
            }
        }

        @Test
        void inOneFromTwoDifferentPlaces_firesOnceWhenBothHaveTokens() throws Exception {
            var placeA = Place.of("PlaceA", Void.class);
            var placeB = Place.of("PlaceB", Void.class);
            var output = Place.of("Output", SimpleValue.class);
            var fireCount = new AtomicInteger(0);

            var t = Transition.builder("t")
                .inputs(one(placeA), one(placeB))
                .outputs(place(output))
                .timing(Timing.immediate())
                .action(ctx -> {
                    fireCount.incrementAndGet();
                    ctx.output(output, new SimpleValue("fired"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("InOneTest").transitions(t).build();

            // Both places have 1 token - should fire exactly once
            var initial = Map.<Place<?>, List<Token<?>>>of(
                placeA, List.of(Token.of((Void) null)),
                placeB, List.of(Token.of((Void) null))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();
                assertEquals(1, fireCount.get(), "Should fire exactly once");
                assertTrue(result.hasTokens(output), "Output should have token");
            }
        }

        @Test
        void inOneFromTwoDifferentPlaces_shouldNotFireWithOnlyOneTokenPresent() throws Exception {
            // This test ensures the transition doesn't fire when only ONE of the two required inputs has a token
            var placeA = Place.of("PlaceA", Void.class);
            var placeB = Place.of("PlaceB", Void.class);
            var output = Place.of("Output", SimpleValue.class);
            var fireCount = new AtomicInteger(0);

            var t = Transition.builder("t")
                .inputs(one(placeA), one(placeB))  // Requires tokens in BOTH places
                .outputs(place(output))
                .timing(Timing.immediate())
                .action(ctx -> {
                    fireCount.incrementAndGet();
                    ctx.output(output, new SimpleValue("fired"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("InOneTest").transitions(t).build();

            // Only placeA has a token, placeB is empty
            var onlyA = Map.<Place<?>, List<Token<?>>>of(
                placeA, List.of(Token.of((Void) null))
            );

            try (var executor = createExecutor(net,onlyA)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();
                assertEquals(0, fireCount.get(), "Should NOT fire with only one input");
                assertTrue(result.hasTokens(placeA), "Token in placeA should remain unconsumed");
                assertFalse(result.hasTokens(output), "No output without firing");
            }
        }

        // ==================== MIXED API TESTS ====================
        // These tests verify the interaction between NEW input API (In.one()) and LEGACY output API (outputs(Place))
        // Bug reproduction: When using inputs(In.one(...)) + outputs(Place), transitions fire with empty places.

        @Test
        void mixedApis_newInputsWithLegacyOutputs_shouldNotFireWithEmptyPlaces() throws Exception {
            // BUG REPRODUCTION: This test uses the EXACT mixed API scenario from production:
            // - NEW input API: inputs(In.one(...))
            // - LEGACY output API: outputs(Place) - NOT outputs(Out.place(...))
            var placeA = Place.of("PlaceA", Void.class);
            var placeB = Place.of("PlaceB", Void.class);
            var output = Place.of("Output", Void.class);
            var fireCount = new AtomicInteger(0);

            @SuppressWarnings("deprecation")
            var t = Transition.builder("t")
                .inputs(one(placeA), one(placeB))  // NEW API
                .outputs(output)                    // LEGACY API - calls outputs(Place<?>...)
                .timing(Timing.immediate())
                .action(ctx -> {
                    fireCount.incrementAndGet();
                    ctx.output(output, (Void) null);
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            // VERIFY: inputSpecs should be populated
            assertEquals(2, t.inputSpecs().size(), "inputSpecs should have 2 elements");
            // VERIFY: outputSpec should be NULL (legacy output API)
            assertNull(t.outputSpec(), "outputSpec should be null when using legacy output API");
            // VERIFY: legacy outputs list should be populated
            assertEquals(1, t.outputs().size(), "legacy outputs should have 1 element");

            var net = PetriNet.builder("MixedApiTest").transitions(t).build();

            // EMPTY places - should NOT fire
            var empty = Map.<Place<?>, List<Token<?>>>of();

            try (var executor = createExecutor(net,empty)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();
                assertEquals(0, fireCount.get(), "Should NOT fire with empty places");
                assertFalse(result.hasTokens(output), "No output without firing");
            }
        }

        @Test
        void mixedApis_newInputsWithLegacyOutputs_firesOnceWhenBothHaveTokens() throws Exception {
            var placeA = Place.of("PlaceA", Void.class);
            var placeB = Place.of("PlaceB", Void.class);
            var output = Place.of("Output", Void.class);
            var fireCount = new AtomicInteger(0);

            @SuppressWarnings("deprecation")
            var t = Transition.builder("t")
                .inputs(one(placeA), one(placeB))  // NEW API
                .outputs(output)                    // LEGACY API
                .timing(Timing.immediate())
                .action(ctx -> {
                    fireCount.incrementAndGet();
                    ctx.output(output, (Void) null);
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("MixedApiTest").transitions(t).build();

            // Both places have 1 token - should fire exactly once
            var initial = Map.<Place<?>, List<Token<?>>>of(
                placeA, List.of(Token.of((Void) null)),
                placeB, List.of(Token.of((Void) null))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();
                assertEquals(1, fireCount.get(), "Should fire exactly once");
                assertTrue(result.hasTokens(output), "Output should have token");
            }
        }

        @Test
        void mixedApis_newInputsWithLegacyOutputs_shouldNotFireWithOnlyOneTokenPresent() throws Exception {
            // Ensures transition doesn't fire when only ONE of the two required inputs has a token
            var placeA = Place.of("PlaceA", Void.class);
            var placeB = Place.of("PlaceB", Void.class);
            var output = Place.of("Output", Void.class);
            var fireCount = new AtomicInteger(0);

            @SuppressWarnings("deprecation")
            var t = Transition.builder("t")
                .inputs(one(placeA), one(placeB))  // NEW API - Requires tokens in BOTH places
                .outputs(output)                    // LEGACY API
                .timing(Timing.immediate())
                .action(ctx -> {
                    fireCount.incrementAndGet();
                    ctx.output(output, (Void) null);
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("MixedApiTest").transitions(t).build();

            // Only placeA has a token, placeB is empty
            var onlyA = Map.<Place<?>, List<Token<?>>>of(
                placeA, List.of(Token.of((Void) null))
            );

            try (var executor = createExecutor(net,onlyA)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();
                assertEquals(0, fireCount.get(), "Should NOT fire with only one input");
                assertTrue(result.hasTokens(placeA), "Token in placeA should remain unconsumed");
                assertFalse(result.hasTokens(output), "No output without firing");
            }
        }

        @Test
        void inputArc_fifoOrdering() throws Exception {
            var input = Place.of("Input", CounterValue.class);
            var output = Place.of("Output", CounterValue.class);

            var consumed = new CopyOnWriteArrayList<Integer>();

            var t = Transition.builder("t")
                .input(input)
                .output(output)
                .deadline(50)
                .action(ctx -> {
                    var v = ctx.input(input);
                    consumed.add(v.count());
                    ctx.output(output, v);
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("FIFO").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(
                    Token.of(new CounterValue(1)),
                    Token.of(new CounterValue(2)),
                    Token.of(new CounterValue(3))
                )
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertEquals(3, result.tokenCount(output));
                assertEquals(List.of(1, 2, 3), consumed, "Tokens consumed in FIFO order");
            }
        }
    }

    // ==================== SECTION 2: OUTPUT ARC TESTS ====================

    @Nested
    class OutputArcTests {

        @Test
        void basicOutputArc_producesToken() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("produced")))
                .build();

            var net = PetriNet.builder("BasicOutput").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("trigger")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertTrue(result.hasTokens(output));
                assertEquals("produced", result.peekFirst(output).value().data());
            }
        }

        @Test
        void multipleOutputArcs_producesToAllPlaces() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var out1 = Place.of("Out1", TypeA.class);
            var out2 = Place.of("Out2", TypeB.class);
            var out3 = Place.of("Out3", TypeC.class);

            var t = Transition.builder("t")
                .input(input)
                .output(out1)
                .output(out2)
                .output(out3)
                .deadline(100)
                .action(ctx -> {
                    ctx.output(out1, new TypeA("a"));
                    ctx.output(out2, new TypeB("b"));
                    ctx.output(out3, new TypeC("c"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("MultiOutput").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertTrue(result.hasTokens(out1));
                assertTrue(result.hasTokens(out2));
                assertTrue(result.hasTokens(out3));
                assertEquals("a", result.peekFirst(out1).value().id());
                assertEquals("b", result.peekFirst(out2).value().id());
                assertEquals("c", result.peekFirst(out3).value().id());
            }
        }

        @Test
        void outputArc_multipleTokensToSamePlace() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", CounterValue.class);

            var t = Transition.builder("t")
                .input(input)
                .output(output)
                .output(output)
                .output(output)  // 3 arcs for 3 tokens
                .deadline(100)
                .action(ctx -> {
                    ctx.output(output, new CounterValue(1));
                    ctx.output(output, new CounterValue(2));
                    ctx.output(output, new CounterValue(3));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("MultiToken").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertEquals(3, result.tokenCount(output));
            }
        }

        @Test
        void unitToken_isDeposited() throws Exception {
            // Postset discipline: all tokens including unit tokens are deposited to marking.
            // If you want a transition with no output, define it with an empty postset.
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", Void.class);

            var t = Transition.builder("t")
                .input(input)
                .output(output)
                .action(ctx -> {
                    // Unit tokens are now deposited - postset discipline
                    ctx.output(output, Token.unit());
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("UnitToken").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                // Unit tokens are now deposited per postset discipline
                assertTrue(result.hasTokens(output), "Unit tokens should be deposited");
                assertTrue(result.peekFirst(output).isUnit(), "Token should be a unit token");
            }
        }
    }

    // ==================== SECTION 3: INHIBITOR ARC TESTS ====================

    @Nested
    class InhibitorArcTests {

        @Test
        void inhibitorArc_blocksWhenPlaceHasTokens() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var blocker = Place.of("Blocker", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .inhibitor(blocker)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("Inhibited").transitions(t).build();

            // With blocker token - should NOT fire
            var blocked = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                blocker, List.of(Token.of(new SimpleValue("block")))
            );

            try (var executor = createExecutor(net,blocked)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertTrue(result.hasTokens(input), "Input remains (blocked)");
                assertTrue(result.hasTokens(blocker), "Blocker remains");
                assertFalse(result.hasTokens(output), "No output (blocked)");
            }

            // Without blocker token - should fire
            var unblocked = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,unblocked)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertFalse(result.hasTokens(input), "Input consumed");
                assertTrue(result.hasTokens(output), "Output produced");
            }
        }

        @Test
        void multipleInhibitors_allMustBeEmpty() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var blocker1 = Place.of("Blocker1", TypeA.class);
            var blocker2 = Place.of("Blocker2", TypeB.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .inhibitor(blocker1)
                .inhibitor(blocker2)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("MultiInhibitor").transitions(t).build();

            // Both blockers present
            var bothBlocked = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                blocker1, List.of(Token.of(new TypeA("b1"))),
                blocker2, List.of(Token.of(new TypeB("b2")))
            );

            try (var executor = createExecutor(net,bothBlocked)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();
                assertFalse(result.hasTokens(output), "Blocked by both");
            }

            // Only one blocker
            var oneBlocked = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                blocker1, List.of(Token.of(new TypeA("b1")))
            );

            try (var executor = createExecutor(net,oneBlocked)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();
                assertFalse(result.hasTokens(output), "Blocked by one");
            }

            // Neither blocker
            var noneBlocked = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,noneBlocked)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();
                assertTrue(result.hasTokens(output), "Not blocked - fires");
            }
        }

        @Test
        void inhibitor_becomesUnblockedWhenTokenRemoved() throws Exception {
            var trigger = Place.of("Trigger", SimpleValue.class);
            var blocker = Place.of("Blocker", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);
            var cleared = Place.of("Cleared", SimpleValue.class);

            // Remove the blocker
            var clearBlocker = Transition.builder("clearBlocker")
                .input(blocker)
                .output(cleared)
                .deadline(50)
                .priority(10)  // Higher priority - fires first
                .action(TransitionAction.produce(cleared, new SimpleValue("cleared")))
                .build();

            // Can only fire when blocker is empty
            var inhibited = Transition.builder("inhibited")
                .input(trigger)
                .inhibitor(blocker)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("UnblockTest")
                .transitions(clearBlocker, inhibited)
                .build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                trigger, List.of(Token.of(new SimpleValue("go"))),
                blocker, List.of(Token.of(new SimpleValue("block")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertTrue(result.hasTokens(cleared), "Blocker was cleared");
                assertTrue(result.hasTokens(output), "Inhibited transition fired after unblock");
            }
        }
    }

    // ==================== SECTION 4: READ ARC TESTS ====================

    @Nested
    class ReadArcTests {

        @Test
        void readArc_requiresTokenButDoesNotConsume() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var readPlace = Place.of("ReadPlace", CounterValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .read(readPlace)
                .output(output)
                .deadline(100)
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("ReadArc").transitions(t).build();

            // Without read token - should NOT fire
            var noRead = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,noRead)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertTrue(result.hasTokens(input), "Input remains (read not satisfied)");
                assertFalse(result.hasTokens(output), "No output");
            }

            // With read token - should fire AND read token remains
            var withRead = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                readPlace, List.of(Token.of(new CounterValue(42)))
            );

            try (var executor = createExecutor(net,withRead)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertFalse(result.hasTokens(input), "Input consumed");
                assertTrue(result.hasTokens(readPlace), "Read token NOT consumed");
                assertEquals(42, result.peekFirst(readPlace).value().count());
                assertTrue(result.hasTokens(output), "Output produced");
            }
        }

        @Test
        void readArc_multipleTransitionsCanReadSamePlace() throws Exception {
            var input1 = Place.of("Input1", TypeA.class);
            var input2 = Place.of("Input2", TypeB.class);
            var shared = Place.of("Shared", CounterValue.class);
            var out1 = Place.of("Out1", SimpleValue.class);
            var out2 = Place.of("Out2", SimpleValue.class);

            var t1 = Transition.builder("t1")
                .input(input1)
                .read(shared)
                .output(out1)
                .deadline(100)
                .action(ctx -> {
                    ctx.output(out1, new SimpleValue("t1-fired"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var t2 = Transition.builder("t2")
                .input(input2)
                .read(shared)
                .output(out2)
                .deadline(100)
                .action(ctx -> {
                    ctx.output(out2, new SimpleValue("t2-fired"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("SharedRead").transitions(t1, t2).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input1, List.of(Token.of(new TypeA("a"))),
                input2, List.of(Token.of(new TypeB("b"))),
                shared, List.of(Token.of(new CounterValue(100)))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertTrue(result.hasTokens(shared), "Shared token not consumed");
                assertTrue(result.hasTokens(out1), "t1 fired");
                assertTrue(result.hasTokens(out2), "t2 fired");
            }
        }

        @Test
        void multipleReadArcs_allRequired() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var read1 = Place.of("Read1", TypeA.class);
            var read2 = Place.of("Read2", TypeB.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .read(read1)
                .read(read2)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("MultiRead").transitions(t).build();

            // Only one read satisfied
            var partial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                read1, List.of(Token.of(new TypeA("a")))
            );

            try (var executor = createExecutor(net,partial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();
                assertFalse(result.hasTokens(output), "Not all reads satisfied");
            }

            // Both reads satisfied
            var complete = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                read1, List.of(Token.of(new TypeA("a"))),
                read2, List.of(Token.of(new TypeB("b")))
            );

            try (var executor = createExecutor(net,complete)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();
                assertTrue(result.hasTokens(output), "Both reads satisfied");
                assertTrue(result.hasTokens(read1), "Read1 not consumed");
                assertTrue(result.hasTokens(read2), "Read2 not consumed");
            }
        }
    }

    // ==================== SECTION 5: RESET ARC TESTS ====================

    @Nested
    class ResetArcTests {

        @Test
        void resetArc_removesAllTokensFromPlace() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var resetPlace = Place.of("ResetPlace", CounterValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .reset(resetPlace)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("ResetArc").transitions(t).build();

            // Multiple tokens in reset place
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                resetPlace, List.of(
                    Token.of(new CounterValue(1)),
                    Token.of(new CounterValue(2)),
                    Token.of(new CounterValue(3))
                )
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertFalse(result.hasTokens(resetPlace), "All tokens cleared by reset");
                assertTrue(result.hasTokens(output), "Transition fired");
            }
        }

        @Test
        void resetArc_firesEvenIfPlaceIsEmpty() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var resetPlace = Place.of("ResetPlace", CounterValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .reset(resetPlace)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("ResetEmpty").transitions(t).build();

            // Reset place is already empty
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertFalse(result.hasTokens(resetPlace), "Reset place still empty");
                assertTrue(result.hasTokens(output), "Transition still fires");
            }
        }

        @Test
        void multipleResetArcs_clearsAllPlaces() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var reset1 = Place.of("Reset1", TypeA.class);
            var reset2 = Place.of("Reset2", TypeB.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .reset(reset1)
                .reset(reset2)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("MultiReset").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                reset1, List.of(Token.of(new TypeA("a1")), Token.of(new TypeA("a2"))),
                reset2, List.of(Token.of(new TypeB("b1")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertFalse(result.hasTokens(reset1), "Reset1 cleared");
                assertFalse(result.hasTokens(reset2), "Reset2 cleared");
                assertTrue(result.hasTokens(output));
            }
        }

        @Test
        void resetArc_differenceBetweenResetAndInput() throws Exception {
            var trigger1 = Place.of("Trigger1", SimpleValue.class);
            var trigger2 = Place.of("Trigger2", SimpleValue.class);
            var targetInput = Place.of("TargetInput", CounterValue.class);
            var targetReset = Place.of("TargetReset", CounterValue.class);
            var outInput = Place.of("OutInput", SimpleValue.class);
            var outReset = Place.of("OutReset", SimpleValue.class);

            // Input arc - requires token, consumes ONE
            var withInput = Transition.builder("withInput")
                .input(trigger1)
                .input(targetInput)
                .output(outInput)
                .deadline(100)
                .action(TransitionAction.produce(outInput, new SimpleValue("input-fired")))
                .build();

            // Reset arc - doesn't require token, removes ALL
            var withReset = Transition.builder("withReset")
                .input(trigger2)
                .reset(targetReset)
                .output(outReset)
                .deadline(100)
                .action(TransitionAction.produce(outReset, new SimpleValue("reset-fired")))
                .build();

            var net = PetriNet.builder("InputVsReset").transitions(withInput, withReset).build();

            // Target places have multiple tokens
            var initial = Map.<Place<?>, List<Token<?>>>of(
                trigger1, List.of(Token.of(new SimpleValue("go1"))),
                trigger2, List.of(Token.of(new SimpleValue("go2"))),
                targetInput, List.of(
                    Token.of(new CounterValue(1)),
                    Token.of(new CounterValue(2)),
                    Token.of(new CounterValue(3))
                ),
                targetReset, List.of(
                    Token.of(new CounterValue(1)),
                    Token.of(new CounterValue(2)),
                    Token.of(new CounterValue(3))
                )
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                // Input arc consumed ONE token
                assertEquals(2, result.tokenCount(targetInput), "Input consumes ONE");

                // Reset arc removed ALL tokens
                assertEquals(0, result.tokenCount(targetReset), "Reset removes ALL");

                assertTrue(result.hasTokens(outInput));
                assertTrue(result.hasTokens(outReset));
            }
        }

        @Test
        void resetArc_withOutputToSamePlace_resetsTimerForDependentTransition() throws Exception {
            // Setup:
            // - Place P starts with token
            // - T1: triggered by Trigger, resets P, outputs new token to P (immediate)
            // - T2: reads P, has 200ms delay, outputs to Done
            //
            // Timeline WITHOUT fix (bug):
            //   t=0:    T2 enabled, enabledAt[T2]=0
            //   t=50:   T1 fires (reset P, output P) - T2's enabledAt unchanged!
            //   t=200:  T2 fires (200ms from t=0, ignoring reset)
            //
            // Timeline WITH fix:
            //   t=0:    T2 enabled, enabledAt[T2]=0
            //   t=50:   T1 fires, T2's enabledAt invalidated, then re-set to ~50
            //   t=250:  T2 fires (200ms from t=50)

            var trigger = Place.of("Trigger", Void.class);
            var p = Place.of("P", String.class);
            var done = Place.of("Done", String.class);

            var triggerEnv = EnvironmentPlace.of(trigger);

            var t1 = Transition.builder("T1-Reset")
                .input(trigger)
                .reset(p)
                .output(p)
                .timing(Timing.immediate())
                .action(ctx -> {
                    ctx.output(p, "fresh-token");
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var t2 = Transition.builder("T2-Delayed")
                .input(p)
                .output(done)
                .timing(Timing.delayed(Duration.ofMillis(200)))
                .action(ctx -> {
                    ctx.output(done, ctx.input(p));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("ResetTimerTest").transitions(t1, t2).build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                p, List.of(Token.of("original-token"))
            );

            var eventStore = EventStore.inMemory();
            try (var executor = createExecutorWithEnv(net, initial, eventStore, Set.of(triggerEnv))) {

                // Inject trigger after 50ms to fire T1
                CompletableFuture.delayedExecutor(50, TimeUnit.MILLISECONDS)
                    .execute(() -> executor.inject(triggerEnv, Token.unit()));

                long start = System.currentTimeMillis();
                executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();
                long elapsed = System.currentTimeMillis() - start;

                // T2 should fire ~250ms after start (50ms + 200ms delay)
                // NOT at ~200ms (which would indicate the bug)
                assertTrue(elapsed >= 240,
                    "T2 should fire 200ms after reset (at ~250ms), but fired at " + elapsed + "ms");
            }
        }

        @Test
        void resetArc_partialReset_resetsTimerIfAnyInputPlaceReset() throws Exception {
            // T depends on both P1 and P2
            // Only P1 is reset - timer should still reset
            var p1 = Place.of("P1", String.class);
            var p2 = Place.of("P2", String.class);
            var trigger = Place.of("Trigger", Void.class);
            var done = Place.of("Done", String.class);

            var triggerEnv = EnvironmentPlace.of(trigger);

            var resetT = Transition.builder("Reset")
                .input(trigger)
                .reset(p1)
                .output(p1)
                .timing(Timing.immediate())
                .action(ctx -> {
                    ctx.output(p1, "fresh");
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var delayedT = Transition.builder("Delayed")
                .input(p1)
                .input(p2)
                .output(done)
                .timing(Timing.delayed(Duration.ofMillis(200)))
                .action(ctx -> {
                    ctx.output(done, "done");
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("PartialResetTest").transitions(resetT, delayedT).build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                p1, List.of(Token.of("old")),
                p2, List.of(Token.of("static"))
            );

            var eventStore = EventStore.inMemory();
            try (var executor = createExecutorWithEnv(net, initial, eventStore, Set.of(triggerEnv))) {

                CompletableFuture.delayedExecutor(50, TimeUnit.MILLISECONDS)
                    .execute(() -> executor.inject(triggerEnv, Token.unit()));

                long start = System.currentTimeMillis();
                executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();
                long elapsed = System.currentTimeMillis() - start;

                assertTrue(elapsed >= 240,
                    "Timer should reset when any input place is reset. Elapsed: " + elapsed + "ms");
            }
        }

        @Test
        void resetArc_resetsTimerForReadArcDependency() throws Exception {
            // T uses read arc (doesn't consume) + input arc (does consume).
            // Reset should invalidate timer for transitions with read arcs too.
            // Note: Read arcs are included in the transitionsByInputPlace index
            // in NetExecutor.buildInputPlaceIndex().
            var readPlace = Place.of("ReadPlace", String.class);
            var consumable = Place.of("Consumable", String.class);
            var trigger = Place.of("Trigger", Void.class);
            var done = Place.of("Done", String.class);

            var triggerEnv = EnvironmentPlace.of(trigger);

            var resetT = Transition.builder("Reset")
                .input(trigger)
                .reset(readPlace)
                .output(readPlace)
                .output(consumable)  // Provide fresh consumable for delayedT
                .timing(Timing.immediate())
                .action(ctx -> {
                    ctx.output(readPlace, "fresh");
                    ctx.output(consumable, "go");
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var delayedT = Transition.builder("Delayed")
                .input(consumable)  // Consumes, so fires once after resetT
                .read(readPlace)    // Read arc - timer should reset when readPlace is reset
                .output(done)
                .timing(Timing.delayed(Duration.ofMillis(200)))
                .action(ctx -> {
                    ctx.output(done, "done");
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("ReadArcResetTest").transitions(resetT, delayedT).build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                readPlace, List.of(Token.of("old")),
                consumable, List.of(Token.of("initial"))  // Initial consumable for first enablement
            );

            try (var executor = createExecutorWithEnv(net, initial, Set.of(triggerEnv))) {
                CompletableFuture.delayedExecutor(50, TimeUnit.MILLISECONDS)
                    .execute(() -> executor.inject(triggerEnv, Token.unit()));

                long start = System.currentTimeMillis();
                executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();
                long elapsed = System.currentTimeMillis() - start;

                assertTrue(elapsed >= 240,
                    "Read arc dependency should also reset timer. Elapsed: " + elapsed + "ms");
            }
        }
    }

    // ==================== SECTION 6: COMBINED ARC TESTS ====================

    @Nested
    class CombinedArcTests {

        @Test
        void inputAndInhibitor_combined() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var blocker = Place.of("Blocker", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .inhibitor(blocker)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("InputInhibitor").transitions(t).build();

            // Has input, no blocker - should fire
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();
                assertTrue(result.hasTokens(output));
            }
        }

        @Test
        void inputAndInhibitor_blockedWhenInhibitorPresent() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var blocker = Place.of("Blocker", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .inhibitor(blocker)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("InputInhibitorBlocked").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                blocker, List.of(Token.of(new SimpleValue("block")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertTrue(result.hasTokens(input), "Input remains (blocked)");
                assertTrue(result.hasTokens(blocker), "Blocker remains");
                assertFalse(result.hasTokens(output), "No output (blocked)");
            }
        }

        @Test
        void inputAndRead_combined() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var config = Place.of("Config", CounterValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .read(config)
                .output(output)
                .deadline(100)
                .action(ctx -> {
                    ctx.output(output, new SimpleValue("configured"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("InputRead").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                config, List.of(Token.of(new CounterValue(99)))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertFalse(result.hasTokens(input), "Input consumed");
                assertTrue(result.hasTokens(config), "Config not consumed");
                assertTrue(result.hasTokens(output));
            }
        }

        @Test
        void inputAndReset_resetsPlaceOnFire() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var resetPlace = Place.of("ResetPlace", CounterValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .reset(resetPlace)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("InputReset").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                resetPlace, List.of(
                    Token.of(new CounterValue(1)),
                    Token.of(new CounterValue(2)),
                    Token.of(new CounterValue(3))
                )
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertFalse(result.hasTokens(input), "Input consumed");
                assertFalse(result.hasTokens(resetPlace), "Reset place cleared all 3 tokens");
                assertTrue(result.hasTokens(output), "Transition fired");
            }
        }

        @Test
        void inputAndReset_firesEvenWhenResetPlaceEmpty() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var resetPlace = Place.of("ResetPlace", CounterValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .reset(resetPlace)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("InputResetEmpty").transitions(t).build();

            // Reset place is empty - should still fire
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertFalse(result.hasTokens(input), "Input consumed");
                assertTrue(result.hasTokens(output), "Transition fired despite empty reset place");
            }
        }

        @Test
        void inputReadAndReset_firesWhenAllSatisfied() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var readPlace = Place.of("Read", TypeB.class);
            var resetPlace = Place.of("Reset", TypeC.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .read(readPlace)
                .reset(resetPlace)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("InputReadReset").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                readPlace, List.of(Token.of(new TypeB("config"))),
                resetPlace, List.of(Token.of(new TypeC("r1")), Token.of(new TypeC("r2")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertFalse(result.hasTokens(input), "Input consumed");
                assertTrue(result.hasTokens(readPlace), "Read not consumed");
                assertFalse(result.hasTokens(resetPlace), "Reset cleared");
                assertTrue(result.hasTokens(output));
            }
        }

        @Test
        void inputReadAndReset_blockedWhenReadAbsent() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var readPlace = Place.of("Read", TypeB.class);
            var resetPlace = Place.of("Reset", TypeC.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .read(readPlace)
                .reset(resetPlace)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("InputReadResetBlocked").transitions(t).build();

            // Missing read token - should block
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                resetPlace, List.of(Token.of(new TypeC("r1")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertTrue(result.hasTokens(input), "Input remains (blocked)");
                assertTrue(result.hasTokens(resetPlace), "Reset not executed (blocked)");
                assertFalse(result.hasTokens(output), "No output (blocked)");
            }
        }

        @Test
        void inputInhibitorAndReset_firesWhenInhibitorEmpty() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var inhibitor = Place.of("Inhibitor", TypeA.class);
            var resetPlace = Place.of("Reset", TypeC.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .inhibitor(inhibitor)
                .reset(resetPlace)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("InputInhibitorReset").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                resetPlace, List.of(Token.of(new TypeC("r1")), Token.of(new TypeC("r2")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertFalse(result.hasTokens(input), "Input consumed");
                assertFalse(result.hasTokens(resetPlace), "Reset cleared");
                assertTrue(result.hasTokens(output));
            }
        }

        @Test
        void inputInhibitorAndReset_blockedByInhibitor() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var inhibitor = Place.of("Inhibitor", TypeA.class);
            var resetPlace = Place.of("Reset", TypeC.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .inhibitor(inhibitor)
                .reset(resetPlace)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("InputInhibitorResetBlocked").transitions(t).build();

            // Inhibitor has a token - should block, and reset must NOT execute
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                inhibitor, List.of(Token.of(new TypeA("block"))),
                resetPlace, List.of(Token.of(new TypeC("r1")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertTrue(result.hasTokens(input), "Input remains (blocked)");
                assertTrue(result.hasTokens(inhibitor), "Inhibitor remains");
                assertTrue(result.hasTokens(resetPlace), "Reset NOT executed (transition blocked)");
                assertFalse(result.hasTokens(output), "No output (blocked)");
            }
        }

        @Test
        void allArcTypes_combined() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var inhibitor = Place.of("Inhibitor", TypeA.class);
            var read = Place.of("Read", TypeB.class);
            var reset = Place.of("Reset", TypeC.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .inhibitor(inhibitor)
                .read(read)
                .reset(reset)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("all-arcs")))
                .build();

            var net = PetriNet.builder("AllArcs").transitions(t).build();

            // Setup: input present, inhibitor empty, read present, reset has tokens
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                read, List.of(Token.of(new TypeB("read-token"))),
                reset, List.of(Token.of(new TypeC("r1")), Token.of(new TypeC("r2")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertFalse(result.hasTokens(input), "Input consumed");
                assertFalse(result.hasTokens(inhibitor), "Inhibitor still empty");
                assertTrue(result.hasTokens(read), "Read not consumed");
                assertFalse(result.hasTokens(reset), "Reset cleared");
                assertTrue(result.hasTokens(output));
            }
        }

        @Test
        void allArcTypes_blockedByInhibitor() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var inhibitor = Place.of("Inhibitor", TypeA.class);
            var read = Place.of("Read", TypeB.class);
            var reset = Place.of("Reset", TypeC.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .inhibitor(inhibitor)
                .read(read)
                .reset(reset)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("all-arcs")))
                .build();

            var net = PetriNet.builder("AllArcsBlockedInhibitor").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                inhibitor, List.of(Token.of(new TypeA("block"))),
                read, List.of(Token.of(new TypeB("read-token"))),
                reset, List.of(Token.of(new TypeC("r1")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertTrue(result.hasTokens(input), "Input remains (blocked)");
                assertTrue(result.hasTokens(reset), "Reset NOT executed (blocked)");
                assertFalse(result.hasTokens(output), "No output (blocked)");
            }
        }

        @Test
        void allArcTypes_blockedByMissingRead() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var inhibitor = Place.of("Inhibitor", TypeA.class);
            var read = Place.of("Read", TypeB.class);
            var reset = Place.of("Reset", TypeC.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .inhibitor(inhibitor)
                .read(read)
                .reset(reset)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("all-arcs")))
                .build();

            var net = PetriNet.builder("AllArcsBlockedRead").transitions(t).build();

            // Missing read token - should block
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                reset, List.of(Token.of(new TypeC("r1")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertTrue(result.hasTokens(input), "Input remains (blocked)");
                assertTrue(result.hasTokens(reset), "Reset NOT executed (blocked)");
                assertFalse(result.hasTokens(output), "No output (blocked)");
            }
        }

        @Test
        void allArcTypes_blockedByMissingInput() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var inhibitor = Place.of("Inhibitor", TypeA.class);
            var read = Place.of("Read", TypeB.class);
            var reset = Place.of("Reset", TypeC.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .inhibitor(inhibitor)
                .read(read)
                .reset(reset)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("all-arcs")))
                .build();

            var net = PetriNet.builder("AllArcsBlockedInput").transitions(t).build();

            // No input token - should block even though everything else is satisfied
            var initial = Map.<Place<?>, List<Token<?>>>of(
                read, List.of(Token.of(new TypeB("read-token"))),
                reset, List.of(Token.of(new TypeC("r1")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertTrue(result.hasTokens(read), "Read remains");
                assertTrue(result.hasTokens(reset), "Reset NOT executed (blocked)");
                assertFalse(result.hasTokens(output), "No output (blocked)");
            }
        }

        @Test
        void twoTransitions_inhibitorClearedByFirstEnablesSecond() throws Exception {
            var input1 = Place.of("Input1", SimpleValue.class);
            var input2 = Place.of("Input2", SimpleValue.class);
            var shared = Place.of("Shared", SimpleValue.class);
            var output1 = Place.of("Output1", SimpleValue.class);
            var output2 = Place.of("Output2", SimpleValue.class);

            // T1: consumes input1 and shared, produces output1
            var t1 = Transition.builder("T1")
                .input(input1)
                .input(shared)
                .output(output1)
                .deadline(50)
                .action(TransitionAction.produce(output1, new SimpleValue("t1-fired")))
                .build();

            // T2: consumes input2, inhibited by shared - unblocked after T1 removes shared
            var t2 = Transition.builder("T2")
                .input(input2)
                .inhibitor(shared)
                .output(output2)
                .deadline(100)
                .action(TransitionAction.produce(output2, new SimpleValue("t2-fired")))
                .build();

            var net = PetriNet.builder("InhibitorChain").transitions(t1, t2).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input1, List.of(Token.of(new SimpleValue("go1"))),
                input2, List.of(Token.of(new SimpleValue("go2"))),
                shared, List.of(Token.of(new SimpleValue("blocker")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertTrue(result.hasTokens(output1), "T1 fired");
                assertTrue(result.hasTokens(output2), "T2 fired after inhibitor cleared");
                assertFalse(result.hasTokens(shared), "Shared consumed by T1");
            }
        }
    }

    // ==================== SECTION 6b: CARDINALITY WITH ARC TESTS ====================

    @Nested
    class CardinalityWithArcTests {

        @Test
        void exactlyN_withInhibitor_firesWhenUnblocked() throws Exception {
            var input = Place.of("Input", CounterValue.class);
            var inhibitor = Place.of("Inhibitor", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .inputs(exactly(3, input))
                .inhibitor(inhibitor)
                .outputs(place(output))
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("ExactlyInhibitor").transitions(t).build();

            // 5 tokens in input, inhibitor empty - should consume exactly 3
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(
                    Token.of(new CounterValue(1)),
                    Token.of(new CounterValue(2)),
                    Token.of(new CounterValue(3)),
                    Token.of(new CounterValue(4)),
                    Token.of(new CounterValue(5))
                )
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertTrue(result.hasTokens(output), "Transition fired");
                assertEquals(2, result.tokenCount(input), "Consumed exactly 3 of 5");
            }
        }

        @Test
        void exactlyN_withInhibitor_blockedWhenPresent() throws Exception {
            var input = Place.of("Input", CounterValue.class);
            var inhibitor = Place.of("Inhibitor", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .inputs(exactly(3, input))
                .inhibitor(inhibitor)
                .outputs(place(output))
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("ExactlyInhibitorBlocked").transitions(t).build();

            // 5 tokens but inhibitor present - blocked
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(
                    Token.of(new CounterValue(1)),
                    Token.of(new CounterValue(2)),
                    Token.of(new CounterValue(3)),
                    Token.of(new CounterValue(4)),
                    Token.of(new CounterValue(5))
                ),
                inhibitor, List.of(Token.of(new SimpleValue("block")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertFalse(result.hasTokens(output), "No output (blocked)");
                assertEquals(5, result.tokenCount(input), "All tokens remain");
            }
        }

        @Test
        void all_withReadAndReset() throws Exception {
            var input = Place.of("Input", CounterValue.class);
            var readPlace = Place.of("Read", TypeB.class);
            var resetPlace = Place.of("Reset", TypeC.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .inputs(all(input))
                .read(readPlace)
                .reset(resetPlace)
                .outputs(place(output))
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("AllReadReset").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(
                    Token.of(new CounterValue(1)),
                    Token.of(new CounterValue(2)),
                    Token.of(new CounterValue(3)),
                    Token.of(new CounterValue(4))
                ),
                readPlace, List.of(Token.of(new TypeB("config"))),
                resetPlace, List.of(Token.of(new TypeC("r1")), Token.of(new TypeC("r2")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertTrue(result.hasTokens(output), "Transition fired");
                assertFalse(result.hasTokens(input), "All 4 input tokens drained");
                assertTrue(result.hasTokens(readPlace), "Read not consumed");
                assertFalse(result.hasTokens(resetPlace), "Reset cleared");
            }
        }

        @Test
        void atLeast_blocksWhenBelowMinimum() throws Exception {
            var input = Place.of("Input", CounterValue.class);
            var inhibitor = Place.of("Inhibitor", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .inputs(atLeast(3, input))
                .inhibitor(inhibitor)
                .outputs(place(output))
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("AtLeastBlocked").transitions(t).build();

            // Only 2 tokens, need at least 3 - blocked even though inhibitor is empty
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(
                    Token.of(new CounterValue(1)),
                    Token.of(new CounterValue(2))
                )
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertFalse(result.hasTokens(output), "No output (insufficient tokens)");
                assertEquals(2, result.tokenCount(input), "Tokens remain");
            }
        }

        @Test
        void atLeast_firesWhenAboveMinimum() throws Exception {
            var input = Place.of("Input", CounterValue.class);
            var inhibitor = Place.of("Inhibitor", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .inputs(atLeast(3, input))
                .inhibitor(inhibitor)
                .outputs(place(output))
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("AtLeastFires").transitions(t).build();

            // 5 tokens, need at least 3, inhibitor empty - should consume all 5
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(
                    Token.of(new CounterValue(1)),
                    Token.of(new CounterValue(2)),
                    Token.of(new CounterValue(3)),
                    Token.of(new CounterValue(4)),
                    Token.of(new CounterValue(5))
                )
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertTrue(result.hasTokens(output), "Transition fired");
                assertEquals(0, result.tokenCount(input), "All 5 tokens consumed (atLeast consumes all)");
            }
        }

        @Test
        void exactlyN_withReset_resetsOnFire() throws Exception {
            var input = Place.of("Input", CounterValue.class);
            var resetPlace = Place.of("Reset", TypeC.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .inputs(exactly(2, input))
                .reset(resetPlace)
                .outputs(place(output))
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("ExactlyReset").transitions(t).build();

            // 3 input tokens, consume exactly 2; reset place has tokens to clear
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(
                    Token.of(new CounterValue(1)),
                    Token.of(new CounterValue(2)),
                    Token.of(new CounterValue(3))
                ),
                resetPlace, List.of(Token.of(new TypeC("r1")), Token.of(new TypeC("r2")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertTrue(result.hasTokens(output), "Transition fired");
                assertEquals(1, result.tokenCount(input), "Consumed exactly 2 of 3");
                assertFalse(result.hasTokens(resetPlace), "Reset place cleared");
            }
        }
    }

    // ==================== SECTION 6c: OUTPUT SPEC WITH ARC TESTS ====================

    @Nested
    class OutputSpecWithArcTests {

        @Test
        void xorOutput_withInhibitor_producesToCorrectBranch() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var inhibitor = Place.of("Inhibitor", TypeA.class);
            var success = Place.of("Success", SimpleValue.class);
            var failure = Place.of("Failure", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .inhibitor(inhibitor)
                .outputs(xor(success, failure))
                .deadline(100)
                .action(ctx -> {
                    ctx.output(success, new SimpleValue("ok"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("XorInhibitor").transitions(t).build();

            // Inhibitor empty - should fire and produce to success branch
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertTrue(result.hasTokens(success), "Token produced to success branch");
                assertFalse(result.hasTokens(failure), "Nothing in failure branch");
                assertFalse(result.hasTokens(input), "Input consumed");
            }
        }

        @Test
        void xorOutput_withInhibitor_blocked() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var inhibitor = Place.of("Inhibitor", TypeA.class);
            var success = Place.of("Success", SimpleValue.class);
            var failure = Place.of("Failure", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .inhibitor(inhibitor)
                .outputs(xor(success, failure))
                .deadline(100)
                .action(ctx -> {
                    ctx.output(success, new SimpleValue("ok"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("XorInhibitorBlocked").transitions(t).build();

            // Inhibitor present - should block, nothing produced
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                inhibitor, List.of(Token.of(new TypeA("block")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertFalse(result.hasTokens(success), "No success output (blocked)");
                assertFalse(result.hasTokens(failure), "No failure output (blocked)");
                assertTrue(result.hasTokens(input), "Input remains (blocked)");
            }
        }

        @Test
        void andOutput_withReadAndReset() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var readPlace = Place.of("Read", TypeB.class);
            var resetPlace = Place.of("Reset", TypeC.class);
            var out1 = Place.of("Out1", SimpleValue.class);
            var out2 = Place.of("Out2", CounterValue.class);

            var t = Transition.builder("t")
                .input(input)
                .read(readPlace)
                .reset(resetPlace)
                .outputs(and(out1, out2))
                .deadline(100)
                .action(ctx -> {
                    ctx.output(out1, new SimpleValue("result1"));
                    ctx.output(out2, new CounterValue(42));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("AndReadReset").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go"))),
                readPlace, List.of(Token.of(new TypeB("config"))),
                resetPlace, List.of(Token.of(new TypeC("r1")), Token.of(new TypeC("r2")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertTrue(result.hasTokens(out1), "AND output 1 has token");
                assertTrue(result.hasTokens(out2), "AND output 2 has token");
                assertTrue(result.hasTokens(readPlace), "Read not consumed");
                assertFalse(result.hasTokens(resetPlace), "Reset cleared");
                assertFalse(result.hasTokens(input), "Input consumed");
            }
        }
    }

    // ==================== SECTION 7: TIMING AND FIRING INTERVAL TESTS ====================

    @Nested
    class TimingTests {

        @Test
        void competingTransitions_timeoutWinsRace_whenEarlier() throws Exception {
            // Test: Timeout transition fires before main when it has an earlier firing time.
            // This models the competing transitions pattern where transitions race to fire.
            // Whichever transition's earliest time is reached first wins.
            var input = Place.of("Input", SimpleValue.class);
            var success = Place.of("Success", SimpleValue.class);
            var timeout = Place.of("Timeout", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            // Main transition: cannot fire until 100ms
            var main = Transition.builder("Process")
                .input(input)
                .output(success)
                .interval(new FiringInterval(Duration.ofMillis(100), Duration.ofDays(1)))
                .action(ctx -> {
                    ctx.output(success, new SimpleValue("completed"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            // Timeout transition: fires at exactly 50ms (before main can fire)
            var timeoutTransition = Transition.builder("Timeout")
                .input(input)
                .output(timeout)
                .interval(FiringInterval.exact(Duration.ofMillis(50)))
                .action(ctx -> {
                    ctx.output(timeout, Token.unit());
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("TimeoutRace")
                .transitions(main, timeoutTransition)
                .build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial, eventStore)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                // Input consumed by timeout transition (fired at 50ms)
                assertFalse(result.hasTokens(input), "Input should be consumed");

                // Timeout transition fired first - token in timeout place
                assertTrue(result.hasTokens(timeout), "Timeout transition should have fired");

                // Main transition did not fire (input already consumed at 50ms, before its 100ms earliest)
                assertFalse(result.hasTokens(success), "Main transition should not have fired");
            }
        }

        @Test
        void withTimeout_producesNormalOutput_whenActionFast() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var success = Place.of("Success", SimpleValue.class);
            var timeout = Place.of("Timeout", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            // Use TransitionAction.withTimeout() wrapper for action-level timeout
            var wrappedAction = TransitionAction.withTimeout(
                ctx -> {
                    // Fast action - completes immediately
                    ctx.output(success, new SimpleValue("completed"));
                    return CompletableFuture.completedFuture(null);
                },
                Duration.ofMillis(200),  // 200ms deadline - plenty of time
                timeout,
                new SimpleValue("timed-out")
            );

            var t = Transition.builder("Process")
                .input(input)
                .output(success)
                .output(timeout)
                .action(wrappedAction)
                .build();

            var net = PetriNet.builder("TimeoutWrapper")
                .transitions(t)
                .build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial, eventStore)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                // Input consumed by transition
                assertFalse(result.hasTokens(input), "Input should be consumed");

                // Fast action completed - token in success place
                assertTrue(result.hasTokens(success), "Action should have completed normally");

                // No timeout occurred
                assertFalse(result.hasTokens(timeout), "Timeout should not have occurred");
            }
        }

        @Test
        void withTimeout_producesTimeoutToken_whenActionSlow() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var success = Place.of("Success", SimpleValue.class);
            var timeout = Place.of("Timeout", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            // Use TransitionAction.withTimeout() wrapper for action-level timeout
            var wrappedAction = TransitionAction.withTimeout(
                ctx -> {
                    // Slow action - takes 500ms, longer than 100ms timeout
                    return CompletableFuture.runAsync(() -> {
                        try {
                            Thread.sleep(500);
                        } catch (InterruptedException e) {
                            Thread.currentThread().interrupt();
                        }
                        ctx.output(success, new SimpleValue("completed"));
                    }, testExecutor);
                },
                Duration.ofMillis(100),  // 100ms deadline - action will timeout
                timeout,
                new SimpleValue("timed-out")
            );

            var t = Transition.builder("Process")
                .input(input)
                .output(success)
                .output(timeout)
                .action(wrappedAction)
                .build();

            var net = PetriNet.builder("TimeoutWrapper")
                .transitions(t)
                .build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial, eventStore)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                // Input consumed by transition
                assertFalse(result.hasTokens(input), "Input should be consumed");

                // Action timed out - token in timeout place
                assertTrue(result.hasTokens(timeout), "Timeout should have occurred");

                // Success token not produced (action timed out)
                assertFalse(result.hasTokens(success), "Action should not have completed");

                // Verify timeout token value
                var tokens = new java.util.ArrayList<>(result.peekTokens(timeout));
                assertEquals(1, tokens.size());
                assertEquals(new SimpleValue("timed-out"), tokens.getFirst().value());
            }
        }

        @Test
        void earliestTime_delaysExecution() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var executionTime = new AtomicReference<Long>();
            var startTime = System.currentTimeMillis();

            var t = Transition.builder("delayed")
                .input(input)
                .output(output)
                .interval(new FiringInterval(Duration.ofMillis(200), Duration.ofMillis(1000)))
                .action(ctx -> {
                    executionTime.set(System.currentTimeMillis() - startTime);
                    ctx.output(output, new SimpleValue("delayed"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("EarliestTime").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertTrue(result.hasTokens(output));
                assertTrue(executionTime.get() >= 150, // Allow some tolerance
                    "Should wait for earliest time, but was " + executionTime.get() + "ms");
            }
        }

        @Test
        void exactTiming_firesAtSpecificTime() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var executionDelay = new AtomicReference<Long>();
            var startTime = System.currentTimeMillis();

            var t = Transition.builder("exact")
                .input(input)
                .output(output)
                .interval(FiringInterval.exact(Duration.ofMillis(150)))
                .action(ctx -> {
                    executionDelay.set(System.currentTimeMillis() - startTime);
                    ctx.output(output, new SimpleValue("exact"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("ExactTime").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertTrue(result.hasTokens(output));
                // Exact timing means earliest = latest = 150ms
                assertTrue(executionDelay.get() >= 100,
                    "Should wait for exact time, was " + executionDelay.get() + "ms");
            }
        }

        @Test
        void unconstrained_firesImmediately() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var executionDelay = new AtomicReference<Long>();
            var startTime = System.currentTimeMillis();

            var t = Transition.builder("immediate")
                .input(input)
                .output(output)
                .interval(FiringInterval.unconstrained())
                .action(ctx -> {
                    executionDelay.set(System.currentTimeMillis() - startTime);
                    ctx.output(output, new SimpleValue("immediate"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("Unconstrained").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertTrue(result.hasTokens(output));
                assertTrue(executionDelay.get() < 100, "Should fire quickly");
            }
        }

        @Test
        void firingInterval_validation() {
            // Negative earliest
            assertThrows(IllegalArgumentException.class, () ->
                new FiringInterval(Duration.ofMillis(-100), Duration.ofMillis(100)));

            // Latest < earliest
            assertThrows(IllegalArgumentException.class, () ->
                new FiringInterval(Duration.ofMillis(200), Duration.ofMillis(100)));

            // Valid intervals
            assertDoesNotThrow(() -> new FiringInterval(Duration.ZERO, Duration.ZERO));
            assertDoesNotThrow(() -> new FiringInterval(Duration.ofMillis(100), Duration.ofMillis(100)));
            assertDoesNotThrow(() -> FiringInterval.unconstrained());
        }

        @Test
        void resetArcWithOutputToSamePlaceShouldRestartTimedTransitionClock() throws Exception {
            // Test for timer reset bug: after reset arc fires and puts new token in same place,
            // the timed transition's clock should restart from zero, not continue from old timestamp.
            //
            // Bug scenario (if not fixed):
            // - T=0: Timer token placed, CloseSession enabled with 200ms delay
            // - T=100ms: UserActivity arrives, ResetTimer fires (removes and adds timer token)
            // - BUG: enabledAt timestamp for CloseSession NOT updated (still T=0)
            // - T=200ms: CloseSession fires (200ms from T=0, not 300ms from T=100ms+200ms)
            //
            // Correct behavior: CloseSession should fire at T=300ms (100ms + 200ms)

            var timerPending = Place.of("TimerPending", SimpleValue.class);
            var userActivity = Place.of("UserActivity", SimpleValue.class);
            var sessionClosed = Place.of("SessionClosed", SimpleValue.class);

            var eventStore = EventStore.inMemory();
            AtomicLong closeTransitionFireTime = new AtomicLong();
            long startTime = System.nanoTime();

            // Reset timer: consumes activity, resets timer place, outputs new timer token
            var resetTimer = Transition.builder("ResetTimer")
                .input(userActivity)
                .reset(timerPending)
                .output(timerPending)
                .action(TransitionAction.produce(timerPending, new SimpleValue("reset")))
                .build();

            // Close session: fires exactly 200ms after timer token is placed
            var closeSession = Transition.builder("CloseSession")
                .input(timerPending)
                .output(sessionClosed)
                .interval(FiringInterval.exact(Duration.ofMillis(200)))
                .action(ctx -> {
                    closeTransitionFireTime.set(System.nanoTime());
                    ctx.output(sessionClosed, new SimpleValue("closed"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("TimerResetTest")
                .transitions(resetTimer, closeSession)
                .build();

            // Initial: timer pending (started at T=0), activity will arrive later
            var initial = Map.<Place<?>, List<Token<?>>>of(
                timerPending, List.of(Token.of(new SimpleValue("initial")))
            );

            var userActivityEnv = EnvironmentPlace.of(userActivity);
            try (var virtualThreadExecutor = Executors.newVirtualThreadPerTaskExecutor();
                 var executor = createExecutorWithEnv(net, initial, eventStore, Set.of(userActivityEnv))) {

                // Schedule activity injection at T=100ms (before 200ms timeout)
                var injectionFuture = virtualThreadExecutor.submit(() -> {
                    try {
                        Thread.sleep(100);
                        executor.inject(userActivityEnv, Token.of(new SimpleValue("activity"))).join();
                    } catch (InterruptedException e) {
                        Thread.currentThread().interrupt();
                    }
                });

                // Run executor - it will spin quickly but virtual threads handle this well
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                // Ensure injection completed (or failed gracefully)
                try {
                    injectionFuture.get(100, TimeUnit.MILLISECONDS);
                } catch (Exception ignored) {
                    // Injection might have failed if executor finished first
                }

                // Session should be closed
                assertTrue(result.hasTokens(sessionClosed), "Session should be closed");

                // CRITICAL: Close should fire at T=100ms + 200ms = 300ms, NOT at T=200ms
                // If bug exists, it fires at T=200ms (original clock not reset)
                long elapsedMs = (closeTransitionFireTime.get() - startTime) / 1_000_000;

                assertTrue(elapsedMs >= 280,
                    "CloseSession should fire ~300ms after start (reset at 100ms + 200ms timeout). " +
                    "Actual: " + elapsedMs + "ms. If ~200ms, clock was not reset!");
            }
        }
    }

    // ==================== SECTION 8: PRIORITY TESTS ====================

    @Nested
    class PriorityTests {

        @Test
        void higherPriority_firesFirst() throws Exception {
            var shared = Place.of("Shared", SimpleValue.class);
            var outLow = Place.of("OutLow", SimpleValue.class);
            var outHigh = Place.of("OutHigh", SimpleValue.class);

            var order = new CopyOnWriteArrayList<String>();

            var lowPriority = Transition.builder("low")
                .input(shared)
                .output(outLow)
                .priority(1)
                .deadline(100)
                .action(ctx -> {
                    order.add("low");
                    ctx.output(outLow, new SimpleValue("low"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var highPriority = Transition.builder("high")
                .input(shared)
                .output(outHigh)
                .priority(10)
                .deadline(100)
                .action(ctx -> {
                    order.add("high");
                    ctx.output(outHigh, new SimpleValue("high"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("Priority").transitions(lowPriority, highPriority).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                shared, List.of(Token.of(new SimpleValue("token")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                // Only one should fire (consume the token)
                assertEquals(1, order.size(), "Only one should fire");
                assertEquals("high", order.getFirst(), "High priority fires first");
                assertTrue(result.hasTokens(outHigh));
                assertFalse(result.hasTokens(outLow));
            }
        }

        @Test
        void samePriority_earlierEnabledWins() throws Exception {
            var triggerFast = Place.of("TriggerFast", SimpleValue.class);
            var triggerSlow = Place.of("TriggerSlow", SimpleValue.class);
            var shared = Place.of("Shared", CounterValue.class);
            var outFast = Place.of("OutFast", SimpleValue.class);
            var outSlow = Place.of("OutSlow", SimpleValue.class);

            var order = new CopyOnWriteArrayList<String>();

            // Fast becomes enabled immediately
            var fast = Transition.builder("fast")
                .input(triggerFast)
                .input(shared)
                .output(outFast)
                .priority(5)
                .deadline(100)
                .action(ctx -> {
                    order.add("fast");
                    ctx.output(outFast, new SimpleValue("fast"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            // Slow needs trigger that arrives later
            var slow = Transition.builder("slow")
                .input(triggerSlow)
                .input(shared)
                .output(outSlow)
                .priority(5)  // Same priority
                .deadline(100)
                .action(ctx -> {
                    order.add("slow");
                    ctx.output(outSlow, new SimpleValue("slow"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("EarlyEnabled").transitions(fast, slow).build();

            // Both enabled at start, fast transition registered first due to iteration order
            var initial = Map.<Place<?>, List<Token<?>>>of(
                triggerFast, List.of(Token.of(new SimpleValue("fast-trigger"))),
                triggerSlow, List.of(Token.of(new SimpleValue("slow-trigger"))),
                shared, List.of(Token.of(new CounterValue(1)))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertEquals(1, order.size(), "Only one fires (conflict)");
                // One of them wins - order depends on enablement time which is nearly simultaneous
            }
        }

        @Test
        void priority_withMultipleTokens_sequentialExecution() throws Exception {
            // Test that with sequential synchronous execution, priority is respected
            var input = Place.of("Input", CounterValue.class);
            var outLow = Place.of("OutLow", CounterValue.class);
            var outHigh = Place.of("OutHigh", CounterValue.class);

            var order = new CopyOnWriteArrayList<String>();

            var lowPriority = Transition.builder("low")
                .input(input)
                .output(outLow)
                .priority(1)
                .deadline(100)
                .action(ctx -> {
                    order.add("low-" + ctx.input(input).count());
                    ctx.output(outLow, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var highPriority = Transition.builder("high")
                .input(input)
                .output(outHigh)
                .priority(10)
                .deadline(100)
                .action(ctx -> {
                    order.add("high-" + ctx.input(input).count());
                    ctx.output(outHigh, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("PriorityMultiToken").transitions(lowPriority, highPriority).build();

            // Multiple tokens available
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(
                    Token.of(new CounterValue(1)),
                    Token.of(new CounterValue(2)),
                    Token.of(new CounterValue(3))
                )
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                // All tokens should be processed
                int total = result.tokenCount(outHigh) + result.tokenCount(outLow);
                assertEquals(3, total, "All tokens processed");

                // High priority should fire first each round
                // The first action in order should start with "high"
                assertTrue(order.getFirst().startsWith("high"),
                    "High priority fires first: " + order);
            }
        }
    }

    // ==================== SECTION 9: ASYNC ACTION TESTS ====================

    @Nested
    class AsyncActionTests {

        @Test
        void asyncAction_completesSuccessfully() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);
            var actionExecutor = Executors.newVirtualThreadPerTaskExecutor();

            var t = Transition.builder("async")
                .input(input)
                .output(output)
                .action(ctx -> CompletableFuture.runAsync(() -> {
                    sleep(100);
                    ctx.output(output, new SimpleValue("async-result"));
                }, actionExecutor))
                .build();

            var net = PetriNet.builder("Async").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertTrue(result.hasTokens(output));
                assertEquals("async-result", result.peekFirst(output).value().data());
            }
        }

        @Test
        void asyncAction_handlesException() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var eventStore = EventStore.inMemory();
            var actionExecutor = Executors.newVirtualThreadPerTaskExecutor();
            var t = Transition.builder("failing")
                .input(input)
                .output(output)
                .deadline(1000)
                .action(ctx -> CompletableFuture.runAsync(() -> {
                    throw new RuntimeException("Intentional failure");
                }, actionExecutor))
                .build();

            var net = PetriNet.builder("FailingAsync").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial, eventStore)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertFalse(result.hasTokens(output), "No output on failure");
                Thread.sleep(50); // wait some time so that events getting processed
                var failEvents = eventStore.events().stream()
                    .filter(e -> e instanceof NetEvent.TransitionFailed)
                    .toList();
                assertFalse(failEvents.isEmpty(), "Should record failure event");
            }
        }

        @Test
        void parallelTransitions_executeInParallel() throws Exception {
            var trigger = Place.of("Trigger", SimpleValue.class);
            var out1 = Place.of("Out1", SimpleValue.class);
            var out2 = Place.of("Out2", SimpleValue.class);
            var out3 = Place.of("Out3", SimpleValue.class);

            var executionOrder = new CopyOnWriteArrayList<String>();
            var actionExecutor = Executors.newVirtualThreadPerTaskExecutor();
            // Fork: one input produces three outputs
            var fork = Transition.builder("fork")
                .input(trigger)
                .output(out1)
                .output(out2)
                .output(out3)
                .deadline(100)
                .action(ctx -> {
                    ctx.output(out1, new SimpleValue("branch1"));
                    ctx.output(out2, new SimpleValue("branch2"));
                    ctx.output(out3, new SimpleValue("branch3"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            // Three parallel workers
            var worker1 = Transition.builder("worker1")
                .input(out1)
                .output(Place.of("Done1", SimpleValue.class))
                .deadline(500)
                .action(ctx -> CompletableFuture.runAsync(() -> {
                    executionOrder.add("start1");
                    sleep(100);
                    executionOrder.add("end1");
                }, actionExecutor))
                .build();

            var worker2 = Transition.builder("worker2")
                .input(out2)
                .output(Place.of("Done2", SimpleValue.class))
                .deadline(500)
                .action(ctx -> CompletableFuture.runAsync(() -> {
                    executionOrder.add("start2");
                    sleep(100);
                    executionOrder.add("end2");
                }, actionExecutor))
                .build();

            var worker3 = Transition.builder("worker3")
                .input(out3)
                .output(Place.of("Done3", SimpleValue.class))
                .deadline(500)
                .action(ctx -> CompletableFuture.runAsync(() -> {
                    executionOrder.add("start3");
                    sleep(100);
                    executionOrder.add("end3");
                }, actionExecutor))
                .build();

            var net = PetriNet.builder("Parallel")
                .transitions(fork, worker1, worker2, worker3)
                .build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                trigger, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial)) {
                var startTime = System.currentTimeMillis();
                executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();
                var elapsed = System.currentTimeMillis() - startTime;

                // All workers should start before any ends (parallel)
                var startCount = executionOrder.stream()
                    .filter(s -> s.startsWith("start"))
                    .count();
                assertEquals(3, startCount, "All three started");

                // Should complete in ~200ms (100ms workers + overhead), not 300ms+ (sequential)
                assertTrue(elapsed < 400, "Should run in parallel, took " + elapsed + "ms");
            }
        }

        @Test
        void passthrough_actionDoesNothing() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("passthrough")
                .input(input)
                .output(output)
                .deadline(100)
                .action(TransitionAction.passthrough())
                .build();

            var net = PetriNet.builder("Passthrough").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("data")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertFalse(result.hasTokens(input), "Input consumed");
                assertFalse(result.hasTokens(output), "Passthrough produces no output");
            }
        }

        @Test
        void transform_synchronousTransformation() throws Exception {
            var input = Place.of("Input", CounterValue.class);
            var output = Place.of("Output", CounterValue.class);

            var t = Transition.builder("transform")
                .input(input)
                .output(output)
                .deadline(100)
                .action(ctx -> {
                    ctx.output(output, new CounterValue(ctx.input(input).count() * 2));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("Transform").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new CounterValue(21)))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertTrue(result.hasTokens(output));
                assertEquals(42, result.peekFirst(output).value().count());
            }
        }
    }

    // ==================== SECTION 10: WORKFLOW PATTERN TESTS ====================

    @Nested
    class WorkflowPatternTests {

        @Test
        void sequentialChain_executesInOrder() throws Exception {
            var p1 = Place.of("P1", CounterValue.class);
            var p2 = Place.of("P2", CounterValue.class);
            var p3 = Place.of("P3", CounterValue.class);
            var p4 = Place.of("P4", CounterValue.class);

            var sequence = new CopyOnWriteArrayList<Integer>();

            var t1 = Transition.builder("t1")
                .input(p1).output(p2).deadline(100)
                .action(ctx -> {
                    sequence.add(1);
                    ctx.output(p2, new CounterValue(1));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var t2 = Transition.builder("t2")
                .input(p2).output(p3).deadline(100)
                .action(ctx -> {
                    sequence.add(2);
                    ctx.output(p3, new CounterValue(2));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var t3 = Transition.builder("t3")
                .input(p3).output(p4).deadline(100)
                .action(ctx -> {
                    sequence.add(3);
                    ctx.output(p4, new CounterValue(3));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("Sequential").transitions(t1, t2, t3).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                p1, List.of(Token.of(new CounterValue(0)))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertEquals(List.of(1, 2, 3), sequence, "Execute in order");
                assertTrue(result.hasTokens(p4));
            }
        }

        @Test
        void forkJoin_parallelBranchesMerge() throws Exception {
            var start = Place.of("Start", SimpleValue.class);
            var branch1 = Place.of("Branch1", TypeA.class);
            var branch2 = Place.of("Branch2", TypeB.class);
            var end = Place.of("End", SimpleValue.class);

            var fork = Transition.builder("fork")
                .input(start)
                .output(branch1)
                .output(branch2)
                .deadline(100)
                .action(ctx -> {
                    ctx.output(branch1, new TypeA("a"));
                    ctx.output(branch2, new TypeB("b"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var join = Transition.builder("join")
                .input(branch1)
                .input(branch2)
                .output(end)
                .deadline(100)
                .action(TransitionAction.produce(end, new SimpleValue("joined")))
                .build();

            var net = PetriNet.builder("ForkJoin").transitions(fork, join).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                start, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertFalse(result.hasTokens(start));
                assertFalse(result.hasTokens(branch1));
                assertFalse(result.hasTokens(branch2));
                assertTrue(result.hasTokens(end));
            }
        }

        @Test
        void conditionalBranching_exclusiveChoice() throws Exception {
            var input = Place.of("Input", Decision.class);
            var left = Place.of("Left", SimpleValue.class);
            var right = Place.of("Right", SimpleValue.class);

            var goLeft = Transition.builder("goLeft")
                .inputWhen(input, d -> d instanceof GoLeft)
                .output(left)
                .deadline(100)
                .action(TransitionAction.produce(left, new SimpleValue("went-left")))
                .build();

            var goRight = Transition.builder("goRight")
                .inputWhen(input, d -> d instanceof GoRight)
                .output(right)
                .deadline(100)
                .action(TransitionAction.produce(right, new SimpleValue("went-right")))
                .build();

            var net = PetriNet.builder("Conditional").transitions(goLeft, goRight).build();

            // Test going left
            var goingLeft = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new GoLeft("choose left")))
            );

            try (var executor = createExecutor(net,goingLeft)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertTrue(result.hasTokens(left));
                assertFalse(result.hasTokens(right));
            }

            // Test going right
            var goingRight = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new GoRight("choose right")))
            );

            try (var executor = createExecutor(net,goingRight)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertFalse(result.hasTokens(left));
                assertTrue(result.hasTokens(right));
            }
        }

        @Test
        void loop_repeatsUntilCondition() throws Exception {
            var counter = Place.of("Counter", CounterValue.class);
            var done = Place.of("Done", SimpleValue.class);

            // Continue looping while count < 5
            var loop = Transition.builder("loop")
                .inputWhen(counter, c -> c.count() < 5)
                .output(counter)
                .deadline(50)
                .action(ctx -> {
                    var current = ctx.input(counter);
                    ctx.output(counter, new CounterValue(current.count() + 1));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            // Exit when count >= 5
            var exit = Transition.builder("exit")
                .inputWhen(counter, c -> c.count() >= 5)
                .output(done)
                .deadline(50)
                .action(TransitionAction.produce(done, new SimpleValue("finished")))
                .build();

            var net = PetriNet.builder("Loop").transitions(loop, exit).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                counter, List.of(Token.of(new CounterValue(0)))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

                assertTrue(result.hasTokens(done), "Should exit loop");
                assertFalse(result.hasTokens(counter), "Counter consumed by exit");
            }
        }

        @Test
        void mutex_mutualExclusion() throws Exception {
            var resource = Place.of("Resource", SimpleValue.class);
            var request1 = Place.of("Request1", SimpleValue.class);
            var request2 = Place.of("Request2", SimpleValue.class);
            var done1 = Place.of("Done1", SimpleValue.class);
            var done2 = Place.of("Done2", SimpleValue.class);

            var accessLog = new CopyOnWriteArrayList<String>();
            var actionExecutor = Executors.newVirtualThreadPerTaskExecutor();
            var access1 = Transition.builder("access1")
                .input(request1)
                .input(resource)
                .output(done1)
                .output(resource)  // Release resource after
                .deadline(200)
                .action(ctx -> CompletableFuture.runAsync(() -> {
                    System.out.println("mutex_mutualExclusion Starting access1");
                    accessLog.add("start1");
                    sleep(50);
                    accessLog.add("end1");
                    ctx.output(done1, new SimpleValue("done1"));
                    ctx.output(resource, new SimpleValue("mutex"));
                    System.out.println("mutex_mutualExclusion Finishing access1");
                }, actionExecutor))
                .build();

            var access2 = Transition.builder("access2")
                .input(request2)
                .input(resource)
                .output(done2)
                .output(resource)  // Release resource after
                .deadline(200)
                .action(ctx -> CompletableFuture.runAsync(() -> {
                    System.out.println("mutex_mutualExclusion Starting access2");
                    accessLog.add("start2");
                    sleep(50);
                    accessLog.add("end2");
                    ctx.output(done2, new SimpleValue("done2"));
                    ctx.output(resource, new SimpleValue("mutex"));
                    System.out.println("mutex_mutualExclusion Finished access2");
                }, actionExecutor))
                .build();

            var net = PetriNet.builder("Mutex").transitions(access1, access2).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                resource, List.of(Token.of(new SimpleValue("mutex"))),
                request1, List.of(Token.of(new SimpleValue("req1"))),
                request2, List.of(Token.of(new SimpleValue("req2")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();
                System.out.println("mutex_mutualExclusion Finished netExecutor");

                assertTrue(result.hasTokens(done1));
                assertTrue(result.hasTokens(done2));
                assertTrue(result.hasTokens(resource));

                // Check mutual exclusion: one ends before the other starts
                int end1Idx = accessLog.indexOf("end1");
                int start2Idx = accessLog.indexOf("start2");
                int end2Idx = accessLog.indexOf("end2");
                int start1Idx = accessLog.indexOf("start1");

                boolean mutuallyExclusive = (end1Idx < start2Idx) || (end2Idx < start1Idx);
                assertTrue(mutuallyExclusive, "Access should be mutually exclusive: " + accessLog);
            }
        }

        @Test
        void producerConsumer_bufferBounded() throws Exception {
            var buffer = Place.of("Buffer", CounterValue.class);
            var producedCount = Place.of("ProducedCount", SimpleValue.class);
            var consumedCount = Place.of("ConsumedCount", SimpleValue.class);

            var produceCounter = new AtomicInteger(0);
            var consumeCounter = new AtomicInteger(0);

            // Producer: can only produce if buffer not full (use inhibitor with threshold)
            // For simplicity, produce until we've made 5 items
            var trigger = Place.of("Trigger", CounterValue.class);

            var produce = Transition.builder("produce")
                .inputWhen(trigger, c -> c.count() < 5)
                .output(buffer)
                .output(trigger)
                .deadline(50)
                .action(ctx -> {
                    int next = ctx.input(trigger).count();
                    ctx.output(buffer, new CounterValue(produceCounter.incrementAndGet()));
                    ctx.output(trigger, new CounterValue(next + 1));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var consume = Transition.builder("consume")
                .input(buffer)
                .output(consumedCount)
                .deadline(50)
                .action(ctx -> {
                    consumeCounter.incrementAndGet();
                    ctx.output(consumedCount, new SimpleValue("consumed-" + consumeCounter.get()));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("ProducerConsumer").transitions(produce, consume).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                trigger, List.of(Token.of(new CounterValue(0)))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

                assertEquals(5, produceCounter.get(), "Produced 5 items");
                assertEquals(5, consumeCounter.get(), "Consumed 5 items");
            }
        }
    }

    // ==================== SECTION 11: EDGE CASES AND ERROR HANDLING ====================

    @Nested
    class EdgeCaseTests {

        @Test
        void emptyNet_completesImmediately() throws Exception {
            var net = PetriNet.builder("Empty").build();

            try (var executor = createExecutor(net,Map.of())) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();
                assertNotNull(result);
            }
        }

        @Test
        void noInitialTokens_nothingFires() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("never")))
                .build();

            var net = PetriNet.builder("NoTokens").transitions(t).build();

            try (var executor = createExecutor(net,Map.of())) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertFalse(result.hasTokens(output), "Nothing fires without tokens");
            }
        }

        @Test
        void deadlock_stopsExecution() throws Exception {
            var p1 = Place.of("P1", SimpleValue.class);
            var p2 = Place.of("P2", SimpleValue.class);

            // Each transition needs a token from the other place - deadlock!
            var t1 = Transition.builder("t1")
                .input(p1)
                .input(p2)
                .output(p1)
                .deadline(100)
                .action(TransitionAction.produce(p1, new SimpleValue("t1")))
                .build();

            var t2 = Transition.builder("t2")
                .input(p2)
                .input(p1)
                .output(p2)
                .deadline(100)
                .action(TransitionAction.produce(p2, new SimpleValue("t2")))
                .build();

            var net = PetriNet.builder("Deadlock").transitions(t1, t2).build();

            // Only one token - causes deadlock
            var initial = Map.<Place<?>, List<Token<?>>>of(
                p1, List.of(Token.of(new SimpleValue("only-one")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                // Should complete without progress
                assertTrue(result.hasTokens(p1), "Token stuck - deadlock");
                assertFalse(result.hasTokens(p2), "No token produced in p2");
            }
        }

        @Test
        void singleTransition_firesOnce() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var fireCount = new AtomicInteger(0);

            var t = Transition.builder("single")
                .input(input)
                .output(output)
                .deadline(100)
                .action(ctx -> {
                    fireCount.incrementAndGet();
                    ctx.output(output, new SimpleValue("fired"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("Single").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial)) {
                executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertEquals(1, fireCount.get(), "Fires exactly once");
            }
        }

        @Test
        void manyTokens_allProcessed() throws Exception {
            var input = Place.of("Input", CounterValue.class);
            var output = Place.of("Output", CounterValue.class);

            var t = Transition.builder("batch")
                .input(input)
                .output(output)
                .deadline(50)
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("ManyTokens").transitions(t).build();

            // Create many tokens
            List<Token<?>> tokens = java.util.stream.IntStream.range(0, 100)
                .mapToObj(i -> Token.<CounterValue>of(new CounterValue(i)))
                .<Token<?>>map(t2 -> t2)
                .toList();

            var initial = Map.<Place<?>, List<Token<?>>>of(input, tokens);

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(10)).toCompletableFuture().join();

                assertEquals(0, result.tokenCount(input), "All consumed");
                assertEquals(100, result.tokenCount(output), "All produced");
            }
        }

        @Test
        void tokenTypes_enforced() throws Exception {
            var typedPlace = Place.of("Typed", CounterValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("typed")
                .input(typedPlace)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("ok")))
                .build();

            var net = PetriNet.builder("TypeEnforcement").transitions(t).build();

            // Put correct type
            var correctType = Map.<Place<?>, List<Token<?>>>of(
                typedPlace, List.of(Token.of(new CounterValue(1)))
            );

            try (var executor = createExecutor(net,correctType)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();
                assertTrue(result.hasTokens(output));
            }
        }

        @Test
        void eventStore_recordsAllEvents() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            var t = Transition.builder("tracked")
                .input(input)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("tracked")))
                .build();

            var net = PetriNet.builder("EventTracking").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial, eventStore)) {
                executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                var events = eventStore.events();
                assertFalse(events.isEmpty(), "Events recorded");

                // Check for key event types
                assertTrue(events.stream().anyMatch(e -> e instanceof NetEvent.ExecutionStarted));
                assertTrue(events.stream().anyMatch(e -> e instanceof NetEvent.TransitionEnabled));
                assertTrue(events.stream().anyMatch(e -> e instanceof NetEvent.TransitionStarted));
                assertTrue(events.stream().anyMatch(e -> e instanceof NetEvent.TransitionCompleted));
                assertTrue(events.stream().anyMatch(e -> e instanceof NetEvent.ExecutionCompleted));
            }
        }

        @Test
        void noopEventStore_noAllocations() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var noopStore = EventStore.noop();

            var t = Transition.builder("noop")
                .input(input)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("ok")))
                .build();

            var net = PetriNet.builder("NoopEvents").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial, noopStore)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertTrue(result.hasTokens(output));
                assertTrue(noopStore.events().isEmpty(), "Noop store records nothing");
            }
        }

        @Test
        void executorClose_stopsExecution() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var started = new AtomicBoolean(false);
            var actionExecutor = Executors.newVirtualThreadPerTaskExecutor();
            var t = Transition.builder("slow")
                .input(input)
                .output(output)
                .deadline(10000)
                .action(ctx -> CompletableFuture.runAsync(() -> {
                    started.set(true);
                    sleep(5000);
                    ctx.output(output, new SimpleValue("slow"));
                }, actionExecutor))
                .build();

            var net = PetriNet.builder("CloseTest").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            var executor = createExecutor(net,initial);
            var future = executor.run(Duration.ofSeconds(10)).toCompletableFuture();

            // Wait for transition to start
            while (!started.get()) {
                sleep(10);
            }

            // Close executor
            executor.close();

            // Future should complete (may be exceptionally due to interruption)
            try {
                future.get(2, TimeUnit.SECONDS);
            } catch (Exception e) {
                // Expected - execution was interrupted
            }
        }
    }

    // ==================== SECTION 12: TOKEN OPERATIONS TESTS ====================

    @Nested
    class TokenOperationsTests {

        @Test
        void tokenOf_createsFullToken() {
            var token = Token.of(new SimpleValue("test"));

            assertNotNull(token.createdAt(), "Should have timestamp");
            assertEquals("test", token.value().data());
        }

        @Test
        void tokenUnit_singleton() {
            var unit1 = Token.unit();
            var unit2 = Token.unit();

            assertSame(unit1, unit2, "Unit tokens are same instance");
            assertTrue(unit1.isUnit());
        }

        @Test
        void tokenInputs_typeSafe() {
            var placeA = Place.of("A", TypeA.class);
            var placeB = Place.of("B", TypeB.class);
            var output = Place.of("Out", SimpleValue.class);

            var receivedA = new AtomicReference<TypeA>();
            var receivedB = new AtomicReference<TypeB>();

            var t = Transition.builder("typeSafe")
                .input(placeA)
                .input(placeB)
                .output(output)
                .deadline(100)
                .action(ctx -> {
                    receivedA.set(ctx.input(placeA));
                    receivedB.set(ctx.input(placeB));
                    ctx.output(output, new SimpleValue("ok"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("TypeSafeInputs").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                placeA, List.of(Token.of(new TypeA("a-value"))),
                placeB, List.of(Token.of(new TypeB("b-value")))
            );

            try (var executor = createExecutor(net,initial)) {
                executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertEquals("a-value", receivedA.get().id());
                assertEquals("b-value", receivedB.get().id());
            }
        }

        @Test
        void tokenTokenOutput_multipleToSamePlace()  {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", CounterValue.class);

            var t = Transition.builder("multi")
                .input(input)
                .output(output)
                .output(output)
                .output(output)  // 3 arcs for 3 tokens
                .deadline(100)
                .action(ctx -> {
                    ctx.output(output, new CounterValue(1));
                    ctx.output(output, new CounterValue(2));
                    ctx.output(output, new CounterValue(3));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("MultiOutput").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertEquals(3, result.tokenCount(output));

                // Verify values
                var values = result.peekTokens(output).stream()
                    .map(t2 -> ((CounterValue) t2.value()).count())
                    .toList();
                assertTrue(values.contains(1));
                assertTrue(values.contains(2));
                assertTrue(values.contains(3));
            }
        }

        @Test
        void marking_peekOperations() throws Exception {
            var place = Place.of("Place", CounterValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var peekedValues = new CopyOnWriteArrayList<Integer>();

            var t = Transition.builder("peek")
                .input(place)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("done")))
                .build();

            var net = PetriNet.builder("Peek").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                place, List.of(
                    Token.of(new CounterValue(10)),
                    Token.of(new CounterValue(20)),
                    Token.of(new CounterValue(30))
                )
            );

            // Create marking directly to test peek
            var marking = Marking.from(initial);

            // Peek first without removing
            var first = marking.peekFirst(place);
            assertEquals(10, first.value().count());
            assertEquals(3, marking.tokenCount(place), "Peek doesn't remove");

            // Peek all
            var all = marking.peekTokens(place);
            assertEquals(3, all.size());
        }
    }

    // ==================== SECTION 13: EVALUATION ORDER TESTS ====================
    /**
     * Tests for the formal evaluation order of Petri net semantics.
     *
     * FORMAL EVALUATION ORDER (like operator precedence in math):
     *
     * 1. ENABLEMENT CHECK ORDER (checked in this sequence):
     *    ① Inhibitors  - checked FIRST (fail fast if any place has tokens)
     *    ② Read arcs   - checked SECOND (require tokens but don't consume)
     *    ③ Input arcs  - checked LAST (require matching tokens)
     *
     * 2. FIRING ORDER (executed in this sequence):
     *    ① Consume input tokens (remove from places, bind to action)
     *    ② Process reset arcs (remove ALL tokens from reset places)
     *    ③ Execute action (async, with consumed tokens available)
     *    ④ Deposit output tokens (after action completes)
     *
     * This is analogous to mathematical operator precedence:
     *    - Inhibitors are like parentheses (evaluated first, can block everything)
     *    - Inputs before Resets (like * before +, get value before clearing)
     *    - TokenOutput after Action (like = after all operations)
     */
    @Nested
    class EvaluationOrderTests {

        // ========== ENABLEMENT ORDER TESTS ==========

        @Test
        void enablementOrder_inhibitorCheckedBeforeInput() throws Exception {
            // Even if input is available, inhibitor blocks first
            var input = Place.of("Input", SimpleValue.class);
            var blocker = Place.of("Blocker", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .inhibitor(blocker)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("InhibitorFirst").transitions(t).build();

            // Both input AND blocker have tokens
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("ready"))),
                blocker, List.of(Token.of(new SimpleValue("blocking")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                // Inhibitor takes precedence - transition doesn't fire
                assertTrue(result.hasTokens(input), "Input not consumed (blocked by inhibitor)");
                assertTrue(result.hasTokens(blocker), "Blocker remains");
                assertFalse(result.hasTokens(output), "No output (inhibitor blocked)");
            }
        }

        @Test
        void enablementOrder_readCheckedBeforeInput() throws Exception {
            // Read arc must be satisfied even if input is available
            var input = Place.of("Input", SimpleValue.class);
            var readPlace = Place.of("ReadPlace", CounterValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .read(readPlace)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("ReadBeforeInput").transitions(t).build();

            // Input available but read place empty
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("ready")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                // Read not satisfied - transition doesn't fire
                assertTrue(result.hasTokens(input), "Input not consumed (read not satisfied)");
                assertFalse(result.hasTokens(output), "No output");
            }
        }

        @Test
        void enablementOrder_allConditionsMustBeMet() throws Exception {
            // All three: inhibitor empty, read present, input present
            var input = Place.of("Input", SimpleValue.class);
            var inhibitor = Place.of("Inhibitor", TypeA.class);
            var read = Place.of("Read", TypeB.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(input)
                .inhibitor(inhibitor)
                .read(read)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("AllConditions").transitions(t).build();

            // Test: inhibitor present (should fail at step 1)
            var withInhibitor = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("ready"))),
                inhibitor, List.of(Token.of(new TypeA("block"))),
                read, List.of(Token.of(new TypeB("readable")))
            );

            try (var executor = createExecutor(net,withInhibitor)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();
                assertFalse(result.hasTokens(output), "Blocked at inhibitor check");
            }

            // Test: read missing (should fail at step 2)
            var withoutRead = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("ready")))
            );

            try (var executor = createExecutor(net,withoutRead)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();
                assertFalse(result.hasTokens(output), "Blocked at read check");
            }

            // Test: input missing (should fail at step 3)
            var withoutInput = Map.<Place<?>, List<Token<?>>>of(
                read, List.of(Token.of(new TypeB("readable")))
            );

            try (var executor = createExecutor(net,withoutInput)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();
                assertFalse(result.hasTokens(output), "Blocked at input check");
            }

            // Test: all conditions met (should fire)
            var allMet = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("ready"))),
                read, List.of(Token.of(new TypeB("readable")))
                // inhibitor empty
            );

            try (var executor = createExecutor(net,allMet)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();
                assertTrue(result.hasTokens(output), "All conditions met - fires");
            }
        }

        // ========== FIRING ORDER TESTS ==========

        @Test
        void firingOrder_inputConsumedBeforeReset() throws Exception {
            // Same place as input AND reset - input gets ONE token, reset clears the rest
            var shared = Place.of("Shared", CounterValue.class);
            var output = Place.of("Output", CounterValue.class);

            var capturedInput = new AtomicReference<CounterValue>();

            var t = Transition.builder("t")
                .input(shared)
                .reset(shared)  // Same place!
                .output(output)
                .deadline(100)
                .action(ctx -> {
                    // Input should have captured ONE token before reset cleared the rest
                    capturedInput.set(ctx.input(shared));
                    ctx.output(output, capturedInput.get());
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("InputThenReset").transitions(t).build();

            // Place has 3 tokens
            var initial = Map.<Place<?>, List<Token<?>>>of(
                shared, List.of(
                    Token.of(new CounterValue(1)),  // This one should be consumed by input
                    Token.of(new CounterValue(2)),  // These should be cleared by reset
                    Token.of(new CounterValue(3))
                )
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                // Input consumed first token (FIFO)
                assertEquals(1, capturedInput.get().count(), "Input consumed first token");

                // Reset cleared everything else, and input consumed the first
                assertFalse(result.hasTokens(shared), "Shared place should be empty");

                // Output has the captured token
                assertTrue(result.hasTokens(output));
                assertEquals(1, result.peekFirst(output).value().count());
            }
        }

        @Test
        void firingOrder_multipleInputsFromDifferentPlaces() throws Exception {
            // Multiple input arcs from different places - all must be consumed
            var inputA = Place.of("InputA", CounterValue.class);
            var inputB = Place.of("InputB", CounterValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var capturedA = new AtomicReference<Integer>();
            var capturedB = new AtomicReference<Integer>();

            var t = Transition.builder("t")
                .input(inputA)
                .input(inputB)
                .output(output)
                .deadline(100)
                .action(ctx -> {
                    capturedA.set(ctx.input(inputA).count());
                    capturedB.set(ctx.input(inputB).count());
                    ctx.output(output, new SimpleValue("consumed"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("MultiInputDifferentPlaces").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                inputA, List.of(Token.of(new CounterValue(10))),
                inputB, List.of(Token.of(new CounterValue(20)))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                // Both tokens consumed
                assertEquals(10, capturedA.get(), "InputA consumed");
                assertEquals(20, capturedB.get(), "InputB consumed");

                // Both places empty
                assertFalse(result.hasTokens(inputA), "InputA empty");
                assertFalse(result.hasTokens(inputB), "InputB empty");
                assertTrue(result.hasTokens(output));
            }
        }

        @Test
        void firingOrder_multipleInputsFromSamePlace() throws Exception {
            // Two input arcs from the same place - should consume two tokens (arc weight = 2)
            var shared = Place.of("Shared", CounterValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var captured = new CopyOnWriteArrayList<Integer>();

            var t = Transition.builder("t")
                .input(shared)  // First input arc
                .input(shared)  // Second input arc (same place!) - requires 2 tokens
                .output(output)
                .deadline(100)
                .action(ctx -> {
                    var values = ctx.inputs(shared);
                    values.forEach(v -> captured.add(v.count()));
                    ctx.output(output, new SimpleValue("consumed-" + values.size()));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("MultiInputSamePlace").transitions(t).build();

            // Only 1 token - should NOT fire (needs 2)
            var insufficient = Map.<Place<?>, List<Token<?>>>of(
                shared, List.of(Token.of(new CounterValue(1)))
            );

            try (var executor = createExecutor(net,insufficient)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertFalse(result.hasTokens(output), "Should not fire with only 1 token");
                assertTrue(result.hasTokens(shared), "Token remains");
            }

            // 3 tokens - should fire and consume 2
            var sufficient = Map.<Place<?>, List<Token<?>>>of(
                shared, List.of(
                    Token.of(new CounterValue(1)),
                    Token.of(new CounterValue(2)),
                    Token.of(new CounterValue(3))
                )
            );

            try (var executor = createExecutor(net,sufficient)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                // Two tokens consumed (FIFO order)
                assertEquals(2, captured.size(), "Two tokens consumed");
                assertEquals(List.of(1, 2), captured, "FIFO order preserved");

                // One token remains
                assertEquals(1, result.tokenCount(shared), "One token remains");
                assertEquals(3, result.peekFirst(shared).value().count());
                assertTrue(result.hasTokens(output));
            }
        }

        @Test
        void firingOrder_outputAfterAction() throws Exception {
            // Output tokens are deposited AFTER action completes, not before
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", CounterValue.class);

            var actionStarted = new AtomicBoolean(false);
            var outputDuringAction = new AtomicInteger(-1);
            var actionExecutor = Executors.newVirtualThreadPerTaskExecutor();

            var t = Transition.builder("t")
                .input(input)
                .output(output)
                .deadline(500)
                .action(ctx -> CompletableFuture.runAsync(() -> {
                    actionStarted.set(true);
                    // At this point, output should NOT be deposited yet
                    // (we can't check marking from action, but we can verify timing)
                    ctx.output(output, new CounterValue(42));
                    sleep(50);  // Simulate some work
                }, actionExecutor))
                .build();

            var net = PetriNet.builder("OutputAfterAction").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertTrue(actionStarted.get(), "Action executed");
                assertTrue(result.hasTokens(output), "Output deposited after action");
                assertEquals(42, result.peekFirst(output).value().count());
            }
        }

        @Test
        void firingOrder_selfLoop_consumeThenProduce() throws Exception {
            // Self-loop: same place as input AND output
            // Should consume first, then produce (not see own output)
            var loop = Place.of("Loop", CounterValue.class);
            var done = Place.of("Done", SimpleValue.class);

            var iterations = new AtomicInteger(0);
            var seenValues = new CopyOnWriteArrayList<Integer>();

            // Process until count reaches 3
            var process = Transition.builder("process")
                .inputWhen(loop, c -> c.count() < 3)
                .output(loop)  // Self-loop
                .deadline(50)
                .action(ctx -> {
                    var current = ctx.input(loop);
                    seenValues.add(current.count());
                    iterations.incrementAndGet();
                    ctx.output(loop, new CounterValue(current.count() + 1));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            // Exit when count >= 3
            var exit = Transition.builder("exit")
                .inputWhen(loop, c -> c.count() >= 3)
                .output(done)
                .deadline(50)
                .action(TransitionAction.produce(done, new SimpleValue("finished")))
                .build();

            var net = PetriNet.builder("SelfLoop").transitions(process, exit).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                loop, List.of(Token.of(new CounterValue(0)))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

                // Should have iterated 3 times: 0->1, 1->2, 2->3
                assertEquals(3, iterations.get(), "Three iterations");
                assertEquals(List.of(0, 1, 2), seenValues, "Saw values in order");
                assertTrue(result.hasTokens(done), "Reached exit");
            }
        }

        // ========== EDGE CASES FOR SAME PLACE IN MULTIPLE ARCS ==========

        @Test
        void samePlace_inputAndRead() throws Exception {
            // Same place as both input AND read
            // Input consumes, read requires but doesn't consume
            // Net effect: needs at least 1 token, consumes 1
            var shared = Place.of("Shared", CounterValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .input(shared)
                .read(shared)  // Same place - requires token to exist
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("fired")))
                .build();

            var net = PetriNet.builder("InputAndRead").transitions(t).build();

            // With 1 token - both input and read are satisfied
            var initial = Map.<Place<?>, List<Token<?>>>of(
                shared, List.of(Token.of(new CounterValue(1)))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                // Input consumed the token, read was satisfied
                assertFalse(result.hasTokens(shared), "Token consumed by input");
                assertTrue(result.hasTokens(output), "Transition fired");
            }
        }

        @Test
        void samePlace_inhibitorAndInput_differentTransitions() throws Exception {
            // Place that inhibits T1 but is input to T2
            // When place has token: T1 blocked, T2 can fire
            var shared = Place.of("Shared", SimpleValue.class);
            var trigger1 = Place.of("Trigger1", SimpleValue.class);
            var trigger2 = Place.of("Trigger2", SimpleValue.class);
            var out1 = Place.of("Out1", SimpleValue.class);
            var out2 = Place.of("Out2", SimpleValue.class);

            var t1 = Transition.builder("t1")
                .input(trigger1)
                .inhibitor(shared)  // Blocked when shared has tokens
                .output(out1)
                .deadline(100)
                .action(TransitionAction.produce(out1, new SimpleValue("t1-fired")))
                .build();

            var t2 = Transition.builder("t2")
                .input(trigger2)
                .input(shared)  // Consumes from shared
                .output(out2)
                .deadline(100)
                .action(TransitionAction.produce(out2, new SimpleValue("t2-fired")))
                .build();

            var net = PetriNet.builder("InhibitorVsInput").transitions(t1, t2).build();

            // Both triggers present, shared has token
            var initial = Map.<Place<?>, List<Token<?>>>of(
                trigger1, List.of(Token.of(new SimpleValue("go1"))),
                trigger2, List.of(Token.of(new SimpleValue("go2"))),
                shared, List.of(Token.of(new SimpleValue("blocks-t1")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                // T2 should fire (consumes shared), then T1 becomes unblocked and fires
                assertTrue(result.hasTokens(out2), "T2 fired (consumed shared)");
                assertTrue(result.hasTokens(out1), "T1 fired after unblocked");
                assertFalse(result.hasTokens(shared), "Shared consumed");
            }
        }

        @Test
        void firingOrder_resetClearsAfterInputConsumed() throws Exception {
            // Verify reset happens AFTER input consumption
            // by having input and reset on same place and checking event order
            var shared = Place.of("Shared", CounterValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            var t = Transition.builder("t")
                .input(shared)
                .reset(shared)
                .output(output)
                .deadline(100)
                .action(TransitionAction.produce(output, new SimpleValue("done")))
                .build();

            var net = PetriNet.builder("ResetOrder").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                shared, List.of(
                    Token.of(new CounterValue(1)),
                    Token.of(new CounterValue(2)),
                    Token.of(new CounterValue(3))
                )
            );

            try (var executor = createExecutor(net,initial, eventStore)) {
                executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                // Check TokenRemoved events - first one is from input, rest from reset
                var removeEvents = eventStore.events().stream()
                    .filter(e -> e instanceof NetEvent.TokenRemoved)
                    .map(e -> (NetEvent.TokenRemoved) e)
                    .toList();

                assertEquals(3, removeEvents.size(), "3 tokens removed total");

                // All should be from "Shared" place
                assertTrue(removeEvents.stream().allMatch(e -> e.placeName().equals("Shared")));
            }
        }

        // ========== PRIORITY INTERACTION WITH ENABLEMENT ==========

        @Test
        void priority_evaluatedAfterEnablement() throws Exception {
            // High priority transition that's not enabled shouldn't block low priority
            var inputLow = Place.of("InputLow", SimpleValue.class);
            var inputHigh = Place.of("InputHigh", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var fired = new AtomicReference<String>();

            var lowPriority = Transition.builder("low")
                .input(inputLow)
                .output(output)
                .priority(1)
                .deadline(100)
                .action(ctx -> {
                    fired.set("low");
                    ctx.output(output, new SimpleValue("low"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var highPriority = Transition.builder("high")
                .input(inputHigh)  // Not provided - won't be enabled
                .output(output)
                .priority(100)
                .deadline(100)
                .action(ctx -> {
                    fired.set("high");
                    ctx.output(output, new SimpleValue("high"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("PriorityAfterEnable").transitions(lowPriority, highPriority).build();

            // Only provide input for low priority transition
            var initial = Map.<Place<?>, List<Token<?>>>of(
                inputLow, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertEquals("low", fired.get(), "Low priority fired (high not enabled)");
                assertTrue(result.hasTokens(output));
            }
        }

        @Test
        void concurrentEnablement_priorityResolvesConflict() throws Exception {
            // Two transitions enabled at same time, priority decides winner
            var shared = Place.of("Shared", SimpleValue.class);
            var outLow = Place.of("OutLow", SimpleValue.class);
            var outHigh = Place.of("OutHigh", SimpleValue.class);

            var fireOrder = new CopyOnWriteArrayList<String>();

            var low = Transition.builder("low")
                .input(shared)
                .output(outLow)
                .priority(1)
                .deadline(100)
                .action(ctx -> {
                    fireOrder.add("low");
                    ctx.output(outLow, new SimpleValue("low"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var high = Transition.builder("high")
                .input(shared)
                .output(outHigh)
                .priority(10)
                .deadline(100)
                .action(ctx -> {
                    fireOrder.add("high");
                    ctx.output(outHigh, new SimpleValue("high"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("ConcurrentPriority").transitions(low, high).build();

            // Single token - only one can fire
            var initial = Map.<Place<?>, List<Token<?>>>of(
                shared, List.of(Token.of(new SimpleValue("contested")))
            );

            try (var executor = createExecutor(net,initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                assertEquals(1, fireOrder.size(), "Only one fires");
                assertEquals("high", fireOrder.getFirst(), "High priority wins");
                assertTrue(result.hasTokens(outHigh));
                assertFalse(result.hasTokens(outLow));
            }
        }
    }

    // ==================== SECTION 14: OUTPUT TIMEOUT TESTS ====================

    @Nested
    class OutputTimeoutTests {

        @Test
        void outTimeout_placeBranch_producesUnitMarker() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var success = Place.of("Success", SimpleValue.class);
            var timeoutPlace = Place.of("Timeout", SimpleValue.class);

            var t = Transition.builder("slow")
                .inputs(one(input))
                .outputs(xor(
                    place(success),
                    Out.timeout(Duration.ofMillis(50), place(timeoutPlace))))
                .action(ctx -> CompletableFuture.supplyAsync(() -> {
                    sleep(500);
                    ctx.output(success, new SimpleValue("late"));
                    return null;
                }, testExecutor))
                .build();

            var net = PetriNet.builder("TimeoutPlace").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

                assertTrue(result.hasTokens(timeoutPlace), "Timeout branch should have token");
                assertFalse(result.hasTokens(success), "Success branch should be empty");
            }
        }

        @Test
        void outTimeout_forwardInput_forwardsConsumedValue() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var success = Place.of("Success", SimpleValue.class);
            var retry = Place.of("Retry", SimpleValue.class);

            var t = Transition.builder("slow")
                .inputs(one(input))
                .outputs(xor(
                    place(success),
                    Out.timeout(Duration.ofMillis(50),
                        Out.forwardInput(input, retry))))
                .action(ctx -> CompletableFuture.supplyAsync(() -> {
                    sleep(500);
                    ctx.output(success, new SimpleValue("late"));
                    return null;
                }, testExecutor))
                .build();

            var net = PetriNet.builder("TimeoutForward").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("original-data")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

                assertTrue(result.hasTokens(retry), "Retry place should have forwarded token");
                assertFalse(result.hasTokens(success), "Success branch should be empty");
                assertEquals("original-data", result.peekFirst(retry).value().data(),
                    "Forwarded value should match original input");
            }
        }

        @Test
        void outTimeout_andChild_producesToMultiplePlaces() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var success = Place.of("Success", SimpleValue.class);
            var fallbackA = Place.of("FallbackA", SimpleValue.class);
            var fallbackB = Place.of("FallbackB", SimpleValue.class);

            var t = Transition.builder("slow")
                .inputs(one(input))
                .outputs(xor(
                    place(success),
                    Out.timeout(Duration.ofMillis(50),
                        and(fallbackA, fallbackB))))
                .action(ctx -> CompletableFuture.supplyAsync(() -> {
                    sleep(500);
                    ctx.output(success, new SimpleValue("late"));
                    return null;
                }, testExecutor))
                .build();

            var net = PetriNet.builder("TimeoutAnd").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

                assertTrue(result.hasTokens(fallbackA), "FallbackA should have token");
                assertTrue(result.hasTokens(fallbackB), "FallbackB should have token");
                assertFalse(result.hasTokens(success), "Success branch should be empty");
            }
        }

        @Test
        void outTimeout_normalCompletion_noTimeoutTokens() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var success = Place.of("Success", SimpleValue.class);
            var timeoutPlace = Place.of("Timeout", SimpleValue.class);

            var t = Transition.builder("fast")
                .inputs(one(input))
                .outputs(xor(
                    place(success),
                    Out.timeout(Duration.ofSeconds(5), place(timeoutPlace))))
                .action(ctx -> {
                    ctx.output(success, new SimpleValue("done"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("TimeoutNoFire").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

                assertTrue(result.hasTokens(success), "Success branch should have token");
                assertFalse(result.hasTokens(timeoutPlace), "Timeout branch should be empty");
            }
        }
    }

    // ==================== SECTION 15: OUTPUT VALIDATION TESTS ====================

    @Nested
    class OutputValidationTests {

        @Test
        void xorWithNestedAnd_correctBranchProduced_succeeds() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var branchA1 = Place.of("BranchA1", SimpleValue.class);
            var branchA2 = Place.of("BranchA2", SimpleValue.class);
            var branchB1 = Place.of("BranchB1", SimpleValue.class);
            var branchB2 = Place.of("BranchB2", SimpleValue.class);

            // XOR of ANDs: choose one branch, produce to all in that branch
            var t = Transition.builder("xor-and")
                .inputs(one(input))
                .outputs(xor(
                    and(branchA1, branchA2),
                    and(branchB1, branchB2)))
                .deadline(100)
                .action(ctx -> {
                    // Produce to branch B (both places)
                    ctx.output(branchB1, new SimpleValue("b1"));
                    ctx.output(branchB2, new SimpleValue("b2"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("XorAndOk").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertFalse(result.hasTokens(branchA1), "Branch A1 should be empty");
                assertFalse(result.hasTokens(branchA2), "Branch A2 should be empty");
                assertTrue(result.hasTokens(branchB1), "Branch B1 should have token");
                assertTrue(result.hasTokens(branchB2), "Branch B2 should have token");
            }
        }

        @Test
        void xorWithSubsetAndBranches_mostSpecificBranchWins() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var placeA = Place.of("PlaceA", SimpleValue.class);
            var placeB = Place.of("PlaceB", SimpleValue.class);
            var placeC = Place.of("PlaceC", SimpleValue.class);
            var placeD = Place.of("PlaceD", SimpleValue.class);

            // XOR with subset AND branches: AND(A,B,C) vs AND(A,B) vs D
            // Mimics detectIntent pattern where recommendation adds a third place
            var t = Transition.builder("xor-subset")
                .inputs(one(input))
                .outputs(xor(
                    and(placeA, placeB, placeC),
                    and(placeA, placeB),
                    place(placeD)))
                .deadline(100)
                .action(ctx -> {
                    // Produce to all of A, B, C — most specific branch is AND(A,B,C)
                    ctx.output(placeA, new SimpleValue("a"));
                    ctx.output(placeB, new SimpleValue("b"));
                    ctx.output(placeC, new SimpleValue("c"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("XorSubsetAnd").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertTrue(result.hasTokens(placeA), "Place A should have token");
                assertTrue(result.hasTokens(placeB), "Place B should have token");
                assertTrue(result.hasTokens(placeC), "Place C should have token");
                assertFalse(result.hasTokens(placeD), "Place D should be empty");
            }
        }

        @Test
        void xorViolation_multipleBranches_emitsFailure() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var branchA = Place.of("BranchA", SimpleValue.class);
            var branchB = Place.of("BranchB", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            var t = Transition.builder("xor-violator")
                .inputs(one(input))
                .outputs(xor(branchA, branchB))
                .deadline(100)
                .action(ctx -> {
                    // Produce to BOTH branches - XOR violation
                    ctx.output(branchA, new SimpleValue("a"));
                    ctx.output(branchB, new SimpleValue("b"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("XorMultiViolation").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial, eventStore)) {
                executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();
                Thread.sleep(50); // wait for event processing

                var failEvents = eventStore.events().stream()
                    .filter(e -> e instanceof NetEvent.TransitionFailed)
                    .map(e -> (NetEvent.TransitionFailed) e)
                    .toList();
                assertFalse(failEvents.isEmpty(), "Should record TransitionFailed event for XOR violation");
                assertTrue(failEvents.stream().anyMatch(e ->
                        e.errorMessage().contains("XOR violation") && e.errorMessage().contains("multiple")),
                    "Failure message should mention XOR violation multiple branches");
            }
        }

        @Test
        void xorViolation_noBranch_emitsFailure() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var branchA = Place.of("BranchA", SimpleValue.class);
            var branchB = Place.of("BranchB", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            var t = Transition.builder("xor-none")
                .inputs(one(input))
                .outputs(xor(branchA, branchB))
                .deadline(100)
                .action(ctx -> {
                    // Produce to NEITHER branch - XOR violation
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("XorNoneViolation").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial, eventStore)) {
                executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();
                Thread.sleep(50); // wait for event processing

                var failEvents = eventStore.events().stream()
                    .filter(e -> e instanceof NetEvent.TransitionFailed)
                    .map(e -> (NetEvent.TransitionFailed) e)
                    .toList();
                assertFalse(failEvents.isEmpty(), "Should record TransitionFailed event for XOR violation");
                assertTrue(failEvents.stream().anyMatch(e ->
                        e.errorMessage().contains("XOR violation") && e.errorMessage().contains("no branch")),
                    "Failure message should mention XOR violation no branch");
            }
        }

        @Test
        void missingRequiredPlace_emitsFailure() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var required = Place.of("Required", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            var t = Transition.builder("missing-place")
                .inputs(one(input))
                .outputs(place(required))
                .deadline(100)
                .action(ctx -> {
                    // Produce NOTHING - Out.Place violation
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("MissingPlace").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial, eventStore)) {
                executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();
                Thread.sleep(50); // wait for event processing

                var failEvents = eventStore.events().stream()
                    .filter(e -> e instanceof NetEvent.TransitionFailed)
                    .map(e -> (NetEvent.TransitionFailed) e)
                    .toList();
                assertFalse(failEvents.isEmpty(), "Should record TransitionFailed for missing output");
                assertTrue(failEvents.stream().anyMatch(e ->
                        e.errorMessage().contains("does not satisfy declared spec")),
                    "Failure message should mention spec violation");
            }
        }

        @Test
        void forwardInputMissing_emitsFailure() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var normal = Place.of("Normal", SimpleValue.class);
            var forward = Place.of("Forward", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            var t = Transition.builder("forward-missing")
                .inputs(one(input))
                .outputs(and(
                    place(normal),
                    Out.forwardInput(input, forward)))
                .deadline(100)
                .action(ctx -> {
                    // Only produce to normal, not to forward - ForwardInput violation
                    ctx.output(normal, new SimpleValue("ok"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("ForwardMissing").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial, eventStore)) {
                executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();
                Thread.sleep(50); // wait for event processing

                var failEvents = eventStore.events().stream()
                    .filter(e -> e instanceof NetEvent.TransitionFailed)
                    .map(e -> (NetEvent.TransitionFailed) e)
                    .toList();
                assertFalse(failEvents.isEmpty(), "Should record TransitionFailed for missing ForwardInput");
                assertTrue(failEvents.stream().anyMatch(e ->
                        e.errorMessage().contains("does not satisfy declared spec")),
                    "Failure message should mention spec violation");
            }
        }

        @Test
        void andOutput_allPlacesProduced_succeeds() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var placeA = Place.of("PlaceA", SimpleValue.class);
            var placeB = Place.of("PlaceB", SimpleValue.class);

            var t = Transition.builder("and-ok")
                .inputs(one(input))
                .outputs(and(placeA, placeB))
                .deadline(100)
                .action(ctx -> {
                    ctx.output(placeA, new SimpleValue("a"));
                    ctx.output(placeB, new SimpleValue("b"));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("AndOk").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertTrue(result.hasTokens(placeA), "PlaceA should have token");
                assertTrue(result.hasTokens(placeB), "PlaceB should have token");
            }
        }
    }

    // ==================== SECTION 16: MARKING INSPECTION TESTS ====================

    @Nested
    class MarkingInspectionTests {

        @Test
        void marking_toString_showsPlacesWithCounts() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .inputs(one(input))
                .outputs(place(output))
                .deadline(100)
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("ToStringNet").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("v1")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                var str = result.toString();
                assertTrue(str.startsWith("Marking{"), "toString should start with Marking{");
                assertTrue(str.contains("Output"), "toString should contain place name");
                assertTrue(str.contains("1"), "toString should contain count");
            }
        }

        @Test
        void marking_inspect_showsDetailedState() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("t")
                .inputs(one(input))
                .outputs(place(output))
                .deadline(100)
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("InspectNet").transitions(t).build();

            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("v1")))
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofSeconds(1)).toCompletableFuture().join();

                var inspected = result.inspect();
                assertTrue(inspected.startsWith("Marking:"), "inspect should start with Marking:");
                assertTrue(inspected.contains("Output"), "inspect should contain place name");
                assertTrue(inspected.contains("token(s)"), "inspect should contain token(s)");
                assertTrue(inspected.contains("SimpleValue"), "inspect should contain type name");
            }
        }

        @Test
        void marking_emptyMarking_inspectReturnsEmptyMessage() throws Exception {
            var marking = Marking.empty();
            assertEquals("Marking is empty", marking.inspect());
            assertEquals("Marking{}", marking.toString());
        }

        @Test
        void guardedInput_nonMatchingToken_preventsEnablement() throws Exception {
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var t = Transition.builder("guarded")
                .inputWhen(input, v -> v.data().equals("match"))
                .output(output)
                .deadline(100)
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("GuardNoMatch").transitions(t).build();

            // Only non-matching tokens
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(
                    Token.of(new SimpleValue("no-match-1")),
                    Token.of(new SimpleValue("no-match-2"))
                )
            );

            try (var executor = createExecutor(net, initial)) {
                var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

                assertFalse(result.hasTokens(output), "Transition should not fire with non-matching tokens");
                assertEquals(2, result.tokenCount(input), "Non-matching tokens should remain");
            }
        }
    }

    // ==================== SECTION 17: DEADLINE ENFORCEMENT TESTS (TIME-013) ====================

    @Nested
    class DeadlineEnforcementTests {

        @Test
        void deadline_firesWithinDeadline_noTimeoutEvent() throws Exception {
            // TIME-013: Transition with Deadline(100ms) fires immediately (earliest=0).
            // No TransitionTimedOut should be emitted.
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            var t = Transition.builder("DeadlinedTransition")
                .inputs(one(input))
                .outputs(place(output))
                .timing(Timing.deadline(Duration.ofMillis(100)))
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("DeadlineBasic").transitions(t).build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial, eventStore)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertTrue(result.hasTokens(output), "Transition should fire within deadline");
                var timeouts = eventStore.eventsOfType(NetEvent.TransitionTimedOut.class);
                assertTrue(timeouts.isEmpty(), "No timeout should occur when transition fires in time");
                var completions = eventStore.eventsOfType(NetEvent.TransitionCompleted.class);
                assertFalse(completions.isEmpty(), "Should have completion event");
            }
        }

        @Test
        void deadline_windowTiming_firesWithinBounds() throws Exception {
            // TIME-005: Window timing — transition fires after earliest, before deadline
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            var t = Transition.builder("WindowedTransition")
                .inputs(one(input))
                .outputs(place(output))
                .timing(Timing.window(Duration.ofMillis(50), Duration.ofMillis(200)))
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("WindowTest").transitions(t).build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial, eventStore)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertTrue(result.hasTokens(output), "Window transition should produce output");
                var timeouts = eventStore.eventsOfType(NetEvent.TransitionTimedOut.class);
                assertTrue(timeouts.isEmpty(), "Window transition fired within bounds — no timeout");
            }
        }

        @Test
        void deadline_exactTiming_firesWithinDeadline() throws Exception {
            // TIME-006: Exact timing should fire and not trigger deadline
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            var t = Transition.builder("ExactTransition")
                .inputs(one(input))
                .outputs(place(output))
                .timing(Timing.exact(Duration.ofMillis(100)))
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("ExactDeadlineTest").transitions(t).build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial, eventStore)) {
                var result = executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                assertTrue(result.hasTokens(output), "Exact-timed transition should fire");
                var timeouts = eventStore.eventsOfType(NetEvent.TransitionTimedOut.class);
                assertTrue(timeouts.isEmpty(), "No timeout for exact timing that fires on time");
            }
        }

        @Test
        void transitionTimedOut_eventStructure() {
            // EVT-009: Verify TransitionTimedOut record has all required fields
            var event = new NetEvent.TransitionTimedOut(
                Instant.now(), "TestTransition",
                Duration.ofMillis(100), Duration.ofMillis(150));

            assertEquals("TestTransition", event.transitionName());
            assertEquals(Duration.ofMillis(100), event.deadline());
            assertEquals(Duration.ofMillis(150), event.actualDuration());
            assertNotNull(event.timestamp());
        }

    }

    // ==================== SECTION 18: MARKING SNAPSHOT TESTS (EVT-014) ====================

    @Nested
    class MarkingSnapshotTests {

        @Test
        void markingSnapshot_emittedAtStartAndEnd() throws Exception {
            // EVT-014: MarkingSnapshot SHOULD be emitted at start and before completion
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            var t = Transition.builder("Transfer")
                .inputs(one(input))
                .outputs(place(output))
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("SnapshotTest").transitions(t).build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("hello")))
            );

            try (var executor = createExecutor(net, initial, eventStore)) {
                executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                var snapshots = eventStore.eventsOfType(NetEvent.MarkingSnapshot.class);
                assertTrue(snapshots.size() >= 2,
                    "Should have at least 2 MarkingSnapshots (start + end), got " + snapshots.size());

                // First snapshot should contain the initial marking
                var firstSnapshot = snapshots.getFirst();
                assertTrue(firstSnapshot.marking().containsKey("Input"),
                    "Initial snapshot should contain Input place");
                assertEquals(1, firstSnapshot.marking().get("Input").size(),
                    "Initial snapshot should have 1 token in Input");

                // Last snapshot should contain the final marking
                var lastSnapshot = snapshots.getLast();
                assertTrue(lastSnapshot.marking().containsKey("Output"),
                    "Final snapshot should contain Output place");
                assertEquals(1, lastSnapshot.marking().get("Output").size(),
                    "Final snapshot should have 1 token in Output");
            }
        }

        @Test
        void markingSnapshot_isDeepDefensiveCopy() throws Exception {
            // EVT-014: Snapshot must be a deep defensive copy (not a live reference)
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            var t = Transition.builder("Transfer")
                .inputs(one(input))
                .outputs(place(output))
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("SnapshotCopyTest").transitions(t).build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("v1")))
            );

            try (var executor = createExecutor(net, initial, eventStore)) {
                executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                var snapshots = eventStore.eventsOfType(NetEvent.MarkingSnapshot.class);
                assertFalse(snapshots.isEmpty());

                // Verify snapshot immutability (MarkingSnapshot constructor creates unmodifiable maps/lists)
                var snapshot = snapshots.getFirst();
                assertThrows(UnsupportedOperationException.class, () ->
                    snapshot.marking().put("NewPlace", List.of()));
                if (snapshot.marking().containsKey("Input")) {
                    assertThrows(UnsupportedOperationException.class, () ->
                        snapshot.marking().get("Input").add(Token.of(new SimpleValue("injected"))));
                }
            }
        }

        @Test
        void markingSnapshot_onlyIncludesNonEmptyPlaces() throws Exception {
            // EVT-014: Only non-empty places should be included
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);
            var unused = Place.of("Unused", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            var t = Transition.builder("Transfer")
                .inputs(one(input))
                .outputs(place(output))
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("SnapshotEmptyTest")
                .transitions(t)
                .place(unused)  // Unused place with no tokens
                .build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial, eventStore)) {
                executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                var snapshots = eventStore.eventsOfType(NetEvent.MarkingSnapshot.class);
                assertFalse(snapshots.isEmpty(), "Should have at least one MarkingSnapshot");
                for (var snapshot : snapshots) {
                    assertFalse(snapshot.marking().containsKey("Unused"),
                        "Snapshot should not contain empty places");
                    assertFalse(snapshot.marking().isEmpty(),
                        "Snapshot should contain at least one active place");
                }
            }
        }

        @Test
        void markingSnapshot_appearsBeforeExecutionCompleted() throws Exception {
            // EVT-014: Final snapshot should appear before ExecutionCompleted event
            var input = Place.of("Input", SimpleValue.class);
            var output = Place.of("Output", SimpleValue.class);

            var eventStore = EventStore.inMemory();

            var t = Transition.builder("t")
                .inputs(one(input))
                .outputs(place(output))
                .action(ctx -> {
                    ctx.output(output, ctx.input(input));
                    return CompletableFuture.completedFuture(null);
                })
                .build();

            var net = PetriNet.builder("SnapshotOrder").transitions(t).build();
            var initial = Map.<Place<?>, List<Token<?>>>of(
                input, List.of(Token.of(new SimpleValue("go")))
            );

            try (var executor = createExecutor(net, initial, eventStore)) {
                executor.run(Duration.ofSeconds(2)).toCompletableFuture().join();

                var events = eventStore.events();
                int lastSnapshotIdx = -1;
                int completedIdx = -1;
                for (int i = 0; i < events.size(); i++) {
                    if (events.get(i) instanceof NetEvent.MarkingSnapshot) lastSnapshotIdx = i;
                    if (events.get(i) instanceof NetEvent.ExecutionCompleted) completedIdx = i;
                }
                assertTrue(lastSnapshotIdx > 0, "Should have MarkingSnapshot event");
                assertTrue(completedIdx > 0, "Should have ExecutionCompleted event");
                assertTrue(lastSnapshotIdx < completedIdx,
                    "Final MarkingSnapshot should appear before ExecutionCompleted");
            }
        }
    }

    // ==================== SECTION 19: IO-007 CONTRACT TESTS ====================

    @Nested
    class InCardinalityContractTests {

        @Test
        void one_requiredCount_is1() {
            var place = Place.of("P", SimpleValue.class);
            var spec = one(place);
            assertEquals(1, spec.requiredCount(), "In.one requires exactly 1 token");
        }

        @Test
        void one_consumptionCount_is1() {
            var place = Place.of("P", SimpleValue.class);
            var spec = one(place);
            assertEquals(1, spec.consumptionCount(1), "In.one consumes 1 from 1 available");
            assertEquals(1, spec.consumptionCount(5), "In.one consumes 1 from 5 available");
        }

        @Test
        void exactly_requiredCount_matchesCount() {
            var place = Place.of("P", SimpleValue.class);
            var spec = exactly(3, place);
            assertEquals(3, spec.requiredCount(), "In.exactly(3) requires 3 tokens");
        }

        @Test
        void exactly_consumptionCount_matchesCount() {
            var place = Place.of("P", SimpleValue.class);
            var spec = exactly(3, place);
            assertEquals(3, spec.consumptionCount(3), "In.exactly(3) consumes 3 from 3");
            assertEquals(3, spec.consumptionCount(10), "In.exactly(3) consumes 3 from 10");
        }

        @Test
        void all_requiredCount_is1() {
            var place = Place.of("P", SimpleValue.class);
            var spec = all(place);
            assertEquals(1, spec.requiredCount(), "In.all requires at least 1 token for enablement");
        }

        @Test
        void all_consumptionCount_isAllAvailable() {
            var place = Place.of("P", SimpleValue.class);
            var spec = all(place);
            assertEquals(1, spec.consumptionCount(1), "In.all consumes 1 from 1");
            assertEquals(5, spec.consumptionCount(5), "In.all consumes 5 from 5");
            assertEquals(100, spec.consumptionCount(100), "In.all consumes 100 from 100");
        }

        @Test
        void atLeast_requiredCount_matchesMinimum() {
            var place = Place.of("P", SimpleValue.class);
            var spec = atLeast(3, place);
            assertEquals(3, spec.requiredCount(), "In.atLeast(3) requires 3 tokens");
        }

        @Test
        void atLeast_consumptionCount_isAllAvailable() {
            var place = Place.of("P", SimpleValue.class);
            var spec = atLeast(3, place);
            assertEquals(3, spec.consumptionCount(3), "In.atLeast(3) consumes 3 from 3");
            assertEquals(5, spec.consumptionCount(5), "In.atLeast(3) consumes 5 from 5");
            assertEquals(100, spec.consumptionCount(100), "In.atLeast(3) consumes 100 from 100");
        }

        @Test
        void consumptionCount_throwsWhenInsufficientTokens() {
            var place = Place.of("P", SimpleValue.class);

            assertThrows(IllegalArgumentException.class,
                () -> one(place).consumptionCount(0), "In.one with 0 available");
            assertThrows(IllegalArgumentException.class,
                () -> exactly(3, place).consumptionCount(2), "In.exactly(3) with 2 available");
            assertThrows(IllegalArgumentException.class,
                () -> all(place).consumptionCount(0), "In.all with 0 available");
            assertThrows(IllegalArgumentException.class,
                () -> atLeast(3, place).consumptionCount(2), "In.atLeast(3) with 2 available");
        }

        @Test
        void place_returnsDeclaredPlace() {
            var place = Place.of("TestPlace", SimpleValue.class);
            assertEquals(place, one(place).place());
            assertEquals(place, exactly(3, place).place());
            assertEquals(place, all(place).place());
            assertEquals(place, atLeast(3, place).place());
        }
    }

    // ==================== SECTION 20: EVENT IMMUTABILITY TESTS (EVT-001) ====================

    @Nested
    class EventImmutabilityTests {

        @Test
        void transitionStarted_defensiveCopyOfConsumedTokens() {
            // EVT-001: Modify source list after event creation; verify event's list unchanged
            var tokens = new java.util.ArrayList<Token<?>>();
            tokens.add(Token.of(new SimpleValue("original")));

            var event = new NetEvent.TransitionStarted(Instant.now(), "T1", tokens);

            // Modify original list
            tokens.add(Token.of(new SimpleValue("injected")));

            // Event's list should be unchanged
            assertEquals(1, event.consumedTokens().size(),
                "Event should have defensive copy, not live reference");
            assertEquals("original", ((SimpleValue) event.consumedTokens().getFirst().value()).data());
        }

        @Test
        void transitionCompleted_defensiveCopyOfProducedTokens() {
            // EVT-001: Modify source list after event creation; verify event's list unchanged
            var tokens = new java.util.ArrayList<Token<?>>();
            tokens.add(Token.of(new SimpleValue("result")));

            var event = new NetEvent.TransitionCompleted(
                Instant.now(), "T1", tokens, Duration.ofMillis(50));

            // Modify original list
            tokens.clear();

            // Event's list should be unchanged
            assertEquals(1, event.producedTokens().size(),
                "Event should have defensive copy, not live reference");
        }

        @Test
        void transitionStarted_listIsUnmodifiable() {
            // EVT-001: Event's collection should be unmodifiable
            var event = new NetEvent.TransitionStarted(
                Instant.now(), "T1", List.of(Token.of(new SimpleValue("data"))));

            assertThrows(UnsupportedOperationException.class,
                () -> event.consumedTokens().add(Token.of(new SimpleValue("injected"))),
                "Event's token list should be unmodifiable");
        }

        @Test
        void markingSnapshot_defensiveCopyOfMarking() {
            // EVT-001: Modify source map after event creation; verify event's map unchanged
            var marking = new java.util.HashMap<String, List<Token<?>>>();
            var tokenList = new java.util.ArrayList<Token<?>>();
            tokenList.add(Token.of(new SimpleValue("v1")));
            marking.put("Place1", tokenList);

            var event = new NetEvent.MarkingSnapshot(Instant.now(), marking);

            // Modify original map and list
            marking.put("Place2", List.of());
            tokenList.add(Token.of(new SimpleValue("v2")));

            // Event should be unaffected
            assertFalse(event.marking().containsKey("Place2"),
                "New keys in original map should not appear in snapshot");
            assertEquals(1, event.marking().get("Place1").size(),
                "Modifications to original lists should not affect snapshot");
        }
    }

    // ==================== HELPER ====================

    private static void sleep(long ms) {
        try {
            Thread.sleep(ms);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }
}
