package org.libpetri.runtime;

import org.libpetri.core.*;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Stress test for thread safety of token passing.
 *
 * The key insight: if outputs weren't properly synchronized between
 * action threads and the orchestrator, tokens would be lost when
 * multiple transitions fire concurrently.
 * This test creates many parallel transitions and verifies every
 * single token arrives.
 */
@Timeout(30)  // Fail fast if hanging
class ThreadSafetyStressTest {

    private final ExecutorService actionExecutor = Executors.newVirtualThreadPerTaskExecutor();

    record Counter(int id) {}

    @Test
    void allTokensMustArrive_manyParallelTransitions() throws Exception {
        // Setup: N input tokens fire N parallel transitions, each producing 1 output
        final int N = 1000;

        var input = Place.of("Input", Counter.class);
        var output = Place.of("Output", Counter.class);

        var fired = new AtomicInteger(0);

        var t = Transition.builder("Process")
            .input(input)
            .output(output)
            .deadline(5000)
            .action(ctx -> CompletableFuture.runAsync(() -> {
                var c = ctx.input(input);
                fired.incrementAndGet();
                // Small delay to increase chance of concurrent execution
                try { Thread.sleep(1); } catch (InterruptedException e) {}
                ctx.output(output, new Counter(c.id * 10));
            }, actionExecutor))
            .build();

        var net = PetriNet.builder("Stress").transitions(t).build();

        // Create N input tokens
        List<Token<?>> inputs = new ArrayList<>();
        for (int i = 0; i < N; i++) {
            inputs.add(Token.of(new Counter(i)));
        }

        var initial = Map.<Place<?>, List<Token<?>>>of(input, inputs);

        try (var executor = NetExecutor.create(net, initial)) {
            var result = executor.run(Duration.ofSeconds(10)).toCompletableFuture().join();

            assertEquals(N, fired.get(), "All transitions should have fired");
            assertEquals(N, result.tokenCount(output),
                "All " + N + " output tokens must arrive - race condition if less!");

            // Verify all values are correct (no corruption)
            var outputs = result.peekTokens(output);
            var ids = outputs.stream().map(tok -> tok.value().id()).sorted().toList();
            for (int i = 0; i < N; i++) {
                assertEquals(i * 10, ids.get(i), "Token " + i + " should have value " + (i * 10));
            }
        }
    }

    @Test
    void allTokensMustArrive_multipleTokenOutputPerTransition() throws Exception {
        // Each transition produces 3 tokens - tests slot allocation
        final int N = 500;
        final int OUTPUTS_PER_TRANSITION = 3;

        var input = Place.of("Input", Counter.class);
        var output = Place.of("Output", Counter.class);

        var t = Transition.builder("MultiOutput")
            .input(input)
            .output(output)
            .output(output)
            .output(output)  // 3 output arcs
            .deadline(5000)
            .action(ctx -> CompletableFuture.runAsync(() -> {
                var c = ctx.input(input);
                ctx.output(output, new Counter(c.id * 100));
                ctx.output(output, new Counter(c.id * 100 + 1));
                ctx.output(output, new Counter(c.id * 100 + 2));
            }, actionExecutor))
            .build();

        var net = PetriNet.builder("MultiStress").transitions(t).build();

        List<Token<?>> inputs = new ArrayList<>();
        for (int i = 0; i < N; i++) {
            inputs.add(Token.of(new Counter(i)));
        }

        var initial = Map.<Place<?>, List<Token<?>>>of(input, inputs);

        try (var executor = NetExecutor.create(net, initial)) {
            var result = executor.run(Duration.ofSeconds(10)).toCompletableFuture().join();

            int expected = N * OUTPUTS_PER_TRANSITION;
            assertEquals(expected, result.tokenCount(output),
                "Expected " + expected + " tokens (" + N + " x " + OUTPUTS_PER_TRANSITION + ")");
        }
    }

    @Test
    void chainedTransitions_noTokenLoss() throws Exception {
        // A -> B -> C chain, each step must preserve count
        final int N = 200;

        var placeA = Place.of("A", Counter.class);
        var placeB = Place.of("B", Counter.class);
        var placeC = Place.of("C", Counter.class);

        var t1 = Transition.builder("A->B")
            .input(placeA)
            .output(placeB)
            .deadline(5000)
            .action(ctx -> CompletableFuture.runAsync(() -> {
                ctx.output(placeB, new Counter(ctx.input(placeA).id + 1));
            }, actionExecutor))
            .build();

        var t2 = Transition.builder("B->C")
            .input(placeB)
            .output(placeC)
            .deadline(5000)
            .action(ctx -> CompletableFuture.runAsync(() -> {
                ctx.output(placeC, new Counter(ctx.input(placeB).id + 1));
            }, actionExecutor))
            .build();

        var net = PetriNet.builder("Chain").transitions(t1, t2).build();

        List<Token<?>> inputs = new ArrayList<>();
        for (int i = 0; i < N; i++) {
            inputs.add(Token.of(new Counter(i)));
        }

        var initial = Map.<Place<?>, List<Token<?>>>of(placeA, inputs);

        try (var executor = NetExecutor.create(net, initial)) {
            var result = executor.run(Duration.ofSeconds(10)).toCompletableFuture().join();

            assertEquals(0, result.tokenCount(placeA), "All tokens should leave A");
            assertEquals(0, result.tokenCount(placeB), "All tokens should leave B");
            assertEquals(N, result.tokenCount(placeC), "All " + N + " tokens must arrive at C");

            // Verify values: each went through +1 twice
            var outputs = result.peekTokens(placeC);
            var ids = outputs.stream().map(tok -> tok.value().id()).sorted().toList();
            for (int i = 0; i < N; i++) {
                assertEquals(i + 2, ids.get(i));
            }
        }
    }

    @Test
    void readArc_tokenNotConsumed() throws Exception {
        // Read arc should provide token but NOT consume it
        final int N = 100;

        var input = Place.of("Input", Counter.class);
        var config = Place.of("Config", Counter.class);  // read-only
        var output = Place.of("Output", Counter.class);

        var configValue = new AtomicInteger(0);

        var t = Transition.builder("ReadConfig")
            .input(input)
            .read(config)  // Read but don't consume
            .output(output)
            .deadline(5000)
            .action(ctx -> CompletableFuture.runAsync(() -> {
                var c = ctx.input(input);
                var cfg = ctx.read(config);
                configValue.addAndGet(cfg.id);  // Accumulate to verify all reads see it
                ctx.output(output, new Counter(c.id + cfg.id));
            }, actionExecutor))
            .build();

        var net = PetriNet.builder("ReadTest").transitions(t).build();

        List<Token<?>> inputs = new ArrayList<>();
        for (int i = 0; i < N; i++) {
            inputs.add(Token.of(new Counter(i)));
        }

        var initial = Map.<Place<?>, List<Token<?>>>of(
            input, inputs,
            config, List.of(Token.of(new Counter(42)))  // Single config token
        );

        try (var executor = NetExecutor.create(net, initial)) {
            var result = executor.run(Duration.ofSeconds(10)).toCompletableFuture().join();

            // Config token should still be there (not consumed)
            assertEquals(1, result.tokenCount(config), "Config token should NOT be consumed by read arc");
            assertEquals(N, result.tokenCount(output), "All outputs should arrive");

            // All transitions should have read config value 42
            assertEquals(N * 42, configValue.get(), "All " + N + " transitions should read config=42");
        }
    }

    @Test
    void resetArc_clearsPlace() throws Exception {
        // Reset arc should clear all tokens from the place
        var trigger = Place.of("Trigger", Counter.class);
        var buffer = Place.of("Buffer", Counter.class);
        var done = Place.of("Done", Counter.class);

        var clearedCount = new AtomicInteger(0);

        var t = Transition.builder("ClearBuffer")
            .input(trigger)
            .reset(buffer)  // Clear ALL tokens from buffer
            .output(done)
            .deadline(5000)
            .action(ctx -> CompletableFuture.runAsync(() -> {
                // Reset arc clears buffer before action sees it
                clearedCount.incrementAndGet();
                ctx.output(done, new Counter(1));
            }, actionExecutor))
            .build();

        var net = PetriNet.builder("ResetTest").transitions(t).build();

        // Put multiple tokens in buffer
        List<Token<?>> bufferTokens = new ArrayList<>();
        for (int i = 0; i < 50; i++) {
            bufferTokens.add(Token.of(new Counter(i)));
        }

        var initial = Map.<Place<?>, List<Token<?>>>of(
            trigger, List.of(Token.of(new Counter(0))),
            buffer, bufferTokens
        );

        try (var executor = NetExecutor.create(net, initial)) {
            var result = executor.run(Duration.ofSeconds(10)).toCompletableFuture().join();

            assertEquals(1, clearedCount.get(), "Transition should fire once");
            assertEquals(0, result.tokenCount(buffer), "Reset arc should clear all buffer tokens");
            assertEquals(1, result.tokenCount(done), "Done token should be produced");
        }
    }

    @Test
    void inhibitorArc_blocksTransition() throws Exception {
        // Inhibitor arc should prevent transition from firing
        var input = Place.of("Input", Counter.class);
        var blocker = Place.of("Blocker", Counter.class);
        var output = Place.of("Output", Counter.class);

        var fired = new AtomicInteger(0);

        var t = Transition.builder("Inhibited")
            .input(input)
            .inhibitor(blocker)  // Blocked when blocker has tokens
            .output(output)
            .deadline(5000)
            .action(ctx -> CompletableFuture.runAsync(() -> {
                fired.incrementAndGet();
                ctx.output(output, ctx.input(input));
            }, actionExecutor))
            .build();

        var net = PetriNet.builder("InhibitorTest").transitions(t).build();

        // Input has token, but so does blocker
        var initial = Map.<Place<?>, List<Token<?>>>of(
            input, List.of(Token.of(new Counter(1))),
            blocker, List.of(Token.of(new Counter(999)))
        );

        try (var executor = NetExecutor.create(net, initial)) {
            // Run briefly - transition should NOT fire
            var result = executor.run(Duration.ofMillis(200)).toCompletableFuture().join();

            assertEquals(0, fired.get(), "Transition should NOT fire when inhibitor has tokens");
            assertEquals(1, result.tokenCount(input), "Input token should remain (transition blocked)");
            assertEquals(0, result.tokenCount(output), "No output (transition blocked)");
        }
    }

    @Test
    void allArcTypes_combined() throws Exception {
        // Test all arc types together in one workflow
        final int N = 50;

        var input = Place.of("Input", Counter.class);
        var config = Place.of("Config", Counter.class);   // read
        var buffer = Place.of("Buffer", Counter.class);   // reset
        var blocker = Place.of("Blocker", Counter.class); // inhibitor
        var output = Place.of("Output", Counter.class);

        var t = Transition.builder("Complex")
            .input(input)
            .read(config)
            .reset(buffer)
            .inhibitor(blocker)
            .output(output)
            .deadline(5000)
            .action(ctx -> CompletableFuture.runAsync(() -> {
                var inputVal = ctx.input(input);
                var configVal = ctx.read(config);
                ctx.output(output, new Counter(inputVal.id + configVal.id));
            }, actionExecutor))
            .build();

        var net = PetriNet.builder("AllArcs").transitions(t).build();

        List<Token<?>> inputs = new ArrayList<>();
        for (int i = 0; i < N; i++) {
            inputs.add(Token.of(new Counter(i)));
        }

        List<Token<?>> bufferTokens = new ArrayList<>();
        for (int i = 0; i < 10; i++) {
            bufferTokens.add(Token.of(new Counter(i * 100)));
        }

        // Note: NO blocker token, so transition can fire
        var initial = Map.<Place<?>, List<Token<?>>>of(
            input, inputs,
            config, List.of(Token.of(new Counter(1000))),
            buffer, bufferTokens
            // blocker is empty, so not inhibited
        );

        try (var executor = NetExecutor.create(net, initial)) {
            var result = executor.run(Duration.ofSeconds(10)).toCompletableFuture().join();

            assertEquals(0, result.tokenCount(input), "All inputs should be consumed");
            assertEquals(1, result.tokenCount(config), "Config should remain (read arc)");
            assertEquals(0, result.tokenCount(buffer), "Buffer should be cleared (reset arc)");
            assertEquals(N, result.tokenCount(output), "All outputs should arrive");

            // Verify values include config addition
            var outputs = result.peekTokens(output);
            var ids = outputs.stream().map(tok -> tok.value().id()).sorted().toList();
            for (int i = 0; i < N; i++) {
                assertEquals(i + 1000, ids.get(i), "Output should be input + config");
            }
        }
    }
}
