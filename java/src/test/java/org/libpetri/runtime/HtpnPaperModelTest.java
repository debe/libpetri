package org.libpetri.runtime;

import org.junit.jupiter.api.Test;

import org.libpetri.core.*;
import org.libpetri.runtime.NetExecutor;
import static org.libpetri.core.In.one;
import static org.libpetri.core.Out.and;
import static org.libpetri.core.Out.place;
import static org.libpetri.core.Out.xor;

import java.time.Duration;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.Executors;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Token;
import static org.junit.jupiter.api.Assertions.*;

/**
 * Test implementing the HTPN model from the paper:
 * "Apply Time Petri Nets with Colored Tokens to Model and Verify Agentic Systems"
 *
 * This test models an example agentic workflow with:
 * - Typed tokens using sealed interfaces
 * - Firing intervals [0, β] for deadline semantics
 * - Parallel execution (Guard/Intent, Topic/Search)
 * - Retries, fallbacks, and global timeout
 */
class HtpnPaperModelTest {

    // ==================== SEALED INTERFACES FOR TYPED TOKENS ====================

    /** Initial chat request from user */
    record ChatRequest(String query, String sessionId) {}

    /** Signal that workflow is ready (control token) */
    record ReadySignal(String sessionId) {}

    /** Result from Guard agent */
    sealed interface ValidationResult permits Valid, Invalid {}
    record Valid(String sessionId) implements ValidationResult {}
    record Invalid(String reason) implements ValidationResult {}

    /** Result from Intent agent */
    sealed interface IntentResult permits Intent, UnknownIntent {}
    record Intent(String intent, String topic, double confidence) implements IntentResult {}
    record UnknownIntent(String rawQuery) implements IntentResult {}

    /** Result from Topic agent */
    sealed interface TopicResult permits TopicKnowledge, NoKnowledge {}
    record TopicKnowledge(String category, List<String> facts) implements TopicResult {}
    record NoKnowledge() implements TopicResult {}

    /** Promotions from Topic agent */
    record Promotions(List<String> promoIds) {}

    /** Result from Search agent */
    sealed interface SearchResult permits ProductsFound, FallbackProducts, SearchFailed {}
    record ProductsFound(List<String> productIds, int totalCount) implements SearchResult {}
    record FallbackProducts(List<String> cachedIds) implements SearchResult {}
    record SearchFailed(String error) implements SearchResult {}

    /** Result from Compose agent */
    sealed interface DraftResult permits Draft, DraftFailed {}
    record Draft(String text, boolean hasMarkdown) implements DraftResult {}
    record DraftFailed(String error, int attempt) implements DraftResult {}

    /** Final response after filtering */
    record FinalResponse(String text, long processingTimeMs) {}

    /** Urgent signal from global timeout */
    record UrgentSignal(long triggeredAtMs) {}

    // ==================== TEST: BASIC TPN MODEL (Figure 3 in paper) ====================

    @Test
    void testBasicTpnModel() throws Exception {
        // === PLACES (typed) ===
        var pending = Place.of("Pending", ChatRequest.class);
        var ready = Place.of("Ready", ReadySignal.class);
        var ready2 = Place.of("Ready2", ReadySignal.class);
        var validated = Place.of("Validated", ValidationResult.class);
        var understood = Place.of("Understood", IntentResult.class);
        var understood2 = Place.of("Understood2", IntentResult.class);
        var informed = Place.of("Informed", TopicResult.class);
        var promoted = Place.of("Promoted", Promotions.class);
        var found = Place.of("Found", SearchResult.class);
        var drafted = Place.of("Drafted", DraftResult.class);
        var answered = Place.of("Answered", FinalResponse.class);

        // === TRANSITIONS with firing intervals [0, β] ===

        // ask() - Initialize workflow, produces ReadySignal for parallel branches
        var ask = Transition.builder("ask")
            .inputs(one(pending))
            .outputs(and(ready, ready2))
            .timing(Timing.deadline(Duration.ofMillis(100)))
            .action(ctx -> {
                var request = ctx.input(pending);
                ctx.output(ready, new ReadySignal(request.sessionId()));
                ctx.output(ready2, new ReadySignal(request.sessionId()));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var actionExecutor = Executors.newVirtualThreadPerTaskExecutor();


        // Guard [0, 500ms] - Validate input
        var guard = Transition.builder("Guard")
            .inputs(one(ready))
            .outputs(place(validated))
            .timing(Timing.deadline(Duration.ofMillis(500)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(50);
                var signal = ctx.input(ready);
                ctx.output(validated, new Valid(signal.sessionId()));
            }, actionExecutor))
            .build();

        // Intent [0, 2000ms] - Extract intent, produces two tokens for Topic and Search
        var intent = Transition.builder("Intent")
            .inputs(one(ready2))
            .outputs(and(understood, understood2))
            .timing(Timing.deadline(Duration.ofMillis(2000)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(100);
                ctx.output(understood, new Intent("buy", "shoes", 0.95));
                ctx.output(understood2, new Intent("buy", "shoes", 0.95));
            }, actionExecutor))
            .build();

        // Topic [0, 4500ms] - Lookup knowledge
        var topic = Transition.builder("Topic")
            .inputs(one(understood))
            .outputs(and(informed, promoted))
            .timing(Timing.deadline(Duration.ofMillis(4500)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(200);
                ctx.output(informed, new TopicKnowledge("footwear", List.of("Sneakers are popular")));
                ctx.output(promoted, new Promotions(List.of("PROMO-123")));
            }, actionExecutor))
            .build();

        // Search [0, 3500ms] - Find products
        var search = Transition.builder("Search")
            .inputs(one(understood2))
            .outputs(place(found))
            .timing(Timing.deadline(Duration.ofMillis(3500)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(150);
                ctx.output(found, new ProductsFound(List.of("SKU-001", "SKU-002", "SKU-003"), 42));
            }, actionExecutor))
            .build();

        // Compose [0, 6000ms] - Generate response (waits for all inputs)
        var compose = Transition.builder("Compose")
            .inputs(one(validated), one(informed), one(promoted), one(found))
            .outputs(place(drafted))
            .timing(Timing.deadline(Duration.ofMillis(6000)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(300);
                var products = ctx.input(found);
                String response = switch (products) {
                    case ProductsFound(var ids, var count) ->
                        "Found " + count + " products: " + String.join(", ", ids);
                    case FallbackProducts(var ids) ->
                        "Here are some suggestions: " + String.join(", ", ids);
                    case SearchFailed(var error) ->
                        "Sorry, search failed: " + error;
                };
                ctx.output(drafted, new Draft(response, true));
            }, actionExecutor))
            .build();

        // Filter [0, 500ms] - Apply output filtering
        var filter = Transition.builder("Filter")
            .inputs(one(drafted))
            .outputs(place(answered))
            .timing(Timing.deadline(Duration.ofMillis(500)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(20);
                var draft = ctx.input(drafted);
                String text = switch (draft) {
                    case Draft(var t, _) -> t;
                    case DraftFailed(var error, _) -> "Error: " + error;
                };
                ctx.output(answered, new FinalResponse(text, System.currentTimeMillis()));
            }, actionExecutor))
            .build();

        // === BUILD NET (reusable structure) ===
        var chatNet = PetriNet.builder("ChatWorkflow-Basic")
            .transitions(ask, guard, intent, topic, search, compose, filter)
            .build();

        // === EXECUTE with input tokens ===
        var input = Map.<Place<?>, List<Token<?>>>of(
            pending, List.of(Token.of(new ChatRequest("Show me blue shoes", "session-123")))
        );
        try (var executor = NetExecutor.create(chatNet, input)) {
            var startTime = System.currentTimeMillis();
            var result = executor.run(Duration.ofSeconds(10)).toCompletableFuture().join();
            var elapsed = System.currentTimeMillis() - startTime;

            // Verify final state
            assertTrue(result.hasTokens(answered), "Should reach Answered state");
            assertFalse(result.hasTokens(pending), "Pending should be consumed");
            assertEquals(1, result.tokenCount(answered));

            System.out.println("Basic TPN completed in " + elapsed + "ms");
            assertTrue(elapsed < 2000, "Should complete well within deadlines");

            // Extract and verify final response
            var finalToken = result.peekFirst(answered);
            var response = finalToken.value();
            assertTrue(response.text().contains("products"), "Response should mention products");
        }
    }

    // ==================== TEST: EXTENDED TPN WITH RETRIES/FALLBACKS (Figure 4 in paper) ====================

    @Test
    void testExtendedTpnWithFallbackOnSearchFailure() throws Exception {
        // === PLACES ===
        var pending = Place.of("Pending", ChatRequest.class);
        var ready = Place.of("Ready", ReadySignal.class);
        var ready2 = Place.of("Ready2", ReadySignal.class);
        var validated = Place.of("Validated", ValidationResult.class);
        var understood = Place.of("Understood", IntentResult.class);
        var understood2 = Place.of("Understood2", IntentResult.class);
        var informed = Place.of("Informed", TopicResult.class);
        var promoted = Place.of("Promoted", Promotions.class);
        var found = Place.of("Found", SearchResult.class);
        var drafted = Place.of("Drafted", DraftResult.class);
        var answered = Place.of("Answered", FinalResponse.class);

        // Failure places
        var searchFail = Place.of("SearchFail", SearchFailed.class);

        var actionExecutor = Executors.newVirtualThreadPerTaskExecutor();

        // === TRANSITIONS ===
        var ask = Transition.builder("ask")
            .inputs(one(pending))
            .outputs(and(ready, ready2))
            .timing(Timing.deadline(Duration.ofMillis(100)))
            .action(ctx -> {
                var request = ctx.input(pending);
                ctx.output(ready, new ReadySignal(request.sessionId()));
                ctx.output(ready2, new ReadySignal(request.sessionId()));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var guard = Transition.builder("Guard")
            .inputs(one(ready))
            .outputs(place(validated))
            .timing(Timing.deadline(Duration.ofMillis(500)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(30);
                ctx.output(validated, new Valid("session"));
            }, actionExecutor))
            .build();

        var intent = Transition.builder("Intent")
            .inputs(one(ready2))
            .outputs(and(understood, understood2))
            .timing(Timing.deadline(Duration.ofMillis(2000)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(50);
                ctx.output(understood, new Intent("buy", "shoes", 0.9));
                ctx.output(understood2, new Intent("buy", "shoes", 0.9));
            }, actionExecutor))
            .build();

        var topic = Transition.builder("Topic")
            .inputs(one(understood))
            .outputs(and(informed, promoted))
            .timing(Timing.deadline(Duration.ofMillis(4500)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(100);
                ctx.output(informed, new TopicKnowledge("footwear", List.of()));
                ctx.output(promoted, new Promotions(List.of()));
            }, actionExecutor))
            .build();

        // Search that fails and produces to SearchFail place
        var search = Transition.builder("Search")
            .inputs(one(understood2))
            .outputs(place(searchFail))
            .timing(Timing.deadline(Duration.ofMillis(3500)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(80);
                ctx.output(searchFail, new SearchFailed("Service unavailable"));
            }, actionExecutor))
            .build();

        // Fallback [0, 100ms] - Use cached results when search fails
        var fallback = Transition.builder("Fallback")
            .inputs(one(searchFail))
            .outputs(place(found))
            .timing(Timing.deadline(Duration.ofMillis(100)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(10);
                ctx.output(found, new FallbackProducts(List.of("CACHED-001", "CACHED-002")));
            }, actionExecutor))
            .build();

        var compose = Transition.builder("Compose")
            .inputs(one(validated), one(informed), one(promoted), one(found))
            .outputs(place(drafted))
            .timing(Timing.deadline(Duration.ofMillis(6000)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(150);
                var products = ctx.input(found);
                String response = switch (products) {
                    case ProductsFound(var ids, var count) -> "Found " + count + " products";
                    case FallbackProducts(var ids) -> "Fallback: " + String.join(", ", ids);
                    case SearchFailed(var e) -> "Error: " + e;
                };
                ctx.output(drafted, new Draft(response, false));
            }, actionExecutor))
            .build();

        var filter = Transition.builder("Filter")
            .inputs(one(drafted))
            .outputs(place(answered))
            .timing(Timing.deadline(Duration.ofMillis(500)))
            .action(ctx -> {
                var draft = ctx.input(drafted);
                String text = switch (draft) {
                    case Draft(var t, _) -> t;
                    case DraftFailed(var e, _) -> "Error: " + e;
                };
                ctx.output(answered, new FinalResponse(text, System.currentTimeMillis()));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        // === BUILD NET (reusable structure) ===
        var chatNet = PetriNet.builder("ChatWorkflow-WithFallback")
            .transitions(ask, guard, intent, topic, search, fallback, compose, filter)
            .build();

        // === EXECUTE with input tokens ===
        var input = Map.<Place<?>, List<Token<?>>>of(
            pending, List.of(Token.of(new ChatRequest("blue shoes", "session-456")))
        );
        try (var executor = NetExecutor.create(chatNet, input)) {
            var result = executor.run(Duration.ofSeconds(10)).toCompletableFuture().join();

            assertTrue(result.hasTokens(answered), "Should reach Answered via fallback path");

            var finalToken = result.peekFirst(answered);
            var response = finalToken.value();
            assertTrue(response.text().contains("Fallback"), "Should use fallback results");
            assertTrue(response.text().contains("CACHED"), "Should contain cached product IDs");

            System.out.println("Fallback test - Final response: " + response.text());
        }
    }

    @Test
    void testExtendedTpnWithRetryOnComposeFail() throws Exception {
        // === PLACES ===
        var pending = Place.of("Pending", ChatRequest.class);
        var ready = Place.of("Ready", ReadySignal.class);
        var ready2 = Place.of("Ready2", ReadySignal.class);
        var validated = Place.of("Validated", ValidationResult.class);
        var understood = Place.of("Understood", IntentResult.class);
        var understood2 = Place.of("Understood2", IntentResult.class);
        var informed = Place.of("Informed", TopicResult.class);
        var promoted = Place.of("Promoted", Promotions.class);
        var found = Place.of("Found", SearchResult.class);
        var drafted = Place.of("Drafted", DraftResult.class);
        var answered = Place.of("Answered", FinalResponse.class);

        // Retry place
        var composeFail = Place.of("ComposeFail", DraftFailed.class);

        // Track retry attempts
        var composeAttempts = new AtomicInteger(0);

        var actionExecutor = Executors.newVirtualThreadPerTaskExecutor();
        // === TRANSITIONS ===
        var ask = Transition.builder("ask")
            .inputs(one(pending))
            .outputs(and(ready, ready2))
            .timing(Timing.deadline(Duration.ofMillis(100)))
            .action(ctx -> {
                var request = ctx.input(pending);
                ctx.output(ready, new ReadySignal(request.sessionId()));
                ctx.output(ready2, new ReadySignal(request.sessionId()));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var guard = Transition.builder("Guard")
            .inputs(one(ready))
            .outputs(place(validated))
            .timing(Timing.deadline(Duration.ofMillis(500)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(20);
                ctx.output(validated, new Valid("session"));
            }, actionExecutor))
            .build();

        var intent = Transition.builder("Intent")
            .inputs(one(ready2))
            .outputs(and(understood, understood2))
            .timing(Timing.deadline(Duration.ofMillis(2000)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(30);
                ctx.output(understood, new Intent("buy", "shoes", 0.9));
                ctx.output(understood2, new Intent("buy", "shoes", 0.9));
            }, actionExecutor))
            .build();

        var topic = Transition.builder("Topic")
            .inputs(one(understood))
            .outputs(and(informed, promoted))
            .timing(Timing.deadline(Duration.ofMillis(4500)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(50);
                ctx.output(informed, new TopicKnowledge("footwear", List.of()));
                ctx.output(promoted, new Promotions(List.of()));
            }, actionExecutor))
            .build();

        var search = Transition.builder("Search")
            .inputs(one(understood2))
            .outputs(place(found))
            .timing(Timing.deadline(Duration.ofMillis(3500)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(40);
                ctx.output(found, new ProductsFound(List.of("SKU-1"), 1));
            }, actionExecutor))
            .build();

        // Compose that fails on first attempt
        var compose = Transition.builder("Compose")
            .inputs(one(validated), one(informed), one(promoted), one(found))
            .outputs(place(composeFail))
            .timing(Timing.deadline(Duration.ofMillis(6000)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(100);
                int attempt = composeAttempts.incrementAndGet();
                ctx.output(composeFail, new DraftFailed("LLM timeout", attempt));
            }, actionExecutor))
            .build();

        // Retry transition
        var composeRetry = Transition.builder("ComposeRetry")
            .inputs(one(composeFail))
            .outputs(place(drafted))
            .timing(Timing.deadline(Duration.ofMillis(1000)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(80);
                var failed = ctx.input(composeFail);
                ctx.output(drafted, new Draft("Retry success after " + failed.attempt() + " attempts", false));
            }, actionExecutor))
            .build();

        var filter = Transition.builder("Filter")
            .inputs(one(drafted))
            .outputs(place(answered))
            .timing(Timing.deadline(Duration.ofMillis(500)))
            .action(ctx -> {
                var draft = ctx.input(drafted);
                String text = switch (draft) {
                    case Draft(var t, _) -> t;
                    case DraftFailed(var e, _) -> "Error: " + e;
                };
                ctx.output(answered, new FinalResponse(text, System.currentTimeMillis()));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        // === BUILD NET (reusable structure) ===
        var chatNet = PetriNet.builder("ChatWorkflow-WithRetry")
            .transitions(ask, guard, intent, topic, search, compose, composeRetry, filter)
            .build();

        // === EXECUTE with input tokens ===
        var input = Map.<Place<?>, List<Token<?>>>of(
            pending, List.of(Token.of(new ChatRequest("blue shoes", "session-789")))
        );
        try (var executor = NetExecutor.create(chatNet, input)) {
            var result = executor.run(Duration.ofSeconds(10)).toCompletableFuture().join();

            assertTrue(result.hasTokens(answered), "Should reach Answered via retry path");

            var finalToken = result.peekFirst(answered);
            var response = finalToken.value();
            assertTrue(response.text().contains("Retry success"), "Should indicate retry succeeded");

            System.out.println("Retry test - Final response: " + response.text());
            System.out.println("Compose attempts: " + composeAttempts.get());
        }
    }

    // ==================== TEST: WORKFLOW WITH TIGHT DEADLINES (HTPN composition) ====================

    @Test
    void testTextWorkflowWithRelaxedDeadlines() throws Exception {
        var result = runWorkflow("Text", 500, 2000, 4500, 3500, 6000, 500, 10000);
        assertTrue(result.text().length() > 0);
        System.out.println("Text workflow response: " + result.text());
    }

    @Test
    void testWorkflowWithTightDeadlines() throws Exception {
        var result = runWorkflow("RealTime", 200, 1000, 2000, 1500, 3000, 200, 5000);
        assertTrue(result.text().length() > 0);
        System.out.println("Workflow response: " + result.text());
    }

    /**
     * Parameterized workflow runner - demonstrates HTPN composition with different timing.
     */
    private FinalResponse runWorkflow(
        String workflowName,
        long guardDeadline,
        long intentDeadline,
        long topicDeadline,
        long searchDeadline,
        long composeDeadline,
        long filterDeadline,
        long globalTimeout
    ) throws Exception {
        var pending = Place.of("Pending", ChatRequest.class);
        var ready = Place.of("Ready", ReadySignal.class);
        var ready2 = Place.of("Ready2", ReadySignal.class);
        var validated = Place.of("Validated", ValidationResult.class);
        var understood = Place.of("Understood", IntentResult.class);
        var understood2 = Place.of("Understood2", IntentResult.class);
        var informed = Place.of("Informed", TopicResult.class);
        var promoted = Place.of("Promoted", Promotions.class);
        var found = Place.of("Found", SearchResult.class);
        var drafted = Place.of("Drafted", DraftResult.class);
        var answered = Place.of("Answered", FinalResponse.class);
        var actionExecutor = Executors.newVirtualThreadPerTaskExecutor();

        var ask = Transition.builder("ask")
            .inputs(one(pending))
            .outputs(and(ready, ready2))
            .timing(Timing.deadline(Duration.ofMillis(100)))
            .action(ctx -> {
                var req = ctx.input(pending);
                ctx.output(ready, new ReadySignal(req.sessionId()));
                ctx.output(ready2, new ReadySignal(req.sessionId()));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var guard = Transition.builder("Guard")
            .inputs(one(ready))
            .outputs(place(validated))
            .timing(Timing.deadline(Duration.ofMillis(guardDeadline)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(guardDeadline / 10);
                ctx.output(validated, new Valid("s"));
            }, actionExecutor))
            .build();

        var intent = Transition.builder("Intent")
            .inputs(one(ready2))
            .outputs(and(understood, understood2))
            .timing(Timing.deadline(Duration.ofMillis(intentDeadline)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(intentDeadline / 20);
                ctx.output(understood, new Intent("buy", "shoes", 0.9));
                ctx.output(understood2, new Intent("buy", "shoes", 0.9));
            }, actionExecutor))
            .build();

        var topic = Transition.builder("Topic")
            .inputs(one(understood))
            .outputs(and(informed, promoted))
            .timing(Timing.deadline(Duration.ofMillis(topicDeadline)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(topicDeadline / 20);
                ctx.output(informed, new TopicKnowledge("cat", List.of()));
                ctx.output(promoted, new Promotions(List.of()));
            }, actionExecutor))
            .build();

        var search = Transition.builder("Search")
            .inputs(one(understood2))
            .outputs(place(found))
            .timing(Timing.deadline(Duration.ofMillis(searchDeadline)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(searchDeadline / 20);
                ctx.output(found, new ProductsFound(List.of("P1"), 1));
            }, actionExecutor))
            .build();

        var compose = Transition.builder("Compose")
            .inputs(one(validated), one(informed), one(promoted), one(found))
            .outputs(place(drafted))
            .timing(Timing.deadline(Duration.ofMillis(composeDeadline)))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                sleep(composeDeadline / 20);
                ctx.output(drafted, new Draft(
                    workflowName + " response: Here are your products!", workflowName.equals("Text")
                ));
            }, actionExecutor))
            .build();

        var filter = Transition.builder("Filter")
            .inputs(one(drafted))
            .outputs(place(answered))
            .timing(Timing.deadline(Duration.ofMillis(filterDeadline)))
            .action(ctx -> {
                var draft = ctx.input(drafted);
                String text = switch (draft) {
                    case Draft(var t, _) -> t;
                    case DraftFailed(var e, _) -> "Error: " + e;
                };
                ctx.output(answered, new FinalResponse(text, System.currentTimeMillis()));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var net = PetriNet.builder("ChatWorkflow-" + workflowName)
            .transitions(ask, guard, intent, topic, search, compose, filter)
            .build();

        var input = Map.<Place<?>, List<Token<?>>>of(
            pending, List.of(Token.of(new ChatRequest("shoes", "s")))
        );
        try (var executor = NetExecutor.create(net, input)) {
            var startTime = System.currentTimeMillis();
            var marking = executor.run(Duration.ofMillis(globalTimeout)).toCompletableFuture().join();
            var elapsed = System.currentTimeMillis() - startTime;

            System.out.println(workflowName + " workflow completed in " + elapsed + "ms (budget: " + globalTimeout + "ms)");
            assertTrue(elapsed < globalTimeout, "Should complete within global timeout");

            var token = marking.peekFirst(answered);
            return token.value();
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
