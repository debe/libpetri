package org.libpetri.core;

import java.time.Duration;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionStage;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.function.Function;

/**
 * The action executed when a transition fires.
 *
 * <p>Actions receive a {@link TransitionContext} that provides:
 * <ul>
 *   <li>Filtered input access (only declared inputs)</li>
 *   <li>Filtered read access (only declared reads)</li>
 *   <li>Restricted output (only declared outputs)</li>
 *   <li>Structure introspection for context-aware actions</li>
 * </ul>
 *
 * <h3>Thread Safety</h3>
 * <p>No explicit synchronization is needed. The {@link CompletionStage} establishes
 * a happens-before relationship: all writes to the context in the action thread
 * are visible to the orchestrator when it receives the completed future.
 *
 * <h3>Example</h3>
 * <pre>{@code
 * TransitionAction action = ctx -> {
 *     var request = ctx.input(requestPlace);
 *     return service.process(request)
 *         .thenAccept(response -> ctx.output(responsePlace, response));
 * };
 * }</pre>
 */
@FunctionalInterface
public interface TransitionAction {

    /**
     * Execute the transition action.
     *
     * @param ctx context providing filtered I/O and structure access
     * @return stage completing when done
     */
    CompletionStage<Void> execute(TransitionContext ctx);

    // ==================== Built-in Actions ====================

    /**
     * Identity action: produces no outputs.
     * For transitions that only consume tokens without producing any.
     */
    static TransitionAction passthrough() {
        return ctx -> CompletableFuture.completedFuture(null);
    }

    /**
     * Transform action: applies function to context, copies result to ALL output places.
     * Base for other actions like fork().
     *
     * <p><b>Important:</b> All declared output places must accept the same type as the
     * function's return value. If output places have heterogeneous types, use explicit
     * {@code ctx.output()} calls instead.
     *
     * @param fn function that reads from context and returns value to output
     */
    @SuppressWarnings("unchecked")
    static TransitionAction transform(Function<TransitionContext, Object> fn) {
        return ctx -> {
            try {
                Object result = fn.apply(ctx);
                for (Place<?> outputPlace : ctx.outputPlaces()) {
                    ctx.output((Place<Object>) outputPlace, result);
                }
                return CompletableFuture.completedFuture(null);
            }
            catch (Exception e) {
                return CompletableFuture.failedFuture(e);
            }
        };
    }

    /**
     * Fork action: identity transform - copies single input token to all outputs.
     * Implemented as transform with identity function.
     *
     * <p>Requires: exactly one input place (derived from structure).
     * All output places must accept the same token type as the input place.
     *
     * <p>Note: If the input token value is null, null is propagated to all outputs.
     *
     * <p>Example:
     * <pre>{@code
     * // Structure defines: input=CUSTOMER_INPUT, outputs=A,B,C
     * Transition.builder("ForkCustomerInput")
     *     .input(CUSTOMER_INPUT)
     *     .outputs(A, B, C)
     *     .build();
     *
     * // Binding - fork() derives everything from structure
     * bindActions(Map.of("ForkCustomerInput", TransitionAction.fork()))
     * }</pre>
     */
    @SuppressWarnings("unchecked")
    static TransitionAction fork() {
        return transform(ctx -> {
            var inputPlaces = ctx.inputPlaces();
            if (inputPlaces.size() != 1) {
                throw new IllegalStateException(
                    "Fork requires exactly 1 input place, found " + inputPlaces.size()
                );
            }
            Place<Object> inputPlace = (Place<Object>) inputPlaces.iterator().next();
            return ctx.input(inputPlace);
        });
    }

    /**
     * Transform with explicit input place.
     */
    static <I> TransitionAction transform(Place<I> inputPlace, Function<I, Object> fn) {
        return transform(ctx -> fn.apply(ctx.input(inputPlace)));
    }

    /**
     * Async transform: applies async function, copies result to all outputs.
     *
     * <p><b>Important:</b> All declared output places must accept the same type as the
     * async function's result. If output places have heterogeneous types, use explicit
     * {@code ctx.output()} calls instead.
     *
     * @param fn async function that reads from context and returns value to output
     */
    @SuppressWarnings("unchecked")
    static TransitionAction transformAsync(Function<TransitionContext, CompletionStage<Object>> fn) {
        return ctx -> fn.apply(ctx).thenAccept(result -> {
            for (Place<?> outputPlace : ctx.outputPlaces()) {
                ctx.output((Place<Object>) outputPlace, result);
            }
        });
    }

    /**
     * Produce action: produces a single token with the given value to the specified place.
     */
    static <T> TransitionAction produce(Place<T> place, T value) {
        return ctx -> {
            ctx.output(place, value);
            return CompletableFuture.completedFuture(null);
        };
    }

    /**
     * Wraps an action with timeout handling.
     *
     * <p>If the action completes within the timeout, normal completion.
     * If the timeout expires, the timeoutValue is produced to the timeoutPlace instead.
     *
     * <p>This keeps action classes clean - timeout is applied declaratively at binding time:
     * <pre>{@code
     * TransitionAction.withTimeout(
     *     new MyAction(),
     *     Duration.ofSeconds(2),
     *     timeoutPlace,
     *     new TimeoutMarker()
     * )
     * }</pre>
     *
     * @param action the action to wrap
     * @param timeout maximum duration for action to complete
     * @param timeoutPlace place to produce timeout token
     * @param timeoutValue value to produce on timeout
     * @param <T> type of timeout token
     * @return wrapped action with timeout handling
     */
    static <T> TransitionAction withTimeout(
            TransitionAction action,
            Duration timeout,
            Place<T> timeoutPlace,
            T timeoutValue
    ) {
        return ctx -> action.execute(ctx)
                .toCompletableFuture()
                .orTimeout(timeout.toMillis(), TimeUnit.MILLISECONDS)
                .exceptionally(ex -> {
                    // orTimeout throws TimeoutException directly, but may be wrapped in CompletionException
                    if (ex instanceof TimeoutException
                            || (ex.getCause() != null && ex.getCause() instanceof TimeoutException)) {
                        ctx.output(timeoutPlace, timeoutValue);
                        return null;
                    }
                    if (ex instanceof RuntimeException rte) {
                        throw rte;
                    }
                    throw new RuntimeException(ex);
                });
    }
}
