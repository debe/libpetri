package org.libpetri.runtime;

import java.lang.System.Logger;
import java.lang.System.Logger.Level;
import java.util.*;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionException;
import java.util.concurrent.CompletionStage;
import java.util.concurrent.TimeUnit;

import org.libpetri.core.*;

/**
 * Shared static helpers used by both {@link NetExecutor} and {@link BitmapNetExecutor}.
 */
final class ExecutorSupport {

    private ExecutorSupport() {}

    private static final Logger LOG = System.getLogger("org.libpetri.runtime");

    /**
     * Default handler for an action failure that no {@link org.libpetri.event.EventStore}
     * observed.
     *
     * <p>A failing action destroys the tokens it consumed. With the default
     * {@code EventStore.noop()} the {@code TransitionFailed} event goes nowhere, so without
     * this handler the loss is completely silent. Logs at WARNING; override via
     * {@code Builder.uncaughtActionHandler(...)}.
     */
    static final ActionFailureHandler DEFAULT_UNCAUGHT_ACTION_HANDLER =
        (t, cause) -> LOG.log(Level.WARNING,
            () -> "libpetri: action of transition '" + t.name()
                + "' failed; its consumed tokens are lost", cause);

    /**
     * Reports an action failure to the configured handler.
     *
     * <p>An explicitly configured handler is always invoked. With no handler configured the
     * default only logs when no {@code EventStore} recorded the failure, so enabling an event
     * store does not also produce a duplicate WARNING.
     *
     * <p>A handler that throws is swallowed: reporting a failure must not itself become the
     * failure that kills the orchestrator.
     *
     * @param handler the configured handler, or {@code null} for the default policy
     * @param observed whether a {@code TransitionFailed} event was actually appended to the
     *     store for this failure (not merely whether a store is configured)
     * @param t the transition whose action failed
     * @param cause the unwrapped cause
     */
    static void reportActionFailure(
        ActionFailureHandler handler,
        boolean observed,
        Transition t,
        Throwable cause
    ) {
        if (handler != null) {
            try {
                handler.onActionFailed(t, cause);
            } catch (Throwable suppressed) {
                LOG.log(Level.WARNING, "libpetri: uncaughtActionHandler threw", suppressed);
            }
        } else if (!observed) {
            DEFAULT_UNCAUGHT_ACTION_HANDLER.onActionFailed(t, cause);
        }
    }

    /**
     * Swallows a failure thrown by a user {@link org.libpetri.event.EventStore} from
     * {@code append}, logging it at WARNING.
     *
     * <p>An event emission is observation, not control flow: a store that throws must not
     * unwind the orchestrator loop or escape a failure handler. Callers wrap their
     * {@code emitEvent} in a try/catch that routes here.
     *
     * @param when short description of what was being emitted, for the log message
     * @param storeError the throwable the store raised
     */
    static void swallowEventStoreFailure(String when, Throwable storeError) {
        LOG.log(Level.WARNING,
            () -> "libpetri: EventStore.append threw while emitting " + when
                + "; the event is dropped", storeError);
    }

    /**
     * Unwraps the {@link CompletionException} / {@link java.util.concurrent.ExecutionException}
     * wrapper that {@code join()} adds, so handlers see the cause the action actually threw.
     */
    static Throwable unwrap(Throwable e) {
        Throwable cause = e.getCause();
        return (e instanceof CompletionException && cause != null) ? cause : e;
    }

    /**
     * Invokes a transition action, converting a synchronous throw or a {@code null} return
     * into a failed future.
     *
     * <p>Actions are invoked inline on the orchestrator thread, so an action that throws
     * before returning its stage — an NPE in a lambda, {@code ctx.input(...)} on an undeclared
     * place — would otherwise unwind out of the firing loop and take the whole executor with
     * it. Routing it through a failed future makes it flow the same path as an
     * asynchronously-reported failure.
     *
     * <p>Only {@link Exception} is caught, not {@link Error}: a {@code StackOverflowError} or
     * {@code OutOfMemoryError} is not a per-transition failure to be logged and retried, and
     * would spin the loop re-firing the same transition. It is left to propagate — the firing
     * boundary repairs executor state and rethrows it so the run terminates with the real cause.
     *
     * @param t the transition being fired
     * @param context the context handed to the action
     * @return a future that is already failed if the action threw or returned {@code null}
     */
    static CompletableFuture<Void> executeAction(Transition t, TransitionContext context) {
        try {
            CompletionStage<Void> stage = t.action().execute(context);
            if (stage == null) {
                return CompletableFuture.failedFuture(new IllegalStateException(
                    "'%s': action returned null instead of a CompletionStage".formatted(t.name())));
            }
            return stage.toCompletableFuture();
        } catch (Exception e) {
            return CompletableFuture.failedFuture(e);
        }
    }

    /**
     * Rethrows {@code e} if it is an {@link Error} that must not be contained as a
     * per-transition failure — a JVM-level fault ({@link VirtualMachineError}) or a class
     * linkage failure ({@link LinkageError}). Called by the firing boundary <em>after</em> it
     * has repaired executor state, so the loop terminates with the real cause rather than
     * re-firing against a broken JVM. Ordinary {@link Exception}s (and any other
     * {@code Throwable}) return normally and are handled as transition failures.
     *
     * @param e the throwable caught by the firing boundary
     */
    static void rethrowIfFatal(Throwable e) {
        if (e instanceof VirtualMachineError || e instanceof LinkageError) {
            throw (Error) e;
        }
    }

    /**
     * Default deadline-enforcement tolerance, in milliseconds.
     *
     * <p>A transition with a hard deadline ({@code deadline()} / {@code window()}) is
     * force-disabled only once its elapsed time exceeds {@code latest + DEADLINE_TOLERANCE_MS},
     * absorbing timer-resolution and scheduling jitter (TIME-013). The value is shared across
     * the Java, TypeScript and Rust executors so deadline enforcement behaves identically.
     *
     * <p>{@code exact()} timing is enforced <em>softly</em>: an exact transition fires at the
     * first opportunity at or after its target time and is never force-disabled, so this
     * tolerance does not gate its firing — see {@link org.libpetri.core.Timing.Exact}.
     *
     * <p>Configurable per executor via {@code Builder.deadlineTolerance(Duration)}.
     */
    static final long DEADLINE_TOLERANCE_MS = 5;

    /**
     * Upper bound a foreign-thread {@code marking()} will wait for the orchestrator to publish a
     * fresh snapshot before falling back to the last one it published. The handshake normally
     * resolves in microseconds (the orchestrator services the request at the top of its next
     * loop iteration); this cap only bites while the orchestrator is stuck inside a long inline
     * action, where a slightly stale snapshot is the documented best-effort outcome.
     */
    static final long MARKING_SNAPSHOT_WAIT_NANOS = 2_000_000_000L; // 2s

    /**
     * Recursively validates that a transition's output satisfies its declared {@link Arc.Out} spec.
     *
     * @param tName transition name for error messages
     * @param spec the output specification to validate
     * @param produced set of places that received tokens
     * @return the set of claimed places, or empty if not satisfied
     * @throws OutViolationException if a structural violation is detected
     */
    static Optional<Set<Place<?>>> validateOutSpec(String tName, Arc.Out spec, Set<Place<?>> produced) {
        return switch (spec) {
            case Arc.Out.Place p -> produced.contains(p.place())
                ? Optional.of(Set.of(p.place()))
                : Optional.empty();

            case Arc.Out.And and -> {
                var claimed = new HashSet<Place<?>>();
                for (Arc.Out child : and.children()) {
                    var result = validateOutSpec(tName, child, produced);
                    if (result.isEmpty()) yield Optional.<Set<Place<?>>>empty();
                    claimed.addAll(result.get());
                }
                yield Optional.of(claimed);
            }

            case Arc.Out.Xor xor -> {
                var satisfied = xor.children().stream()
                    .flatMap(child -> validateOutSpec(tName, child, produced).stream())
                    .toList();

                yield switch (satisfied.size()) {
                    case 0 -> throw new OutViolationException(
                        "'%s': XOR violation - no branch produced (exactly 1 required)".formatted(tName));
                    case 1 -> Optional.of(satisfied.getFirst());
                    default -> {
                        // When one branch subsumes all others (e.g., AND(A,B,C) vs AND(A,B)),
                        // select the most specific match.
                        var subsuming = satisfied.stream()
                            .filter(candidate -> satisfied.stream()
                                .allMatch(other -> other == candidate || candidate.containsAll(other)))
                            .toList();
                        if (subsuming.size() == 1) {
                            yield Optional.of(subsuming.getFirst());
                        }
                        throw new OutViolationException(
                            "'%s': XOR violation - multiple branches produced".formatted(tName));
                    }
                };
            }

            case Arc.Out.Timeout timeout -> validateOutSpec(tName, timeout.child(), produced);

            case Arc.Out.ForwardInput f -> produced.contains(f.to())
                ? Optional.of(Set.of(f.to()))
                : Optional.empty();
        };
    }

    /**
     * Produces tokens to the timeout branch output places.
     *
     * <p>Writes through {@link TransitionContext#outputToHarvest} rather than
     * {@code output(...)}: by this point the context has been detached, so the ordinary write
     * target is closed and only the harvest collector still reaches the marking.
     *
     * <p>{@code Out.ForwardInput} re-emits <em>every</em> token consumed from its {@code from}
     * place, in consumption order — one output token per consumed token — so a batched input
     * spec ({@code In.All}, {@code In.Exactly(n)}) conserves its tokens on timeout.
     */
    static void produceTimeoutOutput(TransitionContext context, Arc.Out timeoutChild) {
        produceTimeoutOutputRecursive(context, timeoutChild);
    }

    @SuppressWarnings("unchecked")
    private static void produceTimeoutOutputRecursive(TransitionContext context, Arc.Out out) {
        switch (out) {
            case Arc.Out.Place p ->
                context.outputToHarvest((Place<Object>) p.place(), Token.unit().value());
            case Arc.Out.ForwardInput f -> {
                // Forward *every* token consumed from `from`, not just the first: a batched
                // input spec (In.All, In.Exactly(n), In.AtLeast(n)) consumes N tokens, and
                // re-emitting only one would silently destroy N-1 of them on the retry path.
                // inputs() is the batched accessor and preserves consumption (FIFO) order;
                // the singular input() returns only the first consumed value.
                Place<Object> to = (Place<Object>) f.to();
                for (Object value : context.inputs((Place<Object>) f.from())) {
                    context.outputToHarvest(to, value);
                }
            }
            case Arc.Out.And a ->
                a.children().forEach(c -> produceTimeoutOutputRecursive(context, c));
            case Arc.Out.Xor _ ->
                throw new IllegalStateException("XOR not allowed in timeout child");
            case Arc.Out.Timeout _ ->
                throw new IllegalStateException("Nested Timeout not allowed");
        }
    }

    /**
     * Wraps a firing's future with its declared {@code Out.Timeout} budget.
     *
     * <p>Single implementation shared by all three executors, which previously carried three
     * copies that had already drifted apart.
     *
     * <p>Three things this deliberately does <em>not</em> do:
     * <ul>
     *   <li><b>It does not cancel the action.</b> {@code CompletableFuture.cancel} ignores
     *       {@code mayInterruptIfRunning}, and libpetri does not own the thread anyway. The
     *       action runs to completion; only its <em>result</em> is excluded, by detaching the
     *       context before the timeout branch is produced.</li>
     *   <li><b>It does not complete the caller's future.</b> {@code toCompletableFuture()}
     *       returns the very future the action handed back, which the action may have shared
     *       with metrics or a retry wrapper. {@code copy()} gives a dependent view to arm the
     *       timer on, leaving the original untouched.</li>
     *   <li><b>It does not treat every {@code TimeoutException} as the budget expiring.</b>
     *       The timeout branch is selected by <em>provenance</em>, not by exception type: only
     *       the executor's own timer, signalled through {@link #TIMEOUT_SENTINEL}, takes it. An
     *       action that itself fails with a {@code TimeoutException} (an HTTP or gRPC client
     *       giving up early) flows the ordinary failure path, not the declared timeout branch.</li>
     * </ul>
     *
     * @param t the firing transition (must have an action timeout)
     * @param context the firing's context, detached here if the budget expires
     * @param actionFuture the future the action returned
     * @param onTimeout invoked after the timeout branch is produced, for event emission
     * @return a future that completes normally once either the action finishes in time or the
     *     timeout branch has been deposited, and exceptionally if the action itself failed
     */
    static CompletableFuture<Void> withActionTimeout(
        Transition t,
        TransitionContext context,
        CompletableFuture<Void> actionFuture,
        Runnable onTimeout
    ) {
        Arc.Out.Timeout spec = t.actionTimeout();
        return actionFuture
            .copy()
            .<Object>thenApply(v -> v)
            .completeOnTimeout(TIMEOUT_SENTINEL, spec.after().toMillis(), TimeUnit.MILLISECONDS)
            .thenAccept(result -> {
                if (result == TIMEOUT_SENTINEL) {
                    // Sever first, then produce: the abandoned action may be writing to this
                    // context right now, and the timeout branch must not be merged with it.
                    context.detachForTimeout();
                    produceTimeoutOutput(context, spec.child());
                    onTimeout.run();
                }
                // Otherwise the action completed in time; its own output is already in the
                // context and will be harvested normally. A non-sentinel failure propagates
                // as this stage's exceptional completion and is handled as an action failure.
            });
    }

    /**
     * Marker completed onto a firing's future by {@link #withActionTimeout} when — and only
     * when — the executor's own budget timer fires. Identity-compared so it can never collide
     * with a value or exception the action itself produced.
     */
    static final Object TIMEOUT_SENTINEL = new Object();

    /**
     * Drains pending external events, completing each with {@code false}.
     */
    static void drainPendingExternalEvents(Queue<ExternalEvent<?>> queue) {
        ExternalEvent<?> event;
        while ((event = queue.poll()) != null) {
            event.resultFuture().complete(false);
        }
    }
}
