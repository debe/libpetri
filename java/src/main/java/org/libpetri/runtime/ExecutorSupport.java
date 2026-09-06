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
 * Shared static helpers used by both {@link PrecompiledNetExecutor} and {@link BitmapNetExecutor}.
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
     * [IO-015] output validation as an <b>exact-explanation search</b>.
     *
     * <p>An <em>assignment</em> picks exactly one child at each {@code Xor} it reaches;
     * subtrees under an unselected child are never evaluated. Each assignment claims a set of
     * places, and validation succeeds iff <b>exactly one</b> assignment's claim <em>equals</em>
     * the produced set.
     *
     * <p>Returns that claim on success and throws {@link OutViolationException} otherwise —
     * whether nothing explains the write or two or more branches do.
     *
     * <p>Equality — rather than "every obligation was satisfied" — is what makes a token
     * written to a declared place outside the selected branch a violation instead of a silent
     * deposit. It also removes the need for the old subsumption tie-break:
     * {@code Xor(And(A,B,C), And(A,B))} with A, B and C produced has exactly one
     * <em>exact</em> claim.
     *
     * <p>Being a search rather than an eager walk is what makes {@code And} genuinely unordered
     * ([IO-015] AC8): the old version short-circuited on its first unsatisfied child and let an
     * inner {@code Xor} throw before an enclosing one could try a sibling, so the same write set
     * could pass or fail depending on declaration order.
     *
     * @param tName transition name for error messages
     * @param spec the output specification to validate
     * @param produced set of places that received tokens
     * @return the claim of the single assignment that explains {@code produced}
     * @throws OutViolationException if no assignment explains the write, or more than one does
     */
    static Set<Place<?>> validateOutSpec(String tName, Arc.Out spec, Set<Place<?>> produced) {
        // Equality is tested against the produced places the spec could name at all. A token
        // produced to a place the spec never mentions is [CORE-072]'s business — retained and
        // reported, not an [IO-015] violation — so it must not make the claims unmatchable.
        Set<Place<?>> wrote = declaredAndProduced(spec, produced);

        Set<Place<?>> match = null;
        boolean ambiguous = false;
        for (Set<Place<?>> claim : claimsWithin(spec, produced)) {
            // Every claim is a subset of `wrote` by construction (a leaf claims only a place
            // that was produced, and only places the spec names), so equal size means equal set.
            if (claim.size() == wrote.size()) {
                if (match == null) {
                    match = claim;
                } else {
                    ambiguous = true;
                    break;
                }
            }
        }
        if (match == null) {
            throw new OutViolationException(
                "'%s': output does not match the declared spec - produced {%s}, which no single branch of the spec claims exactly"
                    .formatted(tName, renderPlaces(wrote)));
        }
        if (ambiguous) {
            throw new OutViolationException(
                "'%s': ambiguous output - {%s} is claimed by more than one branch"
                    .formatted(tName, renderPlaces(wrote)));
        }
        return match;
    }

    /**
     * The produced places the spec actually names, which is the set every claim is compared
     * against.
     *
     * <p>Computing the intersection directly rather than the spec's full name set is the same
     * single walk and allocates less: the result doubles as the {@code {a, b}} rendered in a
     * violation message.
     */
    private static Set<Place<?>> declaredAndProduced(Arc.Out spec, Set<Place<?>> produced) {
        var out = new HashSet<Place<?>>();
        collectDeclaredAndProduced(spec, produced, out);
        return out;
    }

    private static void collectDeclaredAndProduced(Arc.Out spec, Set<Place<?>> produced, Set<Place<?>> out) {
        switch (spec) {
            case Arc.Out.Place p -> {
                if (produced.contains(p.place())) out.add(p.place());
            }
            case Arc.Out.ForwardInput f -> {
                if (produced.contains(f.to())) out.add(f.to());
            }
            case Arc.Out.Timeout t -> collectDeclaredAndProduced(t.child(), produced, out);
            case Arc.Out.And a -> {
                for (Arc.Out c : a.children()) collectDeclaredAndProduced(c, produced, out);
            }
            case Arc.Out.Xor x -> {
                for (Arc.Out c : x.children()) collectDeclaredAndProduced(c, produced, out);
            }
        }
    }

    /** Renders a place set as the {@code a, b} body of a violation message, name-sorted. */
    private static String renderPlaces(Set<Place<?>> places) {
        var names = new ArrayList<String>(places.size());
        for (Place<?> p : places) names.add(p.name());
        Collections.sort(names);
        return String.join(", ", names);
    }

    /**
     * Claims of every assignment whose claim is a subset of {@code produced}.
     *
     * <p>These are exactly the branches {@link Arc.Out#enumerateBranches()} enumerates for
     * static analysis, restricted to those consistent with what was written — one runtime
     * definition of "a branch", one static one, and they agree.
     *
     * <p>The subset restriction is the pruning that keeps this linear in practice: a leaf naming
     * a place that was not produced yields nothing, so a {@code Xor} branch dies as soon as it
     * claims something unwritten, and an {@code And} dies with any unsatisfiable child. Branching
     * survives only where several {@code Xor} children are simultaneously consistent with what
     * was produced — the ambiguous case, which is rejected anyway.
     */
    private static List<Set<Place<?>>> claimsWithin(Arc.Out spec, Set<Place<?>> produced) {
        return switch (spec) {
            case Arc.Out.Place p -> produced.contains(p.place())
                ? List.<Set<Place<?>>>of(Set.of(p.place()))
                : List.<Set<Place<?>>>of();

            case Arc.Out.ForwardInput f -> produced.contains(f.to())
                ? List.<Set<Place<?>>>of(Set.of(f.to()))
                : List.<Set<Place<?>>>of();

            case Arc.Out.Timeout t -> claimsWithin(t.child(), produced);

            case Arc.Out.Xor xor -> {
                var out = new ArrayList<Set<Place<?>>>();
                for (Arc.Out child : xor.children()) {
                    out.addAll(claimsWithin(child, produced));
                }
                yield capMultiplicity(out);
            }

            case Arc.Out.And and -> {
                // Unordered: the children are a set of obligations, so this is a join over their
                // claim sets and the result cannot depend on their declaration order.
                List<Set<Place<?>>> acc = List.of(Set.of());
                for (Arc.Out child : and.children()) {
                    var childClaims = claimsWithin(child, produced);
                    if (childClaims.isEmpty()) {
                        yield List.<Set<Place<?>>>of(); // no assignment can satisfy this And
                    }
                    var next = new ArrayList<Set<Place<?>>>(acc.size() * childClaims.size());
                    for (Set<Place<?>> partial : acc) {
                        for (Set<Place<?>> claim : childClaims) {
                            var merged = new HashSet<Place<?>>(partial);
                            merged.addAll(claim);
                            next.add(merged);
                        }
                    }
                    acc = capMultiplicity(next);
                }
                yield acc;
            }
        };
    }

    /**
     * Collapses identical claims, keeping at most two of each.
     *
     * <p>Validation only needs to distinguish "no assignment", "exactly one" and "more than
     * one", so a third assignment claiming an already-seen set carries no information. Without
     * this the {@code And} join is O(2^k) in the number of {@code Xor} children — on a path that
     * runs on every firing. With it the working set is bounded by the number of DISTINCT claim
     * subsets, which is at most 2^|produced|; the produced set is what the action actually wrote,
     * and is small.
     */
    private static List<Set<Place<?>>> capMultiplicity(List<Set<Place<?>>> claims) {
        if (claims.size() < 3) return claims;
        var seen = new HashMap<Set<Place<?>>, Integer>();
        var out = new ArrayList<Set<Place<?>>>(claims.size());
        for (Set<Place<?>> claim : claims) {
            int n = seen.getOrDefault(claim, 0);
            if (n >= 2) continue;
            seen.put(claim, n + 1);
            out.add(claim);
        }
        return out;
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
     * <p>Single implementation shared by both executors, which previously carried separate
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
