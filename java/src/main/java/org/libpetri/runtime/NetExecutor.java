package org.libpetri.runtime;

import java.time.Duration;
import java.time.Instant;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicBoolean;

import org.libpetri.core.*;
import org.libpetri.debug.LogCaptureScope;
import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;
/**
 * Orchestrator for executing Coloured Time Petri Nets.
 *
 * <p>The executor manages the complete lifecycle of a Petri net execution:
 * token flow, transition enablement, firing, and completion detection.
 * It uses virtual threads for scalable async transition execution.
 *
 * <h2>Concurrency Model</h2>
 * <ul>
 *   <li>All Petri net state (marking, enabledAt, inFlight) is owned by the
 *       orchestrator thread (the one calling {@link #run()}).</li>
 *   <li>Transition actions run on the configured {@link ExecutorService} and may
 *       complete on arbitrary threads, but they MUST NOT touch the marking
 *       directly.</li>
 *   <li>Actions signal completion via an internal queue. The orchestrator
 *       then applies marking changes in a thread-safe manner.</li>
 * </ul>
 *
 * <h2>Scheduling Policy</h2>
 * <p>When multiple transitions are ready to fire:
 * <ol>
 *   <li>Higher priority transitions fire first</li>
 *   <li>For equal priority, transitions enabled earlier are preferred (FIFO)</li>
 * </ol>
 *
 * <h2>Usage</h2>
 * <pre>{@code
 * var net = PetriNet.builder("MyNet")
 *     .transitions(t1, t2, t3)
 *     .build();
 *
 * var initial = Map.of(startPlace, List.of(Token.of("input")));
 *
 * // Simple usage
 * try (var executor = NetExecutor.create(net, initial)) {
 *     Marking result = executor.run();
 * }
 *
 * // With configuration
 * try (var executor = NetExecutor.builder(net, initial)
 *         .eventStore(EventStore.inMemory())
 *         .executor(myExecutorService)
 *         .build()) {
 *     Marking result = executor.run();
 * }
 * }</pre>
 *
 * @see PetriNet
 * @see Marking
 * @see EventStore
 */
public final class NetExecutor implements PetriNetExecutor {
    private final PetriNet net;
    private final Marking marking;
    private final EventStore eventStore;
    private final ExecutorService executor;
    private final ExecutionContextProvider executionContextProvider;
    private final long startNanos;

    /** Enabled transitions mapped to their enable time (nanos). */
    private final Map<Transition, Long> enabledAt = new HashMap<>();

    /** Currently executing transitions. */
    private final Map<Transition, InFlightTransition> inFlight = new HashMap<>();

    /** Holds in-flight transition state. */
    private record InFlightTransition(
        CompletableFuture<Void> future,
        TransitionContext context,
        List<Token<?>> consumed,
        long startNanos
    ) {}

    /** Lock-free completion signaling queue. */
    private final Queue<Transition> completionQueue = new ConcurrentLinkedQueue<>();

    /**
     * Places that were reset via reset arcs since the last updateEnabledTransitions() call.
     *
     * <p>Thread-safety: Only accessed from the orchestrator thread (single-threaded).
     * Used to detect when a timed transition's input tokens were replaced (removed and re-added),
     * which requires restarting the transition's clock.
     */
    private final Set<Place<?>> pendingResetPlaces = new HashSet<>();

    /**
     * Precomputed mapping from transition to its input places (both new and legacy API).
     *
     * <p>Thread-safety: Immutable after construction (Map.copyOf with Set.copyOf values).
     * Used for O(1) lookups in {@link #hasInputFromResetPlace(Transition)} instead of
     * iterating through inputSpecs and inputs on every call.
     */
    private final Map<Transition, Set<Place<?>>> transitionInputPlaces;

    /** Lock-free queue for external token injections. */
    private final Queue<ExternalEvent<?>> externalEventQueue = new ConcurrentLinkedQueue<>();

    /** Environment places that can receive external tokens. */
    private final Set<EnvironmentPlace<?>> environmentPlaces;

    /** Wake-up signal for instant response to external events. */
    private final Semaphore wakeUpSignal = new Semaphore(0);

    /** Whether this executor has environment places (implies long-running behavior). */
    private final boolean hasEnvironmentPlaces;

    /** Tracks if drain() was called — reject new inject() calls. */
    private final AtomicBoolean draining = new AtomicBoolean(false);

    /** Tracks if close() was called — immediate shutdown. */
    private final AtomicBoolean closed = new AtomicBoolean(false);

    private volatile boolean running = false;

    private NetExecutor(
        PetriNet net,
        Marking marking,
        EventStore eventStore,
        ExecutorService executor,
        Set<EnvironmentPlace<?>> environmentPlaces,
        ExecutionContextProvider executionContextProvider
    ) {
        this.net = net;
        this.marking = marking;
        this.eventStore = eventStore;
        this.executor = executor;
        this.environmentPlaces = environmentPlaces;
        this.hasEnvironmentPlaces = !environmentPlaces.isEmpty();
        this.executionContextProvider = executionContextProvider;
        this.startNanos = System.nanoTime();

        // Precompute input places per transition for O(1) reset-place lookups
        this.transitionInputPlaces = precomputeInputPlaces(net);
    }

    /**
     * Precomputes the set of input places for each transition.
     * Called once at construction time to avoid repeated iteration at runtime.
     */
    private static Map<Transition, Set<Place<?>>> precomputeInputPlaces(PetriNet net) {
        var result = new HashMap<Transition, Set<Place<?>>>();
        for (var t : net.transitions()) {
            var places = new HashSet<Place<?>>();
            for (var in : t.inputSpecs()) {
                places.add(in.place());
            }
            result.put(t, Set.copyOf(places));
        }
        return Map.copyOf(result);
    }

    // ======================== Factory Methods ========================

    /**
     * Creates an executor with default configuration.
     *
     * <p>Uses in-memory event store and virtual thread executor.
     *
     * @param net the Petri net to execute
     * @param initialTokens initial marking (place → tokens)
     * @return new executor ready to run
     */
    public static NetExecutor create(
        PetriNet net,
        Map<Place<?>, List<Token<?>>> initialTokens
    ) {
        return new NetExecutor(
            net,
            Marking.from(initialTokens),
            EventStore.inMemory(),
            Executors.newVirtualThreadPerTaskExecutor(),
            Set.of(),
            ExecutionContextProvider.NOOP
        );
    }

    /**
     * Creates an executor with custom event store.
     *
     * @param net the Petri net to execute
     * @param initialTokens initial marking (place → tokens)
     * @param eventStore event store for execution history
     * @return new executor ready to run
     */
    public static NetExecutor create(
        PetriNet net,
        Map<Place<?>, List<Token<?>>> initialTokens,
        EventStore eventStore
    ) {
        return new NetExecutor(
            net,
            Marking.from(initialTokens),
            eventStore,
            Executors.newVirtualThreadPerTaskExecutor(),
            Set.of(),
            ExecutionContextProvider.NOOP
        );
    }

    /**
     * Creates an executor with full configuration.
     *
     * @param net the Petri net to execute
     * @param initialTokens initial marking (place → tokens)
     * @param eventStore event store for execution history
     * @param executor executor service for transition actions
     * @return new executor ready to run
     */
    public static NetExecutor create(
        PetriNet net,
        Map<Place<?>, List<Token<?>>> initialTokens,
        EventStore eventStore,
        ExecutorService executor
    ) {
        return new NetExecutor(
            net,
            Marking.from(initialTokens),
            eventStore,
            executor,
            Set.of(),
            ExecutionContextProvider.NOOP
        );
    }

    /**
     * Creates a builder for configuring the executor.
     *
     * @param net the Petri net to execute
     * @param initialTokens initial marking (place → tokens)
     * @return builder for further configuration
     */
    public static Builder builder(PetriNet net, Map<Place<?>, List<Token<?>>> initialTokens) {
        return new Builder(net, initialTokens);
    }

    /**
     * Builder for configuring {@link NetExecutor} instances.
     */
    public static final class Builder {
        private final PetriNet net;
        private final Map<Place<?>, List<Token<?>>> initialTokens;
        private EventStore eventStore = EventStore.inMemory();
        private ExecutorService executor = null; // null = create virtual thread executor
        private Set<EnvironmentPlace<?>> environmentPlaces = Set.of();
        private ExecutionContextProvider executionContextProvider = ExecutionContextProvider.NOOP;

        private Builder(PetriNet net, Map<Place<?>, List<Token<?>>> initialTokens) {
            this.net = Objects.requireNonNull(net, "net");
            this.initialTokens = Objects.requireNonNull(initialTokens, "initialTokens");
        }

        /**
         * Sets the event store for execution history.
         *
         * @param eventStore event store (default: in-memory)
         * @return this builder
         */
        public Builder eventStore(EventStore eventStore) {
            this.eventStore = Objects.requireNonNull(eventStore, "eventStore");
            return this;
        }

        /**
         * Sets the executor service for transition actions.
         *
         * @param executor executor service (default: virtual thread executor)
         * @return this builder
         */
        public Builder executor(ExecutorService executor) {
            this.executor = Objects.requireNonNull(executor, "executor");
            return this;
        }

        /**
         * Declares places as environment places that can receive external tokens.
         *
         * <p>Environment places enable reactive behavior where external threads
         * can inject tokens using {@link NetExecutor#inject}. The executor wakes
         * immediately upon token injection.
         *
         * @param places environment places
         * @return this builder
         */
        @SafeVarargs
        public final Builder environmentPlaces(EnvironmentPlace<?>... places) {
            this.environmentPlaces = Set.of(places);
            return this;
        }

        public final Builder environmentPlaces(Set<EnvironmentPlace<?>> places) {
            this.environmentPlaces = places;
            return this;
        }

        /**
         * Sets the execution context provider for injecting context into transitions.
         *
         * <p>The provider is called once per transition firing, allowing external
         * systems (like tracing) to pass data to transition actions via
         * {@link TransitionContext#executionContext(Class)}.
         *
         * @param provider execution context provider (default: NOOP)
         * @return this builder
         */
        public Builder executionContextProvider(ExecutionContextProvider provider) {
            this.executionContextProvider = Objects.requireNonNull(provider, "executionContextProvider");
            return this;
        }

        /**
         * Builds the executor.
         *
         * @return configured executor ready to run
         */
        public NetExecutor build() {
            ExecutorService exec = executor != null
                ? executor
                : Executors.newVirtualThreadPerTaskExecutor();
            return new NetExecutor(
                net,
                Marking.from(initialTokens),
                eventStore,
                exec,
                environmentPlaces,
                executionContextProvider
            );
        }
    }

    // ======================== Execution ========================

    /**
     * Runs the Petri net to completion synchronously.
     *
     * <p>Executes on the calling thread - the orchestrator is single-threaded.
     * Only transition actions execute asynchronously on the configured executor.
     *
     * <p>Execution completes when no transitions are enabled and no transitions
     * are in-flight (quiescent state). This may indicate:
     * <ul>
     *   <li>Successful completion (tokens in final places)</li>
     *   <li>Deadlock (no progress possible from current marking)</li>
     * </ul>
     *
     * @return final marking after execution
     */
    public Marking run() {
        return executeLoop();
    }

    /**
     * Runs the Petri net with a timeout.
     *
     * <p>Returns a {@link CompletionStage} that completes with the final marking
     * or fails with {@link TimeoutException} if the timeout is exceeded.
     *
     * @param timeout maximum execution time
     * @return completion stage with final marking
     */
    public CompletionStage<Marking> run(Duration timeout) {
        return CompletableFuture.supplyAsync(
            this::executeLoop,
            executor
        ).orTimeout(timeout.toMillis(), TimeUnit.MILLISECONDS);
    }

    // ======================== Environment Place API ========================

    /**
     * Convenience method that wraps the value in a Token before injection.
     *
     * <p>Equivalent to {@code inject(place, Token.of(token))}.
     *
     * @param <T> token type
     * @param place environment place to inject into
     * @param token value to wrap and inject
     * @return future completing with true if injection succeeded
     * @see #inject(EnvironmentPlace, Token)
     */
    public <T> CompletableFuture<Boolean> inject(EnvironmentPlace<T> place, T token) {
        return inject(place, Token.of(token));
    }

    /**
     * Injects a token into an environment place from an external thread.
     *
     * <p>Thread-safe. Can be called from any thread while the executor is running.
     * The orchestrator wakes immediately to process the event.
     *
     * <p><b>Happens-before guarantee:</b> When the returned future completes,
     * the token has been added to the marking and enablement has been recalculated.
     *
     * @param <T> token type
     * @param place environment place to inject into
     * @param token token to inject
     * @return future completing with true if injection succeeded, false if executor is closed,
     *         or failing with {@link IllegalArgumentException} if place is not an environment place
     */
    public <T> CompletableFuture<Boolean> inject(EnvironmentPlace<T> place, Token<T> token) {
        if (!environmentPlaces.contains(place)) {
            return CompletableFuture.failedFuture(new IllegalArgumentException(
                "Place " + place.name() + " is not registered as an environment place"
            ));
        }
        if (closed.get() || draining.get()) {
            return CompletableFuture.completedFuture(false);
        }

        var event = new ExternalEvent<>(place.place(), token, new CompletableFuture<>());
        externalEventQueue.offer(event);

        // Wake up orchestrator immediately
        wakeUp();

        return event.resultFuture();
    }

    /**
     * Injects a token without waiting for completion.
     *
     * <p>Fire-and-forget variant for high-throughput scenarios.
     *
     * @param <T> token type
     * @param place environment place to inject into
     * @param token token to inject
     */
    public <T> void injectAsync(EnvironmentPlace<T> place, Token<T> token) {
        inject(place, token); // Ignore the future
    }

    /**
     * Wakes up the orchestrator thread.
     *
     * <p>Thread-safe, can be called from any thread.
     */
    private void wakeUp() {
        wakeUpSignal.release();
    }

    private Marking executeLoop() {
        running = true;
        emitEvent(
            new NetEvent.ExecutionStarted(
                Instant.now(),
                net.name(),
                executionId()
            )
        );
        emitMarkingSnapshot();

        while (running && !Thread.currentThread().isInterrupted()) {
            // Process completed transitions
            processCompletedTransitions();

            // Process external events (from inject() calls)
            processExternalEvents();

            // Update enabled transitions
            updateEnabledTransitions();

            // Enforce deadlines (disable transitions past their latest bound)
            enforceDeadlines();

            // Check termination conditions
            if (shouldTerminate()) {
                break;
            }

            // Fire ready transitions
            fireReadyTransitions();

            // Wait for work to become available
            awaitWork();
        }

        running = false;

        // Complete any pending external events with false
        drainPendingExternalEvents();

        emitMarkingSnapshot();
        emitEvent(
            new NetEvent.ExecutionCompleted(
                Instant.now(),
                net.name(),
                executionId(),
                elapsedDuration()
            )
        );

        return marking;
    }

    /**
     * Determines if executor should terminate.
     */
    private boolean shouldTerminate() {
        if (closed.get()) {
            // ENV-013: immediate close — wait for in-flight actions to complete
            return inFlight.isEmpty() && completionQueue.isEmpty();
        }
        if (hasEnvironmentPlaces) {
            return draining.get()
                && enabledAt.isEmpty()
                && inFlight.isEmpty()
                && completionQueue.isEmpty();
        }
        return enabledAt.isEmpty() && inFlight.isEmpty() && completionQueue.isEmpty();
    }

    /**
     * Process external events from the queue.
     */
    @SuppressWarnings("unchecked")
    private void processExternalEvents() {
        if (closed.get()) return; // ENV-013: leave queued events for drainPendingExternalEvents()
        ExternalEvent<?> event;
        while ((event = externalEventQueue.poll()) != null) {
            try {
                // Add token to marking
                marking.addToken(
                    (Place<Object>) event.place(),
                    (Token<Object>) event.token()
                );

                emitEvent(
                    new NetEvent.TokenAdded(
                        Instant.now(),
                        event.place().name(),
                        event.token()
                    )
                );

                event.resultFuture().complete(true);
            } catch (Exception e) {
                event.resultFuture().completeExceptionally(e);
            }
        }
    }

    /**
     * Waits for work to become available.
     */
    private void awaitWork() {
        // Fast path: check if work is already available.
        // When closed, ignore external queue — processExternalEvents() won't consume it,
        // drainPendingExternalEvents() handles it after the loop exits.
        if (!completionQueue.isEmpty() || (!closed.get() && !externalEventQueue.isEmpty())) {
            return;
        }

        // Check if transitions will complete
        if (!inFlight.isEmpty()) {
            // Wait for transition completion OR external event
            awaitCompletionOrEvent();
        } else if (!enabledAt.isEmpty() || (hasEnvironmentPlaces && !draining.get())) {
            // Wait for timed transitions to become ready, or for external events
            awaitExternalEvent();
        }
        // If nothing enabled/in-flight/env-waiting, loop will terminate via shouldTerminate()
    }

    /**
     * Waits for either a transition completion or an external event.
     *
     * <p>Uses a polling approach with short timeouts to avoid thread leaks.
     * The semaphore is checked with tryAcquire to prevent indefinite blocking.
     */
    private void awaitCompletionOrEvent() {
        // Fast path: check if any future is already done
        for (var flight : inFlight.values()) {
            if (flight.future().isDone()) return;
        }
        if (!completionQueue.isEmpty() || (!closed.get() && !externalEventQueue.isEmpty())) return;

        if (!inFlight.isEmpty()) {
            var futures = inFlight.values().stream()
                .map(InFlightTransition::future)
                .toArray(CompletableFuture[]::new);

            // Create a future that completes when any transition completes
            CompletableFuture<Object> anyCompletion = CompletableFuture.anyOf(futures);

            // Poll until either a transition completes or an external event arrives
            while (!anyCompletion.isDone()) {
                // Use the shorter of the default poll interval and time until next timed transition
                long pollMs = Math.max(1, Math.min(50, millisUntilNextTimedTransition()));

                // Check for external events with short timeout
                try {
                    if (wakeUpSignal.tryAcquire(pollMs, TimeUnit.MILLISECONDS)) {
                        // External event arrived - drain excess permits and return
                        wakeUpSignal.drainPermits();
                        return;
                    }
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    return;
                }

                // Check queues (external event may have arrived without permit)
                if (!completionQueue.isEmpty() || (!closed.get() && !externalEventQueue.isEmpty())) {
                    return;
                }

                // Timed transition may have become ready (pollMs was bounded by timer)
                if (millisUntilNextTimedTransition() <= 0) return;
            }

            // Drain any accumulated permits
            wakeUpSignal.drainPermits();
        }
    }

    /**
     * Calculates milliseconds until the earliest timed transition becomes ready.
     *
     * @return 0 if any transition is ready now, Long.MAX_VALUE if none are timed
     */
    private long millisUntilNextTimedTransition() {
        if (enabledAt.isEmpty()) return Long.MAX_VALUE;

        long nowNanos = System.nanoTime();
        long minWaitMs = Long.MAX_VALUE;

        for (var entry : enabledAt.entrySet()) {
            Transition t = entry.getKey();
            // Skip immediate/unconstrained transitions — they have no timing to wait for
            if (t.timing() instanceof Timing.Immediate || t.timing() instanceof Timing.Unconstrained) continue;

            long enabledNanos = entry.getValue();
            long elapsedMs = (nowNanos - enabledNanos) / 1_000_000;

            // Time until earliest bound (when transition becomes ready to fire)
            long earliestMs = t.timing().earliest().toMillis();
            long remainingEarliest = earliestMs - elapsedMs;
            if (remainingEarliest <= 0) return 0;
            minWaitMs = Math.min(minWaitMs, remainingEarliest);

            // Time until deadline (when transition must be force-disabled)
            if (t.timing().hasDeadline()) {
                long latestMs = t.timing().latest().toMillis();
                long remainingDeadline = latestMs - elapsedMs;
                if (remainingDeadline <= 0) return 0;
                minWaitMs = Math.min(minWaitMs, remainingDeadline);
            }
        }
        return minWaitMs;
    }

    /**
     * Waits for external event when environment places are registered.
     *
     * <p>Uses timed wait when there are delayed transitions waiting to fire,
     * ensuring the executor wakes up when timed transitions become ready.
     */
    private void awaitExternalEvent() {
        try {
            long waitMs = millisUntilNextTimedTransition();
            if (waitMs <= 0) {
                // Timed transition ready - don't wait
                return;
            } else if (waitMs == Long.MAX_VALUE) {
                // No timed transitions - block until external event
                wakeUpSignal.acquire();
            } else {
                // Wait until next timed transition OR external event
                wakeUpSignal.tryAcquire(waitMs, TimeUnit.MILLISECONDS);
            }
            wakeUpSignal.drainPermits();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }

    /**
     * Drains pending external events when shutting down.
     */
    private void drainPendingExternalEvents() {
        ExecutorSupport.drainPendingExternalEvents(externalEventQueue);
    }

    // ======================== Deadline Enforcement ========================

    /**
     * Disables transitions that have exceeded their timing deadline.
     *
     * <p>For each enabled transition with {@code timing().hasDeadline()}, checks
     * if the elapsed time since enablement exceeds {@code timing().latest()}.
     * If so, the transition is disabled and a {@link NetEvent.TransitionTimedOut}
     * event is emitted.
     *
     * @see org.libpetri.core.Timing#hasDeadline()
     * @see org.libpetri.core.Timing#latest()
     */
    private void enforceDeadlines() {
        long nowNanos = System.nanoTime();
        var expired = new ArrayList<Transition>();

        for (var entry : enabledAt.entrySet()) {
            Transition t = entry.getKey();
            if (!t.timing().hasDeadline()) continue;

            long enabledNanos = entry.getValue();
            long elapsedMillis = (nowNanos - enabledNanos) / 1_000_000;
            long latestMillis = t.timing().latest().toMillis();

            if (elapsedMillis > latestMillis) {
                expired.add(t);
                emitEvent(new NetEvent.TransitionTimedOut(
                    Instant.now(), t.name(),
                    t.timing().latest(),
                    Duration.ofMillis(elapsedMillis)));
            }
        }

        for (Transition t : expired) {
            enabledAt.remove(t);
        }
    }

    // ======================== Transition Lifecycle ========================

    /**
     * Check all transitions for enablement (no dirty set optimization).
     */
    private void updateEnabledTransitions() {
        long nowNanos = System.nanoTime();

        for (Transition t : net.transitions()) {
            if (inFlight.containsKey(t)) continue;

            boolean wasEnabled = enabledAt.containsKey(t);
            boolean canNowEnable = canEnable(t);

            if (canNowEnable && !wasEnabled) {
                enabledAt.put(t, nowNanos);
                emitEvent(
                    new NetEvent.TransitionEnabled(
                        Instant.now(),
                        t.name()
                    )
                );
            } else if (!canNowEnable && wasEnabled) {
                enabledAt.remove(t);
            } else if (canNowEnable && wasEnabled && hasInputFromResetPlace(t)) {
                // BUG FIX: When a transition was enabled before, is still enabled now,
                // but any of its input places was reset (tokens removed and re-added),
                // we must restart the transition's clock. This handles the case where
                // a reset arc removes tokens and the action immediately outputs new tokens
                // to the same place - the timed transition should restart its countdown.
                enabledAt.put(t, nowNanos);
                emitEvent(
                    new NetEvent.TransitionClockRestarted(
                        Instant.now(),
                        t.name()
                    )
                );
            }
        }

        // Clear reset places tracking for next iteration
        pendingResetPlaces.clear();
    }

    /**
     * Checks if any of the transition's input places were recently reset.
     * Uses precomputed {@link #transitionInputPlaces} for O(min(|reset|, |inputs|)) lookup
     * instead of O(|inputSpecs| + |inputs|) iteration.
     */
    private boolean hasInputFromResetPlace(Transition t) {
        if (pendingResetPlaces.isEmpty()) {
            return false;
        }
        // Collections.disjoint returns true if NO common elements
        // We want true if there ARE common elements, hence the negation
        return !Collections.disjoint(pendingResetPlaces, transitionInputPlaces.get(t));
    }

    private boolean canEnable(Transition t) {
        // Check inhibitors
        for (var arc : t.inhibitors()) {
            if (marking.hasTokens(arc.place())) return false;
        }

        // Check reads
        for (var arc : t.reads()) {
            if (!marking.hasTokens(arc.place())) return false;
        }

        // Check input specs with cardinality
        for (var in : t.inputSpecs()) {
            int available = marking.tokenCount(in.place());
            int required = in.requiredCount();
            if (available < required) {
                return false;
            }
        }

        return true;
    }

    /**
     * Fire all ready transitions (those whose earliest time has been reached).
     * Fires transitions in priority order, re-checking enablement after each fire.
     */
    private void fireReadyTransitions() {
        if (enabledAt.isEmpty()) return;

        long nowNanos = System.nanoTime();
        List<Map.Entry<Transition, Long>> ready = new ArrayList<>();
        for (var entry : enabledAt.entrySet()) {
            Transition t = entry.getKey();
            long enabledNanos = entry.getValue();
            long elapsedMillis = (nowNanos - enabledNanos) / 1_000_000;
            if (t.timing().earliest().toMillis() <= elapsedMillis) {
                ready.add(entry);
            }
        }
        if (ready.isEmpty()) return;

        List<Transition> fireOrder = selectFireOrder(ready);
        for (Transition t : fireOrder) {
            if (enabledAt.containsKey(t) && canEnable(t)) {
                fireTransition(t);
            } else {
                enabledAt.remove(t);
            }
        }
    }

    /**
     * Scheduler policy: choose an order in which to fire ready transitions.
     *
     * Current policy:
     * - Higher priority transitions first.
     * - For equal priority, transitions enabled earlier are preferred.
     */
    private List<Transition> selectFireOrder(
        List<Map.Entry<Transition, Long>> ready
    ) {
        ready.sort((a, b) -> {
            int prioCmp = Integer.compare(
                b.getKey().priority(),
                a.getKey().priority()
            );
            if (prioCmp != 0) return prioCmp;
            return Long.compare(a.getValue(), b.getValue());
        });

        return ready.stream().map(Map.Entry::getKey).toList();
    }

    // Unchecked casts are safe: Place<?> type parameters are erased at runtime,
    // and the marking preserves token types by construction (tokens are added
    // with their correct type from inputSpecs/inputs declarations).
    @SuppressWarnings("unchecked")
    private void fireTransition(Transition t) {
        var inputs = new TokenInput();
        List<Token<?>> consumed = new ArrayList<>();

        // Consume tokens based on input specs with cardinality
        for (var in : t.inputSpecs()) {
            int toConsume = switch (in) {
                case Arc.In.One _ -> 1;
                case Arc.In.Exactly e -> e.count();
                case Arc.In.All _ -> marking.tokenCount(in.place());
                case Arc.In.AtLeast _ -> marking.tokenCount(in.place());
            };

            for (int i = 0; i < toConsume; i++) {
                Token<?> token = marking.removeFirst((Place<Object>) in.place());
                consumed.add(token);
                inputs.add((Place<Object>) in.place(), (Token<Object>) token);
                emitEvent(
                    new NetEvent.TokenRemoved(
                        Instant.now(),
                        in.place().name(),
                        token
                    )
                );
            }
        }

        for (var arc : t.reads()) {
            Token<?> token = marking.peekFirst((Place<Object>) arc.place());
            if (token != null) {
                inputs.add(
                    (Place<Object>) arc.place(),
                    (Token<Object>) token
                );
            }
        }

        for (var arc : t.resets()) {
            var removed = marking.removeAll((Place<Object>) arc.place());
            // Track this place as reset so timed transitions consuming from it
            // will have their clocks restarted when new tokens arrive
            pendingResetPlaces.add(arc.place());
            for (Token<?> token : removed) {
                consumed.add(token);
                emitEvent(
                    new NetEvent.TokenRemoved(
                        Instant.now(),
                        arc.place().name(),
                        token
                    )
                );
            }
        }

        emitEvent(
            new NetEvent.TransitionStarted(Instant.now(), t.name(), consumed)
        );

        // Create execution context from provider (e.g., for tracing)
        Map<Class<?>, Object> execContext = executionContextProvider.createContext(t, consumed);

        // Create TransitionContext with filtered I/O based on structure
        var context = new TransitionContext(t, inputs, new TokenOutput(), execContext);

        CompletableFuture<Void> transitionFuture = eventStore.isEnabled()
            ? LogCaptureScope.call(t.name(), eventStore::append,
                  () -> t.action().execute(context).toCompletableFuture())
            : t.action().execute(context).toCompletableFuture();

        // Handle Out.Timeout: If the transition has a timeout in its output spec,
        // wrap the action with timeout handling. On timeout, we cancel the action
        // and produce tokens to the timeout branch.
        if (t.hasActionTimeout()) {
            var timeoutSpec = t.actionTimeout();
            long timeoutMillis = timeoutSpec.after().toMillis();
            var originalFuture = transitionFuture;

            transitionFuture = transitionFuture
                .orTimeout(timeoutMillis, TimeUnit.MILLISECONDS)
                .exceptionally(ex -> {
                    if (ex instanceof TimeoutException || ex.getCause() instanceof TimeoutException) {
                        // Cancel the original action to prevent it from producing output
                        originalFuture.cancel(true);
                        // Produce tokens to timeout branch (synchronized via context)
                        produceTimeoutOutput(context, timeoutSpec.child());
                        emitEvent(new NetEvent.ActionTimedOut(
                            Instant.now(), t.name(), timeoutSpec.after()));
                        return null;  // Swallow timeout exception, we handled it
                    }
                    // Re-throw other exceptions
                    throw (ex instanceof RuntimeException re) ? re : new RuntimeException(ex);
                });
        }

        // Signal completion to orchestrator and wake up if waiting
        transitionFuture.whenComplete((_, _) -> {
            completionQueue.offer(t);
            wakeUp();
        });

        inFlight.put(t, new InFlightTransition(transitionFuture, context, consumed, System.nanoTime()));
        enabledAt.remove(t);
    }

    private void produceTimeoutOutput(TransitionContext context, Arc.Out timeoutChild) {
        ExecutorSupport.produceTimeoutOutput(context, timeoutChild);
    }

    /**
     * Process completed transitions from the completion queue.
     *
     * <p>Thread safety: The outputs are returned through the CompletionStage,
     * which provides the happens-before guarantee. When join() returns, all
     * writes to the TokenOutput object are visible to this thread.
     */
    @SuppressWarnings("unchecked")
    private void processCompletedTransitions() {
        Transition t;
        while ((t = completionQueue.poll()) != null) {
            InFlightTransition flight = inFlight.remove(t);
            if (flight == null) continue;  // Already processed (shouldn't happen)

            try {
                // join() establishes happens-before - all context writes are now visible
                flight.future().join();

                // Get outputs from context (where action wrote them)
                TokenOutput outputs = flight.context().rawOutput();

                // NEW: Validate output against declared Out spec
                validateOutput(t, outputs);

                List<Token<?>> produced = new ArrayList<>();

                for (var entry : outputs.entries()) {
                    var token = entry.token();
                    // All tokens go to marking - postset discipline (no isUnit filtering)
                    marking.addToken((Place<Object>) entry.place(), (Token<Object>) token);
                    produced.add(token);
                    emitEvent(new NetEvent.TokenAdded(Instant.now(), entry.place().name(), token));
                }

                var transitionDuration = Duration.ofNanos(System.nanoTime() - flight.startNanos());
                emitEvent(new NetEvent.TransitionCompleted(
                    Instant.now(), t.name(), produced, transitionDuration));

            } catch (OutViolationException e) {
                // Output validation failed - treat as transition failure
                handleTransitionFailure(t, new CompletionException(e));
            } catch (CompletionException e) {
                handleTransitionFailure(t, e);
            }
        }
    }

    /**
     * Handle transition action failures.
     *
     * <p>Note: Timeout is no longer handled here as a failure. Use
     * {@link TransitionAction#withTimeout} to wrap actions with timeout handling.
     * The wrapper ensures actions always produce output (normal or timeout marker),
     * preserving proper TPN semantics.
     */
    private void handleTransitionFailure(Transition t, CompletionException e) {
        emitEvent(
            new NetEvent.TransitionFailed(
                Instant.now(),
                t.name(),
                e.getCause().getMessage(),
                e.getCause().getClass().getName()
            )
        );
    }

    // ======================== State Inspection ========================

    /**
     * Returns the current marking (token state) of the net.
     *
     * <p>The returned marking is the live internal state. During execution,
     * it may change as transitions fire. For a snapshot, call after execution
     * completes.
     *
     * @return current marking
     */
    public Marking marking() {
        return marking;
    }

    /**
     * Checks if execution has reached a quiescent state.
     *
     * <p>A quiescent state means no transitions are enabled and no transitions
     * are in-flight. This indicates execution has completed (either successfully
     * or in a deadlock).
     *
     * @return {@code true} if no transitions are enabled or in-flight
     */
    public boolean isQuiescent() {
        return enabledAt.isEmpty() && inFlight.isEmpty();
    }

    /**
     * Checks if execution is waiting for in-flight transitions.
     *
     * <p>This state occurs when no transitions can be newly enabled, but
     * some transitions are still executing. Progress depends on the completion
     * of currently running transition actions.
     *
     * @return {@code true} if waiting for in-flight transitions to complete
     */
    public boolean isWaitingForCompletion() {
        return enabledAt.isEmpty() && !inFlight.isEmpty();
    }

    /**
     * Returns the number of transitions currently executing.
     *
     * @return count of in-flight transitions
     */
    public int inFlightCount() {
        return inFlight.size();
    }

    /**
     * Returns the number of enabled transitions waiting to fire.
     *
     * @return count of enabled transitions
     */
    public int enabledCount() {
        return enabledAt.size();
    }

    /**
     * Returns a unique identifier for this execution.
     *
     * <p>Based on the start time in nanoseconds (hex-encoded).
     *
     * @return execution identifier
     */
    public String executionId() {
        return Long.toHexString(startNanos);
    }

    // ======================== Internal Helpers ========================

    private void emitEvent(NetEvent event) {
        if (eventStore.isEnabled()) {
            eventStore.append(event);
        }
    }

    private Duration elapsedDuration() {
        return Duration.ofNanos(System.nanoTime() - startNanos);
    }

    private void emitMarkingSnapshot() {
        emitEvent(new NetEvent.MarkingSnapshot(Instant.now(), marking.snapshot()));
    }

    // ======================== Output Validation ========================

    /**
     * Validates that the transition output satisfies its declared Out spec.
     *
     * @param t the transition that just completed
     * @param outputs the produced tokens
     * @throws OutViolationException if output doesn't match declared spec
     */
    private void validateOutput(Transition t, TokenOutput outputs) {
        if (t.outputSpec() == null) return; // No spec = no validation (legacy mode)

        Set<Place<?>> produced = outputs.placesWithTokens();
        ExecutorSupport.validateOutSpec(t.name(), t.outputSpec(), produced)
            .orElseThrow(() -> new OutViolationException(
                "'%s': output does not satisfy declared spec".formatted(t.name())));
    }

    @Override
    public void drain() {
        draining.set(true);
        wakeUp();
    }

    @Override
    public void close() {
        draining.set(true);
        closed.set(true);
        wakeUp();
    }
}
