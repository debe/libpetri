package org.libpetri.runtime;

import java.time.Duration;
import java.time.Instant;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.locks.LockSupport;
import java.util.concurrent.atomic.AtomicLongArray;
import java.util.function.Function;
import java.util.function.Predicate;

import org.libpetri.core.*;
import org.libpetri.debug.LogCaptureScope;
import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;

/**
 * Lock-free bitmap-based executor for Coloured Time Petri Nets.
 *
 * <p>Replaces the O(n²) full-scan approach of {@link NetExecutor} with:
 * <ul>
 *   <li><b>Presence bitmap</b> — one bit per place, orchestrator-confined</li>
 *   <li><b>Event-driven dirty set</b> — only transitions affected by a token change
 *       are re-evaluated, using a precomputed reverse index from {@link CompiledNet}</li>
 *   <li><b>BitSet mask checks</b> — enablement verified via bitwise AND/compare
 *       against precomputed read-only masks</li>
 * </ul>
 *
 * <h2>Concurrency Model</h2>
 *
 * <p><b>Transition actions are invoked inline, on the orchestrator thread.</b> The
 * executor never submits them anywhere: {@code action.execute(ctx)} is called directly
 * from the firing loop, and an action that blocks blocks the whole net. What runs
 * concurrently is whatever the action's returned {@link CompletionStage} is driven by —
 * the action's own thread pool, HTTP client or scheduler, none of which libpetri owns.
 *
 * <p>The {@link ExecutorService} configured on this executor hosts exactly one task:
 * the orchestrator loop itself, and only under {@link #run(Duration)}. It does not
 * dispatch actions.
 *
 * <pre>
 *   Thread completing an action              Orchestrator Thread
 *   ───────────────────────────              ──────────────────
 *   1. completionQueue.offer(t)       ──→    processCompletedTransitions()
 *   2. wakeUpSignal.release()         ──→    awaitWork() returns
 *                                            3. set bits in markingBitmap
 *                                            4. set bits in dirtyBitmap
 * </pre>
 *
 * <p>Completion is handed over through the lock-free {@code completionQueue} plus a
 * semaphore release, which establishes the happens-before edge the orchestrator relies
 * on. All marking and bitmap mutation happens on the orchestrator thread, so no
 * synchronization is needed anywhere else.
 *
 * @see CompiledNet
 * @see NetExecutor
 */
public final class BitmapNetExecutor implements PetriNetExecutor, AwaitPollTunable {
    /** Number of bits to shift for word index (2^6 = 64 bits per long). */
    static final int WORD_SHIFT = 6;
    /** Mask for bit position within a word (0x3F = 63). */
    static final int BIT_MASK = 63;

    private final CompiledNet compiled;
    private final Marking marking;

    // ν-net incremental match caches (NU-020): per matched transition, an
    // IncrementalMatcher kept in lockstep with the FIFO marking when the
    // transition is fast-path eligible (every correlated input is One/Exactly,
    // consumed by no other transition, never reset), else null → fall back to
    // the O(n) rebuild MatchEngine.findBinding. Turns a draining matched join
    // from O(n²) into O(n log n). (Java's ArrayDeque marking already removes the
    // head in O(1), so only the selection rebuild needed fixing here.)
    private MatchEngine.IncrementalMatcher[] matchCaches;
    private java.util.List<int[]>[] placeMatchTargets;
    private final EventStore eventStore;
    private final ExecutorService executor;
    private final ExecutionContextProvider executionContextProvider;
    private final long startNanos;

    /** Monotonic source for ν-name minting ({@link TransitionContext#freshName()}, NU-010). */
    private final AtomicLong freshNameCounter = new AtomicLong();

    // Place-presence bitmap driving the hot-path enablement check.
    // Orchestrator-confined, so a plain long[] — no volatile reads, no atomics.
    private final long[] markingBitmap;

    // Orchestrator-owned state (single-threaded)
    private final long[] enabledAtNanos;
    private final long[] enabledBitmap;
    private final long[] inFlightBitmap;
    private final long[] dirtyBitmap;
    /** Reusable buffer for dirty-set snapshots (orchestrator-thread only). */
    private final long[] dirtyScanBuffer;
    /** Number of long words needed for transition bitmaps. */
    private final int transitionWords;
    /** Reusable list for ready transitions (orchestrator-thread only). */
    private final List<ReadyTransition> readyBuffer = new ArrayList<>();
    /** Cached flag: true if any transition in the net has a deadline. */
    private final boolean hasAnyDeadlines;
    /** Grace band (ms) before a hard deadline ({@code deadline()}/{@code window()}) force-disables. */
    private final long deadlineToleranceMillis;
    /** Cached flag: true if event store accepts events (avoids eager Instant.now() allocation). */
    private final boolean eventStoreEnabled;
    /** Cached flag: true if all transitions have immediate timing (earliest=0, no deadline). */
    private final boolean allImmediate;
    /** Bitmap mask of transitions that have non-trivial timing (delayed, windowed, deadline, exact). */
    private final long[] timedMask;
    /** Cached flag: true if all transitions share the same priority. */
    private final boolean allSamePriority;
    /** Number of currently enabled transitions — maintained incrementally for O(1) queries. */
    private int enabledTransitionCount;

    // In-flight tracking
    private final Map<Transition, InFlightTransition> inFlight = new HashMap<>();

    private record InFlightTransition(
        CompletableFuture<Void> future,
        TransitionContext context,
        List<Token<?>> consumed,
        long startNanos
    ) {}

    private record ReadyTransition(int tid, int priority, long enabledAtNanos) {}

    /** Lock-free completion signaling queue. */
    private final Queue<Transition> completionQueue = new ConcurrentLinkedQueue<>();

    /** Places reset since last updateDirtyTransitions call. */
    private final Set<Place<?>> pendingResetPlaces = new HashSet<>();

    /** Precomputed input places per transition for reset-clock detection. */
    private final Map<Transition, Set<Place<?>>> transitionInputPlaces;

    /** Lock-free queue for external token injections. */
    private final Queue<ExternalEvent<?>> externalEventQueue = new ConcurrentLinkedQueue<>();

    /** Environment places that can receive external tokens. */
    private final Set<EnvironmentPlace<?>> environmentPlaces;

    /** Wake-up signal for instant response to events. */
    private final Semaphore wakeUpSignal = new Semaphore(0);

    /** Completion-wait poll fallback (ms). Only lengthened by tests; see {@link AwaitPollTunable}. */
    private volatile long awaitPollMillis = 50;

    /** Whether this executor has environment places (implies long-running behavior). */
    private final boolean hasEnvironmentPlaces;

    /** Tracks if drain() was called — reject new inject() calls. */
    private final AtomicBoolean draining = new AtomicBoolean(false);

    /** Tracks if close() was called — immediate shutdown. */
    private final AtomicBoolean closed = new AtomicBoolean(false);

    /** Optional handler for action failures; null selects the default logging policy. */
    private final ActionFailureHandler uncaughtActionHandler;

    private volatile boolean running = false;

    /**
     * Set synchronously by {@code run(...)} before the loop task is submitted, so
     * {@link #awaitTermination(Duration)} can tell "not started yet" (return early) from
     * "started, running or finished" (wait on {@link #terminatedFuture}). {@code running}
     * cannot do this: it is written by the loop task, which may not have been scheduled yet.
     */
    private volatile boolean started = false;

    /**
     * Requests immediate termination without waiting for in-flight actions. Set by
     * {@link #terminateNow()} from a foreign thread and read in the loop condition; leaves
     * {@code running} to be cleared by the loop's own {@code finally}, so {@code running}
     * stays a truthful "the loop is alive" signal for {@link #marking()}.
     */
    private volatile boolean stopRequested = false;

    /**
     * Set once the execute loop has finished. Distinct from {@code !running}, which is also
     * true before the loop starts — an inject() before run() is legitimate and must not be
     * drained, whereas one after termination has nobody left to complete it.
     */
    private volatile boolean terminated = false;

    /** Completes when the execute loop finishes, however it finishes. */
    private final CompletableFuture<Marking> terminatedFuture = new CompletableFuture<>();

    /**
     * Whether this executor created its own {@link ExecutorService} and may therefore shut it
     * down. A caller-supplied executor is never shut down — it may host other work.
     */
    private final boolean ownsExecutor;

    /**
     * Owned snapshot published by the orchestrator for foreign-thread {@link #marking()} reads.
     * Refreshed when {@link #markingRequestSeq} outpaces {@link #markingServedSeq}, so observers
     * never read the live marking and the copy costs nothing when nobody is watching. Written
     * only by the orchestrator; {@code volatile} for cross-thread visibility.
     */
    private volatile Marking publishedMarking;

    /** Incremented by a foreign-thread {@link #marking()} to request a fresh {@link #publishedMarking}. */
    private final AtomicLong markingRequestSeq = new AtomicLong();

    /** Highest request sequence the orchestrator has published a snapshot for. */
    private volatile long markingServedSeq = 0;

    /**
     * The orchestrator loop's thread, or {@code null} before it starts and after it finishes.
     * {@code volatile} and published <em>before</em> {@code running = true}, so a foreign
     * {@link #marking()} that observes the loop as live also observes this reference, and is
     * routed to the snapshot rather than the live marking.
     */
    private volatile Thread orchestratorThread;

    private BitmapNetExecutor(
        CompiledNet compiled,
        Marking marking,
        EventStore eventStore,
        ExecutorService executor,
        Set<EnvironmentPlace<?>> environmentPlaces,
        ExecutionContextProvider executionContextProvider,
        long deadlineToleranceMillis,
        ActionFailureHandler uncaughtActionHandler,
        boolean ownsExecutor
    ) {
        this.compiled = compiled;
        this.marking = marking;
        this.eventStore = eventStore;
        this.executor = executor;
        this.ownsExecutor = ownsExecutor;
        this.uncaughtActionHandler = uncaughtActionHandler;
        this.environmentPlaces = environmentPlaces;
        this.hasEnvironmentPlaces = !environmentPlaces.isEmpty();
        this.executionContextProvider = executionContextProvider;
        this.deadlineToleranceMillis = deadlineToleranceMillis;
        this.startNanos = System.nanoTime();

        int wordCount = compiled.wordCount();
        this.markingBitmap = new long[wordCount];

        this.transitionWords = (compiled.transitionCount() + BIT_MASK) >>> WORD_SHIFT;
        this.enabledAtNanos = new long[compiled.transitionCount()];
        this.enabledBitmap = new long[transitionWords];
        this.inFlightBitmap = new long[transitionWords];
        this.dirtyBitmap = new long[transitionWords];
        this.dirtyScanBuffer = new long[transitionWords];
        Arrays.fill(enabledAtNanos, Long.MIN_VALUE); // sentinel: not enabled

        this.eventStoreEnabled = eventStore.isEnabled();
        boolean anyDeadlines = false;
        boolean allImm = true;
        boolean samePrio = true;
        int firstPriority = compiled.transitionCount() > 0 ? compiled.transition(0).priority() : 0;
        for (int tid = 0; tid < compiled.transitionCount(); tid++) {
            Transition t = compiled.transition(tid);
            if (t.timing().hasDeadline()) anyDeadlines = true;
            if (!(t.timing() instanceof Timing.Immediate) && !(t.timing() instanceof Timing.Unconstrained)) {
                allImm = false;
            }
            if (t.priority() != firstPriority) samePrio = false;
        }
        this.hasAnyDeadlines = anyDeadlines;
        this.allImmediate = allImm;
        this.timedMask = new long[transitionWords];
        for (int tid = 0; tid < compiled.transitionCount(); tid++) {
            Transition t = compiled.transition(tid);
            if (!(t.timing() instanceof Timing.Immediate) && !(t.timing() instanceof Timing.Unconstrained)) {
                timedMask[tid >>> WORD_SHIFT] |= 1L << (tid & BIT_MASK);
            }
        }
        this.allSamePriority = samePrio;

        this.transitionInputPlaces = precomputeInputPlaces(compiled.net());

        initMatchCaches();
    }

    /**
     * Builds the ν-net incremental match caches (NU-020). A matched join is
     * fast-path eligible only when every correlated input is One/Exactly, is
     * consumed by no other transition, and is never reset — so the cache can
     * never desync from the marking. Mirrors {@code PrecompiledNetExecutor}.
     */
    @SuppressWarnings("unchecked")
    private void initMatchCaches() {
        int tc = compiled.transitionCount();
        int pc = compiled.placeCount();
        matchCaches = new MatchEngine.IncrementalMatcher[tc];
        placeMatchTargets = new java.util.List[pc];
        for (int pid = 0; pid < pc; pid++) {
            placeMatchTargets[pid] = new ArrayList<>();
        }

        boolean anyMatch = false;
        for (int tid = 0; tid < tc; tid++) {
            if (compiled.transition(tid).matchSpec() != null) { anyMatch = true; break; }
        }
        if (!anyMatch) return;

        List<Integer>[] inputConsumers = new java.util.List[pc];
        boolean[] resetTarget = new boolean[pc];
        for (int pid = 0; pid < pc; pid++) {
            inputConsumers[pid] = new ArrayList<>();
        }
        for (int tid = 0; tid < tc; tid++) {
            Transition t = compiled.transition(tid);
            for (var in : t.inputSpecs()) {
                inputConsumers[compiled.placeId(in.place())].add(tid);
            }
            for (var rs : t.resets()) {
                resetTarget[compiled.placeId(rs.place())] = true;
            }
        }

        for (int tid = 0; tid < tc; tid++) {
            Transition t = compiled.transition(tid);
            MatchSpec ms = t.matchSpec();
            if (ms == null) continue;

            int[] requireds = new int[ms.keys().size()];
            boolean eligible = true;
            int ki = 0;
            for (var key : ms.keys()) {
                int pid = compiled.placeId(key.place());
                int required = -1;
                for (var in : t.inputSpecs()) {
                    if (in.place().equals(key.place())) {
                        if (in instanceof Arc.In.One) required = 1;
                        else if (in instanceof Arc.In.Exactly e) required = e.count();
                        break;
                    }
                }
                if (required < 0) { eligible = false; break; } // AtLeast/All → fall back
                List<Integer> cons = inputConsumers[pid];
                if (resetTarget[pid] || cons.size() != 1 || cons.get(0) != tid) { eligible = false; break; }
                requireds[ki++] = required;
            }
            if (!eligible) continue;

            var matcher = new MatchEngine.IncrementalMatcher(requireds);
            int keyIdx = 0;
            for (var key : ms.keys()) {
                int pid = compiled.placeId(key.place());
                for (Token<?> token : marking.peekTokens((Place<Object>) key.place())) {
                    NameId name = key.extract(token.value());
                    if (name != null) {
                        matcher.add(keyIdx, name, token.createdAt().toEpochMilli());
                    }
                }
                placeMatchTargets[pid].add(new int[] {tid, keyIdx});
                keyIdx++;
            }
            matchCaches[tid] = matcher;
        }
    }

    /** Mirror a token added to correlated input {@code place} into every fast-path matcher. */
    private void cacheAddToken(Place<?> place, Token<?> token) {
        int pid = compiled.placeId(place);
        if (pid < 0) return;
        List<int[]> targets = placeMatchTargets[pid];
        if (targets.isEmpty()) return;
        for (int[] tgt : targets) {
            int tid = tgt[0];
            int keyIdx = tgt[1];
            MatchEngine.IncrementalMatcher cache = matchCaches[tid];
            if (cache == null) continue;
            var key = compiled.transition(tid).matchSpec().keys().get(keyIdx);
            NameId name = key.extract(token.value());
            if (name != null) {
                cache.add(keyIdx, name, token.createdAt().toEpochMilli());
            }
        }
    }

    private static Map<Transition, Set<Place<?>>> precomputeInputPlaces(PetriNet net) {
        var result = new HashMap<Transition, Set<Place<?>>>();
        for (var t : net.transitions()) {
            var places = new HashSet<Place<?>>();
            for (var in : t.inputSpecs()) places.add(in.place());
            result.put(t, Set.copyOf(places));
        }
        return Map.copyOf(result);
    }

    // ======================== Bitmap Helpers ========================

    private void setEnabledBit(int tid) {
        enabledBitmap[tid >>> WORD_SHIFT] |= 1L << (tid & BIT_MASK);
    }

    private void clearEnabledBit(int tid) {
        enabledBitmap[tid >>> WORD_SHIFT] &= ~(1L << (tid & BIT_MASK));
    }

    private boolean isEnabled(int tid) {
        return (enabledBitmap[tid >>> WORD_SHIFT] & (1L << (tid & BIT_MASK))) != 0;
    }

    private void setInFlightBit(int tid) {
        inFlightBitmap[tid >>> WORD_SHIFT] |= 1L << (tid & BIT_MASK);
    }

    private void clearInFlightBit(int tid) {
        inFlightBitmap[tid >>> WORD_SHIFT] &= ~(1L << (tid & BIT_MASK));
    }

    private boolean isInFlight(int tid) {
        return (inFlightBitmap[tid >>> WORD_SHIFT] & (1L << (tid & BIT_MASK))) != 0;
    }

    private void setMarkingBit(int pid) {
        markingBitmap[pid >>> WORD_SHIFT] |= 1L << (pid & BIT_MASK);
    }

    private void clearMarkingBit(int pid) {
        markingBitmap[pid >>> WORD_SHIFT] &= ~(1L << (pid & BIT_MASK));
    }

    // ======================== Factory Methods ========================

    public static BitmapNetExecutor create(
        PetriNet net,
        Map<Place<?>, List<Token<?>>> initialTokens
    ) {
        return builder(net, initialTokens).build();
    }

    public static BitmapNetExecutor create(
        PetriNet net,
        Map<Place<?>, List<Token<?>>> initialTokens,
        EventStore eventStore
    ) {
        return builder(net, initialTokens).eventStore(eventStore).build();
    }

    /**
     * @deprecated The {@code executor} argument never dispatched actions; it only hosts the
     *     orchestrator loop under {@link #run(Duration)}. Use
     *     {@code builder(net, initial).eventStore(...).orchestratorExecutor(...).build()}.
     *     Scheduled for removal in 3.0.
     */
    @Deprecated(since = "2.13", forRemoval = true)
    public static BitmapNetExecutor create(
        PetriNet net,
        Map<Place<?>, List<Token<?>>> initialTokens,
        EventStore eventStore,
        ExecutorService executor
    ) {
        return builder(net, initialTokens)
            .eventStore(eventStore)
            .orchestratorExecutor(executor)
            .build();
    }

    public static Builder builder(PetriNet net, Map<Place<?>, List<Token<?>>> initialTokens) {
        return new Builder(net, initialTokens);
    }

    public static final class Builder {
        private final PetriNet net;
        private final Map<Place<?>, List<Token<?>>> initialTokens;
        private CompiledNet compiledNet = null;
        private EventStore eventStore = EventStore.noop();
        private ExecutorService executor = null;
        private Set<EnvironmentPlace<?>> environmentPlaces = Set.of();
        private ExecutionContextProvider executionContextProvider = ExecutionContextProvider.NOOP;
        private long deadlineToleranceMillis = ExecutorSupport.DEADLINE_TOLERANCE_MS;
        private ActionFailureHandler uncaughtActionHandler = null;

        private Builder(PetriNet net, Map<Place<?>, List<Token<?>>> initialTokens) {
            this.net = Objects.requireNonNull(net);
            this.initialTokens = Objects.requireNonNull(initialTokens);
        }

        /**
         * Provide a pre-compiled net to avoid recompilation.
         * The compiled net must correspond to the same PetriNet passed to the builder.
         */
        public Builder compiledNet(CompiledNet compiledNet) {
            this.compiledNet = Objects.requireNonNull(compiledNet);
            return this;
        }

        public Builder eventStore(EventStore eventStore) {
            this.eventStore = Objects.requireNonNull(eventStore);
            return this;
        }

        /**
         * Sets the executor that hosts the orchestrator loop under {@link #run(Duration)}.
         *
         * <p>This is the loop's own thread, not an action dispatcher: transition actions are
         * invoked inline on the orchestrator thread and are never submitted here. Supplying
         * an executor changes nothing about how or where actions run.
         *
         * @param executor hosts the single orchestrator-loop task
         * @return this builder
         */
        public Builder orchestratorExecutor(ExecutorService executor) {
            this.executor = Objects.requireNonNull(executor);
            return this;
        }

        /**
         * @deprecated Misleading name: this never dispatched actions. Renamed to
         *     {@link #orchestratorExecutor(ExecutorService)}, which says what it does.
         *     Scheduled for removal in 3.0.
         */
        @Deprecated(since = "2.13", forRemoval = true)
        public Builder executor(ExecutorService executor) {
            return orchestratorExecutor(executor);
        }

        @SafeVarargs
        public final Builder environmentPlaces(EnvironmentPlace<?>... places) {
            this.environmentPlaces = Set.of(places);
            return this;
        }

        public final Builder environmentPlaces(Set<EnvironmentPlace<?>> places) {
            this.environmentPlaces = places;
            return this;
        }

        public Builder executionContextProvider(ExecutionContextProvider provider) {
            this.executionContextProvider = Objects.requireNonNull(provider);
            return this;
        }

        /**
         * Sets the deadline-enforcement tolerance — the grace band beyond a hard deadline
         * ({@code deadline()} / {@code window()}) before the transition is force-disabled with a
         * {@code TransitionTimedOut} event. Absorbs timer-resolution and scheduling jitter
         * (TIME-013). Defaults to {@code 5ms}.
         *
         * <p>Real-time orchestrators whose cycles can stall (GC pauses, long action callbacks)
         * may widen this. A value of {@code 0} gives strict, deterministic enforcement.
         *
         * <p>Does not affect {@code exact()} transitions, which are enforced softly and never
         * force-disabled (see TIME-006).
         *
         * @param tolerance non-negative grace duration
         * @return this builder
         */
        public Builder deadlineTolerance(Duration tolerance) {
            if (tolerance == null || tolerance.isNegative()) {
                throw new IllegalArgumentException("Deadline tolerance must be non-negative: " + tolerance);
            }
            this.deadlineToleranceMillis = tolerance.toMillis();
            return this;
        }

        /**
         * Sets a handler invoked when a transition action fails.
         *
         * <p>A failing action destroys the tokens it consumed. That loss is reported as a
         * {@code TransitionFailed} event, but the default {@code EventStore.noop()} discards
         * it, so without a handler the failure is entirely silent.
         *
         * <p>With no handler configured, libpetri logs at WARNING when — and only when — no
         * event store recorded the failure. A configured handler is always invoked, and one
         * that throws is swallowed rather than allowed to stop the orchestrator.
         *
         * @param handler receives the transition and the unwrapped cause
         * @return this builder
         */
        public Builder uncaughtActionHandler(ActionFailureHandler handler) {
            this.uncaughtActionHandler = Objects.requireNonNull(handler);
            return this;
        }

        public BitmapNetExecutor build() {
            var compiled = compiledNet != null ? compiledNet : CompiledNet.compile(net);
            var marking = Marking.from(initialTokens);
            ExecutorService exec = executor != null
                ? executor
                : Executors.newVirtualThreadPerTaskExecutor();
            return new BitmapNetExecutor(
                compiled, marking, eventStore, exec,
                environmentPlaces, executionContextProvider,
                deadlineToleranceMillis, uncaughtActionHandler,
                executor == null
            );
        }
    }

    // ======================== Execution ========================

    public Marking run() {
        started = true;
        return executeLoop();
    }

    public CompletionStage<Marking> run(Duration timeout) {
        return run(timeout, RunTimeoutPolicy.ABANDON);
    }

    @Override
    public CompletionStage<Marking> run(Duration timeout, RunTimeoutPolicy policy) {
        started = true; // before submit, so awaitTermination cannot mistake this for "never started"
        CompletableFuture<Marking> loop = CompletableFuture.supplyAsync(this::executeLoop, executor);
        // copy() so the timer never completes the loop's own future: ABANDON must leave the
        // orchestrator running and still able to report its real result to terminatedFuture.
        return loop.copy()
            .orTimeout(timeout.toMillis(), TimeUnit.MILLISECONDS)
            .whenCompleteAsync((_, ex) -> {
                if (ex != null && policy == RunTimeoutPolicy.CLOSE) close();
            });
    }

    @Override
    public boolean awaitTermination(Duration timeout) throws InterruptedException {
        if (!started) return true; // never started
        try {
            terminatedFuture.get(timeout.toMillis(), TimeUnit.MILLISECONDS);
            return true;
        } catch (TimeoutException e) {
            return false;
        } catch (ExecutionException e) {
            return true; // the loop finished, just not happily
        }
    }

    @Override
    public void terminateNow() {
        draining.set(true);
        closed.set(true);
        stopRequested = true; // loop exits at its next condition check; running stays truthful
        wakeUp();
        if (!terminated) drainPendingExternalEvents();
    }

    // ======================== Environment Place API ========================

    public <T> CompletableFuture<Boolean> inject(EnvironmentPlace<T> place, T token) {
        return inject(place, Token.of(token));
    }

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
        wakeUp();

        // The flag check above and this offer are not atomic. If the loop closed or terminated
        // in between, nothing will ever complete this future and the caller blocks on join()
        // forever. Draining here is idempotent and yields the same `false` the pre-check would
        // have returned. `draining` is deliberately NOT in this condition: under drain() (ENV-011)
        // the loop is still alive and processes already-queued events normally, so draining the
        // queue here would discard events other injectors legitimately enqueued.
        if (closed.get() || terminated) {
            drainPendingExternalEvents();
        }
        return event.resultFuture();
    }

    public <T> void injectAsync(EnvironmentPlace<T> place, Token<T> token) {
        inject(place, token);
    }

    private void wakeUp() {
        wakeUpSignal.release();
    }

    @Override
    public void awaitPollMillisForTesting(long millis) {
        this.awaitPollMillis = millis;
    }

    // ======================== Execute Loop ========================

    private Marking executeLoop() {
        // Publish an initial snapshot and the thread reference BEFORE running=true, so a foreign
        // marking() that observes the loop as live also observes both (volatile piggyback).
        publishedMarking = marking.copy();
        orchestratorThread = Thread.currentThread();
        running = true;
        emitEvent(new NetEvent.ExecutionStarted(
            Instant.now(), compiled.net().name(), executionId()));

        // Initialize bitmap from initial marking
        initializeMarkedBitmap();
        // Mark all transitions dirty for initial enablement check
        markAllDirty();
        emitMarkingSnapshot();

        // The loop body must never leave pending inject() futures uncompleted, even when it
        // exits by exception: those callers are blocked on join() and their tokens have
        // already been consumed. Termination bookkeeping therefore lives in the finally.
        try {
            while (running && !stopRequested && !Thread.currentThread().isInterrupted()) {
                serviceMarkingRequest();
                processCompletedTransitions();
                processExternalEvents();
                updateDirtyTransitions();
                if (hasAnyDeadlines) enforceDeadlines();

                if (shouldTerminate()) break;

                fireReadyTransitions();

                // Sync fast-path firings set dirty bits that need processing
                // before the orchestrator can sleep — skip awaitWork and re-loop.
                if (hasDirtyBits()) continue;

                awaitWork();
            }
        } finally {
            running = false;
            terminated = true;
            drainPendingExternalEvents();

            // Emit failures must not prevent the loop from reporting termination: a throwing
            // EventStore here would otherwise leave terminatedFuture uncompleted and hang
            // awaitTermination forever.
            try {
                emitMarkingSnapshot();
                emitEvent(new NetEvent.ExecutionCompleted(
                    Instant.now(), compiled.net().name(), executionId(), elapsedDuration()));
            } catch (Throwable emitError) {
                ExecutorSupport.swallowEventStoreFailure("ExecutionCompleted", emitError);
            } finally {
                terminatedFuture.complete(marking);
                orchestratorThread = null; // last: post-termination marking() reads are exact
            }
        }

        return marking;
    }

    /** Refreshes the published snapshot when a foreign thread has asked for one (see {@link #marking()}). */
    private void serviceMarkingRequest() {
        long req = markingRequestSeq.get();
        if (req != markingServedSeq) {
            publishedMarking = marking.copy();
            markingServedSeq = req;
        }
    }

    /**
     * Initializes the marking bitmap from the current marking state.
     */
    private void initializeMarkedBitmap() {
        for (int pid = 0; pid < compiled.placeCount(); pid++) {
            Place<?> place = compiled.place(pid);
            if (marking.hasTokens(place)) {
                setMarkingBit(pid);
            }
        }
    }

    /**
     * Marks all transitions as dirty for initial evaluation.
     * Only sets valid bits — excess bits in the last word are left clear
     * to avoid wasted iterations in updateDirtyTransitions().
     */
    private void markAllDirty() {
        int tc = compiled.transitionCount();
        int lastWordBits = tc & BIT_MASK;
        for (int w = 0; w < transitionWords - 1; w++) {
            dirtyBitmap[w] = -1L;
        }
        if (transitionWords > 0) {
            dirtyBitmap[transitionWords - 1] = lastWordBits == 0 ? -1L : (1L << lastWordBits) - 1;
        }
    }

    private boolean shouldTerminate() {
        if (closed.get()) {
            // ENV-013: immediate close — wait for in-flight actions to complete
            return inFlight.isEmpty() && completionQueue.isEmpty();
        }
        if (hasEnvironmentPlaces) {
            return draining.get()
                && enabledTransitionCount == 0
                && inFlight.isEmpty()
                && completionQueue.isEmpty();
        }
        return enabledTransitionCount == 0 && inFlight.isEmpty() && completionQueue.isEmpty();
    }

    // ======================== Dirty Set Transitions ========================

    /**
     * Re-evaluates enablement for transitions marked dirty since the last call.
     *
     * <p><b>Protocol:</b>
     * <ol>
     *   <li>Read and clear each word of the dirty bitmap. Any dirty bits set
     *       <em>after</em> this point will survive into the next cycle.</li>
     *   <li>Iterate over set bits in the snapshot. For each dirty transition, compare
     *       the new enablement state against the previous one and update accordingly.</li>
     * </ol>
     */
    private void updateDirtyTransitions() {
        long nowNanos = System.nanoTime();

        // Read and clear dirty bitmap into reusable buffer
        for (int w = 0; w < transitionWords; w++) {
            dirtyScanBuffer[w] = dirtyBitmap[w];
            dirtyBitmap[w] = 0;
        }

        // Iterate over set bits in dirtyScanBuffer
        for (int w = 0; w < transitionWords; w++) {
            long word = dirtyScanBuffer[w];
            while (word != 0) {
                int bit = Long.numberOfTrailingZeros(word);
                int tid = (w << WORD_SHIFT) | bit;
                word &= word - 1; // clear lowest set bit

                if (tid >= compiled.transitionCount()) break;
                if (isInFlight(tid)) continue;

                boolean wasEnabled = isEnabled(tid);
                boolean canNow = canEnable(tid, markingBitmap);

                if (canNow && !wasEnabled) {
                    setEnabledBit(tid);
                    enabledTransitionCount++;
                    enabledAtNanos[tid] = nowNanos;
                    if (eventStoreEnabled) emitEvent(new NetEvent.TransitionEnabled(
                        Instant.now(), compiled.transition(tid).name()));
                } else if (!canNow && wasEnabled) {
                    clearEnabledBit(tid);
                    enabledTransitionCount--;
                    enabledAtNanos[tid] = Long.MIN_VALUE;
                } else if (canNow && wasEnabled && hasInputFromResetPlace(compiled.transition(tid))) {
                    enabledAtNanos[tid] = nowNanos;
                    if (eventStoreEnabled) emitEvent(new NetEvent.TransitionClockRestarted(
                        Instant.now(), compiled.transition(tid).name()));
                }
            }
        }

        pendingResetPlaces.clear();
        assert enabledTransitionCount == countEnabledFlags();
    }

    /** Brute-force count for assertion checks only. */
    private int countEnabledFlags() {
        int count = 0;
        for (int w = 0; w < transitionWords; w++) {
            count += Long.bitCount(enabledBitmap[w]);
        }
        return count;
    }

    /**
     * Enablement check combining bitmap masks and cardinality checks.
     */
    private boolean canEnable(int tid, long[] markingSnap) {
        // 1. Fast bitmap check
        if (!compiled.canEnableBitmap(tid, markingSnap)) return false;

        // 2. Cardinality check (rare — only for multi-token inputs)
        assert Thread.currentThread() == orchestratorThread;
        var cardCheck = compiled.cardinalityCheck(tid);
        if (cardCheck != null) {
            for (int i = 0; i < cardCheck.placeIds().length; i++) {
                int pid = cardCheck.placeIds()[i];
                int required = cardCheck.requiredCounts()[i];
                Place<?> place = compiled.place(pid);
                if (marking.tokenCount(place) < required) return false;
            }
        }

        // 3. ν-net join: a correlation name must satisfy every matched input (NU-020).
        // Fast-path transitions read the maintained matcher (O(1)); the rest
        // rebuild the index (O(n)).
        if (compiled.transition(tid).matchSpec() != null) {
            MatchEngine.IncrementalMatcher cache = matchCaches[tid];
            boolean noBinding = cache != null
                ? cache.best() == null
                : MatchEngine.findBinding(marking, compiled.transition(tid)) == null;
            if (noBinding) {
                return false;
            }
        }

        return true;
    }

    private boolean hasInputFromResetPlace(Transition t) {
        if (pendingResetPlaces.isEmpty()) return false;
        return !Collections.disjoint(pendingResetPlaces, transitionInputPlaces.get(t));
    }

    // ======================== Deadline Enforcement ========================

    /**
     * Disables transitions that have exceeded their timing deadline.
     * Uses bitmap iteration to visit only enabled transitions.
     */
    private void enforceDeadlines() {
        long nowNanos = System.nanoTime();
        for (int w = 0; w < transitionWords; w++) {
            long word = enabledBitmap[w];
            while (word != 0) {
                int bit = Long.numberOfTrailingZeros(word);
                int tid = (w << WORD_SHIFT) | bit;
                word &= word - 1;

                Transition t = compiled.transition(tid);
                if (!t.timing().hasDeadline()) continue;
                // Exact timing is enforced softly — it fires at the first opportunity at/after its
                // target and is never force-disabled (TIME-006). Only hard deadlines reaped here.
                if (t.timing() instanceof Timing.Exact) continue;

                long enabledNanos = enabledAtNanos[tid];
                long elapsedMillis = (nowNanos - enabledNanos) / 1_000_000;
                long latestMillis = t.timing().latest().toMillis();

                if (elapsedMillis > latestMillis + deadlineToleranceMillis) {
                    clearEnabledBit(tid);
                    enabledTransitionCount--;
                    enabledAtNanos[tid] = Long.MIN_VALUE;
                    markTransitionDirty(tid);  // allow re-enablement next cycle
                    if (eventStoreEnabled) emitEvent(new NetEvent.TransitionTimedOut(
                        Instant.now(), t.name(),
                        t.timing().latest(),
                        Duration.ofMillis(elapsedMillis)));
                }
            }
        }
    }

    // ======================== Firing ========================

    private void fireReadyTransitions() {
        if (allImmediate && allSamePriority) {
            fireReadyImmediate();
            return;
        }
        fireReadyGeneral();
    }

    /**
     * Fast-fire path for nets where all transitions are immediate and same-priority.
     * Skips timing checks, ReadyTransition allocation, and sorting.
     * Fires directly from enabled bitmap in ID order.
     */
    private void fireReadyImmediate() {
        for (int w = 0; w < transitionWords; w++) {
            long word = enabledBitmap[w] & ~inFlightBitmap[w];
            while (word != 0) {
                int bit = Long.numberOfTrailingZeros(word);
                int tid = (w << WORD_SHIFT) | bit;
                word &= word - 1;

                if (canEnable(tid, markingBitmap)) {
                    fireTransitionGuarded(tid);
                } else {
                    clearEnabledBit(tid);
                    enabledTransitionCount--;
                    enabledAtNanos[tid] = Long.MIN_VALUE;
                }
            }
        }
    }

    /**
     * General-purpose firing path with timing checks, priority sorting, and FIFO ordering.
     */
    private void fireReadyGeneral() {
        long nowNanos = System.nanoTime();

        // Collect ready transitions into reusable buffer using bitmap iteration
        readyBuffer.clear();
        for (int w = 0; w < transitionWords; w++) {
            long word = enabledBitmap[w] & ~inFlightBitmap[w];
            while (word != 0) {
                int bit = Long.numberOfTrailingZeros(word);
                int tid = (w << WORD_SHIFT) | bit;
                word &= word - 1;

                Transition t = compiled.transition(tid);
                long enabledNanos = enabledAtNanos[tid];
                long elapsedMillis = (nowNanos - enabledNanos) / 1_000_000;
                if (t.timing().earliest().toMillis() <= elapsedMillis) {
                    readyBuffer.add(new ReadyTransition(tid, t.priority(), enabledNanos));
                }
            }
        }
        if (readyBuffer.isEmpty()) return;

        // Sort: higher priority first, then earlier enablement (FIFO)
        if (readyBuffer.size() > 1) {
            readyBuffer.sort((a, b) -> {
                int prioCmp = Integer.compare(b.priority(), a.priority());
                if (prioCmp != 0) return prioCmp;
                return Long.compare(a.enabledAtNanos(), b.enabledAtNanos());
            });
        }

        for (var entry : readyBuffer) {
            int tid = entry.tid();
            if (isEnabled(tid) && canEnable(tid, markingBitmap)) {
                fireTransitionGuarded(tid);
            } else {
                clearEnabledBit(tid);
                enabledTransitionCount--;
                enabledAtNanos[tid] = Long.MIN_VALUE;
            }
        }
    }

    /**
     * Fires a transition, containing any failure to that one firing.
     *
     * <p>Without this boundary an unchecked throw from a firing — an action throwing before it
     * returns its stage, a user {@link org.libpetri.event.EventStore} throwing from
     * {@code append}, a token-type violation — unwinds out of the orchestrator loop and kills
     * the executor. The transition is instead failed and marked dirty for re-evaluation, which
     * is the same treatment an asynchronously-reported failure already gets.
     *
     * <p>{@code fireTransition} removes tokens from the marking before it reconciles the
     * presence bitmap, so a throw <em>inside</em> that window (a hostile EventStore on
     * {@code TokenRemoved}, a ν {@code keyFn}) would leave bits asserting tokens that are gone.
     * The recovery re-runs {@link #updateBitmapAfterConsumption} against the real marking so the
     * re-evaluation cannot fire against a phantom. A fatal {@link Error} is repaired the same way
     * but rethrown, terminating the run rather than being retried.
     */
    private void fireTransitionGuarded(int tid) {
        try {
            fireTransition(tid);
        } catch (Throwable e) {
            Transition t = compiled.transition(tid);
            if (isEnabled(tid)) {
                clearEnabledBit(tid);
                enabledTransitionCount--;
                enabledAtNanos[tid] = Long.MIN_VALUE;
            }
            if (inFlight.remove(t) != null) clearInFlightBit(tid);
            updateBitmapAfterConsumption(tid);
            // fireTransition mirrors the matched consume into the ν fast-path matcher
            // (cache.consume) BEFORE the tokens physically leave the marking, so a throw in
            // that window (a hostile EventStore on TokenRemoved, a throwing keyFn) leaves the
            // matcher believing tokens are gone that remain. Reconciling the presence bitmap is
            // not enough — the matcher is authoritative for ν enablement. Drop it so the next
            // canEnable/fire rebuilds the binding from the live marking via findBinding; the
            // O(1) fast path is forfeited only for this transition, only after a failure.
            matchCaches[tid] = null;
            ExecutorSupport.rethrowIfFatal(e);
            handleTransitionFailure(t, e);
            markTransitionDirty(tid);
        }
    }

    @SuppressWarnings("unchecked")
    private void fireTransition(int tid) {
        Transition t = compiled.transition(tid);
        var inputs = new TokenInput();
        List<Token<?>> consumed = new ArrayList<>();

        assert Thread.currentThread() == orchestratorThread;

        // ν-net join: resolve the correlation name once, then consume the
        // matched tokens for correlated inputs; others consume FIFO (NU-020).
        MatchSpec ms = t.matchSpec();
        MatchEngine.IncrementalMatcher cache = ms != null ? matchCaches[tid] : null;
        NameId chosen = ms == null ? null
            : (cache != null ? cache.best() : MatchEngine.findBinding(marking, t));
        // Mirror the matched consume into the fast-path matcher (the only path by
        // which tokens leave this join's correlated inputs) before the marking changes.
        if (cache != null && chosen != null) {
            cache.consume(chosen);
        }

        // Consume tokens based on input specs with cardinality
        for (var in : t.inputSpecs()) {
            Place<Object> place = (Place<Object>) in.place();
            Function<Object, NameId> keyFn = ms != null ? ms.keyFor(in.place()) : null;

            if (keyFn != null && chosen != null) {
                Predicate<Token<?>> pred = tok -> {
                    try {
                        return chosen.equals(keyFn.apply(tok.value()));
                    } catch (ClassCastException e) {
                        return false;
                    }
                };
                int toConsume = switch (in) {
                    case Arc.In.One _ -> 1;
                    case Arc.In.Exactly e -> e.count();
                    default -> {
                        int c = 0;
                        for (Token<?> tk : marking.peekTokens(place)) if (pred.test(tk)) c++;
                        yield c;
                    }
                };
                for (int i = 0; i < toConsume; i++) {
                    Token<?> token = marking.removeFirstMatching(place, pred);
                    if (token == null) break;
                    consumed.add(token);
                    inputs.add(place, (Token<Object>) token);
                    if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
                        Instant.now(), in.place().name(), token));
                }
            } else {
                int toConsume = switch (in) {
                    case Arc.In.One _ -> 1;
                    case Arc.In.Exactly e -> e.count();
                    case Arc.In.All _ -> marking.tokenCount(place);
                    case Arc.In.AtLeast _ -> marking.tokenCount(place);
                };
                for (int i = 0; i < toConsume; i++) {
                    Token<?> token = marking.removeFirst(place);
                    consumed.add(token);
                    inputs.add(place, (Token<Object>) token);
                    if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
                        Instant.now(), in.place().name(), token));
                }
            }
        }

        // Read arcs (peek, don't consume)
        for (var arc : t.reads()) {
            Token<?> token = marking.peekFirst((Place<Object>) arc.place());
            if (token != null) {
                inputs.add((Place<Object>) arc.place(), (Token<Object>) token);
            }
        }

        // Reset arcs
        for (var arc : t.resets()) {
            var removed = marking.removeAll((Place<Object>) arc.place());
            pendingResetPlaces.add(arc.place());
            for (Token<?> token : removed) {
                consumed.add(token);
                if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
                    Instant.now(), arc.place().name(), token));
            }
        }

        // Update bitmap for consumed/reset places
        updateBitmapAfterConsumption(tid);

        if (eventStoreEnabled) emitEvent(new NetEvent.TransitionStarted(Instant.now(), t.name(), consumed));

        Map<Class<?>, Object> execContext = executionContextProvider.createContext(t, consumed);
        var context = new TransitionContext(t, inputs, new TokenOutput(), execContext);
        final String freshNameBase = t.name();
        context.setFreshNameSupplier(() ->
            new NameId(freshNameBase + "#" + freshNameCounter.getAndIncrement()));

        CompletableFuture<Void> transitionFuture = eventStore.isEnabled()
            ? LogCaptureScope.call(t.name(), eventStore::append,
                  () -> ExecutorSupport.executeAction(t, context))
            : ExecutorSupport.executeAction(t, context);

        // Handle Out.Timeout
        if (t.hasActionTimeout()) {
            transitionFuture = ExecutorSupport.withActionTimeout(
                t, context, transitionFuture,
                () -> { if (eventStoreEnabled) emitEvent(new NetEvent.ActionTimedOut(
                    Instant.now(), t.name(), t.actionTimeout().after())); });
        }

        // Clear enabled status (common to both paths)
        clearEnabledBit(tid);
        enabledTransitionCount--;
        enabledAtNanos[tid] = Long.MIN_VALUE;

        // Sync fast path: if future already completed and no timeout, process inline
        if (!t.hasActionTimeout() && transitionFuture.isDone()) {
            processSyncOutput(t, tid, transitionFuture, context, consumed);
        } else {
            // Async path: track in-flight, process on completion
            transitionFuture.whenComplete((_, _) -> {
                completionQueue.offer(t);
                wakeUp();
            });
            inFlight.put(t, new InFlightTransition(transitionFuture, context, consumed, System.nanoTime()));
            setInFlightBit(tid);
        }
    }

    /**
     * Processes output from a synchronously completed transition inline,
     * avoiding the completionQueue → processCompletedTransitions round-trip.
     */
    @SuppressWarnings("unchecked")
    private void processSyncOutput(Transition t, int tid, CompletableFuture<Void> future,
                                   TransitionContext context, List<Token<?>> consumed) {
        try {
            future.join(); // won't block; may throw CompletionException

            TokenOutput outputs = context.rawOutput();
            validateOutput(t, outputs);

            // One entry = add token, set its presence bit, mark dirty — kept together so a
            // throw mid-commit (a hostile EventStore on TokenAdded) cannot leave a token in the
            // marking with its bit unset. A defensive copy guards against a misbehaving action
            // still mutating the collector.
            var entries = List.copyOf(outputs.entries());
            List<Token<?>> produced = eventStoreEnabled ? new ArrayList<>(entries.size()) : null;
            for (var entry : entries) {
                var token = entry.token();
                int pid = compiled.placeId(entry.place());
                cacheAddToken(entry.place(), token);
                marking.addToken((Place<Object>) entry.place(), (Token<Object>) token);
                setMarkingBit(pid);
                markDirty(pid);
                if (eventStoreEnabled) {
                    produced.add(token);
                    emitEvent(new NetEvent.TokenAdded(
                        Instant.now(), entry.place().name(), token));
                }
            }

            // Mark the completed transition dirty for re-evaluation
            markTransitionDirty(tid);

            if (eventStoreEnabled) {
                emitEvent(new NetEvent.TransitionCompleted(
                    Instant.now(), t.name(), produced, Duration.ZERO));
            }
        } catch (RuntimeException e) {
            // See processCompletedTransitions: CancellationException arrives unwrapped.
            handleTransitionFailure(t, e);
            markTransitionDirty(tid);
        }
    }

    /**
     * After consuming tokens from a place, update the bitmap if the place is now empty.
     * Also mark affected transitions dirty for those places.
     * Uses precomputed consumption place IDs to avoid HashSet allocation.
     */
    private void updateBitmapAfterConsumption(int tid) {
        int[] pids = compiled.consumptionPlaceIds(tid);
        for (int pid : pids) {
            Place<?> place = compiled.place(pid);
            if (!marking.hasTokens(place)) {
                clearMarkingBit(pid);
            }
            markDirty(pid);
        }
    }

    // ======================== Completion Processing ========================

    @SuppressWarnings("unchecked")
    private void processCompletedTransitions() {
        Transition t;
        while ((t = completionQueue.poll()) != null) {
            InFlightTransition flight = inFlight.remove(t);
            if (flight == null) continue;

            int tid = compiled.transitionId(t);
            clearInFlightBit(tid);

            try {
                flight.future().join();

                TokenOutput outputs = flight.context().rawOutput();
                validateOutput(t, outputs);

                // One entry = add token, set its presence bit, mark dirty — kept together so a
                // throw mid-commit cannot leave a token in the marking with its bit unset. A
                // defensive copy guards against a misbehaving action still mutating the collector.
                var entries = List.copyOf(outputs.entries());
                List<Token<?>> produced = new ArrayList<>(entries.size());
                for (var entry : entries) {
                    var token = entry.token();
                    int pid = compiled.placeId(entry.place());
                    cacheAddToken(entry.place(), token);
                    marking.addToken((Place<Object>) entry.place(), (Token<Object>) token);
                    setMarkingBit(pid);
                    markDirty(pid);
                    produced.add(token);
                    if (eventStoreEnabled) emitEvent(new NetEvent.TokenAdded(
                        Instant.now(), entry.place().name(), token));
                }

                // Also mark the completed transition's own ID dirty
                // so it gets re-evaluated for enablement
                markTransitionDirty(tid);

                if (eventStoreEnabled) {
                    var transitionDuration = Duration.ofNanos(System.nanoTime() - flight.startNanos());
                    emitEvent(new NetEvent.TransitionCompleted(
                        Instant.now(), t.name(), produced, transitionDuration));
                }

            } catch (RuntimeException e) {
                // CompletionException (action failed), OutViolationException (output spec
                // violated) and CancellationException — which join() rethrows *unwrapped*,
                // so it matches neither of the other two — all fail just this transition.
                handleTransitionFailure(t, e);
                markTransitionDirty(tid);
            }
        }
    }

    private void handleTransitionFailure(Transition t, Throwable e) {
        Throwable cause = ExecutorSupport.unwrap(e);
        // Emit is guarded: a throwing EventStore here must not escape the failure handler (this
        // runs inside fireTransitionGuarded's catch) nor rob the handler of its callback.
        // `emitted` reflects whether the event was actually appended, so the default policy
        // logs exactly when no store recorded the failure — not merely when a store exists.
        boolean emitted = false;
        if (eventStoreEnabled) {
            try {
                emitEvent(new NetEvent.TransitionFailed(
                    Instant.now(), t.name(), cause.getMessage(), cause.getClass().getName()));
                emitted = true;
            } catch (Throwable storeError) {
                ExecutorSupport.swallowEventStoreFailure("TransitionFailed", storeError);
            }
        }
        ExecutorSupport.reportActionFailure(uncaughtActionHandler, emitted, t, cause);
    }

    // ======================== External Events ========================

    @SuppressWarnings("unchecked")
    private void processExternalEvents() {
        if (closed.get()) return; // ENV-013: leave queued events for drainPendingExternalEvents()
        ExternalEvent<?> event;
        while ((event = externalEventQueue.poll()) != null) {
            try {
                cacheAddToken(event.place(), event.token());
                marking.addToken(
                    (Place<Object>) event.place(),
                    (Token<Object>) event.token());

                int pid = compiled.placeId(event.place());
                setMarkingBit(pid);
                markDirty(pid);

                if (eventStoreEnabled) emitEvent(new NetEvent.TokenAdded(
                    Instant.now(), event.place().name(), event.token()));
                event.resultFuture().complete(true);
            } catch (Exception e) {
                event.resultFuture().completeExceptionally(e);
            }
        }
    }

    private void drainPendingExternalEvents() {
        ExecutorSupport.drainPendingExternalEvents(externalEventQueue);
    }

    // ======================== Await Work ========================

    private void awaitWork() {
        // When closed, ignore external queue — processExternalEvents() won't consume it,
        // drainPendingExternalEvents() handles it after the loop exits.
        if (!completionQueue.isEmpty() || (!closed.get() && !externalEventQueue.isEmpty())) return;

        if (!inFlight.isEmpty()) {
            awaitCompletionOrEvent();
        } else if (enabledTransitionCount > 0 || (hasEnvironmentPlaces && !draining.get())) {
            // Wait for timed transitions to become ready, or for external events
            awaitExternalEvent();
        }
    }

    private void awaitCompletionOrEvent() {
        for (var flight : inFlight.values()) {
            if (flight.future().isDone()) return;
        }
        if (!completionQueue.isEmpty() || (!closed.get() && !externalEventQueue.isEmpty())) return;

        if (inFlight.isEmpty()) return;

        // A completing action does `completionQueue.offer(t); wakeUp();`, so the semaphore is
        // the wake-up signal and the queue is the durable record. Composing a
        // CompletableFuture.anyOf over every in-flight future once per poll cycle — as this
        // used to — allocated a fresh dependent node on each of those futures every 1-50ms
        // and then abandoned it, which on a long-running action accumulates for the lifetime
        // of the call. The loop below observes exactly the same events.
        while (true) {
            long pollMs = allImmediate ? awaitPollMillis
                : Math.max(1, Math.min(awaitPollMillis, millisUntilNextTimedTransition()));
            try {
                if (wakeUpSignal.tryAcquire(pollMs, TimeUnit.MILLISECONDS)) {
                    wakeUpSignal.drainPermits();
                    return;
                }
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                return;
            }
            if (!completionQueue.isEmpty() || (!closed.get() && !externalEventQueue.isEmpty())) return;

            // Timed transition may have become ready (pollMs was bounded by timer)
            if (!allImmediate && millisUntilNextTimedTransition() <= 0) return;
        }
    }

    private long millisUntilNextTimedTransition() {
        long nowNanos = System.nanoTime();
        long minWaitMs = Long.MAX_VALUE;

        for (int w = 0; w < transitionWords; w++) {
            long word = enabledBitmap[w] & timedMask[w]; // only check timed transitions
            while (word != 0) {
                int bit = Long.numberOfTrailingZeros(word);
                int tid = (w << WORD_SHIFT) | bit;
                word &= word - 1;

                Transition t = compiled.transition(tid);
                long enabledNanos = enabledAtNanos[tid];
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
        }
        return minWaitMs;
    }

    private void awaitExternalEvent() {
        try {
            long waitMs = millisUntilNextTimedTransition();
            if (waitMs <= 0) return;
            else if (waitMs == Long.MAX_VALUE) wakeUpSignal.acquire();
            else wakeUpSignal.tryAcquire(waitMs, TimeUnit.MILLISECONDS);
            wakeUpSignal.drainPermits();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }

    // ======================== Output Validation ========================

    private void validateOutput(Transition t, TokenOutput outputs) {
        if (t.outputSpec() == null) return;
        Set<Place<?>> produced = outputs.placesWithTokens();
        ExecutorSupport.validateOutSpec(t.name(), t.outputSpec(), produced)
            .orElseThrow(() -> new OutViolationException(
                "'%s': output does not satisfy declared spec".formatted(t.name())));
    }

    // ======================== CAS Bitmap Helpers ========================
    //
    // Retained utilities, not on any execution path: every bitmap this executor
    // owns is orchestrator-confined (markingBitmap, enabledBitmap, inFlightBitmap,
    // dirtyBitmap are all plain long[]). They exist for a future in which a bitmap
    // becomes shared with the threads that complete actions.
    //
    // Thread ownership:
    //   - all bitmaps: plain long[], orchestrator-thread only.
    //   - completionQueue, externalEventQueue: lock-free queues shared between
    //     the threads completing actions and the orchestrator.

    static void casSetBit(AtomicLongArray arr, int bit) {
        int word = bit >>> WORD_SHIFT;
        long mask = 1L << (bit & BIT_MASK);
        long prev;
        do {
            prev = arr.get(word);
            if ((prev & mask) != 0) return;
        } while (!arr.compareAndSet(word, prev, prev | mask));
    }

    static void casClearBit(AtomicLongArray arr, int bit) {
        int word = bit >>> WORD_SHIFT;
        long mask = 1L << (bit & BIT_MASK);
        long prev;
        do {
            prev = arr.get(word);
            if ((prev & mask) == 0) return;
        } while (!arr.compareAndSet(word, prev, prev & ~mask));
    }

    static long[] snapshot(AtomicLongArray arr) {
        long[] snap = new long[arr.length()];
        for (int i = 0; i < snap.length; i++) snap[i] = arr.get(i);
        return snap;
    }

    /**
     * Marks all transitions affected by a place change as dirty.
     */
    private void markDirty(int pid) {
        int[] tids = compiled.affectedTransitions(pid);
        for (int tid : tids) {
            markTransitionDirty(tid);
        }
    }

    private void markTransitionDirty(int tid) {
        dirtyBitmap[tid >>> WORD_SHIFT] |= 1L << (tid & BIT_MASK);
    }

    private boolean hasDirtyBits() {
        for (int w = 0; w < transitionWords; w++) {
            if (dirtyBitmap[w] != 0) return true;
        }
        return false;
    }

    // ======================== State Inspection ========================

    /**
     * Returns the current marking.
     *
     * <p>From the orchestrator thread, or once the loop has stopped, this is the executor's own
     * live {@code Marking} — exact, as before. From another thread while the loop is running it
     * returns an independent snapshot the orchestrator publishes for it: the live instance is a
     * {@code HashMap} of {@code ArrayDeque}s the orchestrator mutates on every firing, and
     * reading it from another thread would throw or spin rather than merely return a stale value.
     *
     * <p>The snapshot is best-effort. The caller flags a request and the orchestrator refreshes
     * the published copy at the next safe point in its loop; while the orchestrator is inside a
     * long inline action it may not reach that point immediately, so the returned marking can lag.
     * For a view with defined timing, subscribe to {@code MarkingSnapshot} events, which the
     * orchestrator emits from its own thread.
     */
    @Override
    public Marking marking() {
        Thread orchestrator = orchestratorThread;
        if (orchestrator != null && Thread.currentThread() != orchestrator) {
            Marking snapshot = awaitPublishedSnapshot();
            if (orchestratorThread != null) {
                return snapshot != null ? snapshot : Marking.empty();
            }
            // else: the loop finished while we waited — fall through to the exact live marking.
        }
        return marking;
    }

    /**
     * Requests a fresh published snapshot from the orchestrator and waits, bounded, for it.
     * Returns the freshest {@link #publishedMarking} it can; the caller checks whether the loop
     * ended meanwhile (in which case it reads the exact live marking instead).
     */
    private Marking awaitPublishedSnapshot() {
        long seq = markingRequestSeq.incrementAndGet();
        wakeUp();
        long deadline = System.nanoTime() + ExecutorSupport.MARKING_SNAPSHOT_WAIT_NANOS;
        while (markingServedSeq < seq) {
            if (orchestratorThread == null) return null; // loop finished; caller reads exact
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) break; // best-effort cap: return the last snapshot
            LockSupport.parkNanos(Math.min(remaining, 1_000_000L));
        }
        return publishedMarking;
    }

    public boolean isQuiescent() {
        return enabledTransitionCount == 0 && inFlight.isEmpty();
    }

    public boolean isWaitingForCompletion() {
        return enabledTransitionCount == 0 && !inFlight.isEmpty();
    }

    public int inFlightCount() { return inFlight.size(); }

    public int enabledCount() {
        return enabledTransitionCount;
    }

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

        // No loop is running to reach the drain in executeLoop's finally — either it never
        // started or it already terminated. Either way these futures are ours to complete.
        if (!running) drainPendingExternalEvents();

        // Only ever shut down an executor we created. A caller-supplied one may host
        // other work and is not ours to stop.
        if (ownsExecutor) executor.shutdown();
    }
}
