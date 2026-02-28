package org.libpetri.runtime;

import java.time.Duration;
import java.time.Instant;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLongArray;

import org.libpetri.core.*;
import org.libpetri.debug.LogCaptureScope;
import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;

/**
 * Lock-free bitmap-based executor for Coloured Time Petri Nets.
 *
 * <p>Replaces the O(n²) full-scan approach of {@link NetExecutor} with:
 * <ul>
 *   <li><b>CAS-updatable presence bitmap</b> ({@link AtomicLongArray}) — supports
 *       concurrent updates via compare-and-set without locking</li>
 *   <li><b>Event-driven dirty set</b> — only transitions affected by a token change
 *       are re-evaluated, using a precomputed reverse index from {@link CompiledNet}</li>
 *   <li><b>BitSet mask checks</b> — enablement verified via bitwise AND/compare
 *       against precomputed read-only masks</li>
 * </ul>
 *
 * <h2>Concurrency Model</h2>
 * <pre>
 *   Virtual Thread (action complete)          Orchestrator Thread
 *   ──────────────────────────────            ──────────────────
 *   1. completionQueue.offer(t)       ──→     processCompletedTransitions()
 *   2. wakeUpSignal.release()         ──→     awaitWork() returns
 *                                             3. CAS-set bits in markedPlaces
 *                                             4. CAS-set bits in dirtySet
 * </pre>
 *
 * <p>Virtual threads signal completion via the lock-free {@code completionQueue} and
 * wake up the orchestrator. All bitmap mutations (markedPlaces, dirtySet) happen on
 * the orchestrator thread. The CAS operations future-proof the design for potential
 * direct virtual-thread bitmap updates without requiring architectural changes.
 *
 * <p>Token <em>values</em> still go through {@link Marking}, but since all marking
 * mutations happen on the orchestrator thread, no synchronization is needed.
 * The presence bitmap — which drives the hot-path enablement check — is entirely lock-free.
 *
 * @see CompiledNet
 * @see NetExecutor
 */
public final class BitmapNetExecutor implements PetriNetExecutor {
    /** Number of bits to shift for word index (2^6 = 64 bits per long). */
    static final int WORD_SHIFT = 6;
    /** Mask for bit position within a word (0x3F = 63). */
    static final int BIT_MASK = 63;

    private final CompiledNet compiled;
    private final Marking marking;
    private final EventStore eventStore;
    private final ExecutorService executor;
    private final ExecutionContextProvider executionContextProvider;
    private final long startNanos;

    // Lock-free bitmaps
    private final AtomicLongArray markedPlaces;
    private final AtomicLongArray dirtySet;

    // Orchestrator-owned state (single-threaded)
    private final long[] enabledAtNanos;
    private final boolean[] inFlightFlags;
    private final boolean[] enabledFlags;
    /** Reusable buffer for marking snapshots (orchestrator-thread only). */
    private final long[] markingSnapBuffer;
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

    /** Long-running mode flag. */
    private final boolean longRunning;

    /** Tracks if close() was called. */
    private final AtomicBoolean closed = new AtomicBoolean(false);

    private volatile boolean running = false;

    /** Set at the start of executeLoop; used for thread-safety assertions. */
    private Thread orchestratorThread;

    private BitmapNetExecutor(
        CompiledNet compiled,
        Marking marking,
        EventStore eventStore,
        ExecutorService executor,
        Set<EnvironmentPlace<?>> environmentPlaces,
        boolean longRunning,
        ExecutionContextProvider executionContextProvider
    ) {
        this.compiled = compiled;
        this.marking = marking;
        this.eventStore = eventStore;
        this.executor = executor;
        this.environmentPlaces = environmentPlaces;
        this.longRunning = longRunning;
        this.executionContextProvider = executionContextProvider;
        this.startNanos = System.nanoTime();

        int wordCount = compiled.wordCount();
        this.markedPlaces = new AtomicLongArray(wordCount);
        this.dirtySet = new AtomicLongArray((compiled.transitionCount() + BIT_MASK) >>> WORD_SHIFT);

        this.enabledAtNanos = new long[compiled.transitionCount()];
        this.inFlightFlags = new boolean[compiled.transitionCount()];
        this.enabledFlags = new boolean[compiled.transitionCount()];
        this.markingSnapBuffer = new long[wordCount];
        Arrays.fill(enabledAtNanos, Long.MIN_VALUE); // sentinel: not enabled

        this.transitionInputPlaces = precomputeInputPlaces(compiled.net());
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

    public static BitmapNetExecutor create(
        PetriNet net,
        Map<Place<?>, List<Token<?>>> initialTokens,
        EventStore eventStore,
        ExecutorService executor
    ) {
        return builder(net, initialTokens).eventStore(eventStore).executor(executor).build();
    }

    public static Builder builder(PetriNet net, Map<Place<?>, List<Token<?>>> initialTokens) {
        return new Builder(net, initialTokens);
    }

    public static final class Builder {
        private final PetriNet net;
        private final Map<Place<?>, List<Token<?>>> initialTokens;
        private EventStore eventStore = EventStore.inMemory();
        private ExecutorService executor = null;
        private Set<EnvironmentPlace<?>> environmentPlaces = Set.of();
        private boolean longRunning = false;
        private ExecutionContextProvider executionContextProvider = ExecutionContextProvider.NOOP;

        private Builder(PetriNet net, Map<Place<?>, List<Token<?>>> initialTokens) {
            this.net = Objects.requireNonNull(net);
            this.initialTokens = Objects.requireNonNull(initialTokens);
        }

        public Builder eventStore(EventStore eventStore) {
            this.eventStore = Objects.requireNonNull(eventStore);
            return this;
        }

        public Builder executor(ExecutorService executor) {
            this.executor = Objects.requireNonNull(executor);
            return this;
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

        public Builder longRunning(boolean enabled) {
            this.longRunning = enabled;
            return this;
        }

        public Builder executionContextProvider(ExecutionContextProvider provider) {
            this.executionContextProvider = Objects.requireNonNull(provider);
            return this;
        }

        public BitmapNetExecutor build() {
            var compiled = CompiledNet.compile(net);
            var marking = Marking.from(initialTokens);
            ExecutorService exec = executor != null
                ? executor
                : Executors.newVirtualThreadPerTaskExecutor();
            return new BitmapNetExecutor(
                compiled, marking, eventStore, exec,
                environmentPlaces, longRunning, executionContextProvider
            );
        }
    }

    // ======================== Execution ========================

    public Marking run() {
        return executeLoop();
    }

    public CompletionStage<Marking> run(Duration timeout) {
        return CompletableFuture.supplyAsync(
            this::executeLoop, executor
        ).orTimeout(timeout.toMillis(), TimeUnit.MILLISECONDS);
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
        if (closed.get()) {
            return CompletableFuture.completedFuture(false);
        }
        var event = new ExternalEvent<>(place.place(), token, new CompletableFuture<>());
        externalEventQueue.offer(event);
        wakeUp();
        return event.resultFuture();
    }

    public <T> void injectAsync(EnvironmentPlace<T> place, Token<T> token) {
        inject(place, token);
    }

    private void wakeUp() {
        wakeUpSignal.release();
    }

    // ======================== Execute Loop ========================

    private Marking executeLoop() {
        running = true;
        orchestratorThread = Thread.currentThread();
        emitEvent(new NetEvent.ExecutionStarted(
            Instant.now(), compiled.net().name(), executionId()));

        // Initialize bitmap from initial marking
        initializeMarkedBitmap();
        // Mark all transitions dirty for initial enablement check
        markAllDirty();
        emitMarkingSnapshot();

        while (running && !Thread.currentThread().isInterrupted() && !closed.get()) {
            processCompletedTransitions();
            processExternalEvents();
            updateDirtyTransitions();
            enforceDeadlines();

            if (shouldTerminate()) break;

            fireReadyTransitions();
            awaitWork();
        }

        running = false;
        drainPendingExternalEvents();

        emitMarkingSnapshot();
        emitEvent(new NetEvent.ExecutionCompleted(
            Instant.now(), compiled.net().name(), executionId(), elapsedDuration()));

        return marking;
    }

    /**
     * Initializes the bitmap from the current marking state.
     */
    private void initializeMarkedBitmap() {
        for (int pid = 0; pid < compiled.placeCount(); pid++) {
            Place<?> place = compiled.place(pid);
            if (marking.hasTokens(place)) {
                casSetBit(markedPlaces, pid);
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
        int dirtyWords = dirtySet.length();
        int lastWordBits = tc & BIT_MASK;
        for (int w = 0; w < dirtyWords - 1; w++) {
            dirtySet.set(w, -1L);
        }
        if (dirtyWords > 0) {
            dirtySet.set(dirtyWords - 1, lastWordBits == 0 ? -1L : (1L << lastWordBits) - 1);
        }
    }

    private boolean shouldTerminate() {
        if (longRunning) return closed.get();
        // Standard mode: terminate when quiescent
        return enabledTransitionCount == 0 && inFlight.isEmpty() && completionQueue.isEmpty();
    }

    // ======================== Dirty Set Transitions ========================

    /**
     * Re-evaluates enablement for transitions marked dirty since the last call.
     *
     * <p><b>Protocol:</b>
     * <ol>
     *   <li>Snapshot the marking bitmap (read-only for the rest of this call).</li>
     *   <li>Atomically read-and-clear each word of the dirty set. This ensures that
     *       any dirty bits set <em>after</em> the snapshot was taken will survive into
     *       the next cycle — they cannot be lost.</li>
     *   <li>Iterate over set bits in the snapshot. For each dirty transition, compare
     *       the new enablement state against the previous one and update accordingly.</li>
     * </ol>
     *
     * <p><b>Staleness safety:</b> Because the marking snapshot is taken <em>before</em>
     * the dirty set is cleared, a concurrent bitmap update (e.g. from processCompletedTransitions)
     * that sets a dirty bit after step 2 will be picked up in the next cycle. The worst case is
     * one cycle of delay, which is acceptable for the orchestrator's polling model.
     */
    private void updateDirtyTransitions() {
        long nowNanos = System.nanoTime();

        // Snapshot the marking bitmap into reusable buffer
        long[] markingSnap = snapshotMarking();

        // Read and clear dirty set
        int dirtyWords = dirtySet.length();
        long[] dirtySnap = new long[dirtyWords];
        for (int w = 0; w < dirtyWords; w++) {
            dirtySnap[w] = dirtySet.getAndSet(w, 0L);
        }

        // Iterate over set bits in dirtySnap
        for (int w = 0; w < dirtyWords; w++) {
            long word = dirtySnap[w];
            while (word != 0) {
                int bit = Long.numberOfTrailingZeros(word);
                int tid = (w << WORD_SHIFT) | bit;
                word &= word - 1; // clear lowest set bit

                if (tid >= compiled.transitionCount()) break;
                if (inFlightFlags[tid]) continue;

                boolean wasEnabled = enabledFlags[tid];
                boolean canNow = canEnable(tid, markingSnap);

                if (canNow && !wasEnabled) {
                    enabledFlags[tid] = true;
                    enabledTransitionCount++;
                    enabledAtNanos[tid] = nowNanos;
                    emitEvent(new NetEvent.TransitionEnabled(
                        Instant.now(), compiled.transition(tid).name()));
                } else if (!canNow && wasEnabled) {
                    enabledFlags[tid] = false;
                    enabledTransitionCount--;
                    enabledAtNanos[tid] = Long.MIN_VALUE;
                } else if (canNow && wasEnabled && hasInputFromResetPlace(compiled.transition(tid))) {
                    enabledAtNanos[tid] = nowNanos;
                    emitEvent(new NetEvent.TransitionClockRestarted(
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
        for (int tid = 0; tid < compiled.transitionCount(); tid++) {
            if (enabledFlags[tid]) count++;
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

        return true;
    }

    private boolean hasInputFromResetPlace(Transition t) {
        if (pendingResetPlaces.isEmpty()) return false;
        return !Collections.disjoint(pendingResetPlaces, transitionInputPlaces.get(t));
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
        for (int tid = 0; tid < compiled.transitionCount(); tid++) {
            if (!enabledFlags[tid]) continue;
            Transition t = compiled.transition(tid);
            if (!t.timing().hasDeadline()) continue;

            long enabledNanos = enabledAtNanos[tid];
            long elapsedMillis = (nowNanos - enabledNanos) / 1_000_000;
            long latestMillis = t.timing().latest().toMillis();

            if (elapsedMillis > latestMillis) {
                enabledFlags[tid] = false;
                enabledTransitionCount--;
                enabledAtNanos[tid] = Long.MIN_VALUE;
                markTransitionDirty(tid);  // allow re-enablement next cycle
                emitEvent(new NetEvent.TransitionTimedOut(
                    Instant.now(), t.name(),
                    t.timing().latest(),
                    Duration.ofMillis(elapsedMillis)));
            }
        }
    }

    // ======================== Firing ========================

    private void fireReadyTransitions() {
        long nowNanos = System.nanoTime();

        // Collect ready transitions
        List<ReadyTransition> ready = new ArrayList<>();
        for (int tid = 0; tid < compiled.transitionCount(); tid++) {
            if (!enabledFlags[tid] || inFlightFlags[tid]) continue;
            Transition t = compiled.transition(tid);
            long enabledNanos = enabledAtNanos[tid];
            long elapsedMillis = (nowNanos - enabledNanos) / 1_000_000;
            if (t.timing().earliest().toMillis() <= elapsedMillis) {
                ready.add(new ReadyTransition(tid, t.priority(), enabledNanos));
            }
        }
        if (ready.isEmpty()) return;

        // Sort: higher priority first, then earlier enablement (FIFO)
        ready.sort((a, b) -> {
            int prioCmp = Integer.compare(b.priority(), a.priority());
            if (prioCmp != 0) return prioCmp;
            return Long.compare(a.enabledAtNanos(), b.enabledAtNanos());
        });

        // Take a fresh snapshot for re-checking enablement
        long[] freshSnap = snapshotMarking();
        for (var entry : ready) {
            int tid = entry.tid();
            if (enabledFlags[tid] && canEnable(tid, freshSnap)) {
                fireTransition(tid);
                // Update snapshot after consuming tokens
                snapshotMarking(); // freshSnap is markingSnapBuffer, updated in-place
            } else {
                enabledFlags[tid] = false;
                enabledTransitionCount--;
                enabledAtNanos[tid] = Long.MIN_VALUE;
            }
        }
    }

    @SuppressWarnings("unchecked")
    private void fireTransition(int tid) {
        Transition t = compiled.transition(tid);
        var inputs = new TokenInput();
        List<Token<?>> consumed = new ArrayList<>();

        assert Thread.currentThread() == orchestratorThread;

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
                emitEvent(new NetEvent.TokenRemoved(
                    Instant.now(), in.place().name(), token));
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
                emitEvent(new NetEvent.TokenRemoved(
                    Instant.now(), arc.place().name(), token));
            }
        }

        // Update bitmap for consumed/reset places
        updateBitmapAfterConsumption(tid);

        emitEvent(new NetEvent.TransitionStarted(Instant.now(), t.name(), consumed));

        Map<Class<?>, Object> execContext = executionContextProvider.createContext(t, consumed);
        var context = new TransitionContext(t, inputs, new TokenOutput(), execContext);

        CompletableFuture<Void> transitionFuture = eventStore.isEnabled()
            ? LogCaptureScope.call(t.name(), eventStore::append,
                  () -> t.action().execute(context).toCompletableFuture())
            : t.action().execute(context).toCompletableFuture();

        // Handle Out.Timeout
        if (t.hasActionTimeout()) {
            var timeoutSpec = t.actionTimeout();
            long timeoutMillis = timeoutSpec.after().toMillis();
            var originalFuture = transitionFuture;

            transitionFuture = transitionFuture
                .orTimeout(timeoutMillis, TimeUnit.MILLISECONDS)
                .exceptionally(ex -> {
                    if (ex instanceof TimeoutException || ex.getCause() instanceof TimeoutException) {
                        originalFuture.cancel(true);
                        produceTimeoutOutput(context, timeoutSpec.child());
                        emitEvent(new NetEvent.ActionTimedOut(
                            Instant.now(), t.name(), timeoutSpec.after()));
                        return null;
                    }
                    throw (ex instanceof RuntimeException re) ? re : new RuntimeException(ex);
                });
        }

        transitionFuture.whenComplete((_, _) -> {
            completionQueue.offer(t);
            wakeUp();
        });

        inFlight.put(t, new InFlightTransition(transitionFuture, context, consumed, System.nanoTime()));
        inFlightFlags[tid] = true;
        enabledFlags[tid] = false;
        enabledTransitionCount--;
        enabledAtNanos[tid] = Long.MIN_VALUE;
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
                casClearBit(markedPlaces, pid);
            }
            markDirty(pid);
        }
    }

    private void produceTimeoutOutput(TransitionContext context, Arc.Out timeoutChild) {
        ExecutorSupport.produceTimeoutOutput(context, timeoutChild);
    }

    // ======================== Completion Processing ========================

    @SuppressWarnings("unchecked")
    private void processCompletedTransitions() {
        Transition t;
        while ((t = completionQueue.poll()) != null) {
            InFlightTransition flight = inFlight.remove(t);
            if (flight == null) continue;

            int tid = compiled.transitionId(t);
            inFlightFlags[tid] = false;

            try {
                flight.future().join();

                TokenOutput outputs = flight.context().rawOutput();
                validateOutput(t, outputs);

                List<Token<?>> produced = new ArrayList<>();
                for (var entry : outputs.entries()) {
                    var token = entry.token();
                    marking.addToken((Place<Object>) entry.place(), (Token<Object>) token);
                    produced.add(token);
                    emitEvent(new NetEvent.TokenAdded(
                        Instant.now(), entry.place().name(), token));
                }

                // Update bitmap for produced places and mark dirty
                for (var entry : outputs.entries()) {
                    int pid = compiled.placeId(entry.place());
                    casSetBit(markedPlaces, pid);
                    markDirty(pid);
                }

                // Also mark the completed transition's own ID dirty
                // so it gets re-evaluated for enablement
                markTransitionDirty(tid);

                var transitionDuration = Duration.ofNanos(System.nanoTime() - flight.startNanos());
                emitEvent(new NetEvent.TransitionCompleted(
                    Instant.now(), t.name(), produced, transitionDuration));

            } catch (OutViolationException e) {
                handleTransitionFailure(t, new CompletionException(e));
                markTransitionDirty(tid);
            } catch (CompletionException e) {
                handleTransitionFailure(t, e);
                markTransitionDirty(tid);
            }
        }
    }

    private void handleTransitionFailure(Transition t, CompletionException e) {
        emitEvent(new NetEvent.TransitionFailed(
            Instant.now(), t.name(),
            e.getCause().getMessage(),
            e.getCause().getClass().getName()));
    }

    // ======================== External Events ========================

    @SuppressWarnings("unchecked")
    private void processExternalEvents() {
        ExternalEvent<?> event;
        while ((event = externalEventQueue.poll()) != null) {
            try {
                marking.addToken(
                    (Place<Object>) event.place(),
                    (Token<Object>) event.token());

                int pid = compiled.placeId(event.place());
                casSetBit(markedPlaces, pid);
                markDirty(pid);

                emitEvent(new NetEvent.TokenAdded(
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
        if (!completionQueue.isEmpty() || !externalEventQueue.isEmpty()) return;

        if (!inFlight.isEmpty()) {
            awaitCompletionOrEvent();
        } else if (longRunning && !environmentPlaces.isEmpty()) {
            awaitExternalEvent();
        }
    }

    private void awaitCompletionOrEvent() {
        for (var flight : inFlight.values()) {
            if (flight.future().isDone()) return;
        }
        if (!completionQueue.isEmpty() || !externalEventQueue.isEmpty()) return;

        if (!inFlight.isEmpty()) {
            var futures = inFlight.values().stream()
                .map(InFlightTransition::future)
                .toArray(CompletableFuture[]::new);

            CompletableFuture<Object> anyCompletion = CompletableFuture.anyOf(futures);

            while (!anyCompletion.isDone() && !closed.get()) {
                try {
                    if (wakeUpSignal.tryAcquire(50, TimeUnit.MILLISECONDS)) {
                        wakeUpSignal.drainPermits();
                        return;
                    }
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    return;
                }
                if (!completionQueue.isEmpty() || !externalEventQueue.isEmpty()) return;
            }
            wakeUpSignal.drainPermits();
        }
    }

    private long millisUntilNextTimedTransition() {
        long nowNanos = System.nanoTime();
        long minWaitMs = Long.MAX_VALUE;

        for (int tid = 0; tid < compiled.transitionCount(); tid++) {
            if (!enabledFlags[tid]) continue;
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
    // Thread ownership:
    //   - markedPlaces, dirtySet: mutated only by the orchestrator thread.
    //     CAS is used (instead of plain volatile writes) to future-proof the
    //     design — virtual threads could update bitmaps directly without
    //     requiring architectural changes.
    //   - completionQueue, externalEventQueue: lock-free queues shared between
    //     virtual threads and the orchestrator.
    //
    // Dirty-set staleness guarantee:
    //   A transition may remain in the dirty set even after the marking change
    //   that triggered it has been superseded. This is safe because
    //   updateDirtyTransitions() always re-checks enablement against a fresh
    //   snapshot — a stale dirty bit only causes one redundant canEnable() call,
    //   never a missed evaluation.

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
     * Snapshots the marking bitmap into the reusable buffer.
     * Must only be called from the orchestrator thread.
     */
    private long[] snapshotMarking() {
        for (int i = 0; i < markingSnapBuffer.length; i++) {
            markingSnapBuffer[i] = markedPlaces.get(i);
        }
        return markingSnapBuffer;
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
        int word = tid >>> WORD_SHIFT;
        long mask = 1L << (tid & BIT_MASK);
        long prev;
        do {
            prev = dirtySet.get(word);
            if ((prev & mask) != 0) return;
        } while (!dirtySet.compareAndSet(word, prev, prev | mask));
    }

    // ======================== State Inspection ========================

    public Marking marking() { return marking; }

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
    public void close() {
        running = false;
        closed.set(true);
        wakeUp();
    }
}
