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
 *                                             4. set bits in dirtyBitmap
 * </pre>
 *
 * <p>Virtual threads signal completion via the lock-free {@code completionQueue} and
 * wake up the orchestrator. All bitmap mutations (markedPlaces, dirtyBitmap) happen on
 * the orchestrator thread. The CAS operations on markedPlaces future-proof the design
 * for potential direct virtual-thread bitmap updates without requiring architectural changes.
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

    // Lock-free bitmap for concurrent marking updates
    private final AtomicLongArray markedPlaces;

    // Plain shadow bitmap — always in sync with markedPlaces, avoids volatile reads
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

    /** Whether this executor has environment places (implies long-running behavior). */
    private final boolean hasEnvironmentPlaces;

    /** Tracks if drain() was called — reject new inject() calls. */
    private final AtomicBoolean draining = new AtomicBoolean(false);

    /** Tracks if close() was called — immediate shutdown. */
    private final AtomicBoolean closed = new AtomicBoolean(false);

    private volatile boolean running = false;

    /** Set at the start of executeLoop; used for thread-safety assertions. */
    private Thread orchestratorThread;

    @SuppressWarnings("deprecation") // Executors.newVirtualThreadPerTaskExecutor() marked deprecated-for-removal in JDK 25
    private BitmapNetExecutor(
        CompiledNet compiled,
        Marking marking,
        EventStore eventStore,
        ExecutorService executor,
        Set<EnvironmentPlace<?>> environmentPlaces,
        ExecutionContextProvider executionContextProvider
    ) {
        this.compiled = compiled;
        this.marking = marking;
        this.eventStore = eventStore;
        this.executor = executor;
        this.environmentPlaces = environmentPlaces;
        this.hasEnvironmentPlaces = !environmentPlaces.isEmpty();
        this.executionContextProvider = executionContextProvider;
        this.startNanos = System.nanoTime();

        int wordCount = compiled.wordCount();
        this.markedPlaces = new AtomicLongArray(wordCount);
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
        casSetBit(markedPlaces, pid);
    }

    private void clearMarkingBit(int pid) {
        markingBitmap[pid >>> WORD_SHIFT] &= ~(1L << (pid & BIT_MASK));
        casClearBit(markedPlaces, pid);
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
        private CompiledNet compiledNet = null;
        private EventStore eventStore = EventStore.noop();
        private ExecutorService executor = null;
        private Set<EnvironmentPlace<?>> environmentPlaces = Set.of();
        private ExecutionContextProvider executionContextProvider = ExecutionContextProvider.NOOP;

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

        public Builder executionContextProvider(ExecutionContextProvider provider) {
            this.executionContextProvider = Objects.requireNonNull(provider);
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
                environmentPlaces, executionContextProvider
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
        if (closed.get() || draining.get()) {
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

        while (running && !Thread.currentThread().isInterrupted()) {
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

        running = false;
        drainPendingExternalEvents();

        emitMarkingSnapshot();
        emitEvent(new NetEvent.ExecutionCompleted(
            Instant.now(), compiled.net().name(), executionId(), elapsedDuration()));

        return marking;
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

                long enabledNanos = enabledAtNanos[tid];
                long elapsedMillis = (nowNanos - enabledNanos) / 1_000_000;
                long latestMillis = t.timing().latest().toMillis();

                if (elapsedMillis > latestMillis) {
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
                    fireTransition(tid);
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
                fireTransition(tid);
            } else {
                clearEnabledBit(tid);
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
                if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
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
                if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
                    Instant.now(), arc.place().name(), token));
            }
        }

        // Update bitmap for consumed/reset places
        updateBitmapAfterConsumption(tid);

        if (eventStoreEnabled) emitEvent(new NetEvent.TransitionStarted(Instant.now(), t.name(), consumed));

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
                        if (eventStoreEnabled) emitEvent(new NetEvent.ActionTimedOut(
                            Instant.now(), t.name(), timeoutSpec.after()));
                        return null;
                    }
                    throw (ex instanceof RuntimeException re) ? re : new RuntimeException(ex);
                });
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

            List<Token<?>> produced = eventStoreEnabled ? new ArrayList<>() : null;
            for (var entry : outputs.entries()) {
                var token = entry.token();
                marking.addToken((Place<Object>) entry.place(), (Token<Object>) token);
                if (eventStoreEnabled) {
                    produced.add(token);
                    emitEvent(new NetEvent.TokenAdded(
                        Instant.now(), entry.place().name(), token));
                }
            }

            // Update bitmap for produced places and mark dirty
            for (var entry : outputs.entries()) {
                int pid = compiled.placeId(entry.place());
                setMarkingBit(pid);
                markDirty(pid);
            }

            // Mark the completed transition dirty for re-evaluation
            markTransitionDirty(tid);

            if (eventStoreEnabled) {
                emitEvent(new NetEvent.TransitionCompleted(
                    Instant.now(), t.name(), produced, Duration.ZERO));
            }
        } catch (OutViolationException e) {
            handleTransitionFailure(t, new CompletionException(e));
            markTransitionDirty(tid);
        } catch (CompletionException e) {
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
            clearInFlightBit(tid);

            try {
                flight.future().join();

                TokenOutput outputs = flight.context().rawOutput();
                validateOutput(t, outputs);

                List<Token<?>> produced = new ArrayList<>();
                for (var entry : outputs.entries()) {
                    var token = entry.token();
                    marking.addToken((Place<Object>) entry.place(), (Token<Object>) token);
                    produced.add(token);
                    if (eventStoreEnabled) emitEvent(new NetEvent.TokenAdded(
                        Instant.now(), entry.place().name(), token));
                }

                // Update bitmap for produced places and mark dirty
                for (var entry : outputs.entries()) {
                    int pid = compiled.placeId(entry.place());
                    setMarkingBit(pid);
                    markDirty(pid);
                }

                // Also mark the completed transition's own ID dirty
                // so it gets re-evaluated for enablement
                markTransitionDirty(tid);

                if (eventStoreEnabled) {
                    var transitionDuration = Duration.ofNanos(System.nanoTime() - flight.startNanos());
                    emitEvent(new NetEvent.TransitionCompleted(
                        Instant.now(), t.name(), produced, transitionDuration));
                }

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
        if (eventStoreEnabled) emitEvent(new NetEvent.TransitionFailed(
            Instant.now(), t.name(),
            e.getCause().getMessage(),
            e.getCause().getClass().getName()));
    }

    // ======================== External Events ========================

    @SuppressWarnings("unchecked")
    private void processExternalEvents() {
        if (closed.get()) return; // ENV-013: leave queued events for drainPendingExternalEvents()
        ExternalEvent<?> event;
        while ((event = externalEventQueue.poll()) != null) {
            try {
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

        if (!inFlight.isEmpty()) {
            var futures = inFlight.values().stream()
                .map(InFlightTransition::future)
                .toArray(CompletableFuture[]::new);

            CompletableFuture<Object> anyCompletion = CompletableFuture.anyOf(futures);

            while (!anyCompletion.isDone()) {
                long pollMs = allImmediate ? 50 : Math.max(1, Math.min(50, millisUntilNextTimedTransition()));
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
            wakeUpSignal.drainPermits();
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
    // Thread ownership:
    //   - markedPlaces: mutated only by the orchestrator thread.
    //     CAS is used (instead of plain volatile writes) to future-proof the
    //     design — virtual threads could update bitmaps directly without
    //     requiring architectural changes.
    //   - dirtyBitmap: plain long[], orchestrator-thread only.
    //   - completionQueue, externalEventQueue: lock-free queues shared between
    //     virtual threads and the orchestrator.

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
     * Returns the shadow marking bitmap directly — zero-copy.
     * Must only be called from the orchestrator thread.
     */
    private long[] snapshotMarking() {
        return markingBitmap;
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
