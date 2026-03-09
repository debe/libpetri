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
 * High-performance precompiled flat-array Petri net executor.
 *
 * <p>Compiles a {@link PetriNet} into a {@link PrecompiledNet} of flat-array operation
 * sequences and executes transitions via opcode dispatch, eliminating all virtual dispatch,
 * HashMap lookups, and priority sorting from the hot path.
 *
 * <h2>Key Optimizations over {@link BitmapNetExecutor}</h2>
 * <ul>
 *   <li><b>Flat array token storage</b> — ring buffers indexed by place ID replace
 *       {@code Map<Place, ArrayDeque>} for O(1) access with no hashing</li>
 *   <li><b>Opcode-based consume operations</b> — each transition's input/reset arcs are
 *       precompiled to a flat {@code int[]} of opcodes, eliminating sealed-type
 *       pattern matching per firing</li>
 *   <li><b>Priority-partitioned ready queues</b> — O(1) next-to-fire selection
 *       replaces O(k log k) sorting</li>
 *   <li><b>Flat in-flight tracking</b> — arrays indexed by transition ID replace
 *       {@code HashMap<Transition, InFlightTransition>}</li>
 * </ul>
 *
 * <h2>Concurrency Model</h2>
 * <p>Same as {@link BitmapNetExecutor}: single orchestrator thread owns all mutable
 * state; virtual threads execute async actions and signal completion via lock-free queues.
 *
 * @see PrecompiledNet
 * @see BitmapNetExecutor
 */
public final class PrecompiledNetExecutor implements PetriNetExecutor {
    static final int WORD_SHIFT = 6;
    static final int BIT_MASK = 63;

    private static final int INITIAL_RING_CAPACITY = 4;
    private static final long AWAIT_POLL_MS = 50;

    private final PrecompiledNet program;
    private final EventStore eventStore;
    private final ExecutorService executor;
    private final ExecutionContextProvider executionContextProvider;
    private final long startNanos;

    // ==================== Flat Token Pool ====================

    // Single flat array holding all places' token ring buffers contiguously.
    // tokenPool[placeOffset[pid] + localIndex] = Token<?> for place pid.
    private Object[] tokenPool;
    private int[] placeOffset;    // starting index in tokenPool for each place
    private int[] tokenCounts;
    private int[] ringHead;
    private int[] ringTail;
    private int[] ringCapacity;

    // ==================== Marking (synced from ring buffers on demand) ====================

    private final Marking marking;

    // ==================== Presence Bitmap ====================

    private final long[] markingBitmap;  // orchestrator-only, no CAS needed

    // ==================== Transition State ====================

    private final long[] enabledBitmap;
    private final long[] inFlightBitmap;
    private final long[] dirtyBitmap;
    private final long[] dirtyScanBuffer;
    private final long[] enabledAtNanos;
    private final int transitionWords;

    private int enabledTransitionCount;

    // ==================== Priority-Partitioned Ready Queues ====================

    private final int[][] readyQueues;
    private final int[] readyQueueHead;
    private final int[] readyQueueTail;
    private final int[] readyQueueSize;

    // ==================== Pooled Per-Transition Objects (sync fast path) ====================

    private final TransitionContext[] contextPool;  // one per transition, reused on sync path

    // ==================== In-Flight Tracking (Flat Arrays) ====================

    @SuppressWarnings("unchecked")
    private final CompletableFuture<Void>[] inFlightFutures;
    private final TransitionContext[] inFlightContexts;
    private final List<Token<?>>[] inFlightConsumed;
    private final long[] inFlightStartNanos;
    private int inFlightCount;

    // ==================== Completion & External Queues ====================

    private final Queue<Integer> completionQueue = new ConcurrentLinkedQueue<>();
    private final Queue<ExternalEvent<?>> externalEventQueue = new ConcurrentLinkedQueue<>();
    private final Semaphore wakeUpSignal = new Semaphore(0);
    private final CompletableFuture<Void>[] awaitFuturesBuffer; // reused in awaitCompletionOrEvent

    // ==================== Summary Bitmaps (two-level) ====================
    // Summary word s, bit w set ⇒ dirtyBitmap[(s<<6)|w] != 0
    private final long[] dirtyWordSummary;
    private final long[] enabledWordSummary;
    private final int summaryWords;

    // ==================== Reset-Clock Detection ====================

    private final long[] pendingResetWords;
    private boolean hasPendingResets; // set during fireTransition (RESET opcode), cleared at end of updateDirtyTransitions

    // ==================== Cached Flags ====================

    private final boolean eventStoreEnabled;
    private final boolean trackConsumed; // true if events enabled or custom context provider

    // ==================== Environment & Lifecycle ====================

    private final Set<EnvironmentPlace<?>> environmentPlaces;
    private final boolean longRunning;
    private final AtomicBoolean closed = new AtomicBoolean(false);
    private volatile boolean running = false;
    private Thread orchestratorThread;

    @SuppressWarnings({"unchecked", "deprecation"})
    private final boolean skipOutputValidation;

    private PrecompiledNetExecutor(
        PrecompiledNet program,
        Map<Place<?>, List<Token<?>>> initialTokens,
        EventStore eventStore,
        ExecutorService executor,
        Set<EnvironmentPlace<?>> environmentPlaces,
        boolean longRunning,
        ExecutionContextProvider executionContextProvider,
        boolean skipOutputValidation
    ) {
        this.program = program;
        this.eventStore = eventStore;
        this.executor = executor;
        this.environmentPlaces = environmentPlaces;
        this.longRunning = longRunning;
        this.executionContextProvider = executionContextProvider;
        this.skipOutputValidation = skipOutputValidation;
        this.startNanos = System.nanoTime();

        this.eventStoreEnabled = eventStore.isEnabled();
        this.trackConsumed = eventStoreEnabled || executionContextProvider != ExecutionContextProvider.NOOP;

        // Initialize Marking (single instance, synced from ring buffers on demand)
        this.marking = Marking.from(initialTokens);

        // Initialize flat token pool
        int totalSlots = program.placeCount * INITIAL_RING_CAPACITY;
        this.tokenPool = new Object[totalSlots];
        this.placeOffset = new int[program.placeCount];
        this.tokenCounts = new int[program.placeCount];
        this.ringHead = new int[program.placeCount];
        this.ringTail = new int[program.placeCount];
        this.ringCapacity = new int[program.placeCount];

        for (int pid = 0; pid < program.placeCount; pid++) {
            placeOffset[pid] = pid * INITIAL_RING_CAPACITY;
            ringCapacity[pid] = INITIAL_RING_CAPACITY;
        }

        // Load initial tokens into ring buffers
        for (var entry : initialTokens.entrySet()) {
            Place<?> place = entry.getKey();
            Integer pid = program.placeIndex.get(place);
            if (pid == null) continue;
            for (Token<?> token : entry.getValue()) {
                ringAddLast(pid, token);
            }
        }

        // Initialize marking bitmap
        int wordCount = program.wordCount;
        this.markingBitmap = new long[wordCount];

        // Transition bitmaps
        this.transitionWords = (program.transitionCount + BIT_MASK) >>> WORD_SHIFT;
        this.summaryWords = (transitionWords + BIT_MASK) >>> WORD_SHIFT;
        this.enabledBitmap = new long[transitionWords];
        this.inFlightBitmap = new long[transitionWords];
        this.dirtyBitmap = new long[transitionWords];
        this.dirtyScanBuffer = new long[transitionWords];
        this.dirtyWordSummary = new long[summaryWords];
        this.enabledWordSummary = new long[summaryWords];
        this.enabledAtNanos = new long[program.transitionCount];
        Arrays.fill(enabledAtNanos, Long.MIN_VALUE);

        // Priority-partitioned ready queues
        int prioCount = program.distinctPriorityCount;
        this.readyQueues = new int[prioCount][];
        this.readyQueueHead = new int[prioCount];
        this.readyQueueTail = new int[prioCount];
        this.readyQueueSize = new int[prioCount];
        for (int i = 0; i < prioCount; i++) {
            readyQueues[i] = new int[Math.max(program.transitionCount, 4)];
        }

        // Pooled per-transition objects for sync fast path
        this.contextPool = new TransitionContext[program.transitionCount];
        for (int tid = 0; tid < program.transitionCount; tid++) {
            Transition t = program.transitionsById[tid];
            contextPool[tid] = new TransitionContext(
                t, new TokenInput(program.inputPlaceCount[tid]), new TokenOutput());
        }

        // In-flight tracking
        this.inFlightFutures = new CompletableFuture[program.transitionCount];
        this.inFlightContexts = new TransitionContext[program.transitionCount];
        this.inFlightConsumed = new List[program.transitionCount];
        this.inFlightStartNanos = new long[program.transitionCount];
        this.awaitFuturesBuffer = new CompletableFuture[program.transitionCount];

        // Reset detection
        this.pendingResetWords = new long[program.wordCount];
    }

    // ==================== Ring Buffer Operations ====================

    private Token<?> ringRemoveFirst(int pid) {
        int head = ringHead[pid];
        int offset = placeOffset[pid];
        Token<?> token = (Token<?>) tokenPool[offset + head];
        tokenPool[offset + head] = null;
        ringHead[pid] = (head + 1) % ringCapacity[pid];
        tokenCounts[pid]--;
        return token;
    }

    private void ringAddLast(int pid, Token<?> token) {
        if (tokenCounts[pid] == ringCapacity[pid]) {
            growRing(pid);
        }
        int tail = ringTail[pid];
        int offset = placeOffset[pid];
        tokenPool[offset + tail] = token;
        ringTail[pid] = (tail + 1) % ringCapacity[pid];
        tokenCounts[pid]++;
    }

    private Token<?> ringPeekFirst(int pid) {
        if (tokenCounts[pid] == 0) return null;
        return (Token<?>) tokenPool[placeOffset[pid] + ringHead[pid]];
    }

    @SuppressWarnings("unchecked")
    private <T> List<Token<T>> ringRemoveAll(int pid) {
        int count = tokenCounts[pid];
        if (count == 0) return List.of();
        var result = new ArrayList<Token<T>>(count);
        for (int i = 0; i < count; i++) {
            result.add((Token<T>) ringRemoveFirst(pid));
        }
        return result;
    }

    private void ringClearAll(int pid) {
        int offset = placeOffset[pid];
        int cap = ringCapacity[pid];
        Arrays.fill(tokenPool, offset, offset + cap, null);
        tokenCounts[pid] = 0;
        ringHead[pid] = 0;
        ringTail[pid] = 0;
    }

    private void growRing(int pid) {
        int oldCap = ringCapacity[pid];
        int newCap = oldCap * 2;
        int oldOffset = placeOffset[pid];
        int head = ringHead[pid];

        // Relocate this place to new space at end of pool
        int newOffset = tokenPool.length;
        Object[] newPool = new Object[newOffset + newCap];
        System.arraycopy(tokenPool, 0, newPool, 0, tokenPool.length);

        // Copy ring contents linearized
        for (int i = 0; i < oldCap; i++) {
            newPool[newOffset + i] = tokenPool[oldOffset + (head + i) % oldCap];
        }

        tokenPool = newPool;
        placeOffset[pid] = newOffset;
        ringHead[pid] = 0;
        ringTail[pid] = oldCap;
        ringCapacity[pid] = newCap;
    }

    // ==================== Bitmap Helpers ====================

    private void setEnabledBit(int tid) {
        int w = tid >>> WORD_SHIFT;
        enabledBitmap[w] |= 1L << (tid & BIT_MASK);
        enabledWordSummary[w >>> WORD_SHIFT] |= 1L << (w & BIT_MASK);
    }

    private void clearEnabledBit(int tid) {
        int w = tid >>> WORD_SHIFT;
        enabledBitmap[w] &= ~(1L << (tid & BIT_MASK));
        if (enabledBitmap[w] == 0) {
            enabledWordSummary[w >>> WORD_SHIFT] &= ~(1L << (w & BIT_MASK));
        }
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

    // ==================== Ready Queue Operations ====================

    private void readyQueuePush(int tid) {
        int pi = program.transitionToPriorityIndex[tid];
        int tail = readyQueueTail[pi];
        int cap = readyQueues[pi].length;
        if (readyQueueSize[pi] == cap) {
            // Grow
            int[] newQueue = new int[cap * 2];
            int head = readyQueueHead[pi];
            for (int i = 0; i < cap; i++) {
                newQueue[i] = readyQueues[pi][(head + i) % cap];
            }
            readyQueues[pi] = newQueue;
            readyQueueHead[pi] = 0;
            tail = cap;
            readyQueueTail[pi] = tail;
        }
        readyQueues[pi][tail] = tid;
        readyQueueTail[pi] = (tail + 1) % readyQueues[pi].length;
        readyQueueSize[pi]++;
    }

    private int readyQueuePop(int pi) {
        int head = readyQueueHead[pi];
        int tid = readyQueues[pi][head];
        readyQueueHead[pi] = (head + 1) % readyQueues[pi].length;
        readyQueueSize[pi]--;
        return tid;
    }

    private void clearAllReadyQueues() {
        for (int pi = 0; pi < program.distinctPriorityCount; pi++) {
            readyQueueHead[pi] = 0;
            readyQueueTail[pi] = 0;
            readyQueueSize[pi] = 0;
        }
    }

    // ==================== Factory Methods ====================

    public static PrecompiledNetExecutor create(
        PetriNet net,
        Map<Place<?>, List<Token<?>>> initialTokens
    ) {
        return builder(net, initialTokens).build();
    }

    public static PrecompiledNetExecutor create(
        PetriNet net,
        Map<Place<?>, List<Token<?>>> initialTokens,
        EventStore eventStore
    ) {
        return builder(net, initialTokens).eventStore(eventStore).build();
    }

    public static Builder builder(PetriNet net, Map<Place<?>, List<Token<?>>> initialTokens) {
        return new Builder(net, initialTokens);
    }

    public static final class Builder {
        private final PetriNet net;
        private final Map<Place<?>, List<Token<?>>> initialTokens;
        private PrecompiledNet program = null;
        private EventStore eventStore = EventStore.noop();
        private ExecutorService executor = null;
        private Set<EnvironmentPlace<?>> environmentPlaces = Set.of();
        private boolean longRunning = false;
        private boolean skipOutputValidation = false;
        private ExecutionContextProvider executionContextProvider = ExecutionContextProvider.NOOP;

        private Builder(PetriNet net, Map<Place<?>, List<Token<?>>> initialTokens) {
            this.net = Objects.requireNonNull(net);
            this.initialTokens = Objects.requireNonNull(initialTokens);
        }

        public Builder program(PrecompiledNet program) {
            this.program = Objects.requireNonNull(program);
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

        public Builder longRunning(boolean enabled) {
            this.longRunning = enabled;
            return this;
        }

        public Builder executionContextProvider(ExecutionContextProvider provider) {
            this.executionContextProvider = Objects.requireNonNull(provider);
            return this;
        }

        /**
         * Skip output validation for trusted transition actions.
         * When enabled, the executor does not verify that transition outputs
         * match their declared output specs. This eliminates significant overhead
         * for high-throughput workloads where actions are known to be correct.
         */
        public Builder skipOutputValidation(boolean skip) {
            this.skipOutputValidation = skip;
            return this;
        }

        @SuppressWarnings("deprecation")
        public PrecompiledNetExecutor build() {
            var prog = program != null ? program : PrecompiledNet.compile(net);
            ExecutorService exec = executor != null
                ? executor
                : Executors.newVirtualThreadPerTaskExecutor();
            return new PrecompiledNetExecutor(
                prog, initialTokens, eventStore, exec,
                environmentPlaces, longRunning, executionContextProvider,
                skipOutputValidation
            );
        }
    }

    // ==================== PetriNetExecutor Interface ====================

    @Override
    public Marking run() {
        return executeLoop();
    }

    @Override
    public CompletionStage<Marking> run(Duration timeout) {
        return CompletableFuture.supplyAsync(
            this::executeLoop, executor
        ).orTimeout(timeout.toMillis(), TimeUnit.MILLISECONDS);
    }

    @Override
    public <T> CompletableFuture<Boolean> inject(EnvironmentPlace<T> place, T token) {
        return inject(place, Token.of(token));
    }

    @Override
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

    @Override
    public <T> void injectAsync(EnvironmentPlace<T> place, Token<T> token) {
        inject(place, token);
    }

    @Override
    public Marking marking() {
        syncMarkingFromRingBuffers();
        return marking;
    }

    /**
     * Syncs the Marking instance from ring buffers. Only called when marking()
     * is accessed (end of execution, external inspection in long-running mode),
     * never on the hot path.
     */
    @SuppressWarnings("unchecked")
    private void syncMarkingFromRingBuffers() {
        marking.clear();
        for (int pid = 0; pid < program.placeCount; pid++) {
            int count = tokenCounts[pid];
            if (count == 0) continue;
            Place<Object> place = (Place<Object>) program.placesById[pid];
            int head = ringHead[pid];
            int cap = ringCapacity[pid];
            int offset = placeOffset[pid];
            for (int i = 0; i < count; i++) {
                marking.addToken(place, (Token<Object>) tokenPool[offset + (head + i) % cap]);
            }
        }
    }

    @Override
    public boolean isQuiescent() {
        return enabledTransitionCount == 0 && inFlightCount == 0;
    }

    @Override
    public boolean isWaitingForCompletion() {
        return enabledTransitionCount == 0 && inFlightCount > 0;
    }

    @Override
    public int inFlightCount() { return inFlightCount; }

    @Override
    public int enabledCount() { return enabledTransitionCount; }

    @Override
    public String executionId() {
        return Long.toHexString(startNanos);
    }

    @Override
    public void close() {
        running = false;
        closed.set(true);
        wakeUp();
    }

    // ==================== Execution Loop ====================

    private Marking executeLoop() {
        running = true;
        orchestratorThread = Thread.currentThread();
        if (eventStoreEnabled) {
            emitEvent(new NetEvent.ExecutionStarted(
                Instant.now(), netName(), executionId()));
        }

        initializeMarkingBitmap();
        markAllDirty();
        emitMarkingSnapshot();

        while (running && !Thread.currentThread().isInterrupted() && !closed.get()) {
            processCompletedTransitions();
            processExternalEvents();
            updateDirtyTransitions();
            if (program.anyDeadlines) enforceDeadlines();

            if (shouldTerminate()) break;

            fireReadyTransitions();

            if (hasDirtyBits()) continue;

            awaitWork();
        }

        running = false;
        drainPendingExternalEvents();

        emitMarkingSnapshot();
        if (eventStoreEnabled) {
            emitEvent(new NetEvent.ExecutionCompleted(
                Instant.now(), netName(), executionId(), elapsedDuration()));
        }

        return marking();
    }

    private String netName() {
        return program.netName;
    }

    private void initializeMarkingBitmap() {
        for (int pid = 0; pid < program.placeCount; pid++) {
            if (tokenCounts[pid] > 0) {
                setMarkingBit(pid);
            }
        }
    }

    private void markAllDirty() {
        int tc = program.transitionCount;
        int lastWordBits = tc & BIT_MASK;
        for (int w = 0; w < transitionWords - 1; w++) {
            dirtyBitmap[w] = -1L;
        }
        if (transitionWords > 0) {
            dirtyBitmap[transitionWords - 1] = lastWordBits == 0 ? -1L : (1L << lastWordBits) - 1;
        }
        // Set all summary bits
        for (int s = 0; s < summaryWords; s++) {
            int firstW = s << WORD_SHIFT;
            int lastW = Math.min(firstW + BIT_MASK, transitionWords - 1);
            int count = lastW - firstW + 1;
            int lastBits = count & BIT_MASK;
            dirtyWordSummary[s] = lastBits == 0 ? -1L : (1L << lastBits) - 1;
        }
    }

    private boolean shouldTerminate() {
        if (longRunning) return closed.get();
        return enabledTransitionCount == 0 && inFlightCount == 0 && completionQueue.isEmpty();
    }

    // ==================== Dirty Set Processing ====================

    private void updateDirtyTransitions() {
        long nowNanos = System.nanoTime();

        // Snapshot and clear dirty bitmap using summary to visit only non-zero words
        for (int s = 0; s < summaryWords; s++) {
            long summary = dirtyWordSummary[s];
            dirtyWordSummary[s] = 0;
            while (summary != 0) {
                int localW = Long.numberOfTrailingZeros(summary);
                summary &= summary - 1;
                int w = (s << WORD_SHIFT) | localW;
                dirtyScanBuffer[w] = dirtyBitmap[w];
                dirtyBitmap[w] = 0;
            }
        }

        // Process dirty transitions — linear scan over pre-zeroed buffer; zero-word continue is O(1)
        for (int w = 0; w < transitionWords; w++) {
            long word = dirtyScanBuffer[w];
            if (word == 0) continue;
            dirtyScanBuffer[w] = 0; // clear for next cycle
            while (word != 0) {
                int bit = Long.numberOfTrailingZeros(word);
                int tid = (w << WORD_SHIFT) | bit;
                word &= word - 1;

                if (tid >= program.transitionCount) break;
                if (isInFlight(tid)) continue;

                boolean wasEnabled = isEnabled(tid);
                boolean canNow = canEnable(tid);

                if (canNow && !wasEnabled) {
                    setEnabledBit(tid);
                    enabledTransitionCount++;
                    enabledAtNanos[tid] = nowNanos;
                    if (eventStoreEnabled) emitEvent(new NetEvent.TransitionEnabled(
                        Instant.now(), program.transitionsById[tid].name()));
                } else if (!canNow && wasEnabled) {
                    clearEnabledBit(tid);
                    enabledTransitionCount--;
                    enabledAtNanos[tid] = Long.MIN_VALUE;
                } else if (canNow && wasEnabled && hasInputFromResetPlace(tid)) {
                    enabledAtNanos[tid] = nowNanos;
                    if (eventStoreEnabled) emitEvent(new NetEvent.TransitionClockRestarted(
                        Instant.now(), program.transitionsById[tid].name()));
                }
            }
        }

        clearPendingResets();
    }

    private boolean canEnable(int tid) {
        if (!program.canEnableBitmap(tid, markingBitmap)) return false;

        var cardCheck = program.cardinalityChecks[tid];
        if (cardCheck != null) {
            for (int i = 0; i < cardCheck.placeIds().length; i++) {
                int pid = cardCheck.placeIds()[i];
                int required = cardCheck.requiredCounts()[i];
                if (tokenCounts[pid] < required) return false;
            }
        }
        return true;
    }

    private boolean hasInputFromResetPlace(int tid) {
        if (!hasPendingResets) return false;
        long[] inputMask = program.inputPlaceMaskWords[tid];
        int len = Math.min(inputMask.length, pendingResetWords.length);
        for (int i = 0; i < len; i++) {
            if ((inputMask[i] & pendingResetWords[i]) != 0) {
                return true;
            }
        }
        return false;
    }

    private void clearPendingResets() {
        if (hasPendingResets) {
            Arrays.fill(pendingResetWords, 0);
            hasPendingResets = false;
        }
    }

    // ==================== Deadline Enforcement ====================

    private void enforceDeadlines() {
        long nowNanos = System.nanoTime();
        for (int s = 0; s < summaryWords; s++) {
            long summary = enabledWordSummary[s];
            while (summary != 0) {
                int localW = Long.numberOfTrailingZeros(summary);
                summary &= summary - 1;
                int w = (s << WORD_SHIFT) | localW;
                long word = enabledBitmap[w];
                while (word != 0) {
                    int bit = Long.numberOfTrailingZeros(word);
                    int tid = (w << WORD_SHIFT) | bit;
                    word &= word - 1;

                    if (!program.hasDeadline[tid]) continue;

                    long enabledNanos = enabledAtNanos[tid];
                    long elapsedMillis = (nowNanos - enabledNanos) / 1_000_000;
                    long latestMillis = program.latestMillis[tid];

                    if (elapsedMillis > latestMillis) {
                        clearEnabledBit(tid);
                        enabledTransitionCount--;
                        enabledAtNanos[tid] = Long.MIN_VALUE;
                        markTransitionDirty(tid);
                        if (eventStoreEnabled) {
                            Transition t = program.transitionsById[tid];
                            emitEvent(new NetEvent.TransitionTimedOut(
                                Instant.now(), t.name(),
                                t.timing().latest(),
                                Duration.ofMillis(elapsedMillis)));
                        }
                    }
                }
            }
        }
    }

    // ==================== Firing ====================

    private void fireReadyTransitions() {
        if (program.allImmediate && program.allSamePriority) {
            fireReadyImmediate();
            return;
        }
        fireReadyGeneral();
    }

    /**
     * Fast path for nets where all transitions are immediate and same priority.
     * Fires directly from enabled bitmap — no ready queues, no timing checks.
     */
    private void fireReadyImmediate() {
        for (int s = 0; s < summaryWords; s++) {
            long summary = enabledWordSummary[s];
            while (summary != 0) {
                int localW = Long.numberOfTrailingZeros(summary);
                summary &= summary - 1;
                int w = (s << WORD_SHIFT) | localW;
                long word = enabledBitmap[w] & ~inFlightBitmap[w];
                while (word != 0) {
                    int bit = Long.numberOfTrailingZeros(word);
                    int tid = (w << WORD_SHIFT) | bit;
                    word &= word - 1;

                    if (canEnable(tid)) {
                        fireTransition(tid);
                    } else {
                        clearEnabledBit(tid);
                        enabledTransitionCount--;
                        enabledAtNanos[tid] = Long.MIN_VALUE;
                    }
                }
            }
        }
    }

    /**
     * General firing path using priority-partitioned ready queues.
     */
    private void fireReadyGeneral() {
        long nowNanos = System.nanoTime();

        // Populate ready queues from enabled bitmap using summary
        clearAllReadyQueues();
        for (int s = 0; s < summaryWords; s++) {
            long summary = enabledWordSummary[s];
            while (summary != 0) {
                int localW = Long.numberOfTrailingZeros(summary);
                summary &= summary - 1;
                int w = (s << WORD_SHIFT) | localW;
                long word = enabledBitmap[w] & ~inFlightBitmap[w];
                while (word != 0) {
                    int bit = Long.numberOfTrailingZeros(word);
                    int tid = (w << WORD_SHIFT) | bit;
                    word &= word - 1;

                    long enabledNanos = enabledAtNanos[tid];
                    long elapsedMillis = (nowNanos - enabledNanos) / 1_000_000;

                    if (program.earliestMillis[tid] <= elapsedMillis) {
                        readyQueuePush(tid);
                    }
                }
            }
        }

        // Fire from highest priority queue first
        for (int pi = 0; pi < program.distinctPriorityCount; pi++) {
            while (readyQueueSize[pi] > 0) {
                int tid = readyQueuePop(pi);
                if (!isEnabled(tid) || isInFlight(tid)) continue;

                if (canEnable(tid)) {
                    fireTransition(tid);
                } else {
                    clearEnabledBit(tid);
                    enabledTransitionCount--;
                    enabledAtNanos[tid] = Long.MIN_VALUE;
                }
            }
        }
    }

    // ==================== Consume Operation Execution ====================

    @SuppressWarnings("unchecked")
    private void fireTransition(int tid) {
        Transition t = program.transitionsById[tid];

        // Reuse pooled context (reset input/output)
        TransitionContext context = contextPool[tid];
        TokenInput inputs = context.rawInput();
        inputs.clear();
        TokenOutput output = context.rawOutput();
        output.clear();

        List<Token<?>> consumed = trackConsumed ? new ArrayList<>() : null;

        // Execute consume operations
        int[] prog = program.consumeOps[tid];
        int pc = 0;
        while (pc < prog.length) {
            int opcode = prog[pc++];
            switch (opcode) {
                case PrecompiledNet.CONSUME_ONE -> {
                    int pid = prog[pc++];
                    Token<?> token = ringRemoveFirst(pid);
                    if (consumed != null) consumed.add(token);
                    inputs.add((Place<Object>) program.placesById[pid], (Token<Object>) token);
                    if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
                        Instant.now(), program.placesById[pid].name(), token));
                }
                case PrecompiledNet.CONSUME_N -> {
                    int pid = prog[pc++];
                    int count = prog[pc++];
                    Place<Object> place = (Place<Object>) program.placesById[pid];
                    for (int i = 0; i < count; i++) {
                        Token<?> token = ringRemoveFirst(pid);
                        if (consumed != null) consumed.add(token);
                        inputs.add(place, (Token<Object>) token);
                        if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
                            Instant.now(), place.name(), token));
                    }
                }
                case PrecompiledNet.CONSUME_ALL -> {
                    int pid = prog[pc++];
                    int count = tokenCounts[pid];
                    Place<Object> place = (Place<Object>) program.placesById[pid];
                    for (int i = 0; i < count; i++) {
                        Token<?> token = ringRemoveFirst(pid);
                        if (consumed != null) consumed.add(token);
                        inputs.add(place, (Token<Object>) token);
                        if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
                            Instant.now(), place.name(), token));
                    }
                }
                case PrecompiledNet.CONSUME_ATLEAST -> {
                    int pid = prog[pc++];
                    pc++; // skip minimum (already verified during enablement)
                    int count = tokenCounts[pid];
                    Place<Object> place = (Place<Object>) program.placesById[pid];
                    for (int i = 0; i < count; i++) {
                        Token<?> token = ringRemoveFirst(pid);
                        if (consumed != null) consumed.add(token);
                        inputs.add(place, (Token<Object>) token);
                        if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
                            Instant.now(), place.name(), token));
                    }
                }
                case PrecompiledNet.RESET -> {
                    int pid = prog[pc++];
                    int count = tokenCounts[pid];
                    for (int i = 0; i < count; i++) {
                        Token<?> token = ringRemoveFirst(pid);
                        if (consumed != null) consumed.add(token);
                        if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
                            Instant.now(), program.placesById[pid].name(), token));
                    }
                    pendingResetWords[pid >>> WORD_SHIFT] |= 1L << (pid & BIT_MASK);
                    hasPendingResets = true;
                }
                default -> throw new IllegalStateException("Unknown opcode: " + opcode);
            }
        }

        // Execute read program
        int[] readProg = program.readOps[tid];
        for (int rpid : readProg) {
            Token<?> token = ringPeekFirst(rpid);
            if (token != null) {
                inputs.add((Place<Object>) program.placesById[rpid], (Token<Object>) token);
            }
        }

        // Update bitmap for consumed/reset places
        updateBitmapAfterConsumption(tid);

        if (eventStoreEnabled) emitEvent(new NetEvent.TransitionStarted(
            Instant.now(), t.name(), consumed != null ? consumed : List.of()));

        // Update execution context if custom provider
        if (trackConsumed) {
            context.resetExecutionContext(executionContextProvider.createContext(t, consumed));
        }

        // ScopedValue binding: only when event store is enabled (avoids allocation on fast path).
        // When enabled, TransitionContext.current() returns the active context for
        // framework interceptors (logging adapters, middleware) during action execution.
        CompletableFuture<Void> transitionFuture = eventStoreEnabled
            ? ScopedValue.where(TransitionContext.scopedValue(), context)
                  .call(() -> LogCaptureScope.call(t.name(), eventStore::append,
                      () -> t.action().execute(context).toCompletableFuture()))
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
                        ExecutorSupport.produceTimeoutOutput(context, timeoutSpec.child());
                        if (eventStoreEnabled) emitEvent(new NetEvent.ActionTimedOut(
                            Instant.now(), t.name(), timeoutSpec.after()));
                        return null;
                    }
                    throw (ex instanceof RuntimeException re) ? re : new RuntimeException(ex);
                });
        }

        // Clear enabled status
        clearEnabledBit(tid);
        enabledTransitionCount--;
        enabledAtNanos[tid] = Long.MIN_VALUE;

        // Sync fast path — pooled context reused, no allocation
        if (!t.hasActionTimeout() && transitionFuture.isDone()) {
            processSyncOutput(tid, transitionFuture, context, consumed);
        } else {
            // Async path — pooled context safe: transition can't re-fire while in-flight
            int tidCapture = tid;
            transitionFuture.whenComplete((_, _) -> {
                completionQueue.offer(tidCapture);
                wakeUp();
            });
            inFlightFutures[tid] = transitionFuture;
            inFlightContexts[tid] = context;
            inFlightConsumed[tid] = consumed;
            inFlightStartNanos[tid] = System.nanoTime();
            inFlightCount++;
            setInFlightBit(tid);
        }
    }

    private void updateBitmapAfterConsumption(int tid) {
        int[] pids = program.consumptionPlaceIds[tid];
        for (int pid : pids) {
            if (tokenCounts[pid] == 0) {
                clearMarkingBit(pid);
            }
            markDirty(pid);
        }
    }

    // ==================== Output Processing ====================

    @SuppressWarnings("unchecked")
    private void processSyncOutput(int tid, CompletableFuture<Void> future,
                                   TransitionContext context, List<Token<?>> consumed) {
        Transition t = program.transitionsById[tid];
        try {
            future.join();

            TokenOutput outputs = context.rawOutput();
            validateOutput(tid, t, outputs);

            List<Token<?>> produced = eventStoreEnabled ? new ArrayList<>() : null;
            for (var entry : outputs.entries()) {
                var token = entry.token();
                int pid = program.placeId(entry.place());
                ringAddLast(pid, token);
                setMarkingBit(pid);
                markDirty(pid);
                if (eventStoreEnabled) {
                    produced.add(token);
                    emitEvent(new NetEvent.TokenAdded(
                        Instant.now(), entry.place().name(), token));
                }
            }

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

    // ==================== Completion Processing ====================

    @SuppressWarnings("unchecked")
    private void processCompletedTransitions() {
        Integer tidBox;
        while ((tidBox = completionQueue.poll()) != null) {
            int tid = tidBox;
            CompletableFuture<Void> future = inFlightFutures[tid];
            TransitionContext context = inFlightContexts[tid];
            long flightStart = inFlightStartNanos[tid];

            // Clear in-flight state
            inFlightFutures[tid] = null;
            inFlightContexts[tid] = null;
            inFlightConsumed[tid] = null;
            inFlightCount--;
            clearInFlightBit(tid);

            if (future == null) continue;

            Transition t = program.transitionsById[tid];
            try {
                future.join();

                TokenOutput outputs = context.rawOutput();
                validateOutput(tid, t, outputs);

                List<Token<?>> produced = eventStoreEnabled ? new ArrayList<>() : null;
                for (var entry : outputs.entries()) {
                    var token = entry.token();
                    int pid = program.placeId(entry.place());
                    ringAddLast(pid, token);
                    setMarkingBit(pid);
                    markDirty(pid);
                    if (produced != null) produced.add(token);
                    if (eventStoreEnabled) emitEvent(new NetEvent.TokenAdded(
                        Instant.now(), entry.place().name(), token));
                }

                markTransitionDirty(tid);

                if (eventStoreEnabled) {
                    var transitionDuration = Duration.ofNanos(System.nanoTime() - flightStart);
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

    // ==================== External Events ====================

    @SuppressWarnings("unchecked")
    private void processExternalEvents() {
        ExternalEvent<?> event;
        while ((event = externalEventQueue.poll()) != null) {
            try {
                int pid = program.placeId(event.place());
                ringAddLast(pid, event.token());
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

    // ==================== Await Work ====================

    private void awaitWork() {
        if (!completionQueue.isEmpty() || !externalEventQueue.isEmpty()) return;

        if (inFlightCount > 0) {
            awaitCompletionOrEvent();
        } else if (enabledTransitionCount > 0 || (longRunning && !environmentPlaces.isEmpty())) {
            // Wait for timed transitions to become ready, or for external events
            awaitExternalEvent();
        }
    }

    private void awaitCompletionOrEvent() {
        // Check if any in-flight is already done
        for (int tid = 0; tid < program.transitionCount; tid++) {
            if (inFlightFutures[tid] != null && inFlightFutures[tid].isDone()) return;
        }
        if (!completionQueue.isEmpty() || !externalEventQueue.isEmpty()) return;

        // Collect in-flight futures into pre-allocated buffer
        int count = 0;
        for (int tid = 0; tid < program.transitionCount; tid++) {
            if (inFlightFutures[tid] != null) awaitFuturesBuffer[count++] = inFlightFutures[tid];
        }
        if (count == 0) return;

        CompletableFuture<Object> anyCompletion =
            CompletableFuture.anyOf(Arrays.copyOf(awaitFuturesBuffer, count));

        while (!anyCompletion.isDone() && !closed.get()) {
            try {
                if (wakeUpSignal.tryAcquire(AWAIT_POLL_MS, TimeUnit.MILLISECONDS)) {
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

    private long nanosUntilNextTimedTransition() {
        long nowNanos = System.nanoTime();
        long minWaitNanos = Long.MAX_VALUE;

        for (int s = 0; s < summaryWords; s++) {
            long summary = enabledWordSummary[s];
            while (summary != 0) {
                int localW = Long.numberOfTrailingZeros(summary);
                summary &= summary - 1;
                int w = (s << WORD_SHIFT) | localW;
                long word = enabledBitmap[w];
                while (word != 0) {
                    int bit = Long.numberOfTrailingZeros(word);
                    int tid = (w << WORD_SHIFT) | bit;
                    word &= word - 1;

                    long enabledNanos = enabledAtNanos[tid];
                    long elapsed = nowNanos - enabledNanos;

                    long remainingEarliest = program.earliestNanos[tid] - elapsed;
                    if (remainingEarliest <= 0) return 0;
                    minWaitNanos = Math.min(minWaitNanos, remainingEarliest);

                    if (program.hasDeadline[tid]) {
                        long remainingDeadline = program.latestNanos[tid] - elapsed;
                        if (remainingDeadline <= 0) return 0;
                        minWaitNanos = Math.min(minWaitNanos, remainingDeadline);
                    }
                }
            }
        }
        return minWaitNanos;
    }

    private void awaitExternalEvent() {
        try {
            long waitNanos = nanosUntilNextTimedTransition();
            if (waitNanos <= 0) return;
            long waitMs = waitNanos == Long.MAX_VALUE ? Long.MAX_VALUE : (waitNanos + 999_999) / 1_000_000;
            if (waitMs == Long.MAX_VALUE) wakeUpSignal.acquire();
            else wakeUpSignal.tryAcquire(waitMs, TimeUnit.MILLISECONDS);
            wakeUpSignal.drainPermits();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }

    // ==================== Output Validation ====================

    private void validateOutput(int tid, Transition t, TokenOutput outputs) {
        if (skipOutputValidation) return;
        int simplePid = program.simpleOutputPlaceId[tid];
        if (simplePid == -2) return; // no output spec
        if (simplePid >= 0) {
            // Fast path: Out.Place — just check the single expected place got a token
            var entries = outputs.entries();
            for (var entry : entries) {
                if (program.placeIndex.get(entry.place()) == simplePid) return;
            }
            throw new OutViolationException(
                "'%s': output does not satisfy declared spec".formatted(t.name()));
        }
        // Complex spec: fall back to full validation
        Set<Place<?>> produced = outputs.placesWithTokens();
        ExecutorSupport.validateOutSpec(t.name(), t.outputSpec(), produced)
            .orElseThrow(() -> new OutViolationException(
                "'%s': output does not satisfy declared spec".formatted(t.name())));
    }

    // ==================== Dirty Bitmap Helpers ====================

    private void markDirty(int pid) {
        int[] tids = program.placeToTransitions[pid];
        for (int tid : tids) {
            markTransitionDirty(tid);
        }
    }

    private void markTransitionDirty(int tid) {
        int w = tid >>> WORD_SHIFT;
        dirtyBitmap[w] |= 1L << (tid & BIT_MASK);
        dirtyWordSummary[w >>> WORD_SHIFT] |= 1L << (w & BIT_MASK);
    }

    private boolean hasDirtyBits() {
        for (long s : dirtyWordSummary) if (s != 0) return true;
        return false;
    }

    // ==================== Event Helpers ====================

    private void emitEvent(NetEvent event) {
        if (eventStore.isEnabled()) {
            eventStore.append(event);
        }
    }

    private Duration elapsedDuration() {
        return Duration.ofNanos(System.nanoTime() - startNanos);
    }

    private void emitMarkingSnapshot() {
        if (eventStoreEnabled) {
            emitEvent(new NetEvent.MarkingSnapshot(Instant.now(), marking().snapshot()));
        }
    }

    private void wakeUp() {
        wakeUpSignal.release();
    }
}
