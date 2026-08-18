package org.libpetri.runtime;

import java.time.Duration;
import java.time.Instant;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.locks.LockSupport;
import java.util.function.Function;
import java.util.function.Predicate;

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
 * <p>Same as {@link BitmapNetExecutor}: the single orchestrator thread owns all mutable state and
 * invokes transition actions <b>inline</b>. The executor never submits actions anywhere;
 * concurrency comes from whatever drives the {@link CompletionStage} an action returns, and
 * completion signals back through lock-free queues. The configured {@link ExecutorService} hosts
 * only the orchestrator loop, and only under {@link #run(Duration)}. A blocking action blocks the net.
 *
 * @see PrecompiledNet
 * @see BitmapNetExecutor
 */
public final class PrecompiledNetExecutor implements PetriNetExecutor, AwaitPollTunable {
    static final int WORD_SHIFT = 6;
    static final int BIT_MASK = 63;

    private static final int INITIAL_RING_CAPACITY = 4;
    private static final long AWAIT_POLL_MS = 50;

    /** Completion-wait poll fallback (ms). Only lengthened by tests; see {@link AwaitPollTunable}. */
    private volatile long awaitPollMillis = AWAIT_POLL_MS;

    private final PrecompiledNet program;

    // ν-net incremental match caches (NU-020): per matched transition, an
    // IncrementalMatcher kept in lockstep with the rings when the transition is
    // fast-path eligible (every correlated input is One/Exactly, consumed by no
    // other transition, never reset), else null → fall back to the O(n) rebuild
    // findMatchBinding. Turns a draining matched join from O(n²) into O(n log n).
    private MatchEngine.IncrementalMatcher[] matchCaches;
    /** Per place (by pid): the {tid, keyIndex} of every fast-path correlated input it feeds. */
    private java.util.List<int[]>[] placeMatchTargets;
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

    /** Monotonic source for ν-name minting ({@link TransitionContext#freshName()}, NU-010). */
    private final AtomicLong freshNameCounter = new AtomicLong();

    // ==================== Marking (synced from ring buffers on demand) ====================

    private final Marking marking;

    /**
     * Tokens on places the compiled program does not know (CORE-072 AC3). The ring pool only
     * stores compiled places, so these are retained here and merged into every observable
     * marking by {@link #syncMarkingFromRingBuffers} rather than dropped — the bitmap
     * reference retains them by keeping its whole {@code Marking}. Orchestrator-confined and
     * {@code null} until first needed, so the known-place hot paths never touch it.
     */
    private Map<Place<?>, List<Token<?>>> extraTokens;

    /** Unknown places already reported (CORE-072 AC4) — one diagnostic per place, not per token. */
    private Set<Place<?>> warnedUnknownPlaces;

    // ==================== Presence Bitmap ====================

    private final long[] markingBitmap;  // orchestrator-only, no CAS needed

    /**
     * Post-consumption, pre-deposit presence snapshot used for intra-pass firing rechecks.
     *
     * <p>Outputs deposit in loop step 1 and firing is step 5 (EXEC-001), so tokens a
     * same-cycle sync action produces must be <em>invisible</em> to the recheck of
     * subsequent ready transitions in the same firing pass; consumption, by contrast,
     * must be visible (losers are disabled by consumption, EXEC-003). The buffer is
     * refreshed from {@link #markingBitmap} when the ready set is collected and again
     * after each firing's consumption ({@link #updateBitmapAfterConsumption}) — never on
     * deposit — matching the {@link BitmapNetExecutor} reference and the Rust
     * {@code firing_snap_buffer} (backend divergence #5).
     */
    private final long[] fireScanBitmap;

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
    private final boolean hasEnvironmentPlaces;
    private final AtomicBoolean draining = new AtomicBoolean(false);
    private final AtomicBoolean closed = new AtomicBoolean(false);
    private volatile boolean running = false;

    /**
     * Set synchronously by {@code run(...)} before the loop task is submitted, so
     * {@link #awaitTermination(Duration)} can tell "not started yet" from "started, running or
     * finished". {@code running} cannot: it is written by the loop task, which may not have
     * been scheduled yet.
     */
    private volatile boolean started = false;

    /**
     * Requests immediate termination without waiting for in-flight actions. Set by
     * {@link #terminateNow()} from a foreign thread and read in the loop condition; leaves
     * {@code running} to the loop's own {@code finally}, so {@code running} stays a truthful
     * "the loop is alive" signal for {@link #marking()}.
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

    /** Optional handler for action failures; null selects the default logging policy. */
    private final ActionFailureHandler uncaughtActionHandler;

    /**
     * Owned snapshot published by the orchestrator for foreign-thread {@link #marking()} reads.
     * Built from the ring buffers when {@link #markingRequestSeq} outpaces {@link #markingServedSeq},
     * and once more (as the final marking) in the loop's {@code finally}. Written only by the
     * orchestrator; {@code volatile} for cross-thread visibility. Foreign threads must read this
     * rather than {@code syncMarkingFromRingBuffers()}, which mutates the shared marking.
     */
    private volatile Marking publishedMarking;

    /** Incremented by a foreign-thread {@link #marking()} to request a fresh {@link #publishedMarking}. */
    private final AtomicLong markingRequestSeq = new AtomicLong();

    /** Highest request sequence the orchestrator has published a snapshot for. */
    private volatile long markingServedSeq = 0;

    /**
     * The orchestrator loop's thread, or {@code null} before it starts and after it finishes.
     * {@code volatile} and published <em>before</em> {@code running = true}, so a foreign
     * {@link #marking()} that observes the loop as live also observes this reference and is
     * routed to the published snapshot rather than into {@code syncMarkingFromRingBuffers}.
     */
    private volatile Thread orchestratorThread;

    private final boolean skipOutputValidation;

    /** Grace band (ms) before a hard deadline ({@code deadline()}/{@code window()}) force-disables. */
    private final long deadlineToleranceMillis;

    private PrecompiledNetExecutor(
        PrecompiledNet program,
        Map<Place<?>, List<Token<?>>> initialTokens,
        EventStore eventStore,
        ExecutorService executor,
        Set<EnvironmentPlace<?>> environmentPlaces,
        ExecutionContextProvider executionContextProvider,
        boolean skipOutputValidation,
        long deadlineToleranceMillis,
        ActionFailureHandler uncaughtActionHandler,
        boolean ownsExecutor
    ) {
        this.program = program;
        this.eventStore = eventStore;
        this.executor = executor;
        this.ownsExecutor = ownsExecutor;
        this.uncaughtActionHandler = uncaughtActionHandler;
        this.environmentPlaces = environmentPlaces;
        this.hasEnvironmentPlaces = !environmentPlaces.isEmpty();
        this.executionContextProvider = executionContextProvider;
        this.skipOutputValidation = skipOutputValidation;
        this.deadlineToleranceMillis = deadlineToleranceMillis;
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

        // Load initial tokens into ring buffers; tokens for places the program does not
        // know are retained in the side map (CORE-072 AC3), never dropped.
        for (var entry : initialTokens.entrySet()) {
            Place<?> place = entry.getKey();
            Integer pid = program.placeIndex.get(place);
            if (pid == null) {
                for (Token<?> token : entry.getValue()) {
                    addExtraToken(place, token);
                    warnUnknownPlace(place, "");
                }
                continue;
            }
            for (Token<?> token : entry.getValue()) {
                ringAddLast(pid, token);
            }
        }

        // Initialize marking bitmap
        int wordCount = program.wordCount;
        this.markingBitmap = new long[wordCount];
        this.fireScanBitmap = new long[wordCount];

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
            var ctx = new TransitionContext(
                t, new TokenInput(program.inputPlaceCount[tid]), new TokenOutput());
            // Install the ν-name minter once per pooled context (NU-010, NU-030):
            // monotonic across the run, instance-prefixed via the transition name.
            final String freshNameBase = t.name();
            ctx.setFreshNameSupplier(() ->
                new NameId(freshNameBase + "#" + freshNameCounter.getAndIncrement()));
            contextPool[tid] = ctx;
        }

        // In-flight tracking
        this.inFlightFutures = new CompletableFuture[program.transitionCount];
        this.inFlightContexts = new TransitionContext[program.transitionCount];
        this.inFlightConsumed = new List[program.transitionCount];
        this.inFlightStartNanos = new long[program.transitionCount];

        // Reset detection
        this.pendingResetWords = new long[program.wordCount];

        initMatchCaches();
    }

    /**
     * Builds a fresh, unpooled context for one firing of {@code tid}.
     *
     * <p>Used only for transitions carrying an {@code Out.Timeout}, whose firings can outlive
     * the executor's interest in them. Identical in construction to the pooled entry,
     * including the ν-name minter.
     */
    private TransitionContext newFiringContext(int tid, Transition t) {
        var ctx = new TransitionContext(
            t, new TokenInput(program.inputPlaceCount[tid]), new TokenOutput());
        final String freshNameBase = t.name();
        ctx.setFreshNameSupplier(() ->
            new NameId(freshNameBase + "#" + freshNameCounter.getAndIncrement()));
        return ctx;
    }

    /**
     * Builds the ν-net incremental match caches (NU-020). A matched join is
     * fast-path eligible only when every correlated input is One/Exactly, is
     * consumed by no other transition, and is never reset — so tokens enter a
     * correlated input only via produce/inject (mirrored by {@code add}) and
     * leave only via this join's matched consume (mirrored by {@code consume}),
     * and the cache can never desync. Mirrors the Rust/TS backends.
     */
    @SuppressWarnings("unchecked")
    private void initMatchCaches() {
        int tc = program.transitionCount;
        int pc = program.placeCount;
        matchCaches = new MatchEngine.IncrementalMatcher[tc];
        placeMatchTargets = new java.util.List[pc];
        for (int pid = 0; pid < pc; pid++) {
            placeMatchTargets[pid] = new ArrayList<>();
        }

        boolean anyMatch = false;
        for (int tid = 0; tid < tc; tid++) {
            if (program.hasMatch[tid]) { anyMatch = true; break; }
        }
        if (!anyMatch) return;

        List<Integer>[] inputConsumers = new java.util.List[pc];
        boolean[] resetTarget = new boolean[pc];
        for (int pid = 0; pid < pc; pid++) {
            inputConsumers[pid] = new ArrayList<>();
        }
        for (int tid = 0; tid < tc; tid++) {
            Transition t = program.transitionsById[tid];
            for (var in : t.inputSpecs()) {
                inputConsumers[program.placeIndex.get(in.place())].add(tid);
            }
            for (var rs : t.resets()) {
                resetTarget[program.placeIndex.get(rs.place())] = true;
            }
        }

        for (int tid = 0; tid < tc; tid++) {
            if (!program.hasMatch[tid]) continue;
            Transition t = program.transitionsById[tid];
            MatchSpec ms = t.matchSpec();
            if (ms == null) continue;

            int[] requireds = new int[ms.keys().size()];
            boolean eligible = true;
            int ki = 0;
            for (var key : ms.keys()) {
                Integer pidObj = program.placeIndex.get(key.place());
                if (pidObj == null) { eligible = false; break; }
                int pid = pidObj;
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
                int pid = program.placeIndex.get(key.place());
                int count = tokenCounts[pid];
                int offset = placeOffset[pid];
                int head = ringHead[pid];
                int cap = ringCapacity[pid];
                for (int i = 0; i < count; i++) {
                    Token<?> token = (Token<?>) tokenPool[offset + (head + i) % cap];
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

    /** Mirror a token added to correlated input {@code pid} into every fast-path matcher. */
    private void cacheAddToken(int pid, Token<?> token) {
        List<int[]> targets = placeMatchTargets[pid];
        if (targets.isEmpty()) return;
        for (int[] tgt : targets) {
            int tid = tgt[0];
            int keyIdx = tgt[1];
            MatchEngine.IncrementalMatcher cache = matchCaches[tid];
            if (cache == null) continue;
            var key = program.transitionsById[tid].matchSpec().keys().get(keyIdx);
            NameId name = key.extract(token.value());
            if (name != null) {
                cache.add(keyIdx, name, token.createdAt().toEpochMilli());
            }
        }
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

    /**
     * Removes the first (oldest) ring token at {@code pid} satisfying
     * {@code pred}, compacting the ring (preserves FIFO order). Mirrors the
     * Rust {@code ring_remove_matching}. Returns {@code null} on no match.
     */
    private Token<?> ringRemoveMatching(int pid, Predicate<Token<?>> pred) {
        int count = tokenCounts[pid];
        if (count == 0) return null;
        int offset = placeOffset[pid];
        int head = ringHead[pid];
        int cap = ringCapacity[pid];
        for (int i = 0; i < count; i++) {
            int idx = offset + (head + i) % cap;
            Token<?> token = (Token<?>) tokenPool[idx];
            if (token != null && pred.test(token)) {
                // Close the gap from whichever end is nearer, so removing the
                // ring head (the common ν-net case — the matched token is the
                // oldest, hence at the front with distinct timestamps) is O(1)
                // rather than shifting the whole ring. Keeps a draining matched
                // join linear instead of quadratic.
                if (i <= count - 1 - i) {
                    // Nearer the head: slide the i preceding tokens forward, advance head.
                    for (int j = i; j > 0; j--) {
                        tokenPool[offset + (head + j) % cap] = tokenPool[offset + (head + j - 1) % cap];
                    }
                    tokenPool[offset + head % cap] = null;
                    ringHead[pid] = (head + 1) % cap;
                } else {
                    // Nearer the tail: slide the trailing tokens back, retract tail.
                    for (int j = i; j < count - 1; j++) {
                        tokenPool[offset + (head + j) % cap] = tokenPool[offset + (head + j + 1) % cap];
                    }
                    tokenPool[offset + (head + count - 1) % cap] = null;
                    ringTail[pid] = (ringTail[pid] == 0) ? cap - 1 : ringTail[pid] - 1;
                }
                tokenCounts[pid]--;
                return token;
            }
        }
        return null;
    }

    /** Counts ring tokens at {@code pid} satisfying {@code pred}. */
    private int countMatchingInRing(int pid, Predicate<Token<?>> pred) {
        int count = tokenCounts[pid];
        int offset = placeOffset[pid];
        int head = ringHead[pid];
        int cap = ringCapacity[pid];
        int matched = 0;
        for (int i = 0; i < count; i++) {
            Token<?> token = (Token<?>) tokenPool[offset + (head + i) % cap];
            if (token != null && pred.test(token)) matched++;
        }
        return matched;
    }

    // ==================== ν-net join (NU-020) ====================

    /**
     * Finds the correlation name satisfying this transition's {@link MatchSpec},
     * or {@code null} if the join is not currently enabled (spec NU-020). Builds
     * a per-correlated-input name index over the ring buffers and defers
     * selection + tie-break to the shared {@link MatchEngine}.
     */
    private NameId findMatchBinding(int tid) {
        Transition t = program.transitionsById[tid];
        MatchSpec ms = t.matchSpec();
        if (ms == null) return null;
        var perPlace = new ArrayList<Map<NameId, MatchEngine.NameStat>>(ms.keys().size());
        int[] requireds = new int[ms.keys().size()];
        int k = 0;
        for (var key : ms.keys()) {
            int pid = program.placeIndex.get(key.place());
            var index = new HashMap<NameId, MatchEngine.NameStat>();
            int count = tokenCounts[pid];
            int offset = placeOffset[pid];
            int head = ringHead[pid];
            int cap = ringCapacity[pid];
            for (int i = 0; i < count; i++) {
                Token<?> token = (Token<?>) tokenPool[offset + (head + i) % cap];
                NameId name = key.extract(token.value());
                if (name == null) continue;
                long ts = token.createdAt().toEpochMilli();
                var prev = index.get(name);
                index.put(name, prev == null
                    ? new MatchEngine.NameStat(1, ts)
                    : new MatchEngine.NameStat(prev.count() + 1, Math.min(prev.minCreatedAt(), ts)));
            }
            perPlace.add(index);
            requireds[k++] = MatchEngine.requiredFor(t, key.place());
        }
        return MatchEngine.selectMatchName(perPlace, requireds);
    }

    /**
     * Consumes the name-matched tokens for a ν-net join (NU-020): correlated
     * inputs take tokens whose projected name equals the chosen binding; other
     * inputs consume FIFO. Reset arcs are NOT drained here — they are compiled
     * into the RESET opcode tail, which {@link #fireTransition} runs after the
     * read-arc peeks (EXEC-013 AC4).
     */
    @SuppressWarnings("unchecked")
    private void consumeMatched(int tid, Transition t, TokenInput inputs, List<Token<?>> consumed) {
        MatchSpec ms = t.matchSpec();
        MatchEngine.IncrementalMatcher cache = matchCaches[tid];
        NameId chosen = cache != null ? cache.best() : findMatchBinding(tid);
        // Mirror the matched consume into the fast-path matcher (the only path by
        // which tokens leave this join's correlated inputs) before the rings change.
        if (cache != null && chosen != null) {
            cache.consume(chosen);
        }

        for (var in : t.inputSpecs()) {
            Place<Object> place = (Place<Object>) in.place();
            int pid = program.placeIndex.get(in.place());
            Function<Object, NameId> keyFn = ms.keyFor(in.place());

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
                    default -> countMatchingInRing(pid, pred);
                };
                for (int i = 0; i < toConsume; i++) {
                    Token<?> token = ringRemoveMatching(pid, pred);
                    if (token == null) break;
                    if (consumed != null) consumed.add(token);
                    inputs.add(place, (Token<Object>) token);
                    if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
                        Instant.now(), in.place().name(), token));
                }
            } else {
                int toConsume = switch (in) {
                    case Arc.In.One _ -> 1;
                    case Arc.In.Exactly e -> e.count();
                    default -> tokenCounts[pid];
                };
                for (int i = 0; i < toConsume; i++) {
                    Token<?> token = ringRemoveFirst(pid);
                    if (consumed != null) consumed.add(token);
                    inputs.add(place, (Token<Object>) token);
                    if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
                        Instant.now(), in.place().name(), token));
                }
            }
        }

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

    /**
     * Sorts priority level {@code pi}'s occupied slice {@code [0, size)} in place by
     * ({@code enabledAtNanos[tid]} ASC, tid ASC).
     *
     * <p><b>Invariant: {@code readyQueueHead[pi] == 0}.</b> The slice is contiguous only
     * before the ring wraps, so this is valid solely right after {@link #fireReadyGeneral}'s
     * populate scan, which starts from freshly cleared queues.
     *
     * <p>Insertion sort, boxing-free: O(k) on the already-tid-ordered common case, O(k²)
     * worst case, where k is the level's ready count (at most transitionCount).
     */
    private void sortReadySliceByEnablement(int pi) {
        assert readyQueueHead[pi] == 0 : "ready slice must be unwrapped to sort in place";
        int size = readyQueueSize[pi];
        if (size <= 1) return;
        int[] queue = readyQueues[pi];
        for (int i = 1; i < size; i++) {
            int tid = queue[i];
            long key = enabledAtNanos[tid];
            int j = i - 1;
            while (j >= 0
                   && (enabledAtNanos[queue[j]] > key
                       || (enabledAtNanos[queue[j]] == key && queue[j] > tid))) {
                queue[j + 1] = queue[j];
                j--;
            }
            queue[j + 1] = tid;
        }
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
        private boolean skipOutputValidation = false;
        private ExecutionContextProvider executionContextProvider = ExecutionContextProvider.NOOP;
        private long deadlineToleranceMillis = ExecutorSupport.DEADLINE_TOLERANCE_MS;
        private ActionFailureHandler uncaughtActionHandler = null;

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
         * Skip output validation for trusted transition actions.
         * When enabled, the executor does not verify that transition outputs
         * match their declared output specs. This eliminates significant overhead
         * for high-throughput workloads where actions are known to be correct.
         */
        public Builder skipOutputValidation(boolean skip) {
            this.skipOutputValidation = skip;
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

        public PrecompiledNetExecutor build() {
            var prog = program != null ? program : PrecompiledNet.compile(net);
            ExecutorService exec = executor != null
                ? executor
                : Executors.newVirtualThreadPerTaskExecutor();
            return new PrecompiledNetExecutor(
                prog, initialTokens, eventStore, exec,
                environmentPlaces, executionContextProvider,
                skipOutputValidation, deadlineToleranceMillis, uncaughtActionHandler,
                executor == null
            );
        }
    }

    // ==================== PetriNetExecutor Interface ====================

    @Override
    public Marking run() {
        started = true;
        return executeLoop();
    }

    @Override
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

    @Override
    public <T> void injectAsync(EnvironmentPlace<T> place, Token<T> token) {
        inject(place, token);
    }

    /**
     * Returns the current marking.
     *
     * <p>From the orchestrator thread, or once the loop has stopped, this rebuilds and returns
     * the executor's own {@code Marking} — exact and allocation-free. That covers almost every
     * call, including the one at the end of {@code run()}.
     *
     * <p><b>From another thread while the loop is running</b> it returns an independent snapshot
     * the orchestrator publishes for it, because the in-place rebuild is not safe to perform
     * concurrently: it clears the shared {@code Marking} and re-reads {@code tokenPool}, an array
     * the orchestrator reassigns whenever a place's ring grows. Doing that from a monitoring
     * thread would corrupt the live net rather than merely observe it.
     *
     * <p>The snapshot is best-effort. The caller flags a request and the orchestrator refreshes
     * the published copy at the next safe point in its loop; while it is inside a long inline
     * action it may not reach that point immediately, so the returned marking can lag. For a view
     * with defined timing, subscribe to {@code MarkingSnapshot} events, which the orchestrator
     * emits from its own thread.
     */
    @Override
    public Marking marking() {
        Thread orch = orchestratorThread;
        Thread self = Thread.currentThread();
        if (orch == self) {
            // The orchestrator itself, mid-run: rebuild and return the exact live marking.
            syncMarkingFromRingBuffers();
            return marking;
        }
        if (orch != null) {
            // Foreign thread, loop running: request a fresh snapshot and wait, bounded. Foreign
            // threads NEVER run syncMarkingFromRingBuffers — it mutates the shared marking.
            Marking snapshot = awaitPublishedSnapshot();
            if (orchestratorThread != null) {
                return snapshot != null ? snapshot : Marking.empty();
            }
            // else: the loop finished while we waited — fall through.
        }
        if (terminated) {
            // Loop stopped: the finally published the exact final snapshot. Foreign threads must
            // not sync the rings post-termination — concurrent readers would race on `marking`.
            Marking published = publishedMarking;
            return published != null ? published : Marking.empty();
        }
        // Never started: this is the sole path touching the rings; sync once.
        syncMarkingFromRingBuffers();
        return marking;
    }

    /**
     * Requests a fresh published snapshot from the orchestrator and waits, bounded, for it.
     * Returns the freshest {@link #publishedMarking} it can; the caller decides how to proceed if
     * the loop ended meanwhile.
     */
    private Marking awaitPublishedSnapshot() {
        long seq = markingRequestSeq.incrementAndGet();
        wakeUp();
        long deadline = System.nanoTime() + ExecutorSupport.MARKING_SNAPSHOT_WAIT_NANOS;
        while (markingServedSeq < seq) {
            if (orchestratorThread == null) return null; // loop finished; caller uses final snapshot
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) break; // best-effort cap: return the last snapshot
            LockSupport.parkNanos(Math.min(remaining, 1_000_000L));
        }
        return publishedMarking;
    }

    /**
     * Refreshes the published snapshot when a foreign thread has asked for one (see
     * {@link #marking()}). Runs only on the orchestrator thread, so rebuilding the shared
     * {@code Marking} from the rings and copying it is race-free.
     */
    private void serviceMarkingRequest() {
        long req = markingRequestSeq.get();
        if (req != markingServedSeq) {
            syncMarkingFromRingBuffers();
            publishedMarking = marking.copy();
            markingServedSeq = req;
        }
    }

    /**
     * Syncs the Marking instance from ring buffers. Only called when marking()
     * is accessed (end of execution, external inspection with environment places),
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
        // Merge retained tokens for places the program does not know (CORE-072 AC3)
        if (extraTokens != null) {
            for (var entry : extraTokens.entrySet()) {
                Place<Object> place = (Place<Object>) entry.getKey();
                for (Token<?> token : entry.getValue()) {
                    marking.addToken(place, (Token<Object>) token);
                }
            }
        }
    }

    /** Retains a token for a place the compiled program does not know (CORE-072 AC3). */
    private void addExtraToken(Place<?> place, Token<?> token) {
        if (extraTokens == null) extraTokens = new LinkedHashMap<>();
        extraTokens.computeIfAbsent(place, _ -> new ArrayList<>()).add(token);
    }

    /**
     * Reports an unknown place once (CORE-072 AC4), as the EVT-013 log-message event.
     * Retention (AC3) never depends on this: under a disabled store nothing is emitted.
     */
    private void warnUnknownPlace(Place<?> place, String transitionName) {
        if (!eventStoreEnabled) return;
        if (warnedUnknownPlaces == null) warnedUnknownPlaces = new HashSet<>();
        if (!warnedUnknownPlaces.add(place)) return;
        emitEvent(new NetEvent.LogMessage(Instant.now(), transitionName, "libpetri.runtime", "WARN",
            "unknown place '" + place.name() + "': tokens are retained in the marking but inert "
                + "(the net declares no arc on it)", null, null));
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

    // ==================== Execution Loop ====================

    private Marking executeLoop() {
        // Publish an initial snapshot and the thread reference BEFORE running=true, so a foreign
        // marking() that observes the loop as live also observes both (volatile piggyback).
        syncMarkingFromRingBuffers();
        publishedMarking = marking.copy();
        orchestratorThread = Thread.currentThread();
        running = true;
        if (eventStoreEnabled) {
            emitEvent(new NetEvent.ExecutionStarted(
                Instant.now(), netName(), executionId()));
        }

        initializeMarkingBitmap();
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
                if (program.anyDeadlines) enforceDeadlines();

                if (shouldTerminate()) break;

                fireReadyTransitions();

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
                if (eventStoreEnabled) {
                    emitEvent(new NetEvent.ExecutionCompleted(
                        Instant.now(), netName(), executionId(), elapsedDuration()));
                }
            } catch (Throwable emitError) {
                ExecutorSupport.swallowEventStoreFailure("ExecutionCompleted", emitError);
            } finally {
                // Rebuild the exact final marking on this (the loop) thread, then publish an owned
                // copy for post-termination foreign readers before nulling orchestratorThread —
                // after which no thread runs syncMarkingFromRingBuffers, so `marking` is stable.
                syncMarkingFromRingBuffers();
                publishedMarking = marking.copy();
                terminatedFuture.complete(marking);
                orchestratorThread = null; // last
            }
        }

        return marking;
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
        if (closed.get()) {
            // ENV-013: immediate close — wait for in-flight actions to complete
            return inFlightCount == 0 && completionQueue.isEmpty();
        }
        if (hasEnvironmentPlaces) {
            return draining.get()
                && enabledTransitionCount == 0
                && inFlightCount == 0
                && completionQueue.isEmpty();
        }
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
                boolean canNow = canEnable(tid, markingBitmap);

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

    /**
     * Enablement check combining bitmap masks and cardinality checks. The presence bitmap is
     * a parameter so the firing pass can recheck against {@link #fireScanBitmap} (same-cycle
     * deposits invisible, divergence #5) while dirty re-evaluation uses the live
     * {@link #markingBitmap}; cardinality and ν-binding always consult live token state,
     * matching the {@link BitmapNetExecutor} reference.
     */
    private boolean canEnable(int tid, long[] markingSnap) {
        if (!program.canEnableBitmap(tid, markingSnap)) return false;

        var cardCheck = program.cardinalityChecks[tid];
        if (cardCheck != null) {
            for (int i = 0; i < cardCheck.placeIds().length; i++) {
                int pid = cardCheck.placeIds()[i];
                int required = cardCheck.requiredCounts()[i];
                if (tokenCounts[pid] < required) return false;
            }
        }

        // ν-net join: a correlation name must satisfy every matched input (NU-020).
        // Fast-path transitions read the maintained matcher (O(1)); the rest
        // rebuild the index (O(n)). Gated on the flat flag so non-ν transitions
        // skip this entirely.
        if (program.hasMatch[tid]) {
            MatchEngine.IncrementalMatcher cache = matchCaches[tid];
            boolean noBinding = cache != null ? cache.best() == null : findMatchBinding(tid) == null;
            if (noBinding) {
                return false;
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
                    // Exact timing is enforced softly: an exact transition fires at the first
                    // opportunity at/after its target (see fireReadyGeneral's earliest gate) and is
                    // never force-disabled, so the executor cannot reap it for waking a hair late
                    // (TIME-006). Only hard deadlines (deadline()/window()) are enforced here.
                    if (program.isExact[tid]) continue;

                    long enabledNanos = enabledAtNanos[tid];
                    long elapsedMillis = (nowNanos - enabledNanos) / 1_000_000;
                    long latestMillis = program.latestMillis[tid];

                    if (elapsedMillis > latestMillis + deadlineToleranceMillis) {
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
        if (enabledTransitionCount == 0) return;
        // Firing snapshot: rechecks below must not see same-cycle deposits (divergence #5).
        System.arraycopy(markingBitmap, 0, fireScanBitmap, 0, markingBitmap.length);
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

                    if (canEnable(tid, fireScanBitmap)) {
                        fireTransitionGuarded(tid);
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
        boolean anyReady = false;
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
                        anyReady = true;
                    }
                }
            }
        }
        if (!anyReady) return;

        // Firing snapshot: rechecks below must not see same-cycle deposits (divergence #5).
        System.arraycopy(markingBitmap, 0, fireScanBitmap, 0, markingBitmap.length);

        // Ready order within a level: enablement time ASC, tid tie-break
        // (EXEC-002 AC3/AC4, CONC-023 AC4).
        for (int pi = 0; pi < program.distinctPriorityCount; pi++) {
            sortReadySliceByEnablement(pi);
        }

        // Fire from highest priority queue first
        for (int pi = 0; pi < program.distinctPriorityCount; pi++) {
            while (readyQueueSize[pi] > 0) {
                int tid = readyQueuePop(pi);
                if (!isEnabled(tid) || isInFlight(tid)) continue;

                if (canEnable(tid, fireScanBitmap)) {
                    fireTransitionGuarded(tid);
                } else {
                    clearEnabledBit(tid);
                    enabledTransitionCount--;
                    enabledAtNanos[tid] = Long.MIN_VALUE;
                }
            }
        }
    }

    // ==================== Consume Operation Execution ====================

    /**
     * Fires a transition, containing any failure to that one firing.
     *
     * <p>Without this boundary an unchecked throw from a firing — an action throwing before it
     * returns its stage, a user {@link org.libpetri.event.EventStore} throwing from
     * {@code append}, a token-type violation — unwinds out of the orchestrator loop and kills
     * the executor. The transition is instead failed and marked dirty for re-evaluation, which
     * is the same treatment an asynchronously-reported failure already gets.
     *
     * <p>{@code fireTransition} drains tokens from the rings before it reconciles the presence
     * bitmap, so a throw <em>inside</em> that window (a hostile EventStore on {@code TokenRemoved})
     * would leave bits asserting tokens that are gone. The recovery re-runs
     * {@link #updateBitmapAfterConsumption} against the true {@code tokenCounts} so re-evaluation
     * cannot fire against a phantom. A fatal {@link Error} is repaired the same way but rethrown,
     * terminating the run rather than being retried.
     */
    private void fireTransitionGuarded(int tid) {
        try {
            fireTransition(tid);
        } catch (Throwable e) {
            Transition t = program.transitionsById[tid];
            if (isEnabled(tid)) {
                clearEnabledBit(tid);
                enabledTransitionCount--;
                enabledAtNanos[tid] = Long.MIN_VALUE;
            }
            if (isInFlight(tid)) {
                inFlightFutures[tid] = null;
                inFlightContexts[tid] = null;
                inFlightConsumed[tid] = null;
                inFlightCount--;
                clearInFlightBit(tid);
            }
            updateBitmapAfterConsumption(tid);
            // consumeMatched mirrors the matched consume into the ν fast-path matcher
            // (cache.consume) BEFORE the tokens leave the rings, so a throw in that window (a
            // hostile EventStore on TokenRemoved, a throwing keyFn) leaves the matcher believing
            // tokens are gone that remain. Reconciling tokenCounts is not enough — the matcher is
            // authoritative for ν enablement. Drop it so the next canEnable/fire rebuilds the
            // binding from the live rings via findMatchBinding; the O(1) fast path is forfeited
            // only for this transition, only after a failure.
            matchCaches[tid] = null;
            ExecutorSupport.rethrowIfFatal(e);
            handleTransitionFailure(t, e);
            markTransitionDirty(tid);
        }
    }

    @SuppressWarnings("unchecked")
    private void fireTransition(int tid) {
        Transition t = program.transitionsById[tid];

        // Pooled contexts are reused across firings of the same tid, which is only safe
        // while a firing cannot outlive the executor's interest in it. An Out.Timeout
        // firing can: the timeout deposits its branch and clears the in-flight bit, so this
        // tid may re-fire in the very same loop iteration while the abandoned action still
        // holds this context and keeps writing to it. A pooled context would then be
        // cleared underneath that action and its late writes would land in the next
        // firing's output. Timeout transitions therefore get a fresh context per firing;
        // everything else keeps the zero-allocation fast path.
        TransitionContext context = t.hasActionTimeout()
            ? newFiringContext(tid, t)
            : contextPool[tid];
        TokenInput inputs = context.rawInput();
        inputs.clear();
        TokenOutput output = context.rawOutput();
        output.clear();

        List<Token<?>> consumed = trackConsumed ? new ArrayList<>() : null;

        // In-firing order (EXEC-013 AC4, matching BitmapNetExecutor): inputs → read peeks
        // → resets, split at resetOpsStart, so read(p) + reset(p) sees the pre-reset token.
        // ν-net joins (NU-020) bypass the input opcodes but share the RESET tail.
        int resetStart = program.resetOpsStart[tid];
        if (t.matchSpec() != null) {
            consumeMatched(tid, t, inputs, consumed);
        } else {
            executeConsumeOps(tid, 0, resetStart, inputs, consumed);
        }

        // Execute read program (post-input, pre-reset marking)
        int[] readProg = program.readOps[tid];
        for (int rpid : readProg) {
            Token<?> token = ringPeekFirst(rpid);
            if (token != null) {
                inputs.add((Place<Object>) program.placesById[rpid], (Token<Object>) token);
            }
        }

        // Drain reset arcs (empty segment for transitions without resets)
        executeConsumeOps(tid, resetStart, program.consumeOps[tid].length, inputs, consumed);

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
                      () -> ExecutorSupport.executeAction(t, context)))
            : ExecutorSupport.executeAction(t, context);

        // Handle Out.Timeout
        if (t.hasActionTimeout()) {
            transitionFuture = ExecutorSupport.withActionTimeout(
                t, context, transitionFuture,
                () -> { if (eventStoreEnabled) emitEvent(new NetEvent.ActionTimedOut(
                    Instant.now(), t.name(), t.actionTimeout().after())); });
        }

        // Clear enabled status
        clearEnabledBit(tid);
        enabledTransitionCount--;
        enabledAtNanos[tid] = Long.MIN_VALUE;

        // Sync fast path — pooled context reused, no allocation
        if (!t.hasActionTimeout() && transitionFuture.isDone()) {
            processSyncOutput(tid, transitionFuture, context, consumed);
        } else {
            // Async path. The pooled context is safe here: a non-timeout transition cannot
            // re-fire while in-flight, and a timeout transition was given a fresh context above
            // (see newFiringContext) precisely because that invariant does not hold once the
            // timeout can clear its in-flight bit and let the same tid re-fire in this iteration.
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

    /**
     * Runs the opcode segment {@code [from, to)} of {@code consumeOps[tid]}: once for the
     * inputs, once for the RESET tail — see {@link PrecompiledNet#resetOpsStart} (EXEC-013 AC4).
     */
    @SuppressWarnings("unchecked")
    private void executeConsumeOps(int tid, int from, int to,
                                   TokenInput inputs, List<Token<?>> consumed) {
        int[] prog = program.consumeOps[tid];
        int pc = from;
        while (pc < to) {
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
                case PrecompiledNet.CONSUME_ALL, PrecompiledNet.CONSUME_ATLEAST -> {
                    int pid = prog[pc++];
                    if (opcode == PrecompiledNet.CONSUME_ATLEAST) {
                        pc++; // skip minimum (already verified during enablement)
                    }
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
    }

    private void updateBitmapAfterConsumption(int tid) {
        int[] pids = program.consumptionPlaceIds[tid];
        for (int pid : pids) {
            if (tokenCounts[pid] == 0) {
                clearMarkingBit(pid);
            }
            markDirty(pid);
        }
        // Refresh the firing snapshot so the next intra-pass recheck sees the live marking
        // after this consumption — but not deposits that land later in the same cycle
        // (EXEC-001 step order; EXEC-003 consumption visibility; divergence #5).
        System.arraycopy(markingBitmap, 0, fireScanBitmap, 0, markingBitmap.length);
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

            // Defensive copy: a misbehaving action that kept a reference cannot mutate the
            // list mid-iteration. Each entry is added, bit-set and marked dirty together.
            var entries = List.copyOf(outputs.entries());
            List<Token<?>> produced = eventStoreEnabled ? new ArrayList<>(entries.size()) : null;
            for (var entry : entries) {
                var token = entry.token();
                produceToken(entry.place(), token, t.name());
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
        } catch (RuntimeException e) {
            // See processCompletedTransitions: CancellationException arrives unwrapped.
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

            // Validate BEFORE touching bookkeeping. A stale entry — a firing whose in-flight
            // state was already torn down, e.g. by the failure boundary in
            // fireTransitionGuarded — would otherwise decrement inFlightCount a second time,
            // driving it negative and making isQuiescent() lie.
            if (future == null) continue;

            TransitionContext context = inFlightContexts[tid];
            long flightStart = inFlightStartNanos[tid];

            // Clear in-flight state
            inFlightFutures[tid] = null;
            inFlightContexts[tid] = null;
            inFlightConsumed[tid] = null;
            inFlightCount--;
            clearInFlightBit(tid);

            Transition t = program.transitionsById[tid];
            try {
                future.join();

                TokenOutput outputs = context.rawOutput();
                validateOutput(tid, t, outputs);

                // Defensive copy: a misbehaving action that kept a reference cannot mutate the
                // list mid-iteration. Each entry is added, bit-set and marked dirty together.
                var entries = List.copyOf(outputs.entries());
                List<Token<?>> produced = eventStoreEnabled ? new ArrayList<>(entries.size()) : null;
                for (var entry : entries) {
                    var token = entry.token();
                    produceToken(entry.place(), token, t.name());
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
        // Emit is guarded: a throwing EventStore here must not escape the failure handler nor
        // rob the handler of its callback. `emitted` reflects whether the event was actually
        // appended, so the default policy logs exactly when no store recorded the failure.
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

    // ==================== External Events ====================

    @SuppressWarnings("unchecked")
    private void processExternalEvents() {
        if (closed.get()) return; // ENV-013: leave queued events for drainPendingExternalEvents()
        ExternalEvent<?> event;
        while ((event = externalEventQueue.poll()) != null) {
            try {
                produceToken(event.place(), event.token(), "");

                if (eventStoreEnabled) emitEvent(new NetEvent.TokenAdded(
                    Instant.now(), event.place().name(), event.token()));
                event.resultFuture().complete(true);
            } catch (Exception e) {
                event.resultFuture().completeExceptionally(e);
            }
        }
    }

    /**
     * Adds a produced or injected token to place storage: the ring pool for compiled places
     * (with presence bit, dirty marking and ν-cache mirror), or the retention side map for a
     * place the program does not know (CORE-072 AC3) — retained in the observable marking,
     * never silently dropped.
     *
     * @param transitionName the producing transition, or {@code ""} at the injection seam
     */
    private void produceToken(Place<?> place, Token<?> token, String transitionName) {
        Integer pid = program.placeIndex.get(place);
        if (pid == null) {
            addExtraToken(place, token);
            warnUnknownPlace(place, transitionName);
            return;
        }
        cacheAddToken(pid, token);
        ringAddLast(pid, token);
        setMarkingBit(pid);
        markDirty(pid);
    }

    private void drainPendingExternalEvents() {
        ExecutorSupport.drainPendingExternalEvents(externalEventQueue);
    }

    // ==================== Await Work ====================

    private void awaitWork() {
        // When closed, ignore external queue — processExternalEvents() won't consume it,
        // drainPendingExternalEvents() handles it after the loop exits.
        if (!completionQueue.isEmpty() || (!closed.get() && !externalEventQueue.isEmpty())) return;

        if (inFlightCount > 0) {
            awaitCompletionOrEvent();
        } else if (enabledTransitionCount > 0 || (hasEnvironmentPlaces && !draining.get())) {
            // Wait for timed transitions to become ready, or for external events
            awaitExternalEvent();
        }
    }

    private void awaitCompletionOrEvent() {
        // Check if any in-flight is already done
        for (int tid = 0; tid < program.transitionCount; tid++) {
            if (inFlightFutures[tid] != null && inFlightFutures[tid].isDone()) return;
        }
        if (!completionQueue.isEmpty() || (!closed.get() && !externalEventQueue.isEmpty())) return;

        if (inFlightCount == 0) return;

        // A completing action does `completionQueue.offer(tid); wakeUp();`, so the semaphore
        // is the wake-up signal and the queue is the durable record. Composing a
        // CompletableFuture.anyOf over every in-flight future once per poll cycle — as this
        // used to — allocated a fresh dependent node on each of those futures every 1-50ms
        // and then abandoned it, which on a long-running action accumulates for the lifetime
        // of the call. The loop below observes exactly the same events.
        while (true) {
            long pollMs = program.allImmediate ? awaitPollMillis
                : Math.max(1, Math.min(awaitPollMillis, nanosUntilNextTimedTransition() / 1_000_000));
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
            if (!program.allImmediate && nanosUntilNextTimedTransition() <= 0) return;
        }
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
                long word = enabledBitmap[w] & program.timedMask[w]; // only check timed transitions
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
                // null for a place the program does not know (retained per CORE-072 AC3)
                Integer epid = program.placeIndex.get(entry.place());
                if (epid != null && epid == simplePid) return;
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

    @Override
    public void awaitPollMillisForTesting(long millis) {
        this.awaitPollMillis = millis;
    }
}
