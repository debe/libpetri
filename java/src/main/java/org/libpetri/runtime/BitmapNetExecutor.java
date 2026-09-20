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
 * <p>Replaces the O(n²) full-scan enablement check of a naive interpreter with:
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
 * @see PrecompiledNetExecutor
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

    /**
     * Post-consumption, pre-deposit presence snapshot used for intra-pass firing rechecks.
     *
     * <p>Outputs deposit in loop step 1 and firing is step 5 (EXEC-001), so tokens a
     * same-cycle sync action produces must be <em>invisible</em> to the recheck of
     * subsequent ready transitions in the same firing pass; consumption, by contrast,
     * must be visible (losers are disabled by consumption, EXEC-003 AC3). Copied from
     * {@link #markingBitmap} once per pass by {@link #beginFiringPass()}; after that it
     * is only ever <em>cleared</em>, one place at a time, by
     * {@link #updateBitmapAfterConsumption}. Nothing sets a bit here mid-pass — a
     * wholesale refresh would republish deposits from earlier firings in the same pass.
     * Mirrors the Rust reference's {@code firing_snap_buffer} (backend divergence #5).
     */
    private final long[] fireScanBitmap;

    /**
     * Tokens deposited into each place since the ready set was collected — the count-side
     * twin of {@link #fireScanBitmap}. A cardinality gate or ν-join re-evaluated inside a
     * firing pass judges {@code tokenCount - depositDelta[pid]}, so a same-pass deposit
     * satisfies neither (EXEC-003 AC4). {@link #depositTouched} lists the pids to reset so
     * clearing costs O(deposits), never O(places), and {@link #hasDeposits} keeps a pass
     * with no deposits at one predictable branch.
     */
    private final int[] depositDelta;
    private final int[] depositTouched;
    private int depositTouchedCount;
    private boolean hasDeposits;

    /**
     * Correlated input place ids per matched transition (null for the rest), for the
     * EXEC-003 AC4 deposit check in {@link #canEnable}. Null until {@link #initMatchCaches}
     * finds a ν transition.
     */
    private int[][] matchInputPids;

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
    /**
     * ν-name scope ([NU-011]): the host-pinned one, or {@code null} until the default is drawn
     * by {@link #executionScope()}.
     */
    private volatile String executionScope;

    /**
     * Name of a place the net declares twice under different token types, or {@code null}
     * ([MOD-024]). The name-keyed snapshot form cannot tell such places apart, so
     * {@link #snapshot()} rejects the net on the caller's thread rather than lose tokens.
     */
    private final String ambiguousPlaceName;

    /** Stable per-executor id ([EXEC-041] diagnostics); see {@link #executionId()}. */
    private final String executionId = ExecutorSupport.nextExecutionId();

    /** Set when the wait itself was interrupted, so the finally can report INTERRUPTED. */
    private volatile boolean interruptedDuringWait = false;

    /**
     * An interrupt flag the run found set and took down, to be put back when {@code run()}
     * returns ([EXEC-041] AC#4/AC#5); see {@link #absorbInterruptFlag()}. Orchestrator-only.
     */
    private boolean interruptDeferred;

    /** Why the last run stopped ([EXEC-041] AC#3). */
    private volatile TerminationReason terminationReason = TerminationReason.RUNNING;

    /** Host-supplied clock and cooperative wait, or null for the default sources ([TIME-015]). */
    private final ExecutionEnvironment environment;

    /** Cached so the hosted wait does not allocate a lambda per cycle. */
    private final java.util.function.BooleanSupplier workReady = this::hasHostWork;

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

    /**
     * Transitions whose clock restarts at the next dirty scan (TIME-012). A transition lands
     * here when another transition's firing leaves it disabled in that firing's intermediate
     * marking (after consumption and reset draining, before any output): it counts as newly
     * enabled once the outputs arrive, even when a synchronous action refills the place before
     * a scan could observe the gap. Set by {@link #flagClockRestarts}, consumed and cleared by
     * {@link #updateDirtyTransitions}; {@link #hasRestartPending} lets a scan with nothing
     * flagged skip the clear.
     */
    private final long[] restartPendingBitmap;
    private boolean hasRestartPending;

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
     * Owned snapshot published by the orchestrator for foreign-thread {@link #marking()} and
     * {@link #snapshot()} reads: the marking <b>and</b> the work-in-flight observation taken
     * with it, as one immutable value behind one reference ([ENV-014] AC#5). Two fields would
     * let a caller read the marking of one capture and the flag of the next.
     *
     * <p>Refreshed when {@link #markingRequestSeq} outpaces {@link #markingServedSeq}, so
     * observers never read the live marking and the copy costs nothing when nobody is watching;
     * and once more, as the final pair, in the loop's {@code finally}. Written only by the
     * orchestrator; {@code volatile} for cross-thread visibility.
     */
    private volatile ExecutorSupport.PublishedState published;

    /** Unknown places already reported (CORE-072 AC4) — one diagnostic per place, not per token. */
    private Set<Place<?>> warnedUnknownPlaces;
    /** Transitions already warned for writing several tokens to a place their spec names once (IO-016 AC4). */
    private Set<String> warnedMultiplicity;

    /** Incremented by a foreign-thread {@link #marking()} to request a fresh {@link #published} pair. */
    private final AtomicLong markingRequestSeq = new AtomicLong();

    /** Highest request sequence the orchestrator has published a snapshot for. */
    private volatile long markingServedSeq = 0;

    /**
     * How long a foreign {@code marking()}/{@code snapshot()} waits to be served; see
     * {@link ExecutorSupport#MARKING_SNAPSHOT_WAIT_NANOS}. A field only so a test can reach
     * the cap without holding an action for two seconds.
     */
    private volatile long snapshotWaitNanos = ExecutorSupport.MARKING_SNAPSHOT_WAIT_NANOS;

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
        boolean ownsExecutor,
        ExecutionEnvironment environment,
        String executionScope
    ) {
        this.executionScope = executionScope;
        this.ambiguousPlaceName = compiled.ambiguousPlaceName();
        this.environment = environment;
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
        this.startNanos = clockNanos();

        int wordCount = compiled.wordCount();
        this.markingBitmap = new long[wordCount];
        this.fireScanBitmap = new long[wordCount];
        // One slot per place: recordDeposit pushes a pid only as its delta leaves zero,
        // so a firing pass never outgrows this and never allocates.
        this.depositDelta = new int[compiled.placeCount()];
        this.depositTouched = new int[compiled.placeCount()];

        this.transitionWords = (compiled.transitionCount() + BIT_MASK) >>> WORD_SHIFT;
        this.enabledAtNanos = new long[compiled.transitionCount()];
        this.enabledBitmap = new long[transitionWords];
        this.inFlightBitmap = new long[transitionWords];
        this.dirtyBitmap = new long[transitionWords];
        this.dirtyScanBuffer = new long[transitionWords];
        this.restartPendingBitmap = new long[transitionWords];
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

        // Correlated input pids per matched transition, fast-path eligible or not —
        // read by canEnable's EXEC-003 AC4 deposit check.
        matchInputPids = new int[tc][];
        for (int tid = 0; tid < tc; tid++) {
            MatchSpec ms = compiled.transition(tid).matchSpec();
            if (ms == null) continue;
            int[] pids = new int[ms.keys().size()];
            int i = 0;
            for (var key : ms.keys()) pids[i++] = compiled.placeId(key.place());
            matchInputPids[tid] = pids;
        }

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
        int pid = compiled.placeIdOrMissing(place);
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

    private boolean isRestartPending(int tid) {
        return (restartPendingBitmap[tid >>> WORD_SHIFT] & (1L << (tid & BIT_MASK))) != 0;
    }

    private void setMarkingBit(int pid) {
        markingBitmap[pid >>> WORD_SHIFT] |= 1L << (pid & BIT_MASK);
    }

    private void clearMarkingBit(int pid) {
        markingBitmap[pid >>> WORD_SHIFT] &= ~(1L << (pid & BIT_MASK));
    }

    /** Clears a place's bit in the pre-deposit firing snapshot; nothing ever sets one. */
    private void clearFireScanBit(int pid) {
        fireScanBitmap[pid >>> WORD_SHIFT] &= ~(1L << (pid & BIT_MASK));
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

        private Map<String, List<Token<?>>> restored;

        /**
         * Seeds this executor from a <b>CORE-073</b> snapshot instead of an explicit initial
         * marking — a <i>resume</i>.
         *
         * <p>Place names are resolved against the net's places, so restored tokens are visible
         * to the net's transitions (AC#10). A name the net does not declare is retained rather
         * than dropped ([CORE-072]), so a snapshot survives a round-trip through a net that has
         * since gained or lost a place. Timestamps are carried through unchanged — restoring is
         * the one path where the engine hands back a {@code created_at} it did not choose.
         *
         * <p>A resumed execution's ν-names are scoped ([NU-011]) so they cannot collide with
         * names already in the restored marking; see {@link #executionScope(String)}.
         *
         * <p><b>Cannot be combined with a non-empty initial marking</b> (AC#11). Pass
         * {@code Map.of()} to {@code builder(net, …)} when restoring.
         *
         * <p><b>A net declaring two places with one name cannot be restored into</b>
         * ([MOD-024]): Java tells such places apart by token type, the snapshot form only by
         * name, so which place a name's tokens belong to is not recoverable. {@link #build()}
         * throws {@link IllegalArgumentException} for it, on the caller's thread.
         *
         * @param snapshot the snapshot form: place name to tokens in FIFO order
         * @return this builder
         * @throws IllegalStateException if a non-empty initial marking was also supplied
         */
        public Builder restore(Map<String, List<Token<?>>> snapshot) {
            Objects.requireNonNull(snapshot, "snapshot");
            if (!initialTokens.isEmpty()) {
                throw new IllegalStateException(
                    "restore() and an explicit initial marking cannot both be supplied "
                        + "(CORE-073 AC11). Merging them would invent a state neither caller "
                        + "described, and preferring either would silently discard the other's "
                        + "tokens. Pass Map.of() as the initial marking when restoring.");
            }
            this.restored = snapshot;
            return this;
        }

        /** The initial tokens to seed with: the restored snapshot when one was supplied. */
        private Map<Place<?>, List<Token<?>>> seedTokens() {
            return restored == null ? initialTokens : Marking.resolveSnapshot(restored, net.places());
        }

        private ExecutionEnvironment environment;

        /**
         * Supplies the executor's firing clock, epoch clock and wait ([TIME-015]).
         *
         * <p>Per executor, never per net. Absent this call the executor reads
         * {@link System#nanoTime()} and {@link Instant#now()} directly.
         *
         * @param environment the host environment; must not be null
         * @return this builder
         */
        public Builder environment(ExecutionEnvironment environment) {
            this.environment = Objects.requireNonNull(environment, "environment");
            return this;
        }

        private String executionScope;

        /**
         * Sets the <b>execution scope</b> woven into every ν-name this executor mints
         * (<b>NU-011</b>).
         *
         * <p>Minted names are {@code <transition>#<scope>:<n>}. Restoring a marking
         * ([CORE-073]) begins a <i>new</i> execution whose initial marking already holds names
         * the previous one minted; an executor that counts from zero re-mints those, and
         * because a [NU-020] join correlates on name equality alone the collision surfaces not
         * as an error but as a <b>silent mis-correlation</b> — a restored token merged with an
         * unrelated fresh one.
         *
         * <p><b>Default: a random token</b> — 32 lowercase hex characters, 128 bits, drawn per
         * executor — so the default is resume-safe across processes, which is where a resume
         * usually happens. It is <b>not</b> the {@link #executionId()}: that stays a
         * reproducible process counter ([TIME-015] AC#14), and a counter restarts at 0 in every
         * JVM, so a scope equal to it re-minted a restored marking's names exactly.
         *
         * <p><b>Pin it when a replay must reproduce the exact name sequence</b>: for a fixed
         * scope and firing order the sequence is reproducible ([NU-010] AC#3, scoped per
         * NU-011) — {@code <n>} is a plain per-executor counter from 0 under any scope, and the
         * default's randomness never reaches it. A pinned scope must be <b>fresh per run
         * segment</b>: resuming under the scope the snapshot was minted under collides just as
         * the counter did.
         *
         * <p>Deriving the floor by scanning the restored marking instead would <b>not</b>
         * suffice: a name minted into a token since consumed leaves no trace in the marking
         * while remaining live in host state.
         *
         * @param scope the scope; must be non-empty and must not contain {@code ':'} or
         *              {@code '#'}, the two separators of a minted name. With both banned a
         *              name parses uniquely: the last {@code ':'} splits off the counter, then
         *              the last {@code '#'} before it splits off the scope. Whitespace is
         *              accepted.
         * @return this builder
         * @throws IllegalArgumentException if the scope is null, empty, or contains {@code ':'}
         *                                  or {@code '#'}
         */
        public Builder executionScope(String scope) {
            this.executionScope = org.libpetri.core.internal.ExecutionScopes.requireValid(scope);
            return this;
        }

        public BitmapNetExecutor build() {
            var compiled = compiledNet != null ? compiledNet : CompiledNet.compile(net);
            var seed = seedTokens();
            var marking = Marking.from(seed);
            ExecutorService exec = executor != null
                ? executor
                : Executors.newVirtualThreadPerTaskExecutor();
            var built = new BitmapNetExecutor(
                compiled, marking, eventStore, exec,
                environmentPlaces, executionContextProvider,
                deadlineToleranceMillis, uncaughtActionHandler,
                executor == null, environment, executionScope
            );
            built.warnUnknownInitialPlaces(seed);
            return built;
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
        return inject(place, environment == null ? Token.of(token) : new Token<>(token, clockInstant()));
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

    // ==================== TIME-015: injectable clock ====================

    /**
     * Firing clock ([TIME-015]). Reads {@link System#nanoTime()} directly when no environment
     * was supplied — a predictable branch on a {@code final} field rather than an interface
     * dispatch, so the unused seam costs nothing on a path read every orchestrator cycle.
     */
    private long clockNanos() {
        return environment == null ? System.nanoTime() : environment.nanoTime();
    }

    /** Epoch clock ([TIME-015]): token creation stamps and event timestamps. */
    private Instant clockInstant() {
        return environment == null ? Instant.now() : environment.now();
    }

    /** A collector stamping produced tokens through the epoch clock ([TIME-015]). */
    private TokenOutput newOutput() {
        return environment == null ? new TokenOutput() : new TokenOutput(environment::now);
    }

    /**
     * The signal half of the hosted wait ([TIME-015]): true when a completing action, an
     * injected external event, or a stop has made work available. Cheap, repeatable and
     * time-free, as the contract on {@code ready} requires.
     */
    private boolean hasHostWork() {
        // shouldTerminate() is part of the predicate, not just the queues. Under a host clock
        // wakeUp() is silenced, so a state change that carries no queue entry — drain() setting
        // `draining`, close() setting `closed` — has nothing else to signal the host with, and a
        // wait asked for Long.MAX_VALUE would never be woken by it. shouldTerminate() is a few
        // field reads: cheap, repeatable, side-effect free and time-free, as the contract on
        // `ready` requires. It is false while a draining net still has work, so it cannot spin.
        return stopRequested || shouldTerminate() || !completionQueue.isEmpty()
            || markingRequestSeq.get() != markingServedSeq
            || (!closed.get() && !externalEventQueue.isEmpty());
    }

    /**
     * Releases the internal wake-up signal.
     *
     * <p>Silenced under a host clock ([TIME-015]): the host owns the wait, nothing drains
     * the semaphore, and permits would accumulate for the executor's lifetime.
     *
     * <p>Because it is silenced, {@link #hasHostWork()} is the <b>sole</b> carrier and must
     * observe every state change reachable from here. The six callers publish:
     * {@code stopRequested} ({@code terminateNow}), the external-event queue ({@code inject}),
     * the completion queue (a finishing action), {@code draining} / {@code closed}
     * ({@code drain}, {@code close} — both reached via {@code shouldTerminate()}), and
     * {@code markingRequestSeq} ({@code marking()} from a foreign thread). Adding a caller
     * without adding its state to that predicate reintroduces a wait nothing can wake, under
     * an injected clock only.
     *
     * <p>The cross-thread part of the predicate — both queues, {@code closed} and
     * {@code stopRequested} — reads {@code ConcurrentLinkedQueue},
     * {@link java.util.concurrent.atomic.AtomicBoolean} and {@code volatile} state, so work
     * published by any thread is visible and a host may complete actions on foreign threads.
     * {@code shouldTerminate()} and {@code markingServedSeq} additionally read plain fields;
     * that is safe only because the predicate is invoked from inside the host's wait, i.e. on
     * the orchestrator thread that owns them.
     */
    private void wakeUp() {
        if (environment != null) return;
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
        published = capturePublishedState();
        orchestratorThread = Thread.currentThread();
        running = true;
        // [EXEC-041] AC#4: an interrupt flag already set is host state this run did not set.
        // Take it down before the first action can trip over it; run() puts it back.
        interruptDeferred = false;
        absorbInterruptFlag();
        emitEvent(new NetEvent.ExecutionStarted(
            clockInstant(), compiled.net().name(), executionId()));

        // Initialize bitmap from initial marking
        initializeMarkedBitmap();
        // Mark all transitions dirty for initial enablement check
        markAllDirty();
        emitMarkingSnapshot();

        // The loop body must never leave pending inject() futures uncompleted, even when it
        // exits by exception: those callers are blocked on join() and their tokens have
        // already been consumed. Termination bookkeeping therefore lives in the finally.
        boolean quiesced = false;
        try {
            // NOTE: the thread's interrupt flag is deliberately NOT a loop condition.
            // [EXEC-041] forbids treating ambient host state as a stop request: the flag
            // may be inherited from earlier work on a reused thread, or set by this run's
            // own action code following Java's convention for propagating a caught
            // interrupt — and actions run inline on this very thread. Consulting it here
            // executed zero cycles, or truncated mid-run, and reported success either way.
            // Stopping is stopRequested / close(); an interrupt counts only where a wait that
            // was ENTERED with the flag clear throws it — or, hosted, returns with the flag
            // set. See absorbInterruptFlag() and awaitHostedWork().
            while (running && !stopRequested) {
                processCompletedTransitions();
                processExternalEvents();
                // After the external-events phase, not before it: an inject() the host made
                // before asking is then already IN the marking it gets back, as it is on the
                // Rust/Python executors, whose injects and snapshot requests share one FIFO
                // channel. Serviced first, every inject-then-snapshot came back "not a restore
                // point" and cost the host a retry.
                serviceMarkingRequest();
                updateDirtyTransitions();
                if (hasAnyDeadlines) enforceDeadlines();

                if (shouldTerminate()) {
                    // shouldTerminate() is also true for a close with nothing in flight, so it
                    // cannot itself mean "finished". Record ACTUAL quiescence instead: a close
                    // that arrives while transitions are still enabled truncates the run and
                    // must report CLOSED, not QUIESCENT ([EXEC-041]).
                    quiesced = enabledTransitionCount == 0 && inFlight.isEmpty() && completionQueue.isEmpty();
                    break;
                }

                fireReadyTransitions();

                // Sync fast-path firings set dirty bits that need processing
                // before the orchestrator can sleep — skip awaitWork and re-loop.
                if (hasDirtyBits()) continue;

                awaitWork();
            }
        } finally {
            running = false;
            terminated = true;
            terminationReason = quiesced ? TerminationReason.QUIESCENT
                : interruptedDuringWait ? TerminationReason.INTERRUPTED
                : closed.get() ? TerminationReason.CLOSED
                : TerminationReason.STOPPED;
            drainPendingExternalEvents();

            // Emit failures must not prevent the loop from reporting termination: a throwing
            // EventStore here would otherwise leave terminatedFuture uncompleted and hang
            // awaitTermination forever.
            try {
                emitMarkingSnapshot();
                // An engine diagnostic, so no transition name ([EVT-013]). Emitted ONLY for an
                // interrupt: [EVT-013] AC#5 bars a diagnostic on a caller-requested termination
                // path, and a close() or a run budget is something the caller already knows it
                // asked for. Warning on those would fire on every clean shutdown of a net whose
                // normal ending IS a shutdown — a reactive net with environment places, designed
                // never to quiesce — and a warning that always fires teaches its reader to ignore
                // the level. The queryable terminationReason() carries the distinction either way
                // ([EXEC-041] AC#3); this event is an addition to it, never the only signal.
                if (terminationReason == TerminationReason.INTERRUPTED) {
                    emitEvent(new NetEvent.LogMessage(clockInstant(), null, "libpetri.runtime", "WARN",
                        "Execution stopped before quiescence (INTERRUPTED): the orchestrator's wait "
                            + "was interrupted, so the returned marking is partial, not final "
                            + "(EXEC-041).", null, null));
                }
                emitEvent(new NetEvent.ExecutionCompleted(
                    clockInstant(), compiled.net().name(), executionId(), elapsedDuration()));
            } catch (Throwable emitError) {
                ExecutorSupport.swallowEventStoreFailure("ExecutionCompleted", emitError);
            } finally {
                // The final pair, for every snapshot() after the loop ([ENV-014]): without it
                // a post-run snapshot paired the final marking with whatever flag the last
                // mid-run request happened to publish. True here means the run was truncated
                // with an action abandoned in flight — not a restore point, and it says so.
                // The external queue was drained above: those events were refused, not accepted.
                // No copy: nothing mutates the live marking once the loop has ended, and this
                // is the same instance a post-termination marking() already hands out.
                published = new ExecutorSupport.PublishedState(marking, workInFlight());
                terminatedFuture.complete(marking);
                orchestratorThread = null; // last: post-termination marking() reads are exact
                // [EXEC-041]: hand back the interrupt this run took down or was stopped by.
                // Last, so nothing above — an event store, a future's dependents — runs with
                // the flag set on the run's account.
                if (interruptDeferred) Thread.currentThread().interrupt();
            }
        }

        return marking;
    }

    /** Refreshes the published pair when a foreign thread has asked for one (see {@link #marking()}). */
    private void serviceMarkingRequest() {
        long req = markingRequestSeq.get();
        if (req != markingServedSeq) {
            published = capturePublishedState(); // before the seq: the seq is the barrier
            markingServedSeq = req;
        }
    }

    /**
     * Captures the marking and the work-in-flight observation as <b>one</b> value, so they
     * describe the same instant on the reading side too ([ENV-014] AC#5). Orchestrator thread,
     * or no orchestrator at all.
     *
     * <p>"Work in flight" is an action, or an <b>accepted but un-injected external event</b>:
     * {@code inject} has taken the token but the external-events phase has not run, so it is
     * in the queue and in no place. Either way restoring the marking drops tokens. A closed
     * executor refuses its queue rather than injecting it, so it does not count.
     */
    private ExecutorSupport.PublishedState capturePublishedState() {
        return new ExecutorSupport.PublishedState(marking.copy(),
            workInFlight());
    }

    /**
     * The one work-in-flight expression, for every pair this executor publishes — mid-run,
     * never-started and final alike; see {@link ExecutorSupport#workInFlight}. Once the loop
     * has ended ({@code terminated}) or the executor is closed, a queued event is one that
     * {@code drainPendingExternalEvents()} refuses — {@code inject} answers {@code false} —
     * so it was never accepted and does not count.
     */
    private boolean workInFlight() {
        return ExecutorSupport.workInFlight(!inFlight.isEmpty(), closed.get() || terminated, externalEventQueue);
    }

    /**
     * Takes the thread's interrupt flag down and remembers it, to be restored when
     * {@code run()} returns ([EXEC-041] AC#4/AC#5). Called at loop start, after every inline
     * action returns, and before every wait — including the hosted one ([TIME-015]).
     *
     * <p><b>Why clear rather than ignore.</b> {@code Semaphore.tryAcquire}/{@code acquire}
     * throw at once when the flag is <i>already</i> set on entry, so merely not consulting the
     * flag in the loop condition still truncated every net that waits: a flag left over from
     * earlier work on a reused thread, or set by an action following the
     * catch-and-re-interrupt idiom (actions run inline on this thread), was reported as "raised
     * while waiting". With the flag down on entry, an {@link InterruptedException} from the
     * wait can only be an interrupt that arrived <i>during</i> it — the one case that is a
     * request against this run, and the only one that ends it {@code INTERRUPTED}.
     *
     * <p><b>Consequence.</b> An external interrupt that lands while an inline action is
     * executing is indistinguishable from one the action set itself, so it too is deferred to
     * {@code run()}'s return rather than stopping the run; a net that never waits is therefore
     * not interruptible — stop it with {@code terminateNow()} or {@code close()}. Later
     * actions of the same run do not observe the flag. The hosted wait has its own form of
     * the rule: see {@link #awaitHostedWork}.
     */
    private void absorbInterruptFlag() {
        if (Thread.interrupted()) interruptDeferred = true;
    }

    /**
     * The [TIME-015] hosted wait, under the same interrupt rule as the built-in ones
     * ([EXEC-041]). {@code ExecutionEnvironment.awaitWork} cannot throw
     * {@link InterruptedException}; a host that blocks interruptibly catches it, restores the
     * flag and returns. Every caller has just run {@link #absorbInterruptFlag()}, so the wait
     * is <b>entered with the flag clear</b>, and a flag found set when it returns was set
     * <i>during</i> the wait — exactly what an {@code InterruptedException} from a built-in
     * wait entered clear means. It ends the run {@code INTERRUPTED} the same way; otherwise
     * an executor under an injected clock could not be interrupted at all.
     *
     * <p><b>Consequence.</b> Whatever runs on this thread <i>inside</i> the host's wait — a
     * cooperative host completing an action, a callback — and sets the flag is
     * indistinguishable from an external interrupt there, and ends the run too. Inside an
     * action the same ambiguity is resolved the other way (deferred), because actions are
     * this run's own code and a wait is not.
     */
    private void awaitHostedWork(long delayNanos) {
        environment.awaitWork(workReady, delayNanos);
        if (Thread.interrupted()) {
            interruptDeferred = true;
            interruptedDuringWait = true;
            stopRequested = true;
        }
    }

    /** The ν-name scope, drawing the random default on first use ([NU-011]). */
    private String executionScope() {
        String scope = executionScope;
        if (scope == null) {
            // Lazy: most nets mint no ν-name, and the draw is a SecureRandom read. Locked
            // because an action may mint from a continuation on any thread.
            synchronized (freshNameCounter) {
                scope = executionScope;
                if (scope == null) {
                    executionScope = scope = org.libpetri.core.internal.ExecutionScopes.random();
                }
            }
        }
        return scope;
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
        long nowNanos = clockNanos();

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
                boolean canNow = canEnable(tid, markingBitmap, false);

                if (canNow && !wasEnabled) {
                    setEnabledBit(tid);
                    enabledTransitionCount++;
                    enabledAtNanos[tid] = nowNanos;
                    if (eventStoreEnabled) emitEvent(new NetEvent.TransitionEnabled(
                        clockInstant(), compiled.transition(tid).name()));
                } else if (!canNow && wasEnabled) {
                    clearEnabledBit(tid);
                    enabledTransitionCount--;
                    enabledAtNanos[tid] = Long.MIN_VALUE;
                } else if (canNow && wasEnabled && isRestartPending(tid)) {
                    // Disabled by another firing's intermediate marking and refilled before
                    // this scan: re-enabled, so a fresh clock (TIME-012).
                    enabledAtNanos[tid] = nowNanos;
                    if (eventStoreEnabled) emitEvent(new NetEvent.TransitionClockRestarted(
                        clockInstant(), compiled.transition(tid).name()));
                }
            }
        }

        if (hasRestartPending) {
            Arrays.fill(restartPendingBitmap, 0);
            hasRestartPending = false;
        }
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
     * Enablement check combining bitmap masks and cardinality checks. {@code markingSnap}
     * carries presence (the live {@link #markingBitmap} for dirty re-evaluation and the
     * clock-restart walk, the {@link #fireScanBitmap} for an intra-pass recheck), and
     * {@code preDeposit} puts the counting checks on that same view: tokens a same-pass sync
     * action deposited are discounted, so they satisfy neither a cardinality gate nor a ν-join
     * (EXEC-003 AC4).
     */
    private boolean canEnable(int tid, long[] markingSnap, boolean preDeposit) {
        // 1. Fast bitmap check
        if (!compiled.canEnableBitmap(tid, markingSnap)) return false;

        boolean discount = preDeposit && hasDeposits;

        // 2. Cardinality check (rare — only for multi-token inputs)
        assert Thread.currentThread() == orchestratorThread;
        var cardCheck = compiled.cardinalityCheck(tid);
        if (cardCheck != null) {
            for (int i = 0; i < cardCheck.placeIds().length; i++) {
                int pid = cardCheck.placeIds()[i];
                int required = cardCheck.requiredCounts()[i];
                Place<?> place = compiled.place(pid);
                int available = marking.tokenCount(place);
                if (discount) available -= Math.min(depositDelta[pid], available);
                if (available < required) return false;
            }
        }

        // 3. ν-net join: a correlation name must satisfy every matched input (NU-020).
        // Fast-path transitions read the maintained matcher (O(1)); the rest
        // rebuild the index (O(n)).
        if (compiled.transition(tid).matchSpec() != null) {
            // A join whose correlated input took a same-pass deposit defers to the next
            // cycle wholesale (EXEC-003 AC4): the binding is chosen over whole queues, so
            // it cannot be answered from a marking this pass may not see.
            if (discount && anyDepositAt(matchInputPids[tid])) return false;
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

    /** True when any of {@code pids} took a deposit in the current firing pass. */
    private boolean anyDepositAt(int[] pids) {
        for (int pid : pids) {
            if (depositDelta[pid] != 0) return true;
        }
        return false;
    }

    /**
     * Starts a firing pass: refreshes the pre-deposit presence snapshot from the live
     * bitmap and drops the previous pass's deposit delta. The only wholesale refresh of
     * either — inside the pass the snapshot is narrowed per place and the delta only grows.
     */
    private void beginFiringPass() {
        System.arraycopy(markingBitmap, 0, fireScanBitmap, 0, markingBitmap.length);
        if (hasDeposits) {
            for (int i = 0; i < depositTouchedCount; i++) depositDelta[depositTouched[i]] = 0;
            depositTouchedCount = 0;
            hasDeposits = false;
        }
    }

    /** Counts a token a sync action deposited into {@code pid} (EXEC-003 AC4). */
    private void recordDeposit(int pid) {
        if (depositDelta[pid] == 0) depositTouched[depositTouchedCount++] = pid;
        depositDelta[pid]++;
        hasDeposits = true;
    }

    /**
     * How many tokens a drain — {@code all()}, {@code atLeast(n)}, or a reset arc — firing
     * later in this pass may take from {@code place}, given its {@code live} count:
     * everything the pass began with, as consumed by earlier firings, but <em>not</em> the
     * tokens a same-pass synchronous action deposited (EXEC-003 AC5). Deposits land at the
     * tail of the FIFO queue (EXEC-010), so the drainable set is the prefix of length
     * {@code live - depositDelta}.
     *
     * <p>A pass that deposited nothing pays one predictable branch and skips the place-id
     * lookup entirely.
     */
    private int drainable(Place<?> place, int live) {
        if (!hasDeposits) return live;
        int pid = compiled.placeIdOrMissing(place);
        return pid < 0 ? live : live - Math.min(depositDelta[pid], live);
    }

    // ======================== Deadline Enforcement ========================

    /**
     * Disables transitions that have exceeded their timing deadline.
     * Uses bitmap iteration to visit only enabled transitions.
     */
    private void enforceDeadlines() {
        long nowNanos = clockNanos();
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
                        clockInstant(), t.name(),
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
        if (enabledTransitionCount == 0) return;
        beginFiringPass();
        for (int w = 0; w < transitionWords; w++) {
            long word = enabledBitmap[w] & ~inFlightBitmap[w];
            while (word != 0) {
                int bit = Long.numberOfTrailingZeros(word);
                int tid = (w << WORD_SHIFT) | bit;
                word &= word - 1;

                if (canEnable(tid, fireScanBitmap, true)) {
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
        long nowNanos = clockNanos();

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

        beginFiringPass();

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
            if (isEnabled(tid) && canEnable(tid, fireScanBitmap, true)) {
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
                        // Count matches only within the drainable prefix (EXEC-003 AC5).
                        // removeFirstMatching always takes the frontmost match, so the
                        // first n it removes are exactly the n counted here — a same-pass
                        // deposit in the tail is never reached.
                        int limit = drainable(place, marking.tokenCount(place));
                        int c = 0;
                        int seen = 0;
                        for (Token<?> tk : marking.peekTokens(place)) {
                            if (seen++ >= limit) break;
                            if (pred.test(tk)) c++;
                        }
                        yield c;
                    }
                };
                for (int i = 0; i < toConsume; i++) {
                    Token<?> token = marking.removeFirstMatching(place, pred);
                    if (token == null) break;
                    consumed.add(token);
                    inputs.add(place, (Token<Object>) token);
                    if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
                        clockInstant(), in.place().name(), token));
                }
            } else {
                // one / exactly(n) take a fixed count off the FIFO head and are already
                // confined to the pre-deposit prefix; only the draining forms need the
                // EXEC-003 AC5 discount.
                int toConsume = switch (in) {
                    case Arc.In.One _ -> 1;
                    case Arc.In.Exactly e -> e.count();
                    case Arc.In.All _ -> drainable(place, marking.tokenCount(place));
                    case Arc.In.AtLeast _ -> drainable(place, marking.tokenCount(place));
                };
                for (int i = 0; i < toConsume; i++) {
                    Token<?> token = marking.removeFirst(place);
                    consumed.add(token);
                    inputs.add(place, (Token<Object>) token);
                    if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
                        clockInstant(), in.place().name(), token));
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

        // Reset arcs. A reset firing later in the pass clears what the pass began with,
        // not what a same-pass action deposited (EXEC-003 AC5): the deposits are the FIFO
        // tail, so the reset takes the prefix and they survive to the next cycle.
        // take == live on every deposit-free pass, keeping the wholesale drain as the
        // fast path.
        for (var arc : t.resets()) {
            Place<Object> rp = (Place<Object>) arc.place();
            int live = marking.tokenCount(rp);
            int take = drainable(rp, live);
            if (take >= live) {
                for (Token<?> token : marking.removeAll(rp)) {
                    consumed.add(token);
                    if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
                        clockInstant(), arc.place().name(), token));
                }
            } else {
                for (int i = 0; i < take; i++) {
                    Token<?> token = marking.removeFirst(rp);
                    if (token == null) break;
                    consumed.add(token);
                    if (eventStoreEnabled) emitEvent(new NetEvent.TokenRemoved(
                        clockInstant(), arc.place().name(), token));
                }
            }
        }

        // Update bitmap for consumed/reset places and flag the clocks this consumption
        // disabled, before the action can refill anything (TIME-012)
        updateBitmapAfterConsumption(tid);

        if (eventStoreEnabled) emitEvent(new NetEvent.TransitionStarted(clockInstant(), t.name(), consumed));

        Map<Class<?>, Object> execContext = executionContextProvider.createContext(t, consumed);
        var context = new TransitionContext(t, inputs, newOutput(), execContext);
        final String freshNameBase = t.name();
        context.setFreshNameSupplier(() ->
            new NameId(freshNameBase + "#" + executionScope() + ":" + freshNameCounter.getAndIncrement()));

        CompletableFuture<Void> transitionFuture = eventStore.isEnabled()
            ? LogCaptureScope.call(t.name(), eventStore::append,
                  () -> ExecutorSupport.executeAction(t, context))
            : ExecutorSupport.executeAction(t, context);
        absorbInterruptFlag(); // [EXEC-041] AC#5: what the action set is not a stop request

        // Handle Out.Timeout
        if (t.hasActionTimeout()) {
            transitionFuture = ExecutorSupport.withActionTimeout(
                t, context, transitionFuture,
                () -> { if (eventStoreEnabled) emitEvent(new NetEvent.ActionTimedOut(
                    clockInstant(), t.name(), t.actionTimeout().after())); });
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
            inFlight.put(t, new InFlightTransition(transitionFuture, context, consumed, clockNanos()));
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
                // Unknown places retain the token (CORE-072 AC3); only compiled
                // places get presence bits and dirty marking.
                int pid = compiled.placeIdOrMissing(entry.place());
                cacheAddToken(entry.place(), token);
                marking.addToken((Place<Object>) entry.place(), (Token<Object>) token);
                if (pid >= 0) {
                    setMarkingBit(pid);
                    // Live presence only — the fire-scan snapshot and the deposit delta
                    // keep this token out of the rest of the pass (EXEC-003).
                    recordDeposit(pid);
                    markDirty(pid);
                } else {
                    warnUnknownPlace(entry.place(), t.name());
                }
                if (eventStoreEnabled) {
                    produced.add(token);
                    emitEvent(new NetEvent.TokenAdded(
                        clockInstant(), entry.place().name(), token));
                }
            }

            // Mark the completed transition dirty for re-evaluation
            markTransitionDirty(tid);

            if (eventStoreEnabled) {
                emitEvent(new NetEvent.TransitionCompleted(
                    clockInstant(), t.name(), produced, Duration.ZERO));
            }
        } catch (RuntimeException e) {
            // See processCompletedTransitions: CancellationException arrives unwrapped.
            handleTransitionFailure(t, e);
            markTransitionDirty(tid);
        }
    }

    /**
     * After consuming tokens from a place, update the bitmaps if the place is now empty.
     * Also mark affected transitions dirty for those places.
     * Uses precomputed consumption place IDs to avoid HashSet allocation.
     *
     * <p>The {@link #fireScanBitmap} is narrowed here and only here (EXEC-003 AC3): a place
     * this firing emptied of the tokens it held when the pass started stops being present
     * for the rest of the pass. Only a clear, and only for the pids this firing touched —
     * a wholesale refresh would republish deposits from earlier firings in the pass.
     *
     * <p>The same loop flags the clocks the consumption disabled (TIME-012): a place still
     * holding the largest count any arc requires of it disabled no one, so only a place whose
     * live count is below that threshold is walked by {@link #flagClockRestarts}, which gives
     * why the count includes same-pass deposits. A transition disabled through another
     * consumed place is caught when that place comes up, since bits not yet reconciled only
     * make {@link #canEnable} more permissive. A ν binding can break at any count, so a join's
     * correlated inputs are always walked.
     */
    private void updateBitmapAfterConsumption(int tid) {
        int[] pids = compiled.consumptionPlaceIds(tid);
        for (int pid : pids) {
            Place<?> place = compiled.place(pid);
            int live = marking.tokenCount(place);
            if (live == 0) {
                clearMarkingBit(pid);
                clearFireScanBit(pid);
            } else if (hasDeposits && live <= depositDelta[pid]) {
                clearFireScanBit(pid);
            }
            markDirty(pid);
            if (compiled.restartAlwaysCheck(pid) || live < compiled.restartThreshold(pid)) {
                flagClockRestarts(tid, pid);
            }
        }
    }

    /**
     * Flags the clock restart of every other enabled transition that {@code tid}'s
     * consumption disabled through {@code pid} (TIME-012). The firing re-enables such a
     * transition once its outputs land, so its clock starts over whether the action deposits
     * before the next dirty scan (synchronous) or after it (asynchronous). Removing tokens
     * never trips an inhibitor, so the bit tests reject every other kind of neighbour.
     *
     * <p>The check runs on the live marking, with none of the in-pass recheck's same-pass
     * discount, because the intermediate marking is taken from the marking {@code tid} fires
     * from. Tokens an earlier firing already deposited are really there, so a transition they
     * keep enabled, a ν-join with its binding intact included, was never disabled. An earlier
     * firing whose action is asynchronous has not deposited yet, so the gap it left is seen.
     */
    private void flagClockRestarts(int tid, int pid) {
        for (int other : compiled.affectedTransitions(pid)) {
            if (other == tid || !isEnabled(other) || isInFlight(other) || isRestartPending(other)) continue;
            if (!canEnable(other, markingBitmap, false)) {
                restartPendingBitmap[other >>> WORD_SHIFT] |= 1L << (other & BIT_MASK);
                hasRestartPending = true;
            }
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
                    // See processSyncOutput: unknown places retain the token (CORE-072 AC3).
                    int pid = compiled.placeIdOrMissing(entry.place());
                    cacheAddToken(entry.place(), token);
                    marking.addToken((Place<Object>) entry.place(), (Token<Object>) token);
                    if (pid >= 0) {
                        setMarkingBit(pid);
                        markDirty(pid);
                    } else {
                        warnUnknownPlace(entry.place(), t.name());
                    }
                    produced.add(token);
                    if (eventStoreEnabled) emitEvent(new NetEvent.TokenAdded(
                        clockInstant(), entry.place().name(), token));
                }

                // Also mark the completed transition's own ID dirty
                // so it gets re-evaluated for enablement
                markTransitionDirty(tid);

                if (eventStoreEnabled) {
                    var transitionDuration = Duration.ofNanos(clockNanos() - flight.startNanos());
                    emitEvent(new NetEvent.TransitionCompleted(
                        clockInstant(), t.name(), produced, transitionDuration));
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
                    clockInstant(), t.name(), cause.getMessage(), cause.getClass().getName()));
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

                // An environment place the compiled net does not know still retains the
                // token in the marking (CORE-072 AC3); it just cannot enable anything.
                int pid = compiled.placeIdOrMissing(event.place());
                if (pid >= 0) {
                    setMarkingBit(pid);
                    markDirty(pid);
                } else {
                    warnUnknownPlace(event.place(), "");
                }

                if (eventStoreEnabled) emitEvent(new NetEvent.TokenAdded(
                    clockInstant(), event.place().name(), event.token()));
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

        absorbInterruptFlag();
        if (environment != null) {
            // The host owns both halves of the wait ([TIME-015]): `workReady` is the signal
            // the semaphore carries by default, the delay is the timeout. No poll loop — a
            // host may return spuriously and the orchestrator re-checks on its next cycle
            // (contract point 3), which is what makes the poll bound unnecessary here.
            awaitHostedWork(allImmediate ? Long.MAX_VALUE : nanosUntilNextTimedTransition());
            return;
        }

        // A completing action does `completionQueue.offer(t); wakeUp();`, so the semaphore is
        // the wake-up signal and the queue is the durable record. Composing a
        // CompletableFuture.anyOf over every in-flight future once per poll cycle — as this
        // used to — allocated a fresh dependent node on each of those futures every 1-50ms
        // and then abandoned it, which on a long-running action accumulates for the lifetime
        // of the call. The loop below observes exactly the same events.
        while (true) {
            long pollMs = allImmediate ? awaitPollMillis
                : Math.max(1, Math.min(awaitPollMillis, nanosUntilNextTimedTransition() / 1_000_000));
            try {
                if (wakeUpSignal.tryAcquire(pollMs, TimeUnit.MILLISECONDS)) {
                    wakeUpSignal.drainPermits();
                    return;
                }
            } catch (InterruptedException e) {
                // A cancellation the executor observed ITSELF, raised while waiting: the flag
                // was down on entry (absorbInterruptFlag above; nothing in this loop sets it),
                // so unlike an ambient flag this IS a request against this run and [EXEC-041]
                // permits it to stop the loop — but only distinguishably. The finally reports
                // INTERRUPTED and hands the flag back to the caller.
                interruptDeferred = true;
                interruptedDuringWait = true;
                stopRequested = true;
                return;
            }
            if (!completionQueue.isEmpty() || (!closed.get() && !externalEventQueue.isEmpty())) return;

            // Timed transition may have become ready (pollMs was bounded by timer)
            if (!allImmediate && nanosUntilNextTimedTransition() <= 0) return;
        }
    }

    /**
     * Nanoseconds until the next timing boundary, or {@link Long#MAX_VALUE} when no timed
     * transition is enabled; {@code 0} when a boundary is already due.
     *
     * <p>Nanoseconds rather than milliseconds so both executors and the [TIME-015] seam share
     * one unit — the millisecond form truncated elapsed time downward, over-reporting the
     * remaining interval by up to a millisecond and waiting marginally longer than needed.
     * Only the wait bound is affected: enablement and deadline decisions are taken elsewhere
     * from {@code enabledAtNanos}, and the orchestrator re-checks after every wait.
     */
    private long nanosUntilNextTimedTransition() {
        long nowNanos = clockNanos();
        long minWaitNanos = Long.MAX_VALUE;

        for (int w = 0; w < transitionWords; w++) {
            long word = enabledBitmap[w] & timedMask[w]; // only check timed transitions
            while (word != 0) {
                int bit = Long.numberOfTrailingZeros(word);
                int tid = (w << WORD_SHIFT) | bit;
                word &= word - 1;

                Transition t = compiled.transition(tid);
                long enabledNanos = enabledAtNanos[tid];
                long elapsed = nowNanos - enabledNanos;

                // Time until earliest bound (when transition becomes ready to fire)
                long remainingEarliest = t.timing().earliest().toNanos() - elapsed;
                if (remainingEarliest <= 0) return 0;
                minWaitNanos = Math.min(minWaitNanos, remainingEarliest);

                // Time until deadline (when transition must be force-disabled)
                if (t.timing().hasDeadline()) {
                    long remainingDeadline = t.timing().latest().toNanos() - elapsed;
                    if (remainingDeadline <= 0) return 0;
                    minWaitNanos = Math.min(minWaitNanos, remainingDeadline);
                }
            }
        }
        return minWaitNanos;
    }

    private void awaitExternalEvent() {
        long waitNanos = nanosUntilNextTimedTransition();
        // Boundary already due: return and let the next cycle act on it rather than waiting.
        // Hoisted above the environment branch so an injected clock cannot make the
        // short-circuit diverge from the default one ([TIME-015], [EXEC-001], [CONC-010]).
        if (waitNanos <= 0) return;

        absorbInterruptFlag();
        if (environment != null) {
            awaitHostedWork(waitNanos);
            return;
        }

        try {
            long waitMs = waitNanos == Long.MAX_VALUE ? Long.MAX_VALUE : (waitNanos + 999_999) / 1_000_000;
            if (waitMs == Long.MAX_VALUE) wakeUpSignal.acquire();
            else wakeUpSignal.tryAcquire(waitMs, TimeUnit.MILLISECONDS);
            wakeUpSignal.drainPermits();
        } catch (InterruptedException e) {
            // See awaitCompletionOrEvent: an interrupt raised AT the wait is a stop request
            // against this run ([EXEC-041]), unlike an ambient flag.
            interruptDeferred = true;
            interruptedDuringWait = true;
            stopRequested = true;
        }
    }

    // ======================== Output Validation ========================

    private void validateOutput(Transition t, TokenOutput outputs) {
        if (t.outputSpec() == null) return;
        // [IO-015]: throws OutViolationException itself when no assignment of the spec tree
        // claims exactly what was produced, or when more than one does.
        Set<Place<?>> produced = outputs.placesWithTokens();
        Set<Place<?>> claim = ExecutorSupport.validateOutSpec(t.name(), t.outputSpec(), produced);
        // IO-016 AC4: a spec names a place once; several tokens into a named place pass
        // validation (IO-015 reads the produced SET) but exceed what every
        // branch-enumerating analysis models. Cheap test first: a repeat exists iff
        // there are more entries than distinct places.
        if (outputs.entries().size() > produced.size()) warnMultiplicity(t.name(), outputs, claim);
    }

    /**
     * Reports, once per transition, a firing that wrote more than one token to a place
     * its output spec names once (IO-016 AC4), as the EVT-013 log-message event. The
     * tokens are deposited regardless: the diagnostic makes the under-approximation
     * every branch-enumerating analysis makes of this transition visible. Mirrors the
     * precompiled executor word for word.
     */
    private void warnMultiplicity(String transitionName, TokenOutput outputs, Set<Place<?>> claim) {
        if (!eventStoreEnabled) return;
        if (warnedMultiplicity != null && warnedMultiplicity.contains(transitionName)) return;
        var counts = new LinkedHashMap<Place<?>, Integer>();
        for (var entry : outputs.entries()) {
            if (claim.contains(entry.place())) counts.merge(entry.place(), 1, Integer::sum);
        }
        var repeated = new ArrayList<String>();
        for (var e : counts.entrySet()) {
            if (e.getValue() > 1) repeated.add(e.getKey().name() + ": " + e.getValue());
        }
        if (repeated.isEmpty()) return;
        if (warnedMultiplicity == null) warnedMultiplicity = new HashSet<>();
        warnedMultiplicity.add(transitionName);
        emitEvent(new NetEvent.LogMessage(clockInstant(), transitionName, "libpetri.runtime", "WARN",
            "'" + transitionName + "': wrote more than one token to a place its output spec names once ("
                + String.join(", ", repeated) + "); branch-enumerating analyses model one token per "
                + "named place, so this firing exceeds what they explore (IO-016)", null, null));
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
        Thread orchestrator = orchestratorOrAwaitStart();
        if (orchestrator != null && Thread.currentThread() != orchestrator) {
            var snapshot = awaitPublishedState();
            if (orchestratorThread != null) {
                return snapshot != null ? snapshot.marking() : Marking.empty();
            }
            // else: the loop finished while we waited — fall through to the exact live marking.
        }
        return marking;
    }

    /** Test hook: shortens the foreign-reader cap. Package-private on purpose. */
    void snapshotWaitNanosForTesting(long nanos) {
        this.snapshotWaitNanos = nanos;
    }

    /**
     * Requests a fresh published pair from the orchestrator and waits, bounded, for it.
     * Returns the freshest {@link #published} pair it can — <b>one</b> volatile read, so the
     * marking and the flag always belong to the same capture — or {@code null} when the loop
     * ended meanwhile; the caller then reads the final state instead. When the request was
     * <b>not served</b> within the cap, the last published marking comes back with
     * {@code workInFlight} forced {@code true}.
     */
    private ExecutorSupport.PublishedState awaitPublishedState() {
        long seq = markingRequestSeq.incrementAndGet();
        wakeUp();
        // Deliberately the REAL clock, not clockNanos(). This runs on a FOREIGN thread and the
        // park below is a real-time parkNanos, so a cap measured on an advance-on-demand host
        // clock would never retire and the caller would wait forever ([TIME-015]). It is a
        // liveness backstop, not a firing decision, so it is not the seam's to virtualize.
        long deadline = System.nanoTime() + snapshotWaitNanos;
        while (markingServedSeq < seq) {
            if (orchestratorThread == null) return null; // loop finished; caller reads exact
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) break; // best-effort cap: return the last snapshot
            LockSupport.parkNanos(Math.min(remaining, 1_000_000L));
        }
        // Served first, pair second: a pair read after the barrier is at least as new as the
        // request. NOT served — the cap expired with the orchestrator stuck in an inline
        // action — the last pair's marking is still the best observation there is, but its
        // flag describes an older instant: since then an accepted event may have been injected
        // and consumed by the very firing that is blocking, leaving it in neither the marking
        // nor that flag. An unserved request is never a restore point ([ENV-014] AC#7).
        boolean served = markingServedSeq >= seq;
        var state = published;
        return served || state == null ? state
            : new ExecutorSupport.PublishedState(state.marking(), true);
    }

    /**
     * Captures a point-in-time snapshot of the marking while the executor runs
     * (<b>ENV-014</b>), together with whether any action was in flight at that instant.
     *
     * <p>Callable at any time while running (AC#1), and also before the run and after it has
     * ended on its own. The request is serviced within one orchestrator cycle, after that
     * cycle's external-events phase — so an {@code inject} made before the call is already in
     * the marking — and execution continues afterwards (AC#2). The returned marking is an owned
     * copy, independent of later executor state (AC#3).
     *
     * <p>Rejected once the executor has been drained or closed (AC#4): after that there is no
     * loop to service the request, so a returned marking would be a different thing — the final
     * marking — wearing the same type. Use {@link #marking()} for that.
     *
     * <p>{@link SnapshotResult#actionInFlight()} is captured at the <b>same instant</b> as the
     * marking and travels with it as one value through one reference, which is what makes
     * AC#5/AC#6 answerable without a race — with any number of concurrent callers. It is true
     * for an in-flight action <b>and</b> for an accepted but un-injected external event.
     *
     * <p><b>From inside an action</b> — or an event-store callback, or the hosted wait: any
     * code on the orchestrator thread — the capture is direct and immediate, of the live
     * marking, and always reports {@code actionInFlight = true}: the calling firing has
     * consumed its inputs and not yet produced its outputs, so it is never a restore point. A
     * "checkpoint" transition therefore cannot checkpoint from within itself; snapshot from a
     * continuation on another thread, or after the firing.
     *
     * <p>Best-effort bound, as for {@link #marking()}: while the orchestrator is stuck inside a
     * long inline action it cannot serve the request, and after 2s a foreign caller gets the
     * <b>last published marking with {@code actionInFlight = true}</b>, whatever that older
     * pair's own flag said. A request that was not served is never a restore point (AC#7): the
     * orchestrator may since have injected an accepted event and handed it to the very firing
     * that is blocking, so the event is in neither the older marking nor the older flag. The
     * marking is still a valid, internally consistent observation — of an earlier instant.
     *
     * @return the marking and the in-flight observation, taken together
     * @throws IllegalStateException if the executor has been drained or closed, or if the net
     *         declares two places with one name ([MOD-024]) — the name-keyed form would
     *         silently lose one place's tokens
     */
    @Override
    public SnapshotResult snapshot() {
        if (closed.get() || draining.get()) {
            throw new IllegalStateException(
                "snapshot() is not available after drain()/close() (ENV-014 AC4): no orchestrator "
                    + "loop remains to service the request. Use marking() for the final marking.");
        }
        ExecutorSupport.requireSnapshotable(ambiguousPlaceName);
        Thread orchestrator = orchestratorOrAwaitStart();
        if (orchestrator == Thread.currentThread()) {
            // Never park waiting for ourselves. True, not the in-flight state: the calling
            // firing is registered in-flight only after its action returns.
            return new SnapshotResult(marking.snapshot(), true);
        }
        ExecutorSupport.PublishedState state = orchestrator != null ? awaitPublishedState() : null;
        if (state == null) {
            // No loop. Finished — while we waited, or before we asked: the finally published
            // the final pair before it cleared the thread reference. Or never started: capture
            // here, nothing else touches the marking.
            state = terminated ? published : capturePublishedState();
        }
        return new SnapshotResult(state.marking().snapshot(), state.workInFlight());
    }

    /**
     * The orchestrator thread, first waiting out the <b>start window</b>: {@code run()} has
     * been called but the loop has not published its thread yet — it may still be queued on a
     * caller-supplied executor. A foreign reader that saw {@code null} there took the
     * never-started path and read (Precompiled: rebuilt) the live marking while the loop's
     * first cycle mutated it, which throws {@code ConcurrentModificationException} or worse.
     * Bounded like every other foreign-thread wait here; on expiry the caller falls back to
     * that old behaviour rather than hang.
     */
    private Thread orchestratorOrAwaitStart() {
        Thread orchestrator = orchestratorThread;
        if (orchestrator != null || !started || terminated) return orchestrator;
        long giveUp = System.nanoTime() + ExecutorSupport.MARKING_SNAPSHOT_WAIT_NANOS;
        while ((orchestrator = orchestratorThread) == null && !terminated
                && System.nanoTime() < giveUp) {
            LockSupport.parkNanos(100_000L);
        }
        return orchestrator;
    }

    /**
     * Why the last run stopped ([EXEC-041] AC#3).
     *
     * <p>{@link TerminationReason#QUIESCENT} is the only value for which the marking returned
     * by {@link #run()} is a <b>final</b> marking; every other value means the run was
     * truncated and the marking is partial.
     *
     * @return the termination reason, or {@link TerminationReason#RUNNING} before the first run
     */
    @Override
    public TerminationReason terminationReason() {
        return terminationReason;
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

    /**
     * This executor's id, assigned at construction from a process-wide counter.
     *
     * <p>Not derived from the clock: an id built from a firing-clock reading violates
     * [TIME-015] contract point 1 (a reading is not a unique key). Under an injected clock two
     * executors seeded at the same virtual instant would share an id, and a replayed run would
     * collide with itself.
     */
    public String executionId() {
        return executionId;
    }

    // ======================== Internal Helpers ========================

    private void emitEvent(NetEvent event) {
        if (eventStore.isEnabled()) {
            eventStore.append(event);
        }
    }

    /**
     * Reports an unknown place once (CORE-072 AC4), as the EVT-013 log-message event.
     * Retention (AC3) never depends on this: under a disabled store nothing is emitted.
     */
    private void warnUnknownPlace(Place<?> place, String transitionName) {
        if (!eventStoreEnabled) return;
        if (warnedUnknownPlaces == null) warnedUnknownPlaces = new HashSet<>();
        if (!warnedUnknownPlaces.add(place)) return;
        emitEvent(new NetEvent.LogMessage(clockInstant(), transitionName, "libpetri.runtime", "WARN",
            "unknown place '" + place.name() + "': tokens are retained in the marking but inert "
                + "(the net declares no arc on it)", null, null));
    }

    /** Initial-marking seam for CORE-072 AC4 — the {@link Marking} retains them either way. */
    private void warnUnknownInitialPlaces(Map<Place<?>, List<Token<?>>> initialTokens) {
        if (!eventStoreEnabled) return;
        for (var entry : initialTokens.entrySet()) {
            if (!entry.getValue().isEmpty() && compiled.placeIdOrMissing(entry.getKey()) < 0) {
                warnUnknownPlace(entry.getKey(), "");
            }
        }
    }

    private Duration elapsedDuration() {
        return Duration.ofNanos(clockNanos() - startNanos);
    }

    private void emitMarkingSnapshot() {
        emitEvent(new NetEvent.MarkingSnapshot(clockInstant(), marking.snapshot()));
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
