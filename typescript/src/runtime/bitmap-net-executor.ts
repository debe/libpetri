/**
 * @module bitmap-net-executor
 *
 * Async bitmap-based executor for Typed Coloured Time Petri Nets.
 *
 * **Execution loop phases** (per cycle):
 * 1. Process completed transitions — collect outputs, validate against Out specs
 * 2. Process external events — inject tokens from EnvironmentPlaces
 * 3. Update dirty transitions — re-evaluate enablement for transitions whose
 *    input/inhibitor/read places changed (bitmap-based dirty set tracking)
 * 4. Fire ready transitions — sorted by priority (desc) then FIFO enablement time
 * 5. Await work — sleep until an action completes, a timer fires, or an external event arrives
 *
 * **Concurrency model**: Single-threaded JS event loop. No locks or CAS needed.
 * Multiple transitions execute concurrently via Promises (actions return Promise<void>).
 * Only the orchestrator mutates marking state — actions communicate via TokenOutput.
 *
 * **Bitmap strategy**: Places are tracked as bits in Uint32Array words. Enablement
 * checks use bitwise AND/OR for O(W) where W = ceil(numPlaces/32). A dirty set
 * bitmap tracks which transitions need re-evaluation, avoiding O(T) scans per cycle.
 *
 * @see CompiledNet for the precomputed bitmap masks and reverse indices
 */
import type { PetriNet } from '../core/petri-net.js';
import type { Place, EnvironmentPlace } from '../core/place.js';
import type { Token } from '../core/token.js';
import type { Transition } from '../core/transition.js';
import type { EventStore } from '../event/event-store.js';
import type { NetEvent } from '../event/net-event.js';
import type { PetriNetExecutor } from './petri-net-executor.js';
import { tokenOf } from '../core/token.js';
import { TokenInput } from '../core/token-input.js';
import { TokenOutput } from '../core/token-output.js';
import { TransitionContext } from '../core/transition-context.js';
import { noopEventStore } from '../event/event-store.js';
import { CompiledNet, WORD_SHIFT, BIT_MASK, setBit, clearBit } from './compiled-net.js';
import { Marking } from './marking.js';
import { validateOutSpec, produceTimeoutOutput } from './executor-support.js';
import { OutViolationError } from './out-violation-error.js';
import { earliest as timingEarliest, latest as timingLatest, hasDeadline as timingHasDeadline } from '../core/timing.js';

/** Tolerance for JS timer jitter (setTimeout resolution ~1-4ms). */
// Tolerance for deadline enforcement to account for Node.js event loop timer jitter.
// setTimeout(fn, N) may fire up to ~5ms late on busy systems. Without this tolerance,
// exact-timed transitions (where earliest == latest) would race the event loop.
const DEADLINE_TOLERANCE_MS = 5;

interface InFlightTransition {
  promise: Promise<void>;
  context: TransitionContext;
  consumed: Token<any>[];
  startMs: number;
  resolve: () => void;
  error?: unknown;
}

interface ExternalEvent<T = any> {
  place: Place<T>;
  token: Token<T>;
  resolve: (value: boolean) => void;
  reject: (err: Error) => void;
}

export interface BitmapNetExecutorOptions {
  eventStore?: EventStore;
  environmentPlaces?: Set<EnvironmentPlace<any>>;
  longRunning?: boolean;
  /** Provides execution context data for each transition firing. */
  executionContextProvider?: (transitionName: string, consumed: Token<any>[]) => Map<string, unknown>;
}

/**
 * Async bitmap-based executor for Coloured Time Petri Nets.
 *
 * Single-threaded JS model: no CAS needed, direct array writes.
 * Actions return Promise<void> — multiple in-flight actions are naturally concurrent.
 *
 * @remarks
 * **Deadline enforcement**: Transitions with finite deadlines (`deadline`, `window`, `exact`)
 * are checked in `enforceDeadlines()`, called from the main loop only when `hasAnyDeadlines`
 * is true (precomputed at construction). If a transition has been enabled longer than
 * `latest(timing)`, it is forcibly disabled and a `TransitionTimedOut` event is emitted.
 * The `awaitWork()` timer also schedules wake-ups for approaching deadlines, not just
 * earliest firing times.
 *
 * **Constructor precomputation**: `hasAnyDeadlines`, `allImmediate`/`allSamePriority`,
 * and `eventStoreEnabled` are computed once to avoid per-cycle overhead. Safe because
 * `isEnabled()` is constant and timing/priority are immutable on Transition.
 */
export class BitmapNetExecutor implements PetriNetExecutor {
  private readonly compiled: CompiledNet;
  private readonly marking: Marking;
  private readonly eventStore: EventStore;
  private readonly environmentPlaces: Set<string>;
  private readonly longRunning: boolean;
  private readonly executionContextProvider?: (transitionName: string, consumed: Token<any>[]) => Map<string, unknown>;
  private readonly startMs: number;
  private readonly hasAnyDeadlines: boolean;
  private readonly allImmediate: boolean;
  private readonly allSamePriority: boolean;
  private readonly eventStoreEnabled: boolean;

  // Bitmaps (Uint32Array, direct writes)
  private readonly markedPlaces: Uint32Array;
  private readonly dirtySet: Uint32Array;
  private readonly markingSnapBuffer: Uint32Array;
  private readonly dirtySnapBuffer: Uint32Array;
  private readonly firingSnapBuffer: Uint32Array;

  // Orchestrator state
  private readonly enabledAtMs: Float64Array;
  private readonly inFlightFlags: Uint8Array;
  private readonly enabledFlags: Uint8Array;
  /** Precomputed: 1 if transition has a finite deadline, 0 otherwise. */
  private readonly hasDeadlineFlags: Uint8Array;
  private enabledTransitionCount = 0;

  // In-flight tracking
  private readonly inFlight = new Map<Transition, InFlightTransition>();
  private readonly inFlightPromises: Promise<void>[] = [];
  private readonly awaitPromises: Promise<void>[] = [];

  // Queues
  private readonly completionQueue: Transition[] = [];
  private readonly externalQueue: ExternalEvent[] = [];

  // Wake-up mechanism
  private wakeUpResolve: (() => void) | null = null;

  // Pre-allocated buffer for fireReadyTransitions() to avoid per-cycle allocation
  private readonly readyBuffer: { tid: number; priority: number; enabledAtMs: number }[] = [];

  // Pending reset places for clock-restart detection
  private readonly pendingResetPlaces = new Set<string>();
  private readonly transitionInputPlaceNames: Map<Transition, Set<string>>;

  private running = false;
  private closed = false;

  constructor(
    net: PetriNet,
    initialTokens: Map<Place<any>, Token<any>[]>,
    options: BitmapNetExecutorOptions = {},
  ) {
    this.compiled = CompiledNet.compile(net);
    this.marking = Marking.from(initialTokens);
    this.eventStore = options.eventStore ?? noopEventStore();
    this.environmentPlaces = new Set(
      [...(options.environmentPlaces ?? [])].map(ep => ep.place.name)
    );
    this.longRunning = options.longRunning ?? false;
    this.executionContextProvider = options.executionContextProvider;
    this.startMs = performance.now();

    const wordCount = this.compiled.wordCount;
    this.markedPlaces = new Uint32Array(wordCount);
    this.markingSnapBuffer = new Uint32Array(wordCount);
    this.firingSnapBuffer = new Uint32Array(wordCount);
    const dirtyWords = (this.compiled.transitionCount + BIT_MASK) >>> WORD_SHIFT;
    this.dirtySet = new Uint32Array(dirtyWords);
    this.dirtySnapBuffer = new Uint32Array(dirtyWords);

    this.enabledAtMs = new Float64Array(this.compiled.transitionCount);
    this.enabledAtMs.fill(-Infinity);
    this.inFlightFlags = new Uint8Array(this.compiled.transitionCount);
    this.enabledFlags = new Uint8Array(this.compiled.transitionCount);
    this.hasDeadlineFlags = new Uint8Array(this.compiled.transitionCount);
    let anyDeadlines = false;
    let allImm = true;
    let samePrio = true;
    const firstPriority = this.compiled.transitionCount > 0
      ? this.compiled.transition(0).priority : 0;
    for (let tid = 0; tid < this.compiled.transitionCount; tid++) {
      const t = this.compiled.transition(tid);
      if (timingHasDeadline(t.timing)) {
        this.hasDeadlineFlags[tid] = 1;
        anyDeadlines = true;
      }
      if (t.timing.type !== 'immediate') allImm = false;
      if (t.priority !== firstPriority) samePrio = false;
    }
    this.hasAnyDeadlines = anyDeadlines;
    this.allImmediate = allImm;
    this.allSamePriority = samePrio;
    this.eventStoreEnabled = this.eventStore.isEnabled();

    // Precompute input place names per transition
    this.transitionInputPlaceNames = new Map();
    for (const t of net.transitions) {
      const names = new Set<string>();
      for (const spec of t.inputSpecs) names.add(spec.place.name);
      this.transitionInputPlaceNames.set(t, names);
    }
  }

  // ======================== Execution ========================

  async run(timeoutMs?: number): Promise<Marking> {
    if (timeoutMs !== undefined) {
      let timer: ReturnType<typeof setTimeout> | undefined;
      const timeoutPromise = new Promise<never>((_, reject) => {
        timer = setTimeout(() => reject(new Error('Execution timed out')), timeoutMs);
      });
      try {
        return await Promise.race([this.executeLoop(), timeoutPromise]);
      } finally {
        if (timer !== undefined) clearTimeout(timer);
      }
    }
    return this.executeLoop();
  }

  private async executeLoop(): Promise<Marking> {
    this.running = true;
    this.emitEvent({
      type: 'execution-started',
      timestamp: Date.now(),
      netName: this.compiled.net.name,
      executionId: this.executionId(),
    });

    this.initializeMarkedBitmap();
    this.markAllDirty();

    this.emitEvent({
      type: 'marking-snapshot',
      timestamp: Date.now(),
      marking: this.snapshotMarking(),
    });

    while (this.running && !this.closed) {
      this.processCompletedTransitions();
      this.processExternalEvents();
      this.updateDirtyTransitions();
      // Single timestamp for this loop iteration: ensures deadline enforcement and
      // firing readiness checks use the same time reference, preventing races where
      // a transition passes the deadline check but is disabled before the fire check.
      const cycleNowMs = performance.now();
      // Deadline enforcement: separate pass over ALL enabled transitions (not just dirty
      // ones), since deadlines tick independently of place changes. Gated by
      // hasAnyDeadlines (O(0) skip for pure immediate nets).
      if (this.hasAnyDeadlines) this.enforceDeadlines(cycleNowMs);

      if (this.shouldTerminate()) break;

      this.fireReadyTransitions(cycleNowMs);
      // Skip awaitWork() when firing produced dirty bits (e.g., token consumption
      // disabled a conflicting transition). Bounded: without microtask yield no new
      // completions arrive, so the loop converges in at most one extra pass.
      if (this.hasDirtyBits()) continue;
      await this.awaitWork();
    }

    this.running = false;
    this.drainPendingExternalEvents();

    this.emitEvent({
      type: 'marking-snapshot',
      timestamp: Date.now(),
      marking: this.snapshotMarking(),
    });

    this.emitEvent({
      type: 'execution-completed',
      timestamp: Date.now(),
      netName: this.compiled.net.name,
      executionId: this.executionId(),
      totalDurationMs: performance.now() - this.startMs,
    });

    return this.marking;
  }

  // ======================== Environment Place API ========================

  async inject<T>(envPlace: EnvironmentPlace<T>, token: Token<T>): Promise<boolean> {
    if (!this.environmentPlaces.has(envPlace.place.name)) {
      throw new Error(`Place ${envPlace.place.name} is not registered as an environment place`);
    }
    if (this.closed) return false;

    return new Promise<boolean>((resolve, reject) => {
      this.externalQueue.push({
        place: envPlace.place,
        token,
        resolve,
        reject,
      });
      this.wakeUp();
    });
  }

  /** Convenience: inject a raw value (creates token with current timestamp). */
  async injectValue<T>(envPlace: EnvironmentPlace<T>, value: T): Promise<boolean> {
    return this.inject(envPlace, tokenOf(value));
  }

  // ======================== Initialize ========================

  private initializeMarkedBitmap(): void {
    for (let pid = 0; pid < this.compiled.placeCount; pid++) {
      const place = this.compiled.place(pid);
      if (this.marking.hasTokens(place)) {
        setBit(this.markedPlaces, pid);
      }
    }
  }

  private markAllDirty(): void {
    const tc = this.compiled.transitionCount;
    const dirtyWords = this.dirtySet.length;
    for (let w = 0; w < dirtyWords - 1; w++) {
      this.dirtySet[w] = 0xFFFFFFFF;
    }
    if (dirtyWords > 0) {
      const lastWordBits = tc & BIT_MASK;
      this.dirtySet[dirtyWords - 1] = lastWordBits === 0 ? 0xFFFFFFFF : (1 << lastWordBits) - 1;
    }
  }

  private shouldTerminate(): boolean {
    if (this.longRunning) return this.closed;
    return this.enabledTransitionCount === 0
      && this.inFlight.size === 0
      && this.completionQueue.length === 0;
  }

  // ======================== Dirty Set Transitions ========================

  private updateDirtyTransitions(): void {
    const nowMs = performance.now();

    // Snapshot the marking bitmap into pre-allocated buffer.
    // We need a consistent snapshot because enablement checks read multiple words,
    // and concurrent completions/injections could modify markedPlaces mid-scan.
    const markingSnap = this.markingSnapBuffer;
    markingSnap.set(this.markedPlaces);

    // Snapshot-and-clear the dirty set in one pass. New dirty bits set during
    // re-evaluation (e.g., by cascading enablement) are captured in the next cycle.
    const dirtyWords = this.dirtySet.length;
    const dirtySnap = this.dirtySnapBuffer;
    for (let w = 0; w < dirtyWords; w++) {
      dirtySnap[w] = this.dirtySet[w]!;
      this.dirtySet[w] = 0;
    }

    // Iterate over set bits using the numberOfTrailingZeros trick.
    for (let w = 0; w < dirtyWords; w++) {
      let word = dirtySnap[w]!;
      while (word !== 0) {
        // Extract lowest set bit index: `word & -word` isolates the lowest set bit,
        // `Math.clz32()` counts leading zeros (0-31), XOR 31 converts to trailing zeros.
        const bit = Math.clz32(word & -word) ^ 31;
        const tid = (w << WORD_SHIFT) | bit;
        word &= word - 1; // clear lowest set bit (Kernighan's trick)

        if (tid >= this.compiled.transitionCount) break;
        if (this.inFlightFlags[tid]) continue;

        const wasEnabled = this.enabledFlags[tid] !== 0;
        const canNow = this.canEnable(tid, markingSnap);

        if (canNow && !wasEnabled) {
          this.enabledFlags[tid] = 1;
          this.enabledTransitionCount++;
          this.enabledAtMs[tid] = nowMs;
          this.emitEvent({
            type: 'transition-enabled',
            timestamp: Date.now(),
            transitionName: this.compiled.transition(tid).name,
          });
        } else if (!canNow && wasEnabled) {
          this.enabledFlags[tid] = 0;
          this.enabledTransitionCount--;
          this.enabledAtMs[tid] = -Infinity;
        } else if (canNow && wasEnabled && this.hasInputFromResetPlace(this.compiled.transition(tid))) {
          this.enabledAtMs[tid] = nowMs;
          this.emitEvent({
            type: 'transition-clock-restarted',
            timestamp: Date.now(),
            transitionName: this.compiled.transition(tid).name,
          });
        }
      }
    }

    this.pendingResetPlaces.clear();
  }

  /**
   * Checks all enabled transitions with finite deadlines. If a transition has been
   * enabled longer than `latest(timing)`, it is forcibly disabled and a
   * `TransitionTimedOut` event is emitted. Classical TPN semantics require transitions
   * to either fire within their window or become disabled.
   *
   * A 1ms tolerance is applied to account for timer jitter and microtask scheduling
   * delays. Without this, exact-timed transitions (where earliest == latest) would
   * almost always be disabled before they can fire.
   */
  private enforceDeadlines(nowMs: number): void {
    for (let tid = 0; tid < this.compiled.transitionCount; tid++) {
      if (!this.hasDeadlineFlags[tid]) continue; // O(1) skip for non-deadline transitions
      if (!this.enabledFlags[tid] || this.inFlightFlags[tid]) continue;
      const t = this.compiled.transition(tid);

      const elapsed = nowMs - this.enabledAtMs[tid]!;
      const latestMs = timingLatest(t.timing);
      if (elapsed > latestMs + DEADLINE_TOLERANCE_MS) {
        this.enabledFlags[tid] = 0;
        this.enabledTransitionCount--;
        this.emitEvent({
          type: 'transition-timed-out',
          timestamp: Date.now(),
          transitionName: t.name,
          deadlineMs: latestMs,
          actualDurationMs: elapsed,
        });
        this.enabledAtMs[tid] = -Infinity;
      }
    }
  }

  private canEnable(tid: number, markingSnap: Uint32Array): boolean {
    if (!this.compiled.canEnableBitmap(tid, markingSnap)) return false;

    // Cardinality check
    const cardCheck = this.compiled.cardinalityCheck(tid);
    if (cardCheck !== null) {
      for (let i = 0; i < cardCheck.placeIds.length; i++) {
        const pid = cardCheck.placeIds[i]!;
        const required = cardCheck.requiredCounts[i]!;
        const place = this.compiled.place(pid);
        if (this.marking.tokenCount(place) < required) return false;
      }
    }

    // Guard check: verify matching tokens exist for each guarded input
    if (this.compiled.hasGuards(tid)) {
      const t = this.compiled.transition(tid);
      for (const spec of t.inputSpecs) {
        if (!spec.guard) continue;
        const requiredCount = spec.type === 'one' ? 1
          : spec.type === 'exactly' ? spec.count
          : spec.type === 'at-least' ? spec.minimum
          : 1; // 'all' requires at least 1 matching
        if (this.marking.countMatching(spec) < requiredCount) return false;
      }
    }

    return true;
  }

  private hasInputFromResetPlace(t: Transition): boolean {
    if (this.pendingResetPlaces.size === 0) return false;
    const inputNames = this.transitionInputPlaceNames.get(t);
    if (!inputNames) return false;
    for (const name of this.pendingResetPlaces) {
      if (inputNames.has(name)) return true;
    }
    return false;
  }

  // ======================== Firing ========================

  private fireReadyTransitions(nowMs: number): void {
    if (this.allImmediate && this.allSamePriority) {
      this.fireReadyImmediate();
      return;
    }
    this.fireReadyGeneral(nowMs);
  }

  /**
   * Fast path for nets where all transitions are immediate and same priority.
   * Skips timing checks, sorting, and snapshot buffer — just scan and fire.
   *
   * Uses live `markedPlaces` instead of a snapshot. Safe because
   * `updateBitmapAfterConsumption()` synchronously updates the bitmap before the next
   * iteration. For equal-priority immediate transitions, tid scan order satisfies
   * FIFO-by-enablement-time (all enabled in the same cycle).
   */
  private fireReadyImmediate(): void {
    for (let tid = 0; tid < this.compiled.transitionCount; tid++) {
      if (!this.enabledFlags[tid] || this.inFlightFlags[tid]) continue;
      if (this.canEnable(tid, this.markedPlaces)) {
        this.fireTransition(tid);
      } else {
        this.enabledFlags[tid] = 0;
        this.enabledTransitionCount--;
        this.enabledAtMs[tid] = -Infinity;
      }
    }
  }

  private fireReadyGeneral(nowMs: number): void {

    // Collect ready transitions into pre-allocated buffer to reduce GC pressure
    const ready = this.readyBuffer;
    ready.length = 0;
    for (let tid = 0; tid < this.compiled.transitionCount; tid++) {
      if (!this.enabledFlags[tid] || this.inFlightFlags[tid]) continue;
      const t = this.compiled.transition(tid);
      const enabledMs = this.enabledAtMs[tid]!;
      const elapsedMs = nowMs - enabledMs;
      const earliestMs = timingEarliest(t.timing);
      if (earliestMs <= elapsedMs) {
        ready.push({ tid, priority: t.priority, enabledAtMs: enabledMs });
      }
    }
    if (ready.length === 0) return;

    // Sort: higher priority first, then earlier enablement (FIFO).
    // This defines the deterministic scheduling contract for conflict resolution.
    // We re-sort each cycle rather than maintaining a sorted invariant because
    // enablement times change on clock-restarts (reset arcs), which would require
    // expensive re-insertion. Sorting ≤T entries per cycle is fast enough.
    ready.sort((a, b) => {
      const prioCmp = b.priority - a.priority;
      if (prioCmp !== 0) return prioCmp;
      return a.enabledAtMs - b.enabledAtMs;
    });

    // Take a fresh snapshot for re-checking (reuse pre-allocated buffer)
    const freshSnap = this.firingSnapBuffer;
    freshSnap.set(this.markedPlaces);
    for (const entry of ready) {
      const { tid } = entry;
      if (this.enabledFlags[tid] && this.canEnable(tid, freshSnap)) {
        this.fireTransition(tid);
        // Update snapshot after consuming tokens
        freshSnap.set(this.markedPlaces);
      } else {
        this.enabledFlags[tid] = 0;
        this.enabledTransitionCount--;
        this.enabledAtMs[tid] = -Infinity;
      }
    }
  }

  private fireTransition(tid: number): void {
    const t = this.compiled.transition(tid);
    const inputs = new TokenInput();
    const consumed: Token<any>[] = [];

    // Consume tokens based on input specs with cardinality and guard.
    // Note: for guarded 'all'/'at-least' inputs, countMatching() is called here AND in
    // canEnable() — a known O(2n) tradeoff. Token queues are typically ≤10 items, so
    // the simplicity of re-scanning outweighs caching complexity.
    for (const inSpec of t.inputSpecs) {
      let toConsume: number;
      switch (inSpec.type) {
        case 'one': toConsume = 1; break;
        case 'exactly': toConsume = inSpec.count; break;
        case 'all':
          toConsume = inSpec.guard
            ? this.marking.countMatching(inSpec)
            : this.marking.tokenCount(inSpec.place);
          break;
        case 'at-least':
          toConsume = inSpec.guard
            ? this.marking.countMatching(inSpec)
            : this.marking.tokenCount(inSpec.place);
          break;
      }

      for (let i = 0; i < toConsume; i++) {
        const token = inSpec.guard
          ? this.marking.removeFirstMatching(inSpec)
          : this.marking.removeFirst(inSpec.place);
        if (token === null) break;
        consumed.push(token);
        inputs.add(inSpec.place, token);
        this.emitEvent({
          type: 'token-removed',
          timestamp: Date.now(),
          placeName: inSpec.place.name,
          token,
        });
      }
    }

    // Read arcs (peek, don't consume)
    for (const arc of t.reads) {
      const token = this.marking.peekFirst(arc.place);
      if (token !== null) {
        inputs.add(arc.place, token);
      }
    }

    // Reset arcs
    for (const arc of t.resets) {
      const removed = this.marking.removeAll(arc.place);
      this.pendingResetPlaces.add(arc.place.name);
      for (const token of removed) {
        consumed.push(token);
        this.emitEvent({
          type: 'token-removed',
          timestamp: Date.now(),
          placeName: arc.place.name,
          token,
        });
      }
    }

    // Update bitmap for consumed/reset places
    this.updateBitmapAfterConsumption(tid);

    this.emitEvent({
      type: 'transition-started',
      timestamp: Date.now(),
      transitionName: t.name,
      consumedTokens: consumed,
    });

    const execCtx = this.executionContextProvider?.(t.name, consumed);
    const logFn = (level: string, message: string, error?: Error) => {
      this.emitEvent({
        type: 'log-message',
        timestamp: Date.now(),
        transitionName: t.name,
        logger: t.name,
        level,
        message,
        error: error?.name ?? null,
        errorMessage: error?.message ?? null,
      });
    };
    const context = new TransitionContext(
      t.name, inputs, new TokenOutput(),
      t.inputPlaces(), t.readPlaces(), t.outputPlaces(),
      execCtx,
      logFn,
    );

    // Create action promise with optional timeout
    let actionPromise = t.action(context);

    if (t.hasActionTimeout()) {
      const timeoutSpec = t.actionTimeout;
      if (timeoutSpec === null) throw new Error(`Expected actionTimeout on ${t.name}`);
      const timeoutMs = timeoutSpec.afterMs;
      actionPromise = Promise.race([
        actionPromise,
        new Promise<void>((_, reject) =>
          setTimeout(() => reject(new TimeoutSentinel()), timeoutMs)
        ),
      ]).catch((err) => {
        if (err instanceof TimeoutSentinel) {
          produceTimeoutOutput(context, timeoutSpec.child);
          this.emitEvent({
            type: 'action-timed-out',
            timestamp: Date.now(),
            transitionName: t.name,
            timeoutMs,
          });
          return;
        }
        throw err;
      });
    }

    // On completion, push to completionQueue
    let resolveInFlight!: () => void;
    const completionPromise = new Promise<void>(r => { resolveInFlight = r; });

    const flight: InFlightTransition = {
      promise: completionPromise,
      context,
      consumed,
      startMs: performance.now(),
      resolve: resolveInFlight,
    };

    actionPromise.then(
      () => {
        this.completionQueue.push(t);
        this.wakeUp();
        resolveInFlight();
      },
      (err) => {
        flight.error = err;
        this.completionQueue.push(t);
        this.wakeUp();
        resolveInFlight();
      },
    );

    this.inFlight.set(t, flight);
    this.inFlightFlags[tid] = 1;
    this.enabledFlags[tid] = 0;
    this.enabledTransitionCount--;
    this.enabledAtMs[tid] = -Infinity;
  }

  private updateBitmapAfterConsumption(tid: number): void {
    const pids = this.compiled.consumptionPlaceIds(tid);
    for (const pid of pids) {
      const place = this.compiled.place(pid);
      if (!this.marking.hasTokens(place)) {
        clearBit(this.markedPlaces, pid);
      }
      this.markDirty(pid);
    }
  }

  // ======================== Completion Processing ========================

  private processCompletedTransitions(): void {
    if (this.completionQueue.length === 0) return;
    // In-place iteration is safe: processing is synchronous and .push() only
    // happens from microtasks which cannot interleave within this loop.
    const len = this.completionQueue.length;
    for (let i = 0; i < len; i++) {
      const t = this.completionQueue[i]!;
      const flight = this.inFlight.get(t);
      if (!flight) continue;
      this.inFlight.delete(t);

      const tid = this.compiled.transitionId(t);
      this.inFlightFlags[tid] = 0;

      if (flight.error) {
        const err = flight.error instanceof Error
          ? flight.error
          : new Error(String(flight.error));
        this.emitEvent({
          type: 'transition-failed',
          timestamp: Date.now(),
          transitionName: t.name,
          errorMessage: err.message,
          exceptionType: err.name,
          stack: err.stack,
        });
        this.markTransitionDirty(tid);
        continue;
      }

      try {
        const outputs = flight.context.rawOutput();

        // Validate output against spec
        if (t.outputSpec !== null) {
          const produced = outputs.placesWithTokens();
          const result = validateOutSpec(t.name, t.outputSpec, produced);
          if (result === null) {
            throw new OutViolationError(
              `'${t.name}': output does not satisfy declared spec`
            );
          }
        }

        // Single pass: add tokens to marking, update bitmap, and emit events
        const produced: Token<any>[] = [];
        for (const entry of outputs.entries()) {
          this.marking.addToken(entry.place, entry.token);
          produced.push(entry.token);
          const pid = this.compiled.placeId(entry.place);
          setBit(this.markedPlaces, pid);
          this.markDirty(pid);
          this.emitEvent({
            type: 'token-added',
            timestamp: Date.now(),
            placeName: entry.place.name,
            token: entry.token,
          });
        }
        this.markTransitionDirty(tid);

        this.emitEvent({
          type: 'transition-completed',
          timestamp: Date.now(),
          transitionName: t.name,
          producedTokens: produced,
          durationMs: performance.now() - flight.startMs,
        });
      } catch (e) {
        const err = e instanceof Error ? e : new Error(String(e));
        this.emitEvent({
          type: 'transition-failed',
          timestamp: Date.now(),
          transitionName: t.name,
          errorMessage: err.message,
          exceptionType: err.name,
          stack: err.stack,
        });
        this.markTransitionDirty(tid);
      }
    }
    this.completionQueue.length = 0;
  }

  // ======================== External Events ========================

  private processExternalEvents(): void {
    if (this.externalQueue.length === 0) return;
    // In-place iteration is safe: processing is synchronous and .push() only
    // happens from microtasks which cannot interleave within this loop.
    const len = this.externalQueue.length;
    for (let i = 0; i < len; i++) {
      const event = this.externalQueue[i]!;
      try {
        this.marking.addToken(event.place, event.token);
        const pid = this.compiled.placeId(event.place);
        setBit(this.markedPlaces, pid);
        this.markDirty(pid);

        this.emitEvent({
          type: 'token-added',
          timestamp: Date.now(),
          placeName: event.place.name,
          token: event.token,
        });
        event.resolve(true);
      } catch (e) {
        event.reject(e instanceof Error ? e : new Error(String(e)));
      }
    }
    this.externalQueue.length = 0;
  }

  private drainPendingExternalEvents(): void {
    while (this.externalQueue.length > 0) {
      this.externalQueue.shift()!.resolve(false);
    }
  }

  // ======================== Await Work ========================

  /**
   * Suspends the executor until work is available. Composes up to 3 promise sources
   * into a single Promise.race: (1) any in-flight action completing, (2) external
   * event injection via wakeUp(), (3) timer for the next delayed transition's earliest
   * firing time. This avoids busy-waiting while remaining responsive to all event types.
   *
   * **Microtask flush**: Before building Promise.race, yields via `await Promise.resolve()`
   * to drain the microtask queue. Sync actions complete via `.then()` microtask; this
   * yield lets those fire, avoiding ~5 allocations when work is already available.
   * After the yield, re-checks queues and `this.closed` for close-during-yield safety.
   */
  private async awaitWork(): Promise<void> {
    if (this.completionQueue.length > 0 || this.externalQueue.length > 0) return;

    // Flush microtask queue: sync actions complete via .then() which schedules a
    // microtask. A single await here lets those fire before we build a full
    // Promise.race (~5 allocations). For async workloads this adds ~0.05us.
    await Promise.resolve();
    if (this.completionQueue.length > 0 || this.externalQueue.length > 0 || this.closed) return;

    const promises = this.awaitPromises;
    promises.length = 0;

    // 1. Any in-flight action completing (reuse array to avoid 2 intermediate allocations)
    if (this.inFlight.size > 0) {
      const arr = this.inFlightPromises;
      arr.length = 0;
      for (const f of this.inFlight.values()) arr.push(f.promise);
      promises.push(Promise.race(arr));
    }

    // 2. External event wake-up
    promises.push(new Promise<void>(resolve => { this.wakeUpResolve = resolve; }));

    // 3. Timer for next delayed transition
    const timerMs = this.millisUntilNextTimedTransition();
    if (timerMs > 0 && timerMs < Infinity) {
      promises.push(new Promise<void>(r => setTimeout(r, timerMs)));
    }

    if (promises.length > 0) {
      await Promise.race(promises);
    }
    this.wakeUpResolve = null;
  }

  private millisUntilNextTimedTransition(): number {
    const nowMs = performance.now();
    let minWaitMs = Infinity;

    for (let tid = 0; tid < this.compiled.transitionCount; tid++) {
      if (!this.enabledFlags[tid]) continue;
      const t = this.compiled.transition(tid);
      const enabledMs = this.enabledAtMs[tid]!;
      const elapsedMs = nowMs - enabledMs;

      // Time until earliest firing
      const earliestMs = timingEarliest(t.timing);
      const remainingEarliest = earliestMs - elapsedMs;
      if (remainingEarliest <= 0) return 0;
      minWaitMs = Math.min(minWaitMs, remainingEarliest);

      // Time until deadline expiry (must wake up to enforce deadline)
      if (timingHasDeadline(t.timing)) {
        const latestMs = timingLatest(t.timing);
        const remainingDeadline = latestMs - elapsedMs;
        if (remainingDeadline <= 0) return 0;
        minWaitMs = Math.min(minWaitMs, remainingDeadline);
      }
    }
    return minWaitMs;
  }

  private wakeUp(): void {
    this.wakeUpResolve?.();
  }

  // ======================== Dirty Set Helpers ========================

  /** Returns true if any transition needs re-evaluation. O(W) where W = ceil(transitions/32). */
  private hasDirtyBits(): boolean {
    for (let w = 0; w < this.dirtySet.length; w++) {
      if (this.dirtySet[w] !== 0) return true;
    }
    return false;
  }

  private markDirty(pid: number): void {
    const tids = this.compiled.affectedTransitions(pid);
    for (const tid of tids) {
      this.markTransitionDirty(tid);
    }
  }

  private markTransitionDirty(tid: number): void {
    this.dirtySet[tid >>> WORD_SHIFT]! |= (1 << (tid & BIT_MASK));
  }

  // ======================== State Inspection ========================

  getMarking(): Marking { return this.marking; }

  /** Builds a snapshot of the current marking for event emission. */
  private snapshotMarking(): ReadonlyMap<string, readonly Token<any>[]> {
    const snap = new Map<string, readonly Token<any>[]>();
    for (let pid = 0; pid < this.compiled.placeCount; pid++) {
      const p = this.compiled.place(pid);
      const tokens = this.marking.peekTokens(p);
      if (tokens.length > 0) {
        snap.set(p.name, [...tokens]);
      }
    }
    return snap;
  }

  isQuiescent(): boolean {
    return this.enabledTransitionCount === 0 && this.inFlight.size === 0;
  }

  executionId(): string {
    return this.startMs.toString(16);
  }

  close(): void {
    this.running = false;
    this.closed = true;
    this.wakeUp();
  }

  // ======================== Event Emission ========================

  private emitEvent(event: NetEvent): void {
    if (this.eventStoreEnabled) {
      this.eventStore.append(event);
    }
  }
}

/** Internal sentinel for timeout detection. */
class TimeoutSentinel extends Error {
  constructor() { super('action timeout'); this.name = 'TimeoutSentinel'; }
}
