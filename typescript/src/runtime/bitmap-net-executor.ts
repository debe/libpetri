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
import { Marking, type PredicateSpec } from './marking.js';
import { findBinding, IncrementalMatcher } from './match-engine.js';
import { keyForPlace } from '../core/match-spec.js';
import { nameId } from '../core/name.js';
import { validateOutSpec, produceTimeoutOutput, executeAction, swallowEventStoreFailure, DEADLINE_TOLERANCE_MS } from './executor-support.js';
import { earliest as timingEarliest, latest as timingLatest, hasDeadline as timingHasDeadline } from '../core/timing.js';

/** Tolerance for JS timer jitter (setTimeout resolution ~1-4ms). */
// Tolerance for deadline enforcement to account for Node.js event loop timer jitter.
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
  /** Provides execution context data for each transition firing. */
  executionContextProvider?: (transitionName: string, consumed: Token<any>[]) => Map<string, unknown>;
  /**
   * Grace band (ms) beyond a hard deadline (`deadline()` / `window()`) before a transition is
   * force-disabled with a `transition-timed-out` event (TIME-013). Defaults to {@link DEADLINE_TOLERANCE_MS}
   * (5ms); `0` gives strict enforcement. Must be non-negative. Does not affect `exact()` transitions,
   * which are enforced softly (TIME-006).
   */
  deadlineToleranceMs?: number;
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
  /** Monotonic source for ν-name minting (ctx.freshName(), NU-010). */
  private freshNameCounter = 0;
  /**
   * ν-net incremental match caches (NU-020): per matched transition, an
   * {@link IncrementalMatcher} kept in lockstep with the marking when the
   * transition is fast-path eligible (every correlated input is `one`/`exactly`,
   * consumed by no other transition, never reset), else `null` → fall back to
   * the O(n) rebuild {@link findBinding}. Turns a draining matched join from
   * O(n²) into O(n log n). Mirrors the precompiled executor and the Rust backends.
   */
  private matchCaches: (IncrementalMatcher | null)[] = [];
  private placeMatchTargets: Array<Array<[number, number]>> = [];
  private readonly eventStore: EventStore;
  private readonly environmentPlaces: Set<string>;
  private readonly hasEnvironmentPlaces: boolean;
  private readonly executionContextProvider?: (transitionName: string, consumed: Token<any>[]) => Map<string, unknown>;
  private readonly startMs: number;
  private readonly hasAnyDeadlines: boolean;
  private readonly allImmediate: boolean;
  private readonly allSamePriority: boolean;
  private readonly eventStoreEnabled: boolean;

  // Bitmaps (Uint32Array, direct writes)
  private readonly markingBitmap: Uint32Array;
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
  /** Precomputed: 1 for exact() transitions — enforced softly, never force-disabled (TIME-006). */
  private readonly isExactFlags: Uint8Array;
  /** Grace band (ms) before a hard deadline force-disables (TIME-013). */
  private readonly deadlineToleranceMs: number;
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
  /**
   * Undeclared place names already reported (CORE-072 AC4). Keyed by name — TS
   * Place identity is name-based — so a hot loop warns once, not per token.
   */
  private readonly warnedUnknownPlaces = new Set<string>();
  private readonly transitionInputPlaceNames: Map<Transition, Set<string>>;

  private running = false;
  private draining = false;
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
    this.hasEnvironmentPlaces = this.environmentPlaces.size > 0;
    this.executionContextProvider = options.executionContextProvider;
    this.deadlineToleranceMs = options.deadlineToleranceMs ?? DEADLINE_TOLERANCE_MS;
    if (this.deadlineToleranceMs < 0) {
      throw new Error(`Deadline tolerance must be non-negative: ${this.deadlineToleranceMs}`);
    }
    this.startMs = performance.now();

    const wordCount = this.compiled.wordCount;
    this.markingBitmap = new Uint32Array(wordCount);
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
    this.isExactFlags = new Uint8Array(this.compiled.transitionCount);
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
      if (t.timing.type === 'exact') this.isExactFlags[tid] = 1;
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

    // CORE-072: the Marking keeps tokens on places the net never declared;
    // report each such place once, matching the precompiled backend's seam.
    for (const [place, tokens] of initialTokens) {
      if (tokens.length > 0 && this.compiled.tryPlaceId(place) === undefined) {
        this.warnUnknownPlace(place, '');
      }
    }

    this.initMatchCaches();
  }

  /**
   * Builds the ν-net incremental match caches (NU-020). A matched join is
   * fast-path eligible only when every correlated input is `one`/`exactly`, is
   * consumed by no other transition, and is never reset — so the cache can never
   * desync from the marking. Mirrors the precompiled executor.
   */
  private initMatchCaches(): void {
    const compiled = this.compiled;
    const tc = compiled.transitionCount;
    const pc = compiled.placeCount;
    this.matchCaches = new Array(tc).fill(null);
    this.placeMatchTargets = Array.from({ length: pc }, () => []);

    let anyMatch = false;
    for (let tid = 0; tid < tc; tid++) {
      if (compiled.hasMatch(tid)) { anyMatch = true; break; }
    }
    if (!anyMatch) return;

    const inputConsumers: number[][] = Array.from({ length: pc }, () => []);
    const resetTarget: boolean[] = new Array(pc).fill(false);
    for (let tid = 0; tid < tc; tid++) {
      const t = compiled.transition(tid);
      for (const spec of t.inputSpecs) inputConsumers[compiled.placeId(spec.place)]!.push(tid);
      for (const arc of t.resets) resetTarget[compiled.placeId(arc.place)] = true;
    }

    for (let tid = 0; tid < tc; tid++) {
      if (!compiled.hasMatch(tid)) continue;
      const t = compiled.transition(tid);
      const ms = t.matchSpec;
      if (!ms) continue;

      const requireds: number[] = [];
      let eligible = true;
      for (const mk of ms.keys) {
        const pid = compiled.placeId(mk.place);
        const spec = t.inputSpecs.find(s => s.place.name === mk.place.name);
        let required: number;
        if (spec?.type === 'one') required = 1;
        else if (spec?.type === 'exactly') required = spec.count;
        else { eligible = false; break; }
        const cons = inputConsumers[pid]!;
        if (resetTarget[pid] || cons.length !== 1 || cons[0] !== tid) { eligible = false; break; }
        requireds.push(required);
      }
      if (!eligible) continue;

      const matcher = new IncrementalMatcher(requireds);
      for (let keyIdx = 0; keyIdx < ms.keys.length; keyIdx++) {
        const mk = ms.keys[keyIdx]!;
        const pid = compiled.placeId(mk.place);
        for (const token of this.marking.peekTokens(mk.place)) {
          const name = mk.key(token.value);
          if (name !== undefined && name !== null) matcher.add(keyIdx, name, token.createdAt);
        }
        this.placeMatchTargets[pid]!.push([tid, keyIdx]);
      }
      this.matchCaches[tid] = matcher;
    }
  }

  /** Mirror a token added to correlated input `pid` into every fast-path matcher. */
  private cacheAddToken(pid: number, token: Token<any>): void {
    const targets = this.placeMatchTargets[pid];
    if (targets === undefined || targets.length === 0) return;
    const compiled = this.compiled;
    for (const [tid, keyIdx] of targets) {
      const cache = this.matchCaches[tid];
      if (cache == null) continue;
      const t = compiled.transition(tid);
      const mk = t.matchSpec!.keys[keyIdx]!;
      const name = mk.key(token.value);
      if (name !== undefined && name !== null) cache.add(keyIdx, name, token.createdAt);
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

    this.initializeMarkingBitmap();
    this.markAllDirty();

    this.emitEvent({
      type: 'marking-snapshot',
      timestamp: Date.now(),
      marking: this.snapshotMarking(),
    });

    while (this.running) {
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
    if (this.closed || this.draining) return false;

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

  private initializeMarkingBitmap(): void {
    for (let pid = 0; pid < this.compiled.placeCount; pid++) {
      const place = this.compiled.place(pid);
      if (this.marking.hasTokens(place)) {
        setBit(this.markingBitmap, pid);
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
    if (this.closed) {
      // ENV-013: immediate close — wait for in-flight actions to complete
      return this.inFlight.size === 0 && this.completionQueue.length === 0;
    }
    if (this.hasEnvironmentPlaces) {
      return this.draining
        && this.enabledTransitionCount === 0
        && this.inFlight.size === 0
        && this.completionQueue.length === 0;
    }
    return this.enabledTransitionCount === 0
      && this.inFlight.size === 0
      && this.completionQueue.length === 0;
  }

  // ======================== Dirty Set Transitions ========================

  private updateDirtyTransitions(): void {
    const nowMs = performance.now();

    // Snapshot the marking bitmap into pre-allocated buffer.
    // We need a consistent snapshot because enablement checks read multiple words,
    // and concurrent completions/injections could modify markingBitmap mid-scan.
    const markingSnap = this.markingSnapBuffer;
    markingSnap.set(this.markingBitmap);

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
      // exact() is enforced softly — it fires at the first opportunity at/after its target and is
      // never force-disabled (TIME-006). Only hard deadlines (deadline()/window()) are reaped here.
      if (this.isExactFlags[tid]) continue;
      if (!this.enabledFlags[tid] || this.inFlightFlags[tid]) continue;
      const t = this.compiled.transition(tid);

      const elapsed = nowMs - this.enabledAtMs[tid]!;
      const latestMs = timingLatest(t.timing);
      if (elapsed > latestMs + this.deadlineToleranceMs) {
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

    // ν-net join: a correlation name must satisfy every matched input (NU-020).
    // Fast-path transitions read the maintained matcher (O(1)); the rest rebuild
    // the index (O(n)).
    if (this.compiled.hasMatch(tid)) {
      const cache = this.matchCaches[tid];
      const noBinding = cache != null
        ? cache.best() === null
        : findBinding(this.compiled.transition(tid), p => this.marking.peekTokens(p)) === null;
      if (noBinding) {
        return false;
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
   * Uses live `markingBitmap` instead of a snapshot. Safe because
   * `updateBitmapAfterConsumption()` synchronously updates the bitmap before the next
   * iteration. For equal-priority immediate transitions, tid scan order satisfies
   * FIFO-by-enablement-time (all enabled in the same cycle).
   */
  private fireReadyImmediate(): void {
    for (let tid = 0; tid < this.compiled.transitionCount; tid++) {
      if (!this.enabledFlags[tid] || this.inFlightFlags[tid]) continue;
      if (this.canEnable(tid, this.markingBitmap)) {
        this.fireTransitionContained(tid);
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
    freshSnap.set(this.markingBitmap);
    for (const entry of ready) {
      const { tid } = entry;
      if (this.enabledFlags[tid] && this.canEnable(tid, freshSnap)) {
        this.fireTransitionContained(tid);
        // Update snapshot after consuming tokens
        freshSnap.set(this.markingBitmap);
      } else {
        this.enabledFlags[tid] = 0;
        this.enabledTransitionCount--;
        this.enabledAtMs[tid] = -Infinity;
      }
    }
  }

  /**
   * Fires a transition, containing any synchronous throw to that one firing so it fails
   * only that transition, not the whole run.
   *
   * Without this boundary an unchecked throw raised while a transition fires — a hostile
   * EventStore.append on a token-removed or transition-started emit, or an error thrown while
   * consuming the matched tokens — unwinds out of the orchestrator loop and kills the executor.
   * The transition is instead failed and marked dirty for re-evaluation, the same treatment an
   * asynchronously-reported failure gets. Enablement-phase throws (a key function that
   * throws inside canEnable, before the firing) run outside this boundary and are not contained
   * here.
   *
   * fireTransition removes tokens from the marking before it reconciles the presence
   * bitmap, so a throw inside that window would leave bits asserting tokens that are gone;
   * the recovery re-runs updateBitmapAfterConsumption against the real marking.
   *
   * Unlike the Java runtime there is no VirtualMachineError/LinkageError analogue on the JS
   * side, so every throw is contained here — there is deliberately no fatal-rethrow escape
   * hatch.
   */
  private fireTransitionContained(tid: number): void {
    try {
      this.fireTransition(tid);
    } catch (e) {
      const t = this.compiled.transition(tid);
      if (this.enabledFlags[tid]) {
        this.enabledFlags[tid] = 0;
        this.enabledTransitionCount--;
        this.enabledAtMs[tid] = -Infinity;
      }
      if (this.inFlight.delete(t)) {
        this.inFlightFlags[tid] = 0;
      }
      this.updateBitmapAfterConsumption(tid);
      // Drop the ν fast-path matcher: fireTransition mirrors the matched consume into it
      // before the tokens physically leave the marking, so a throw in that window desyncs
      // it. Nulling it forces the next canEnable/fire to rebuild the binding via findBinding.
      this.matchCaches[tid] = null;
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

  private fireTransition(tid: number): void {
    const t = this.compiled.transition(tid);
    const inputs = new TokenInput();
    const consumed: Token<any>[] = [];

    // Consume tokens based on input specs with cardinality.
    // ν-net join: resolve the correlation name once; correlated inputs consume
    // the name-matched tokens (name equality — NU-021).
    const ms = t.matchSpec;
    const cache = ms ? this.matchCaches[tid] : null;
    const chosen = ms
      ? (cache != null ? cache.best() : findBinding(t, p => this.marking.peekTokens(p)))
      : null;
    // Mirror the matched consume into the fast-path matcher (the only path by
    // which tokens leave this join's correlated inputs) before the marking changes.
    if (cache != null && chosen !== null) cache.consume(chosen);

    for (const inSpec of t.inputSpecs) {
      const keyFn = ms ? keyForPlace(ms, inSpec.place.name) : undefined;
      // Name-equality predicate when correlated; otherwise a plain FIFO consume.
      let spec: PredicateSpec;
      if (keyFn && chosen !== null) {
        spec = {
          place: inSpec.place,
          predicate: (v: any) => keyFn(v) === chosen,
        };
      } else {
        spec = inSpec;
      }

      let toConsume: number;
      switch (inSpec.type) {
        case 'one': toConsume = 1; break;
        case 'exactly': toConsume = inSpec.count; break;
        case 'all':
        case 'at-least':
          toConsume = spec.predicate
            ? this.marking.countMatching(spec)
            : this.marking.tokenCount(inSpec.place);
          break;
      }

      for (let i = 0; i < toConsume; i++) {
        const token = spec.predicate
          ? this.marking.removeFirstMatching(spec)
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
      t.placeAlias,
    );
    const freshNameBase = t.name;
    context.setFreshNameSupplier(() => nameId(`${freshNameBase}#${this.freshNameCounter++}`));

    // Create action promise with optional timeout. executeAction converts a synchronous
    // throw or a null/non-thenable return into a rejected promise, so a misbehaving action
    // flows the contained failure path instead of unwinding the orchestrator loop.
    let actionPromise = executeAction(t, context);

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
          // Sever first, then produce: the abandoned action may still be writing to this
          // context, and its pre-timeout writes must not merge with the timeout branch.
          context.detachForTimeout();
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
        clearBit(this.markingBitmap, pid);
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
          validateOutSpec(t.name, t.outputSpec, outputs.placesWithTokens());
        }

        // Single pass: add tokens to marking, update bitmap, and emit events
        const produced: Token<any>[] = [];
        for (const entry of outputs.entries()) {
          const pid = this.compiled.tryPlaceId(entry.place);
          this.marking.addToken(entry.place, entry.token);
          produced.push(entry.token);
          if (pid !== undefined) {
            this.cacheAddToken(pid, entry.token);
            setBit(this.markingBitmap, pid);
            this.markDirty(pid);
          } else {
            // Unknown place — retained in the Marking (CORE-072 AC3), no bits to update.
            this.warnUnknownPlace(entry.place, t.name);
          }
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
    if (this.closed) return; // ENV-013: leave queued events for drainPendingExternalEvents()
    // In-place iteration is safe: processing is synchronous and .push() only
    // happens from microtasks which cannot interleave within this loop.
    const len = this.externalQueue.length;
    for (let i = 0; i < len; i++) {
      const event = this.externalQueue[i]!;
      try {
        const pid = this.compiled.tryPlaceId(event.place);
        this.marking.addToken(event.place, event.token);
        if (pid !== undefined) {
          this.cacheAddToken(pid, event.token);
          setBit(this.markingBitmap, pid);
          this.markDirty(pid);
        } else {
          // Unknown place — retained in the Marking (CORE-072 AC3), no bits to update.
          this.warnUnknownPlace(event.place, '');
        }

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
    // When closed, ignore external queue — processExternalEvents() won't consume it,
    // and drainPendingExternalEvents() handles it after the loop exits.
    if (this.completionQueue.length > 0 || (!this.closed && this.externalQueue.length > 0)) return;

    // Flush microtask queue: sync actions complete via .then() which schedules a
    // microtask. A single await here lets those fire before we build a full
    // Promise.race (~5 allocations). For async workloads this adds ~0.05us.
    await Promise.resolve();
    if (this.completionQueue.length > 0 || (!this.closed && this.externalQueue.length > 0)) return;
    // ENV-013: when closed with no in-flight, exit immediately for shouldTerminate()
    if (this.closed && this.inFlight.size === 0) return;

    const promises = this.awaitPromises;
    promises.length = 0;

    // 1. Any in-flight action completing (reuse array to avoid 2 intermediate allocations)
    if (this.inFlight.size > 0) {
      const arr = this.inFlightPromises;
      arr.length = 0;
      for (const f of this.inFlight.values()) arr.push(f.promise);
      promises.push(Promise.race(arr));
    }

    // When closed, only wait for in-flight completions — skip event/timer promises
    if (!this.closed) {
      // Zero means a timing boundary is already due: an earliest firing time has
      // been reached, or a deadline needs enforcing. There is nothing to wait for,
      // and with no action in flight the race below would hold only the external
      // wake-up promise — which a net with no environment places has nobody to
      // resolve, so the loop would sleep until its run budget expired. Return and
      // let the next cycle act on the boundary. Rust reaches the same outcome via
      // sleep(0); Java returns early on `millisUntilNextTimedTransition() <= 0`.
      const timerMs = this.millisUntilNextTimedTransition();
      if (timerMs === 0 && promises.length === 0) return;

      // 2. External event wake-up
      promises.push(new Promise<void>(resolve => { this.wakeUpResolve = resolve; }));

      // 3. Timer for next delayed transition
      if (timerMs > 0 && timerMs < Infinity) {
        promises.push(new Promise<void>(r => setTimeout(r, timerMs)));
      }
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

  drain(): void {
    this.draining = true;
    this.wakeUp();
  }

  close(): void {
    this.draining = true;
    this.closed = true;
    this.wakeUp();
  }

  // ======================== Event Emission ========================

  /**
   * Reports an undeclared place once (CORE-072 AC4, emitted as the EVT-013
   * log-message event). `transitionName` is the producer, empty at the
   * initial-marking and injection seams. Retention never depends on this.
   */
  private warnUnknownPlace(place: Place<any>, transitionName: string): void {
    if (this.warnedUnknownPlaces.has(place.name)) return;
    this.warnedUnknownPlaces.add(place.name);
    this.emitEvent({
      type: 'log-message',
      timestamp: Date.now(),
      transitionName,
      logger: 'libpetri.runtime',
      level: 'WARN',
      message: `unknown place '${place.name}': tokens are retained in the marking but inert `
        + '(the net declares no arc on it)',
      error: null,
      errorMessage: null,
    });
  }

  private emitEvent(event: NetEvent): void {
    if (this.eventStoreEnabled) {
      // A user EventStore.append that throws is observation failing, not control flow:
      // swallow it so a hostile store cannot unwind the orchestrator loop. One choke
      // point covers every emit site.
      try {
        this.eventStore.append(event);
      } catch (err) {
        swallowEventStoreFailure(event.type, err);
      }
    }
  }
}

/** Internal sentinel for timeout detection. */
class TimeoutSentinel extends Error {
  constructor() { super('action timeout'); this.name = 'TimeoutSentinel'; }
}
