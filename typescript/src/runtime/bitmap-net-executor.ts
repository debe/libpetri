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
import type { PetriNetExecutor, RunTimeoutPolicy } from './petri-net-executor.js';
import type { Clock } from './clock.js';
import { tokenAt } from '../core/token.js';
import { TokenInput } from '../core/token-input.js';
import { TokenOutput } from '../core/token-output.js';
import { TransitionContext } from '../core/transition-context.js';
import { noopEventStore } from '../event/event-store.js';
import { CompiledNet, WORD_SHIFT, BIT_MASK, setBit, clearBit, restartThresholds } from './compiled-net.js';
import { Marking, type PredicateSpec } from './marking.js';
import { findBinding, IncrementalMatcher } from './match-engine.js';
import { keyForPlace } from '../core/match-spec.js';
import { nameId } from '../core/name.js';
import { validateOutSpec, produceTimeoutOutput, executeAction, swallowEventStoreFailure, DEADLINE_TOLERANCE_MS, nextExecutionId } from './executor-support.js';
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
   *
   * **Set this to `0` alongside {@link BitmapNetExecutorOptions.clock}.** The default band exists to
   * absorb real timer and scheduling jitter; under an injected clock that jitter is the host's to
   * control, and leaving the band at 5ms masks exactly the deadline discrepancies a virtual clock is
   * introduced to expose (TIME-015).
   */
  deadlineToleranceMs?: number;
  /**
   * Host-supplied time source for **this executor** (TIME-015). Unset — the default — leaves the
   * executor on `performance.now()`, `Date.now()` and `setTimeout`, with no indirection on the hot
   * path. See {@link Clock} for the five-point contract an injected clock must honour.
   */
  clock?: Clock;
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
/** @internal Discarded admission callback for {@link BitmapNetExecutor.injectNoAwait}. */
const NOOP_ADMISSION = (): void => {};

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
  /**
   * Host-supplied time source (TIME-015), or `null` for the default sources. Null-checked at each
   * read rather than defaulted to a {@link systemClock} instance: the firing clock is read on every
   * orchestrator cycle, and a field test plus a direct call keeps the no-clock path as direct as it
   * was, where dispatching through an always-present object would put an interface call on it
   * (TIME-015 AC#9, PERF-010).
   */
  private readonly clock: Clock | null;
  /**
   * Aborted by {@link close} to release a host sleeping on an injected clock (TIME-015 contract 4).
   * Allocated only when a clock is supplied, so the default path carries nothing.
   */
  private readonly abortController: AbortController | null;
  /**
   * Epoch-clock reader handed to each firing's {@link TokenOutput}, or `undefined` when no
   * clock is injected (TIME-015 AC#13). Bound once rather than per firing; `undefined`
   * rather than a wrapper around `Date.now` so the default path allocates and dispatches
   * nothing it did not before.
   */
  private readonly epochNowFn: (() => number) | undefined;
  /** Stable identifier for this execution, allocated at construction (TIME-015 AC#14). */
  private readonly runId: string = nextExecutionId();
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
  /**
   * A wake-up raised while the executor was **not** parked, latched until the next
   * {@link awaitWork} consumes it.
   *
   * `wakeUp()` used to be edge-triggered — it resolved `wakeUpResolve` or did nothing — so a
   * signal raised between cycles was dropped, and the executor then parked despite the state
   * change it was told about. `drain()` is where that bit: with no queue of its own to leave a
   * trace in, a lost drain meant the loop slept to its run budget. `inject()` mostly escaped it
   * because `awaitWork` re-checks `externalQueue` on entry, but it raced the same edge
   * (ENV-005 requires an injection to wake the executor), and `close()` did too.
   *
   * Worth knowing when reading the TIME-015 tests: a host driving an injected clock drains from
   * inside `sleep`, where the signal could never be lost, because `wakeUpResolve` is installed
   * before the clock is called. So the reliable shape was the one our own tests used and the
   * racy one was what a host would write — which is why existing tests carried an
   * `await sleep(...)` before `drain()` and this went unnoticed.
   */
  private wakeUpPending = false;

  // Pre-allocated buffer for fireReadyTransitions() to avoid per-cycle allocation
  private readonly readyBuffer: { tid: number; priority: number; enabledAtMs: number }[] = [];

  /**
   * Per transition, one bit: a firing left it disabled in the intermediate marking while it
   * was marked enabled (TIME-012), so the next dirty scan that finds it enabled restarts its
   * clock. Set at fire time, cleared at the end of every scan; `anyRestartPending` lets the
   * scan skip the clear when nothing was flagged.
   */
  private readonly restartPendingWords: Uint32Array;
  private anyRestartPending = false;
  /** Per place, the count a firing must leave it at to have disabled nothing through it. */
  private readonly restartThresholds: Float64Array;
  /**
   * Undeclared place names already reported (CORE-072 AC4). Keyed by name — TS
   * Place identity is name-based — so a hot loop warns once, not per token.
   */
  private readonly warnedUnknownPlaces = new Set<string>();
  /** Transitions already warned for writing several tokens to a place their spec names once (IO-016 AC4). */
  private readonly warnedMultiplicity = new Set<string>();

  private running = false;
  private draining = false;
  private closed = false;

  /**
   * The **firing clock** (TIME-015): monotonic, arbitrary origin, milliseconds. Every enablement
   * stamp and elapsed-time decision reads here and nowhere else. Never wall time — `enabledAtMs`
   * differences would be meaningless against a clock that can step backwards over an NTP
   * correction.
   */
  private nowMs(): number {
    const c = this.clock;
    return c === null ? performance.now() : c.now();
  }

  /**
   * The **epoch clock** (TIME-015): wall-clock milliseconds, stamping event timestamps and the
   * tokens this executor mints. Its origin is unrelated to {@link nowMs}'s, so the two must never
   * be substituted for one another.
   */
  private epochMs(): number {
    const c = this.clock;
    return c === null ? Date.now() : c.epochNow();
  }

  /**
   * Time-free readiness predicate handed to an injected clock's `sleep` (TIME-015 contract 5):
   * true when non-timing work is already queued and the wait would return immediately anyway. A
   * host consults it to avoid advancing its clock past work that is already waiting. Cheap,
   * repeatable, side-effect free, and — the point of the contract — it reads no clock. Bound once
   * per executor so a host may retain it across waits.
   */
  private readonly isWorkReady = (): boolean =>
    this.completionQueue.length > 0 || (!this.closed && this.externalQueue.length > 0);

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
    // Before the first nowMs() — that read already goes through the seam.
    this.clock = options.clock ?? null;
    this.abortController = this.clock === null ? null : new AbortController();
    this.epochNowFn = this.clock === null ? undefined : (): number => this.epochMs();
    this.startMs = this.nowMs();

    const wordCount = this.compiled.wordCount;
    this.markingBitmap = new Uint32Array(wordCount);
    this.markingSnapBuffer = new Uint32Array(wordCount);
    this.firingSnapBuffer = new Uint32Array(wordCount);
    const dirtyWords = (this.compiled.transitionCount + BIT_MASK) >>> WORD_SHIFT;
    this.dirtySet = new Uint32Array(dirtyWords);
    this.dirtySnapBuffer = new Uint32Array(dirtyWords);
    this.restartPendingWords = new Uint32Array(dirtyWords);
    this.restartThresholds = restartThresholds(this.compiled);

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

  async run(timeoutMs?: number, onTimeout: RunTimeoutPolicy = 'abandon'): Promise<Marking> {
    if (timeoutMs === undefined) return this.executeLoop();

    let timer: ReturnType<typeof setTimeout> | undefined;
    let timedOut = false;
    const timeoutPromise = new Promise<never>((_, reject) => {
      timer = setTimeout(() => {
        timedOut = true;
        reject(new Error('Execution timed out'));
      }, timeoutMs);
    });
    // Held rather than inlined into the race: Promise.race walks away from the
    // loser, it does not cancel it, so the loop needs handling of its own.
    const loop = this.executeLoop();
    try {
      return await Promise.race([loop, timeoutPromise]);
    } finally {
      if (timer !== undefined) clearTimeout(timer);
      if (timedOut) {
        if (onTimeout === 'close') this.close();
        // Nobody is left to observe the abandoned loop's outcome.
        loop.catch(() => {});
      }
    }
  }

  private async executeLoop(): Promise<Marking> {
    this.running = true;
    this.emitEvent({
      type: 'execution-started',
      timestamp: this.epochMs(),
      netName: this.compiled.net.name,
      executionId: this.executionId(),
    });

    this.initializeMarkingBitmap();
    this.markAllDirty();

    this.emitEvent({
      type: 'marking-snapshot',
      timestamp: this.epochMs(),
      marking: this.snapshotMarking(),
    });

    while (this.running) {
      this.processCompletedTransitions();
      this.processExternalEvents();
      this.updateDirtyTransitions();
      // Single timestamp for this loop iteration: ensures deadline enforcement and
      // firing readiness checks use the same time reference, preventing races where
      // a transition passes the deadline check but is disabled before the fire check.
      const cycleNowMs = this.nowMs();
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
      timestamp: this.epochMs(),
      marking: this.snapshotMarking(),
    });

    this.emitEvent({
      type: 'execution-completed',
      timestamp: this.epochMs(),
      netName: this.compiled.net.name,
      executionId: this.executionId(),
      totalDurationMs: this.nowMs() - this.startMs,
    });

    return this.marking;
  }

  // ======================== Environment Place API ========================

  /**
   * Injects a token into an environment place ([ENV-004]). The returned promise reports
   * **admission** — it settles when the orchestrator reaches its external-events phase and
   * takes the token, not when the call returns.
   *
   * **Never `await` this from inside a host clock's wait** ([TIME-015]). Inside the wait the
   * orchestrator *is* the caller, so awaiting admission suspends the only thing that can grant
   * it: a self-deadlock with no error and nothing from the executor's own machinery to explain
   * it. Inject and return — or use {@link injectNoAwait}, which has no result to await. (A
   * `run(timeoutMs)` budget still fires, since it runs on the real timer rather than the
   * injected clock, so the hang surfaces as a run timeout rather than never at all.)
   */
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

  /**
   * Convenience: inject a raw value (creates token with current timestamp).
   *
   * The token is minted *by the executor*, so it is stamped from the epoch clock and follows an
   * injected one (TIME-015 AC#13) — as does every other token libpetri constructs, including
   * `ctx.output(...)` writes and action-timeout recovery outputs. Only tokens the host builds
   * itself keep their own `createdAt`; see {@link Clock.epochNow}.
   */
  async injectValue<T>(envPlace: EnvironmentPlace<T>, value: T): Promise<boolean> {
    return this.inject(envPlace, tokenAt(value, this.epochMs()));
  }

  /**
   * Enqueues an external token and returns immediately, with **no admission signal to await**
   * ([TIME-015], [ENV-004]).
   *
   * The form to call from inside a host clock's `sleep`, where awaiting {@link inject}'s
   * admission promise deadlocks the orchestrator against itself. This one cannot be held wrong:
   * there is no result. The token is admitted in the executor's own external-events phase on a
   * following cycle, exactly as an ordinary injection is — only the acknowledgement is dropped.
   *
   * Throws synchronously for an unregistered place, where {@link inject} returns a rejected
   * promise: a void method has nowhere else to put it.
   */
  injectNoAwait<T>(envPlace: EnvironmentPlace<T>, value: T): void {
    if (!this.environmentPlaces.has(envPlace.place.name)) {
      throw new Error(`Place ${envPlace.place.name} is not registered as an environment place`);
    }
    if (this.closed || this.draining) return;
    this.externalQueue.push({
      place: envPlace.place,
      token: tokenAt(value, this.epochMs()),
      resolve: NOOP_ADMISSION,
      reject: NOOP_ADMISSION,
    });
    this.wakeUp();
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
    const nowMs = this.nowMs();

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
            timestamp: this.epochMs(),
            transitionName: this.compiled.transition(tid).name,
          });
        } else if (!canNow && wasEnabled) {
          this.enabledFlags[tid] = 0;
          this.enabledTransitionCount--;
          this.enabledAtMs[tid] = -Infinity;
        } else if (canNow && wasEnabled && this.anyRestartPending
          && (this.restartPendingWords[w]! & (1 << bit)) !== 0) {
          // A firing disabled it in its intermediate marking and it is enabled again, yet it
          // is still marked enabled: this scan never saw the gap, so restart the clock here
          // (TIME-012). The loop scans between a firing and any deposit, so it normally sees
          // the gap and the fresh clock arrives as transition-enabled above; the flag keeps
          // the rule independent of that ordering.
          this.enabledAtMs[tid] = nowMs;
          this.emitEvent({
            type: 'transition-clock-restarted',
            timestamp: this.epochMs(),
            transitionName: this.compiled.transition(tid).name,
          });
        }
      }
    }

    if (this.anyRestartPending) {
      this.restartPendingWords.fill(0);
      this.anyRestartPending = false;
    }
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
          timestamp: this.epochMs(),
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

  /**
   * Flags each other transition that firing `tid` has just disabled through `pid`
   * (TIME-012). Called from {@link updateBitmapAfterConsumption} on the intermediate marking
   * M - Pre(t) (inputs consumed and resets drained, outputs not yet deposited), and only for
   * a place the firing left below its restart threshold. Removing tokens never trips an
   * inhibitor arc, so the bit tests reject every other kind of neighbour cheaply.
   */
  private flagIntermediateDisablements(tid: number, pid: number): void {
    const affected = this.compiled.affectedTransitions(pid);
    for (let j = 0; j < affected.length; j++) {
      const other = affected[j]!;
      if (other === tid || !this.enabledFlags[other] || this.inFlightFlags[other]) continue;
      const w = other >>> WORD_SHIFT;
      const mask = 1 << (other & BIT_MASK);
      if ((this.restartPendingWords[w]! & mask) !== 0) continue;
      if (!this.canEnable(other, this.markingBitmap)) {
        this.restartPendingWords[w]! |= mask;
        this.anyRestartPending = true;
      }
    }
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

    // Sort: higher priority first, then earlier enablement (FIFO), then declaration order.
    // That third key is carried by `sort` being stable (ES2019+) over a buffer filled in
    // ascending tid — i.e. declaration order — so equal `enabledAtMs` keeps it. Load-bearing
    // under an injected clock (TIME-015 AC#10): a host clock derived from millisecond wall
    // time or a replay log is non-decreasing but *not* strictly increasing, so it returns the
    // same reading across many cycles and ties here become common rather than rare. Ties must
    // fall through to declaration order per EXEC-002 AC3 — do not "optimise" this into an
    // unstable sort, and do not add a tie-break that reads the clock again.
    // This defines the deterministic scheduling contract for conflict resolution.
    // We re-sort each cycle rather than maintaining a sorted invariant because
    // enablement times change on clock restarts (TIME-012), which would require
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
        timestamp: this.epochMs(),
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
          timestamp: this.epochMs(),
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
      for (const token of removed) {
        consumed.push(token);
        this.emitEvent({
          type: 'token-removed',
          timestamp: this.epochMs(),
          placeName: arc.place.name,
          token,
        });
      }
    }

    // Update bitmap for consumed/reset places and flag the clocks this consumption
    // disabled, before any output lands (TIME-012)
    this.updateBitmapAfterConsumption(tid);

    this.emitEvent({
      type: 'transition-started',
      timestamp: this.epochMs(),
      transitionName: t.name,
      consumedTokens: consumed,
    });

    const execCtx = this.executionContextProvider?.(t.name, consumed);
    const logFn = (level: string, message: string, error?: Error) => {
      this.emitEvent({
        type: 'log-message',
        timestamp: this.epochMs(),
        transitionName: t.name,
        logger: t.name,
        level,
        message,
        error: error?.name ?? null,
        errorMessage: error?.message ?? null,
      });
    };
    const context = new TransitionContext(
      t.name, inputs, new TokenOutput(this.epochNowFn),
      t.inputPlaces(), t.readPlaces(), t.outputPlaces(),
      execCtx,
      logFn,
      t.placeAlias,
      this.epochNowFn,
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
            timestamp: this.epochMs(),
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
      startMs: this.nowMs(),
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
      const left = this.marking.tokenCount(place);
      if (left === 0) {
        clearBit(this.markingBitmap, pid);
      }
      this.markDirty(pid);
      // TIME-012. At or above its restart threshold the place still meets every requirement
      // on it, so no transition lost enablement through it; one disabled through another
      // consumed place is caught when that place comes up (bits not yet reconciled only make
      // canEnable more permissive). A ν-matched place's threshold is Infinity: a binding can
      // break at any count.
      if (left < this.restartThresholds[pid]!) this.flagIntermediateDisablements(tid, pid);
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
          timestamp: this.epochMs(),
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
          const claim = validateOutSpec(t.name, t.outputSpec, produced);
          // IO-016 AC4: a spec names a place once; several tokens into a named place
          // pass validation (IO-015 reads the produced SET) but exceed what every
          // branch-enumerating analysis models. Cheap test first: a repeat exists
          // iff there are more entries than distinct places.
          if (outputs.entries().length > produced.size) this.warnMultiplicity(t.name, outputs, claim);
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
            timestamp: this.epochMs(),
            placeName: entry.place.name,
            token: entry.token,
          });
        }
        this.markTransitionDirty(tid);

        this.emitEvent({
          type: 'transition-completed',
          timestamp: this.epochMs(),
          transitionName: t.name,
          producedTokens: produced,
          durationMs: this.nowMs() - flight.startMs,
        });
      } catch (e) {
        const err = e instanceof Error ? e : new Error(String(e));
        this.emitEvent({
          type: 'transition-failed',
          timestamp: this.epochMs(),
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
          timestamp: this.epochMs(),
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
    // Consume a latched wake-up here, *after* the flush — not on entry. The flush is a
    // yield point, so a drain()/inject()/close() from host code lands during it; checking
    // only on entry would latch that signal and then park on it anyway, which is the bug
    // this latch exists to fix. This is the last yield before the waiter is installed, so
    // any wake-up after this point finds `wakeUpResolve` non-null and resolves it directly.
    if (this.wakeUpPending) {
      this.wakeUpPending = false;
      return;
    }
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

      // 3. Wait for the next timing boundary. An injected clock owns this half of the wait
      //    (TIME-015) — only this half: the in-flight and wake-up promises above stay in the
      //    race, so a completing action, an injected external event and close() each still wake
      //    the orchestrator without the interval being waited out, exactly as by default
      //    (TIME-015 AC#8 — a seam expressed purely as a duration could not express that, and a
      //    net under an injected clock would stall where the default path kept running).
      //    `Infinity` reaches the host as "nothing timed is pending, suspend"; `0` never reaches
      //    it at all, because a boundary already due is not waited on (AC#7, above).
      if (timerMs > 0) {
        const clock = this.clock;
        if (clock !== null) {
          // abortController is non-null exactly when clock is — the constructor sets both together.
          promises.push(clock.sleep(timerMs, this.isWorkReady, this.abortController!.signal));
        } else if (timerMs < Infinity) {
          promises.push(new Promise<void>(r => setTimeout(r, timerMs)));
        }
      }
    }

    if (promises.length > 0) {
      await Promise.race(promises);
    }
    this.wakeUpResolve = null;
  }

  private millisUntilNextTimedTransition(): number {
    const nowMs = this.nowMs();
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
    const resolve = this.wakeUpResolve;
    if (resolve === null) {
      // Not parked — latch rather than drop. See wakeUpPending.
      this.wakeUpPending = true;
      return;
    }
    resolve();
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

  /**
   * Identifies this execution in the `execution-started` / `execution-completed` events.
   *
   * See {@link nextExecutionId} for why this is a counter rather than the start clock
   * reading it used to be.
   */
  executionId(): string {
    return this.runId;
  }

  drain(): void {
    this.draining = true;
    this.wakeUp();
  }

  close(): void {
    this.draining = true;
    this.closed = true;
    // Release a host sleeping on an injected clock. Its `sleep` resolves rather than rejecting
    // (TIME-015 contract 4) — this is the teardown path where a rejection escapes unobserved.
    this.abortController?.abort();
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
      timestamp: this.epochMs(),
      transitionName,
      logger: 'libpetri.runtime',
      level: 'WARN',
      message: `unknown place '${place.name}': tokens are retained in the marking but inert `
        + '(the net declares no arc on it)',
      error: null,
      errorMessage: null,
    });
  }

  /**
   * Reports, once per transition, a firing that wrote more than one token to a place
   * its output spec names once (IO-016 AC4), as the EVT-013 log-message event. The
   * tokens are deposited regardless: the diagnostic makes the under-approximation
   * every branch-enumerating analysis makes of this transition visible.
   */
  private warnMultiplicity(transitionName: string, outputs: TokenOutput, claim: ReadonlySet<string>): void {
    if (this.warnedMultiplicity.has(transitionName)) return;
    const counts = new Map<string, number>();
    for (const entry of outputs.entries()) {
      if (claim.has(entry.place.name)) counts.set(entry.place.name, (counts.get(entry.place.name) ?? 0) + 1);
    }
    const repeated: string[] = [];
    for (const [name, n] of counts) if (n > 1) repeated.push(`${name}: ${n}`);
    if (repeated.length === 0) return;
    this.warnedMultiplicity.add(transitionName);
    this.emitEvent({
      type: 'log-message',
      timestamp: this.epochMs(),
      transitionName,
      logger: 'libpetri.runtime',
      level: 'WARN',
      message: `'${transitionName}': wrote more than one token to a place its output spec names once `
        + `(${repeated.join(', ')}); branch-enumerating analyses model one token per named place, `
        + 'so this firing exceeds what they explore (IO-016)',
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
