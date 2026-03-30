/**
 * @module precompiled-net-executor
 *
 * High-performance executor for Typed Coloured Time Petri Nets.
 *
 * **Architecture**: Uses `PrecompiledNet` for all transition/place data, replacing
 * Map lookups and object traversals with typed-array indexing. Token storage uses
 * simple per-place arrays, leveraging V8's optimized small-array shift/push.
 *
 * **Execution loop**: Same 5-phase structure as `BitmapNetExecutor`:
 * 1. Process completed transitions — drain completionQueue, validate outputs
 * 2. Process external events — inject tokens from EnvironmentPlaces
 * 3. Update dirty transitions — sparse enablement via `canEnableSparse()`
 * 4. Enforce deadlines — gated by `anyDeadlines` flag
 * 5. Fire ready transitions — opcode dispatch or priority-queue path
 *
 * **Key optimizations over BitmapNetExecutor**:
 * - Opcode-based consumption (switch on int vs object dispatch)
 * - Cached place references (avoids compiled.place(pid) indirection)
 * - Sparse enablement masks (skip zero words)
 * - Lazy Marking sync (arrays are sole source of truth during execution)
 * - Flat-array in-flight tracking (no Map overhead)
 *
 * @see PrecompiledNet for the precompiled data representation
 * @see BitmapNetExecutor for the reference implementation
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
import { WORD_SHIFT, BIT_MASK } from './compiled-net.js';
import { Marking } from './marking.js';
import { PrecompiledNet, CONSUME_ONE, CONSUME_N, CONSUME_ALL, CONSUME_ATLEAST, RESET } from './precompiled-net.js';
import { validateOutSpec, produceTimeoutOutput } from './executor-support.js';
import { OutViolationError } from './out-violation-error.js';

const DEADLINE_TOLERANCE_MS = 5;

// ==================== Types ====================

interface ExternalEvent<T = any> {
  place: Place<T>;
  token: Token<T>;
  resolve: (value: boolean) => void;
  reject: (err: Error) => void;
}

export interface PrecompiledNetExecutorOptions {
  eventStore?: EventStore;
  environmentPlaces?: Set<EnvironmentPlace<any>>;
  executionContextProvider?: (transitionName: string, consumed: Token<any>[]) => Map<string, unknown>;
  /** Skip output spec validation for trusted actions (CONC-026). */
  skipOutputValidation?: boolean;
  /** Reuse a precompiled program (avoids recompilation). */
  program?: PrecompiledNet;
}

/**
 * High-performance executor using `PrecompiledNet`.
 *
 * Implements `PetriNetExecutor` with the same semantics as `BitmapNetExecutor`
 * but with flat-array optimizations for lower per-transition overhead.
 */
export class PrecompiledNetExecutor implements PetriNetExecutor {
  private readonly program: PrecompiledNet;
  private readonly eventStore: EventStore;
  private readonly environmentPlaces: Set<string>;
  private readonly hasEnvironmentPlaces: boolean;
  private readonly executionContextProvider?: (transitionName: string, consumed: Token<any>[]) => Map<string, unknown>;
  private readonly skipOutputValidation: boolean;
  private readonly startMs: number;
  private readonly eventStoreEnabled: boolean;

  // ==================== Token Storage ====================
  /** Per-place token arrays, indexed by pid. */
  private readonly tokenQueues: Token<any>[][];

  // ==================== Marking Bitmap ====================
  private readonly markingBitmap: Uint32Array;

  // ==================== Transition State ====================
  private readonly dirtyBitmap: Uint32Array;
  private readonly dirtyScanBuffer: Uint32Array;
  private readonly enabledAtMs: Float64Array;
  private readonly inFlightFlags: Uint8Array;
  private readonly enabledFlags: Uint8Array;
  private readonly transitionWords: number;

  // ==================== Enabled Count ====================
  private enabledTransitionCount = 0;

  // ==================== In-Flight Tracking ====================
  private readonly inFlightPromises: (Promise<void> | null)[];
  private readonly inFlightContexts: (TransitionContext | null)[];
  private readonly inFlightConsumed: (Token<any>[] | null)[];
  private readonly inFlightStartMs: Float64Array;
  private readonly inFlightResolves: ((() => void) | null)[];
  private readonly inFlightErrors: (unknown | null)[];
  private inFlightCount = 0;

  // ==================== Reset-Clock Detection ====================
  private readonly pendingResetWords: Uint32Array;
  private hasPendingResets = false;

  // ==================== Queues ====================
  private readonly completionQueue: number[] = [];
  private readonly externalQueue: ExternalEvent[] = [];
  private wakeUpResolve: (() => void) | null = null;

  // ==================== Reusable Buffers ====================
  private readonly markingSnapBuffer: Uint32Array;
  private readonly firingSnapBuffer: Uint32Array;
  private readonly awaitPromises: Promise<void>[] = [];
  private readonly racePromises: Promise<void>[] = [];

  // Pre-allocated buffer for fireReadyGeneral()
  private readonly readyBuffer: { tid: number; priority: number; enabledAtMs: number }[] = [];

  // ==================== Lifecycle ====================
  private running = false;
  private draining = false;
  private closed = false;

  // ==================== Lazy Marking ====================
  private marking: Marking | null = null;

  constructor(
    net: PetriNet,
    initialTokens: Map<Place<any>, Token<any>[]>,
    options: PrecompiledNetExecutorOptions = {},
  ) {
    this.program = options.program ?? PrecompiledNet.compile(net);
    this.eventStore = options.eventStore ?? noopEventStore();
    this.environmentPlaces = new Set(
      [...(options.environmentPlaces ?? [])].map(ep => ep.place.name)
    );
    this.hasEnvironmentPlaces = this.environmentPlaces.size > 0;
    this.executionContextProvider = options.executionContextProvider;
    this.skipOutputValidation = options.skipOutputValidation ?? false;
    this.startMs = performance.now();
    this.eventStoreEnabled = this.eventStore.isEnabled();

    const prog = this.program;
    const pc = prog.placeCount;
    const tc = prog.transitionCount;
    const wc = prog.wordCount;

    // ==================== Token Queues ====================
    this.tokenQueues = new Array(pc);
    for (let pid = 0; pid < pc; pid++) {
      this.tokenQueues[pid] = [];
    }

    // Load initial tokens
    for (const [place, tokens] of initialTokens) {
      const pid = prog.compiled.placeId(place);
      const q = this.tokenQueues[pid]!;
      for (const token of tokens) {
        q.push(token);
      }
    }

    // ==================== Marking Bitmap ====================
    this.markingBitmap = new Uint32Array(wc);

    // ==================== Transition State ====================
    this.transitionWords = (tc + BIT_MASK) >>> WORD_SHIFT;
    this.dirtyBitmap = new Uint32Array(this.transitionWords);
    this.dirtyScanBuffer = new Uint32Array(this.transitionWords);
    this.enabledAtMs = new Float64Array(tc);
    this.enabledAtMs.fill(-Infinity);
    this.inFlightFlags = new Uint8Array(tc);
    this.enabledFlags = new Uint8Array(tc);

    // ==================== In-Flight Arrays ====================
    this.inFlightPromises = new Array(tc).fill(null);
    this.inFlightContexts = new Array(tc).fill(null);
    this.inFlightConsumed = new Array(tc).fill(null);
    this.inFlightStartMs = new Float64Array(tc);
    this.inFlightResolves = new Array(tc).fill(null);
    this.inFlightErrors = new Array(tc).fill(null);

    // ==================== Reset Detection ====================
    this.pendingResetWords = new Uint32Array(wc);

    // ==================== Snapshot Buffers ====================
    this.markingSnapBuffer = new Uint32Array(wc);
    this.firingSnapBuffer = new Uint32Array(wc);
  }

  // ======================== Bitmap Helpers ========================

  private markTransitionDirty(tid: number): void {
    this.dirtyBitmap[tid >>> WORD_SHIFT]! |= (1 << (tid & BIT_MASK));
  }

  private markDirty(pid: number): void {
    const tids = this.program.placeToTransitions[pid]!;
    for (let i = 0; i < tids.length; i++) {
      this.markTransitionDirty(tids[i]!);
    }
  }

  private setMarkingBit(pid: number): void {
    this.markingBitmap[pid >>> WORD_SHIFT]! |= (1 << (pid & BIT_MASK));
  }

  private clearMarkingBit(pid: number): void {
    this.markingBitmap[pid >>> WORD_SHIFT]! &= ~(1 << (pid & BIT_MASK));
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
    const prog = this.program;

    this.emitEvent({
      type: 'execution-started',
      timestamp: Date.now(),
      netName: prog.compiled.net.name,
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

      const cycleNowMs = performance.now();
      if (prog.anyDeadlines) this.enforceDeadlines(cycleNowMs);

      if (this.shouldTerminate()) break;

      this.fireReadyTransitions(cycleNowMs);
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
      netName: prog.compiled.net.name,
      executionId: this.executionId(),
      totalDurationMs: performance.now() - this.startMs,
    });

    return this.syncMarkingFromQueues();
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

  async injectValue<T>(envPlace: EnvironmentPlace<T>, value: T): Promise<boolean> {
    return this.inject(envPlace, tokenOf(value));
  }

  // ======================== Initialize ========================

  private initializeMarkingBitmap(): void {
    for (let pid = 0; pid < this.program.placeCount; pid++) {
      if (this.tokenQueues[pid]!.length > 0) {
        this.setMarkingBit(pid);
      }
    }
  }

  private markAllDirty(): void {
    const tw = this.transitionWords;
    const tc = this.program.transitionCount;
    for (let w = 0; w < tw - 1; w++) {
      this.dirtyBitmap[w] = 0xFFFFFFFF;
    }
    if (tw > 0) {
      const lastBits = tc & BIT_MASK;
      this.dirtyBitmap[tw - 1] = lastBits === 0 ? 0xFFFFFFFF : (1 << lastBits) - 1;
    }
  }

  private shouldTerminate(): boolean {
    if (this.closed) {
      // ENV-013: immediate close — wait for in-flight actions to complete
      return this.inFlightCount === 0 && this.completionQueue.length === 0;
    }
    if (this.hasEnvironmentPlaces) {
      return this.draining
        && this.enabledTransitionCount === 0
        && this.inFlightCount === 0
        && this.completionQueue.length === 0;
    }
    return this.enabledTransitionCount === 0
      && this.inFlightCount === 0
      && this.completionQueue.length === 0;
  }

  // ======================== Dirty Set Processing ========================

  private updateDirtyTransitions(): void {
    const nowMs = performance.now();
    const prog = this.program;
    const tc = prog.transitionCount;

    // Snapshot marking bitmap
    const markingSnap = this.markingSnapBuffer;
    markingSnap.set(this.markingBitmap);

    // Snapshot-and-clear dirty set
    const tw = this.transitionWords;
    const dirtySnap = this.dirtyScanBuffer;
    for (let w = 0; w < tw; w++) {
      dirtySnap[w] = this.dirtyBitmap[w]!;
      this.dirtyBitmap[w] = 0;
    }

    // Iterate dirty transitions using Kernighan's bit trick
    for (let w = 0; w < tw; w++) {
      let word = dirtySnap[w]!;
      if (word === 0) continue;
      dirtySnap[w] = 0; // clear for next cycle
      while (word !== 0) {
        const bit = Math.clz32(word & -word) ^ 31;
        const tid = (w << WORD_SHIFT) | bit;
        word &= word - 1;

        if (tid >= tc) break;
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
            transitionName: prog.compiled.transition(tid).name,
          });
        } else if (!canNow && wasEnabled) {
          this.enabledFlags[tid] = 0;
          this.enabledTransitionCount--;
          this.enabledAtMs[tid] = -Infinity;
        } else if (canNow && wasEnabled && this.hasInputFromResetPlace(tid)) {
          this.enabledAtMs[tid] = nowMs;
          this.emitEvent({
            type: 'transition-clock-restarted',
            timestamp: Date.now(),
            transitionName: prog.compiled.transition(tid).name,
          });
        }
      }
    }

    if (this.hasPendingResets) {
      this.pendingResetWords.fill(0);
      this.hasPendingResets = false;
    }
  }

  private enforceDeadlines(nowMs: number): void {
    const prog = this.program;
    const tc = prog.transitionCount;

    for (let tid = 0; tid < tc; tid++) {
      if (!prog.hasDeadline[tid]) continue;
      if (!this.enabledFlags[tid] || this.inFlightFlags[tid]) continue;

      const elapsed = nowMs - this.enabledAtMs[tid]!;
      const latestMs = prog.latestMs[tid]!;
      if (elapsed > latestMs + DEADLINE_TOLERANCE_MS) {
        this.enabledFlags[tid] = 0;
        this.enabledTransitionCount--;
        this.enabledAtMs[tid] = -Infinity;
        this.emitEvent({
          type: 'transition-timed-out',
          timestamp: Date.now(),
          transitionName: prog.compiled.transition(tid).name,
          deadlineMs: latestMs,
          actualDurationMs: elapsed,
        });
      }
    }
  }

  private canEnable(tid: number, markingSnap: Uint32Array): boolean {
    const prog = this.program;

    // Sparse bitmap check
    if (!prog.canEnableSparse(tid, markingSnap)) return false;

    // Cardinality check
    const cardCheck = prog.cardinalityChecks[tid] ?? null;
    if (cardCheck !== null) {
      for (let i = 0; i < cardCheck.placeIds.length; i++) {
        const pid = cardCheck.placeIds[i]!;
        if (this.tokenQueues[pid]!.length < cardCheck.requiredCounts[i]!) return false;
      }
    }

    // Guard check
    if (prog.hasGuards[tid]) {
      const t = prog.compiled.transition(tid);
      for (const spec of t.inputSpecs) {
        if (!spec.guard) continue;
        const required = spec.type === 'one' ? 1
          : spec.type === 'exactly' ? spec.count
          : spec.type === 'at-least' ? spec.minimum
          : 1;
        if (this.countMatching(prog.compiled.placeId(spec.place), spec.guard) < required) return false;
      }
    }

    return true;
  }

  private countMatching(pid: number, guard: (value: any) => boolean): number {
    const q = this.tokenQueues[pid]!;
    let matching = 0;
    for (let i = 0; i < q.length; i++) {
      if (guard(q[i]!.value)) matching++;
    }
    return matching;
  }

  private removeFirstMatching(pid: number, guard: (value: any) => boolean): Token<any> | null {
    const q = this.tokenQueues[pid]!;
    for (let i = 0; i < q.length; i++) {
      if (guard(q[i]!.value)) {
        return q.splice(i, 1)[0]!;
      }
    }
    return null;
  }

  private hasInputFromResetPlace(tid: number): boolean {
    if (!this.hasPendingResets) return false;
    const inputMask = this.program.inputPlaceMaskWords[tid]!;
    for (let w = 0; w < inputMask.length; w++) {
      if ((inputMask[w]! & this.pendingResetWords[w]!) !== 0) return true;
    }
    return false;
  }

  // ======================== Firing ========================

  private fireReadyTransitions(nowMs: number): void {
    if (this.program.allImmediate && this.program.allSamePriority) {
      this.fireReadyImmediate();
      return;
    }
    this.fireReadyGeneral(nowMs);
  }

  /**
   * Fast path for nets where all transitions are immediate and same priority.
   * Simple linear scan matching BitmapNetExecutor's pattern.
   */
  private fireReadyImmediate(): void {
    const tc = this.program.transitionCount;

    for (let tid = 0; tid < tc; tid++) {
      if (!this.enabledFlags[tid] || this.inFlightFlags[tid]) continue;
      if (this.canEnable(tid, this.markingBitmap)) {
        this.fireTransition(tid);
      } else {
        this.enabledFlags[tid] = 0;
        this.enabledTransitionCount--;
        this.enabledAtMs[tid] = -Infinity;
      }
    }
  }

  private fireReadyGeneral(nowMs: number): void {
    const prog = this.program;
    const tc = prog.transitionCount;

    // Collect ready transitions into pre-allocated buffer
    const ready = this.readyBuffer;
    ready.length = 0;
    for (let tid = 0; tid < tc; tid++) {
      if (!this.enabledFlags[tid] || this.inFlightFlags[tid]) continue;
      const elapsedMs = nowMs - this.enabledAtMs[tid]!;
      if (prog.earliestMs[tid]! <= elapsedMs) {
        ready.push({ tid, priority: prog.priorities[tid]!, enabledAtMs: this.enabledAtMs[tid]! });
      }
    }
    if (ready.length === 0) return;

    // Sort: higher priority first, then earlier enablement (FIFO)
    ready.sort((a, b) => {
      const prioCmp = b.priority - a.priority;
      if (prioCmp !== 0) return prioCmp;
      return a.enabledAtMs - b.enabledAtMs;
    });

    // Take a fresh snapshot for re-checking
    const freshSnap = this.firingSnapBuffer;
    freshSnap.set(this.markingBitmap);
    for (const entry of ready) {
      const { tid } = entry;
      if (this.enabledFlags[tid] && this.canEnable(tid, freshSnap)) {
        this.fireTransition(tid);
        freshSnap.set(this.markingBitmap);
      } else {
        this.enabledFlags[tid] = 0;
        this.enabledTransitionCount--;
        this.enabledAtMs[tid] = -Infinity;
      }
    }
  }

  private fireTransition(tid: number): void {
    const prog = this.program;
    const t = prog.compiled.transition(tid);
    const consumed: Token<any>[] = [];
    const inputs = new TokenInput();

    // ==================== Opcode Dispatch ====================
    if (prog.hasGuards[tid]) {
      this.fireTransitionGuarded(tid, t, inputs, consumed);
    } else {
      const ops = prog.consumeOps[tid]!;
      let pc = 0;
      while (pc < ops.length) {
        const opcode = ops[pc++]!;
        switch (opcode) {
          case CONSUME_ONE: {
            const pid = ops[pc++]!;
            const token = this.tokenQueues[pid]!.shift()!;
            consumed.push(token);
            inputs.add(prog.places[pid]!, token);
            this.emitEvent({
              type: 'token-removed',
              timestamp: Date.now(),
              placeName: prog.places[pid]!.name,
              token,
            });
            break;
          }
          case CONSUME_N: {
            const pid = ops[pc++]!;
            const count = ops[pc++]!;
            const place = prog.places[pid]!;
            for (let i = 0; i < count; i++) {
              const token = this.tokenQueues[pid]!.shift()!;
              consumed.push(token);
              inputs.add(place, token);
              this.emitEvent({
                type: 'token-removed',
                timestamp: Date.now(),
                placeName: place.name,
                token,
              });
            }
            break;
          }
          case CONSUME_ALL: {
            const pid = ops[pc++]!;
            const place = prog.places[pid]!;
            const q = this.tokenQueues[pid]!;
            const count = q.length;
            for (let i = 0; i < count; i++) {
              const token = q.shift()!;
              consumed.push(token);
              inputs.add(place, token);
              this.emitEvent({
                type: 'token-removed',
                timestamp: Date.now(),
                placeName: place.name,
                token,
              });
            }
            break;
          }
          case CONSUME_ATLEAST: {
            const pid = ops[pc++]!;
            pc++; // skip minimum (already validated in canEnable)
            const place = prog.places[pid]!;
            const q = this.tokenQueues[pid]!;
            const count = q.length;
            for (let i = 0; i < count; i++) {
              const token = q.shift()!;
              consumed.push(token);
              inputs.add(place, token);
              this.emitEvent({
                type: 'token-removed',
                timestamp: Date.now(),
                placeName: place.name,
                token,
              });
            }
            break;
          }
          case RESET: {
            const pid = ops[pc++]!;
            const place = prog.places[pid]!;
            const tokens = this.tokenQueues[pid]!.splice(0);
            this.pendingResetWords[pid >>> WORD_SHIFT]! |= (1 << (pid & BIT_MASK));
            this.hasPendingResets = true;
            for (const token of tokens) {
              consumed.push(token);
              this.emitEvent({
                type: 'token-removed',
                timestamp: Date.now(),
                placeName: place.name,
                token,
              });
            }
            break;
          }
        }
      }
    }

    // Read arcs
    const readPids = prog.readOps[tid]!;
    for (let i = 0; i < readPids.length; i++) {
      const pid = readPids[i]!;
      const q = this.tokenQueues[pid]!;
      if (q.length > 0) {
        inputs.add(prog.places[pid]!, q[0]!);
      }
    }

    // Update bitmap after consumption
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

    // Track in-flight
    let resolveInFlight!: () => void;
    const completionPromise = new Promise<void>(r => { resolveInFlight = r; });

    this.inFlightPromises[tid] = completionPromise;
    this.inFlightContexts[tid] = context;
    this.inFlightConsumed[tid] = consumed;
    this.inFlightStartMs[tid] = performance.now();
    this.inFlightResolves[tid] = resolveInFlight;
    this.inFlightErrors[tid] = null;

    actionPromise.then(
      () => {
        this.completionQueue.push(tid);
        this.wakeUp();
        resolveInFlight();
      },
      (err) => {
        this.inFlightErrors[tid] = err;
        this.completionQueue.push(tid);
        this.wakeUp();
        resolveInFlight();
      },
    );

    this.inFlightFlags[tid] = 1;
    this.inFlightCount++;
    this.enabledFlags[tid] = 0;
    this.enabledTransitionCount--;
    this.enabledAtMs[tid] = -Infinity;
  }

  private fireTransitionGuarded(_tid: number, t: Transition, inputs: TokenInput, consumed: Token<any>[]): void {
    const prog = this.program;

    for (const inSpec of t.inputSpecs) {
      const pid = prog.compiled.placeId(inSpec.place);
      let toConsume: number;
      switch (inSpec.type) {
        case 'one': toConsume = 1; break;
        case 'exactly': toConsume = inSpec.count; break;
        case 'all':
          toConsume = inSpec.guard
            ? this.countMatching(pid, inSpec.guard)
            : this.tokenQueues[pid]!.length;
          break;
        case 'at-least':
          toConsume = inSpec.guard
            ? this.countMatching(pid, inSpec.guard)
            : this.tokenQueues[pid]!.length;
          break;
      }

      const guardFn = inSpec.guard;
      for (let i = 0; i < toConsume; i++) {
        const token = guardFn
          ? this.removeFirstMatching(pid, guardFn)
          : this.tokenQueues[pid]!.shift() ?? null;
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

    // Reset arcs
    for (const arc of t.resets) {
      const pid = prog.compiled.placeId(arc.place);
      const tokens = this.tokenQueues[pid]!.splice(0);
      this.pendingResetWords[pid >>> WORD_SHIFT]! |= (1 << (pid & BIT_MASK));
      this.hasPendingResets = true;
      for (const token of tokens) {
        consumed.push(token);
        this.emitEvent({
          type: 'token-removed',
          timestamp: Date.now(),
          placeName: arc.place.name,
          token,
        });
      }
    }
  }

  private updateBitmapAfterConsumption(tid: number): void {
    const pids = this.program.consumptionPlaceIds[tid]!;
    for (let i = 0; i < pids.length; i++) {
      const pid = pids[i]!;
      if (this.tokenQueues[pid]!.length === 0) {
        this.clearMarkingBit(pid);
      }
      this.markDirty(pid);
    }
  }

  // ======================== Completion Processing ========================

  private processCompletedTransitions(): void {
    if (this.completionQueue.length === 0) return;
    const prog = this.program;
    const len = this.completionQueue.length;

    for (let i = 0; i < len; i++) {
      const tid = this.completionQueue[i]!;
      const context = this.inFlightContexts[tid]!;
      const error = this.inFlightErrors[tid];
      const startMs = this.inFlightStartMs[tid]!;
      const t = prog.compiled.transition(tid);

      // Clear in-flight state
      this.inFlightFlags[tid] = 0;
      this.inFlightPromises[tid] = null;
      this.inFlightContexts[tid] = null;
      this.inFlightConsumed[tid] = null;
      this.inFlightResolves[tid] = null;
      this.inFlightErrors[tid] = null;
      this.inFlightCount--;

      if (error) {
        const err = error instanceof Error ? error : new Error(String(error));
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
        const outputs = context.rawOutput();

        // Validate output
        if (!this.skipOutputValidation && t.outputSpec !== null) {
          const simplePid = prog.simpleOutputPlaceId[tid]!;
          if (simplePid >= 0) {
            const produced = outputs.placesWithTokens();
            if (!produced.has(prog.places[simplePid]!.name)) {
              throw new OutViolationError(
                `'${t.name}': output does not satisfy declared spec`
              );
            }
          } else if (simplePid === -1) {
            const produced = outputs.placesWithTokens();
            const result = validateOutSpec(t.name, t.outputSpec, produced);
            if (result === null) {
              throw new OutViolationError(
                `'${t.name}': output does not satisfy declared spec`
              );
            }
          }
        }

        // Add output tokens to queues
        const produced: Token<any>[] = [];
        for (const entry of outputs.entries()) {
          const pid = prog.compiled.placeId(entry.place);
          this.tokenQueues[pid]!.push(entry.token);
          produced.push(entry.token);
          this.setMarkingBit(pid);
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
          durationMs: performance.now() - startMs,
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
    const prog = this.program;
    const len = this.externalQueue.length;

    for (let i = 0; i < len; i++) {
      const event = this.externalQueue[i]!;
      try {
        const pid = prog.compiled.placeId(event.place);
        this.tokenQueues[pid]!.push(event.token);
        this.setMarkingBit(pid);
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

  private async awaitWork(): Promise<void> {
    // When closed, ignore external queue — processExternalEvents() won't consume it,
    // and drainPendingExternalEvents() handles it after the loop exits.
    if (this.completionQueue.length > 0 || (!this.closed && this.externalQueue.length > 0)) return;

    await Promise.resolve();
    if (this.completionQueue.length > 0 || (!this.closed && this.externalQueue.length > 0)) return;
    // ENV-013: when closed with no in-flight, exit immediately for shouldTerminate()
    if (this.closed && this.inFlightCount === 0) return;

    const promises = this.awaitPromises;
    promises.length = 0;

    // In-flight completion
    if (this.inFlightCount > 0) {
      const arr = this.racePromises;
      arr.length = 0;
      for (let tid = 0; tid < this.program.transitionCount; tid++) {
        if (this.inFlightPromises[tid] !== null) {
          arr.push(this.inFlightPromises[tid]!);
        }
      }
      if (arr.length > 0) {
        promises.push(Promise.race(arr));
      }
    }

    // When closed, only wait for in-flight completions — skip event/timer promises
    if (!this.closed) {
      // External event wake-up
      promises.push(new Promise<void>(resolve => { this.wakeUpResolve = resolve; }));

      // Timer for next timed transition
      const timerMs = this.millisUntilNextTimedTransition();
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
    const prog = this.program;
    const tc = prog.transitionCount;
    let minWaitMs = Infinity;

    for (let tid = 0; tid < tc; tid++) {
      if (!this.enabledFlags[tid]) continue;

      const enabledMs = this.enabledAtMs[tid]!;
      const elapsedMs = nowMs - enabledMs;

      const eMs = prog.earliestMs[tid]!;
      const remainingEarliest = eMs - elapsedMs;
      if (remainingEarliest <= 0) return 0;
      minWaitMs = Math.min(minWaitMs, remainingEarliest);

      if (prog.hasDeadline[tid]) {
        const lMs = prog.latestMs[tid]!;
        const remainingDeadline = lMs - elapsedMs;
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

  private hasDirtyBits(): boolean {
    for (let w = 0; w < this.transitionWords; w++) {
      if (this.dirtyBitmap[w] !== 0) return true;
    }
    return false;
  }

  // ======================== Lazy Marking Sync ========================

  private syncMarkingFromQueues(): Marking {
    const prog = this.program;
    const m = Marking.empty();
    for (let pid = 0; pid < prog.placeCount; pid++) {
      const q = this.tokenQueues[pid]!;
      if (q.length === 0) continue;
      const place = prog.places[pid]!;
      for (let i = 0; i < q.length; i++) {
        m.addToken(place, q[i]!);
      }
    }
    this.marking = m;
    return m;
  }

  // ======================== State Inspection ========================

  getMarking(): Marking {
    return this.marking ?? this.syncMarkingFromQueues();
  }

  private snapshotMarking(): ReadonlyMap<string, readonly Token<any>[]> {
    const prog = this.program;
    const snap = new Map<string, readonly Token<any>[]>();
    for (let pid = 0; pid < prog.placeCount; pid++) {
      const q = this.tokenQueues[pid]!;
      if (q.length === 0) continue;
      snap.set(prog.places[pid]!.name, [...q]);
    }
    return snap;
  }

  isQuiescent(): boolean {
    return this.enabledTransitionCount === 0 && this.inFlightCount === 0;
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

  private emitEvent(event: NetEvent): void {
    if (this.eventStoreEnabled) {
      this.eventStore.append(event);
    }
  }
}

class TimeoutSentinel extends Error {
  constructor() { super('action timeout'); this.name = 'TimeoutSentinel'; }
}
