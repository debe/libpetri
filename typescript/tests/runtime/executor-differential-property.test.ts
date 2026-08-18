/**
 * Randomized differential testing of the two executor backends, mirroring
 * `rust/libpetri-runtime/src/differential_prop_tests.rs` (the harness that
 * found Rust divergence #5).
 *
 * fast-check generates small well-formed nets and runs each one through both
 * `BitmapNetExecutor` (reference) and `PrecompiledNetExecutor` (production),
 * asserting observational equality: final marking (token values per place,
 * FIFO order), quiescence, and the timestamp-free projection of the event
 * sequence. Unlike the Rust twin this harness also covers the TIMED path —
 * delayed / window / deadline / exact timings driven by vitest fake timers
 * (`performance.now` and `setTimeout` are both faked, verified below), which
 * previously had no differential coverage in TypeScript at all.
 *
 * BOTH properties run under the fake clock, the untimed one included. The
 * executors stamp `enabledAtMs` from wall `performance.now()` (µs
 * resolution); under real timers two orchestrator cycles can collide on one
 * timestamp in one backend but not the other, silently turning a
 * FIFO-by-enablement tie into a tid-order tie and flipping the ready order —
 * a wall-clock artifact, not a semantic divergence. The fake clock gives both
 * backends the identical deterministic time base, so every failure of these
 * properties is a real finding and every seed replays. The FIFO-across-cycles
 * seam that a frozen clock cannot reach is pinned deterministically with
 * synthetic timestamps in `executor-shared-semantics.test.ts`.
 *
 * Generated fragment (untimed property): 2–8 places (number tokens), 0–4
 * initial tokens per place (values 0–9), 1–6 transitions with 1–3 distinct
 * input places (cardinality one / exactly(2) / all / atLeast(2)), 0–2 read
 * arcs, 0–1 inhibitor arcs (present 50%, mirroring Rust `prop::option::of`),
 * 0–1 reset arcs (same 50%), priority 0–3, timing `immediate`. The timed
 * property adds per-transition timing drawn from {immediate (weighted),
 * delayed(1–30), window(0–20, +0–30), deadline(1–50), exact(0–30)} — all
 * integer milliseconds, so fake-clock arithmetic is exact.
 *
 * Termination by construction: both properties run each net to quiescence,
 * so every generated net must be finite-firing. We enforce a DAG discipline —
 * every output place index of a transition is strictly greater than every
 * input place index of that same transition (read/inhibitor/reset arcs are
 * unconstrained). A firing consumes at least one token at some index <= i_max
 * (its highest input index) and deposits at most two tokens at indices >
 * i_max, so the potential `sum over tokens of 3^(P - place_index)` strictly
 * decreases on every firing (2 * 3^(P - i - 1) < 3^(P - i)). Total firings
 * are therefore bounded and no step budget is needed. Timing cannot restore
 * the potential: it only delays or force-disables firings.
 *
 * Output/action pairing is DERIVED from the generated structure, never
 * generated independently (CORE-043: an output spec must not carry
 * `passthrough()`):
 *
 * - no outputs   -> no output spec + `passthrough()` (sink idiom);
 * - single / AND -> async action echoing the derived value to every declared
 *                   output place (satisfies IO-015 validation);
 * - XOR          -> route by `value % branchCount` to exactly one branch.
 *
 * The echoed value is the first consumed token of the first input place plus
 * the front `ctx.reads(...)` value of every read arc that still holds one at
 * firing time. Folding reads in makes the oracle sensitive to the
 * EXEC-012/EXEC-013 read-peek boundary (post-input, pre-reset) — the
 * historically divergent spot in Rust — while staying total: a read place
 * drained by this very firing's input consumption contributes nothing. (When
 * a read place is also an input place of the same transition, TS `ctx.reads`
 * sees the consumed tokens first — deterministic and identical across
 * backends, which is all the oracle needs.)
 *
 * FAILURE POLICY: a divergence is a FINDING, not a flake. Let fast-check
 * shrink it, verify the minimal counterexample by hand, pin `seed` + `path`
 * in this file, and re-encode the confirmed bug as a named regression in
 * `executor-shared-semantics.test.ts`. Never weaken the oracle to make the
 * property pass; only adjust the event projection for genuinely spec-unfixed
 * nondeterminism, with documentation.
 */
import { describe, it, expect, vi } from 'vitest';
import * as fc from 'fast-check';

import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { PrecompiledNetExecutor } from '../../src/runtime/precompiled-net-executor.js';
import type { Marking } from '../../src/runtime/marking.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one, exactly, all, atLeast } from '../../src/core/in.js';
import type { In } from '../../src/core/in.js';
import { outPlace, and, xor } from '../../src/core/out.js';
import type { Out } from '../../src/core/out.js';
import { immediate, delayed, window, deadline, exact } from '../../src/core/timing.js';
import type { Timing } from '../../src/core/timing.js';
import { passthrough } from '../../src/core/transition-action.js';
import { tokenAt } from '../../src/core/token.js';
import type { Token } from '../../src/core/token.js';
import { InMemoryEventStore } from '../../src/event/event-store.js';
import type { NetEvent } from '../../src/event/net-event.js';

// ---------------------------------------------------------------------------
//  Generator model (ported from the Rust GenNet)
// ---------------------------------------------------------------------------

/**
 * Input-arc cardinality. `exactly2`/`atLeast2` fix n = 2 — enough to exercise
 * the batched-consumption paths without blowing up the state space.
 */
type GenCard = 'one' | 'exactly2' | 'all' | 'atLeast2';

/**
 * Output shape, as indices into the place vector. All variants respect the
 * DAG discipline (indices strictly above every input index); `none` is the
 * forced shape when no higher-indexed place exists.
 */
type GenOut =
  | { readonly kind: 'none' }
  | { readonly kind: 'single'; readonly a: number }
  | { readonly kind: 'and'; readonly a: number; readonly b: number }
  | { readonly kind: 'xor'; readonly a: number; readonly b: number };

type GenTiming =
  | { readonly kind: 'immediate' }
  | { readonly kind: 'delayed'; readonly afterMs: number }
  | { readonly kind: 'window'; readonly earliestMs: number; readonly latestMs: number }
  | { readonly kind: 'deadline'; readonly byMs: number }
  | { readonly kind: 'exact'; readonly atMs: number };

interface GenTrans {
  /**
   * Distinct ascending place indices paired with a cardinality. Distinct
   * because duplicate input arcs on one place are rejected at
   * `CompiledNet.compile` (CORE-030).
   */
  readonly inputs: ReadonlyArray<{ readonly place: number; readonly card: GenCard }>;
  readonly out: GenOut;
  /**
   * Distinct place indices; may overlap inputs/reset (EXEC-012/EXEC-013
   * read-peek semantics are exactly the historically buggy overlap).
   */
  readonly reads: readonly number[];
  readonly inhibitor: number | undefined;
  readonly reset: number | undefined;
  readonly priority: number;
  readonly timing: GenTiming;
}

interface GenNet {
  readonly placeCount: number;
  /** Initial token values per place, in FIFO order. */
  readonly initial: ReadonlyArray<readonly number[]>;
  readonly transitions: readonly GenTrans[];
}

const cardArb: fc.Arbitrary<GenCard> = fc.oneof(
  { weight: 3, arbitrary: fc.constant<GenCard>('one') },
  { weight: 1, arbitrary: fc.constant<GenCard>('exactly2') },
  { weight: 1, arbitrary: fc.constant<GenCard>('all') },
  { weight: 1, arbitrary: fc.constant<GenCard>('atLeast2') },
);

const immediateOnlyArb: fc.Arbitrary<GenTiming> = fc.constant({ kind: 'immediate' });

/**
 * Timing for the timed property. Immediate stays the most common so timed
 * transitions race against untimed ones. All bounds are small integers: the
 * fake clock makes them exact, and small values keep windows overlapping so
 * conflicts actually happen. `window` latest = earliest + width, so the
 * `latestMs >= earliestMs` builder validation holds by construction.
 */
const timedTimingArb: fc.Arbitrary<GenTiming> = fc.oneof(
  { weight: 4, arbitrary: immediateOnlyArb },
  {
    weight: 2,
    arbitrary: fc.integer({ min: 1, max: 30 }).map<GenTiming>(ms => ({ kind: 'delayed', afterMs: ms })),
  },
  {
    weight: 2,
    arbitrary: fc
      .tuple(fc.integer({ min: 0, max: 20 }), fc.integer({ min: 0, max: 30 }))
      .map<GenTiming>(([e, w]) => ({ kind: 'window', earliestMs: e, latestMs: e + w })),
  },
  {
    weight: 1,
    arbitrary: fc.integer({ min: 1, max: 50 }).map<GenTiming>(ms => ({ kind: 'deadline', byMs: ms })),
  },
  {
    weight: 1,
    arbitrary: fc.integer({ min: 0, max: 30 }).map<GenTiming>(ms => ({ kind: 'exact', atMs: ms })),
  },
);

function genTransition(placeCount: number, timingArb: fc.Arbitrary<GenTiming>): fc.Arbitrary<GenTrans> {
  const placeIdx = Array.from({ length: placeCount }, (_, i) => i);
  const maxInputs = Math.min(placeCount, 3);
  return fc
    .record({
      // fc.subarray preserves source order, so `ins` is distinct AND ascending
      // (mirrors proptest's sample::subsequence).
      ins: fc.subarray(placeIdx, { minLength: 1, maxLength: maxInputs }),
      cards: fc.array(cardArb, { minLength: maxInputs, maxLength: maxInputs }),
      // Output shape selector: 0 => none, 1-3 => single, 4-5 => and, 6-7 =>
      // xor (and/xor degrade to single when only one place lies above the
      // inputs).
      outKind: fc.nat({ max: 7 }),
      o1: fc.nat({ max: 0xffff }),
      o2: fc.nat({ max: 0xffff }),
      reads: fc.subarray(placeIdx, { maxLength: 2 }),
      // freq: 2 => present 50%, mirroring Rust's prop::option::of. fc's
      // default (~80% present) drowns the harness in dead transitions: a
      // uniform inhibitor usually lands on a non-empty place and kills
      // enablement (measured: firing coverage more than doubles at 50%).
      inhibitor: fc.option(fc.nat({ max: placeCount - 1 }), { nil: undefined, freq: 2 }),
      reset: fc.option(fc.nat({ max: placeCount - 1 }), { nil: undefined, freq: 2 }),
      priority: fc.integer({ min: 0, max: 3 }),
      timing: timingArb,
    })
    .map(({ ins, cards, outKind, o1, o2, reads, inhibitor, reset, priority, timing }) => {
      const inputs = ins.map((p, i) => ({ place: p, card: cards[i]! }));
      // DAG discipline: outputs live strictly above the highest input index
      // (see file header for the termination argument).
      const lo = ins[ins.length - 1]! + 1;
      const avail = placeCount - lo;
      let out: GenOut;
      if (avail === 0 || outKind === 0) {
        out = { kind: 'none' };
      } else {
        const first = lo + (o1 % avail);
        if (outKind <= 3 || avail < 2) {
          out = { kind: 'single', a: first };
        } else {
          // Second pick: offset into the remaining avail - 1 slots,
          // guaranteed distinct from `first`.
          const second = lo + (first - lo + 1 + (o2 % (avail - 1))) % avail;
          out = outKind <= 5 ? { kind: 'and', a: first, b: second } : { kind: 'xor', a: first, b: second };
        }
      }
      return { inputs, out, reads, inhibitor, reset, priority, timing };
    });
}

function genNet(timingArb: fc.Arbitrary<GenTiming>): fc.Arbitrary<GenNet> {
  return fc.integer({ min: 2, max: 8 }).chain(placeCount =>
    fc
      .record({
        initial: fc.array(fc.array(fc.integer({ min: 0, max: 9 }), { maxLength: 4, size: 'max' }), {
          minLength: placeCount,
          maxLength: placeCount,
        }),
        transitions: fc.array(genTransition(placeCount, timingArb), { minLength: 1, maxLength: 6, size: 'max' }),
      })
      .map(({ initial, transitions }) => ({ placeCount, initial, transitions })),
  );
}

// ---------------------------------------------------------------------------
//  GenNet -> (PetriNet, initial tokens)
// ---------------------------------------------------------------------------

function cardSpec(card: GenCard, p: Place<number>): In {
  switch (card) {
    case 'one': return one(p);
    case 'exactly2': return exactly(2, p);
    case 'all': return all(p);
    case 'atLeast2': return atLeast(2, p);
  }
}

function toTiming(t: GenTiming): Timing {
  switch (t.kind) {
    case 'immediate': return immediate();
    case 'delayed': return delayed(t.afterMs);
    case 'window': return window(t.earliestMs, t.latestMs);
    case 'deadline': return deadline(t.byMs);
    case 'exact': return exact(t.atMs);
  }
}

function buildNet(g: GenNet): { net: PetriNet; places: Place<number>[] } {
  const places = Array.from({ length: g.placeCount }, (_, i) => place<number>(`p${i}`));
  let builder = PetriNet.builder('differential');
  for (const p of places) builder = builder.place(p);

  g.transitions.forEach((gt, ti) => {
    let tb = Transition.builder(`t${ti}`);
    for (const { place: pi, card } of gt.inputs) {
      tb = tb.inputs(cardSpec(card, places[pi]!));
    }
    for (const ri of gt.reads) tb = tb.read(places[ri]!);
    if (gt.inhibitor !== undefined) tb = tb.inhibitor(places[gt.inhibitor]!);
    if (gt.reset !== undefined) tb = tb.reset(places[gt.reset]!);
    tb = tb.priority(gt.priority).timing(toTiming(gt.timing));

    if (gt.out.kind === 'none') {
      // Sink idiom: no output spec, passthrough action (CORE-043 pairing).
      tb = tb.action(passthrough());
    } else {
      const outIndices = gt.out.kind === 'single' ? [gt.out.a] : [gt.out.a, gt.out.b];
      const outs = outIndices.map(i => places[i]!);
      const spec: Out =
        gt.out.kind === 'single'
          ? outPlace(outs[0]!)
          : gt.out.kind === 'and'
            ? and(...outs.map(outPlace))
            : xor(...outs.map(outPlace));
      const firstIn = places[gt.inputs[0]!.place]!;
      const readPlaces = gt.reads.map(i => places[i]!);
      const isXor = gt.out.kind === 'xor';
      tb = tb.outputs(spec).action(async (ctx) => {
        // `one` consumes exactly 1 token and the batched cardinalities are
        // >= 1 (enablement guarantees it), so the first consumed value always
        // exists; `?? 0` keeps the action total regardless.
        const vals = ctx.inputs<number>(firstIn);
        let v = vals[0] ?? 0;
        for (const rp of readPlaces) {
          const rv = ctx.reads<number>(rp);
          if (rv.length > 0) v += rv[0]!;
        }
        if (isXor) {
          const n = outs.length;
          ctx.output(outs[((v % n) + n) % n]!, v);
        } else {
          for (const op of outs) ctx.output(op, v);
        }
      });
    }

    builder = builder.transition(tb.build());
  });

  return { net: builder.build(), places };
}

/** Fresh per-run token map. `tokenAt(v, 0)` keeps createdAt deterministic. */
function initialTokens(g: GenNet, places: Place<number>[]): Map<Place<any>, Token<any>[]> {
  const m = new Map<Place<any>, Token<any>[]>();
  g.initial.forEach((values, i) => {
    m.set(places[i]!, values.map(v => tokenAt(v, 0)));
  });
  return m;
}

// ---------------------------------------------------------------------------
//  Oracle
// ---------------------------------------------------------------------------

/**
 * Strongest deterministic marking signal: token VALUES per place in FIFO
 * order (counts are implied by the lengths). Actions are deterministic and
 * scheduling is priority-then-FIFO, so both backends must agree exactly.
 */
function markingValues(g: GenNet, places: Place<number>[], marking: Marking): Record<string, number[]> {
  const result: Record<string, number[]> = {};
  for (let i = 0; i < g.placeCount; i++) {
    result[`p${i}`] = marking.peekTokens(places[i]!).map(t => t.value);
  }
  return result;
}

/**
 * Deterministic projection of an event: kind plus place/transition names,
 * dropping every wall-clock field (`timestamp`, `durationMs`,
 * `totalDurationMs`, `actualDurationMs`, `executionId`). Token payloads keep
 * their VALUES (deterministic here; matches the precedent set by
 * `executor-shared-semantics.test.ts`) but not their `createdAt`.
 * `deadlineMs`/`timeoutMs` are spec constants, so they stay. Marking
 * snapshots sort their entries so the comparison pinpoints content, not
 * `Marking` insertion order.
 */
function projectEvents(events: readonly NetEvent[]): string[] {
  return events.map((e) => {
    switch (e.type) {
      case 'execution-started':
      case 'execution-completed':
        return `${e.type} ${e.netName}`;
      case 'transition-enabled':
      case 'transition-clock-restarted':
      case 'transition-started':
      case 'transition-completed':
        return `${e.type} ${e.transitionName}`;
      case 'transition-failed':
        return `${e.type} ${e.transitionName}: ${e.errorMessage}`;
      case 'transition-timed-out':
        return `${e.type} ${e.transitionName} deadline=${e.deadlineMs}`;
      case 'action-timed-out':
        return `${e.type} ${e.transitionName} ${e.timeoutMs}`;
      case 'token-added':
      case 'token-removed':
        return `${e.type} ${e.placeName}:${String(e.token.value)}`;
      case 'log-message':
        return `${e.type} ${e.transitionName} ${e.level} ${e.message}`;
      case 'marking-snapshot': {
        const entries = [...e.marking.entries()]
          .map(([name, tokens]) => `${name}=[${tokens.map(t => String(t.value)).join(',')}]`)
          .sort();
        return `${e.type} ${entries.join(' ')}`;
      }
    }
  });
}

// ---------------------------------------------------------------------------
//  Backend runner
// ---------------------------------------------------------------------------

type BackendName = 'bitmap' | 'precompiled';

function makeExecutor(
  name: BackendName,
  net: PetriNet,
  tokens: Map<Place<any>, Token<any>[]>,
  store: InMemoryEventStore,
): BitmapNetExecutor | PrecompiledNetExecutor {
  return name === 'bitmap'
    ? new BitmapNetExecutor(net, tokens, { eventStore: store })
    : new PrecompiledNetExecutor(net, tokens, { eventStore: store });
}

interface RunOutcome {
  /** True iff run() resolved (the net reached quiescence inside the budget). */
  readonly quiescent: boolean;
  readonly values: Record<string, number[]>;
  readonly projection: string[];
}

/**
 * Runs one backend to quiescence under a freshly installed fake clock
 * (verified below to fake `performance.now` — the executors read it directly —
 * plus `setTimeout`/`Date`), advancing timer-by-timer. `setImmediate` is
 * deliberately NOT faked: awaiting it yields a real macrotask boundary, which
 * drains the executor's whole microtask chain between clock advances (a
 * single `await` would interleave with it, resuming after only one microtask
 * generation). run() takes no wall timeout — the fake clock is the only time
 * source, and non-quiescence inside the advance budget throws: a DAG net that
 * fails to quiesce is itself a finding, never silently tolerated.
 */
async function runToQuiescence(name: BackendName, g: GenNet, net: PetriNet, places: Place<number>[]): Promise<RunOutcome> {
  vi.useFakeTimers({ toFake: ['setTimeout', 'clearTimeout', 'Date', 'performance'] });
  try {
    const store = new InMemoryEventStore();
    const executor = makeExecutor(name, net, initialTokens(g, places), store);
    const outcome: { settled: boolean; marking: Marking | null; failure: unknown } = {
      settled: false,
      marking: null,
      failure: null,
    };
    executor.run().then(
      (m) => { outcome.settled = true; outcome.marking = m; },
      (e) => { outcome.settled = true; outcome.failure = e; },
    );

    const macrotask = (): Promise<void> => new Promise(resolve => setImmediate(resolve));
    let advances = 0;
    for (;;) {
      await macrotask();
      if (outcome.settled) break;
      if (vi.getTimerCount() === 0) {
        // No timer pending: give the microtask chain one more macrotask to
        // either settle or park a timer, then treat a bare park as a hang.
        await macrotask();
        if (outcome.settled) break;
        if (vi.getTimerCount() === 0) {
          throw new Error(`${name}: executor parked with no pending timer and no quiescence (hang)`);
        }
        continue;
      }
      if (++advances > 10_000) {
        throw new Error(`${name}: net failed to quiesce within 10000 fake-timer advances`);
      }
      await vi.advanceTimersToNextTimerAsync();
    }
    if (outcome.failure !== null) throw outcome.failure;
    return {
      quiescent: true,
      values: markingValues(g, places, outcome.marking!),
      projection: projectEvents(store.events()),
    };
  } finally {
    vi.useRealTimers();
  }
}

// ---------------------------------------------------------------------------
//  Fake-timer environment guard
// ---------------------------------------------------------------------------

// The harness is meaningful only while vitest can fake `performance.now()`
// (the executors read it directly at ~10 sites) together with `setTimeout`.
// Verified against vitest 4.1.x; this guard fails loudly if a vitest upgrade
// ever drops 'performance' from the fakeable set, in which case the
// documented fallback is a module-level `nowFn` seam in the runtime clock
// read.
describe('fake-timer environment', () => {
  it('fakes performance.now together with setTimeout', async () => {
    vi.useFakeTimers({ toFake: ['setTimeout', 'clearTimeout', 'Date', 'performance'] });
    try {
      const t0 = performance.now();
      let fired = false;
      setTimeout(() => { fired = true; }, 123);
      await vi.advanceTimersByTimeAsync(123);
      expect(fired).toBe(true);
      expect(performance.now() - t0).toBe(123);
    } finally {
      vi.useRealTimers();
    }
  });
});

// ---------------------------------------------------------------------------
//  The differential properties
// ---------------------------------------------------------------------------

// No findings to date: both properties are green at the committed bounds.
// TS was already verified immune to Rust divergence #5 (snapshot recheck +
// microtask-deferred deposits, pinned in executor-shared-semantics.test.ts).
// If a run ever fails here, follow the FAILURE POLICY in the file header and
// pin the reported `seed`/`path` as `{ seed: ..., path: '...', endOnFailure:
// true }` in the fc.assert parameters below while the divergence is open.

async function assertBackendsAgree(g: GenNet): Promise<void> {
  const { net, places } = buildNet(g);
  // Sequential runs, each under its own freshly installed fake clock, so
  // both backends observe the identical deterministic time base.
  const bitmap = await runToQuiescence('bitmap', g, net, places);
  const precompiled = await runToQuiescence('precompiled', g, net, places);

  expect(precompiled.values, 'final markings diverged (token values per place, FIFO order)')
    .toEqual(bitmap.values);
  expect(precompiled.quiescent, 'quiescence diverged').toBe(bitmap.quiescent);
  expect(precompiled.projection, 'event-sequence projections diverged')
    .toEqual(bitmap.projection);
}

describe('executor differential property', () => {
  it(
    'backends agree on generated untimed nets (marking, quiescence, events)',
    async () => {
      await fc.assert(
        fc.asyncProperty(genNet(immediateOnlyArb), assertBackendsAgree),
        { numRuns: 100 },
      );
    },
    60_000,
  );

  it(
    'backends agree on generated timed nets under the fake clock',
    async () => {
      await fc.assert(
        fc.asyncProperty(genNet(timedTimingArb), assertBackendsAgree),
        { numRuns: 60 },
      );
    },
    120_000,
  );
});
