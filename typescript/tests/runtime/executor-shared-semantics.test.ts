/**
 * Cross-executor shared-semantics tests: the BitmapNetExecutor (reference) and
 * the PrecompiledNetExecutor (production) must agree on the canonical behaviors
 * pinned by the spec after the Rust divergence audit:
 *
 * - EXEC-013 AC4: in-firing order is input consumption → read-arc peeks → reset
 *   draining, so read(p)+reset(p) on the same place observes the pre-reset token.
 * - CORE-030 AC3: two input arcs on one place are rejected at compile time.
 * - CORE-072 AC3/AC4: tokens on places the compiled net does not know are
 *   retained in the observable marking, never silently dropped — on every seam
 *   (initial marking, produce, external inject) — and each such place is
 *   reported once as an EVT-013 log-message event.
 * - EXEC-002 AC3/AC4, CONC-023 AC4: within a priority level, ready transitions
 *   fire in enablement-time order (FIFO), not declaration/tid order.
 * - EXEC-001/EXEC-003: outputs of a firing are deposited in loop step 1 of a
 *   LATER cycle, never mid-pass — same-cycle outputs are invisible to the
 *   intra-pass enablement recheck (Rust differential-harness divergence #5).
 */
import { describe, it, expect } from 'vitest';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { PrecompiledNetExecutor } from '../../src/runtime/precompiled-net-executor.js';
import { CompiledNet } from '../../src/runtime/compiled-net.js';
import type { Marking } from '../../src/runtime/marking.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, environmentPlace } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { delayed } from '../../src/core/timing.js';
import { tokenOf } from '../../src/core/token.js';
import type { Token } from '../../src/core/token.js';
import { InMemoryEventStore, eventsOfType } from '../../src/event/event-store.js';
import type { LogMessage, NetEvent } from '../../src/event/net-event.js';

/** Both executors expose the same `new Executor(net, tokens)` + `run(ms)` API. */
interface Backend {
  readonly name: string;
  make(net: PetriNet, tokens: Map<Place<any>, Token<any>[]>): { run(ms: number): Promise<Marking> };
}

const backends: Backend[] = [
  { name: 'BitmapNetExecutor', make: (net, t) => new BitmapNetExecutor(net, t) },
  { name: 'PrecompiledNetExecutor', make: (net, t) => new PrecompiledNetExecutor(net, t) },
];

function initialTokens(...entries: [Place<any>, Token<any>[]][]): Map<Place<any>, Token<any>[]> {
  return new Map(entries);
}

// ==================== EXEC-013: read before reset ====================

for (const backend of backends) {
  describe(`read + reset on the same place (${backend.name})`, () => {
    it('read observes the pre-reset front token; place is empty after (EXEC-013)', async () => {
      const trigger = place<string>('TRIGGER');
      const p = place<string>('P');
      const out = place<string>('OUT');

      const t = Transition.builder('T')
        .inputs(one(trigger))
        .read(p)
        .reset(p)
        .outputs(outPlace(out))
        .action(async (ctx) => {
          // Canonical order: consumption → read peeks → reset draining. The
          // read must see the front token even though the same firing resets p.
          ctx.output(out, ctx.read(p));
        })
        .build();
      const net = PetriNet.builder('N').transition(t).build();

      const marking = await backend
        .make(net, initialTokens(
          [trigger, [tokenOf('go')]],
          [p, [tokenOf('front'), tokenOf('back')]],
        ))
        .run(5000);

      expect(marking.peekTokens(out).map(tok => tok.value)).toEqual(['front']);
      expect(marking.tokenCount(p)).toBe(0);
    });
  });
}

// ==================== CORE-030: duplicate input places ====================

describe('duplicate input arcs on one place (CORE-030)', () => {
  function duplicateInputNet(): PetriNet {
    const p = place<string>('P');
    const out = place<string>('OUT');
    const t = Transition.builder('T')
      .inputs(one(p), one(p))
      .outputs(outPlace(out))
      .action(async (ctx) => { ctx.output(out, ctx.input(p)); })
      .build();
    return PetriNet.builder('N').transition(t).build();
  }

  it('compilation rejects with a descriptive error', () => {
    expect(() => CompiledNet.compile(duplicateInputNet())).toThrowError(/two input arcs/);
    expect(() => CompiledNet.compile(duplicateInputNet())).toThrowError(/CORE-030/);
  });

  for (const backend of backends) {
    it(`${backend.name} construction rejects`, () => {
      const p = place<string>('P');
      expect(() => backend.make(duplicateInputNet(), initialTokens([p, [tokenOf('x')]])))
        .toThrowError(/two input arcs/);
    });
  }
});

// ==================== CORE-072: unknown-place token retention ====================

for (const backend of backends) {
  describe(`unknown-place token retention (${backend.name})`, () => {
    it('initial marking naming an undeclared place is retained, not dropped (CORE-072)', async () => {
      const input = place<string>('IN');
      const out = place<string>('OUT');
      // Never referenced by any transition or the net's declared places.
      const orphan = place<string>('ORPHAN');

      const t = Transition.builder('T')
        .inputs(one(input))
        .outputs(outPlace(out))
        .action(async (ctx) => { ctx.output(out, ctx.input(input)); })
        .build();
      const net = PetriNet.builder('N').transition(t).build();

      const marking = await backend
        .make(net, initialTokens(
          [input, [tokenOf('go')]],
          [orphan, [tokenOf('keep-1'), tokenOf('keep-2')]],
        ))
        .run(5000);

      // Normal execution is unaffected...
      expect(marking.peekTokens(out).map(tok => tok.value)).toEqual(['go']);
      // ...and the orphan tokens reappear in the observable marking.
      expect(marking.peekTokens(orphan).map(tok => tok.value)).toEqual(['keep-1', 'keep-2']);
    });

    it('token produced into an undeclared place is retained, not dropped (CORE-072)', async () => {
      const input = place<string>('IN');
      const out = place<string>('OUT');
      const ghost = place<string>('GHOST');

      const t = Transition.builder('T')
        .inputs(one(input))
        .outputs(outPlace(out))
        .action(async (ctx) => {
          ctx.output(out, ctx.input(input));
          // Widen the declared-outputs guard: composition seams can hand the
          // executor an output place the compiled net never saw (CORE-072 AC3).
          (ctx as any).allowedOutputs.add(ghost.name);
          ctx.output(ghost, 'ghost');
        })
        .build();
      const net = PetriNet.builder('N').transition(t).build();

      const marking = await backend
        .make(net, initialTokens([input, [tokenOf('go')]]))
        .run(5000);

      expect(marking.peekTokens(out).map(tok => tok.value)).toEqual(['go']);
      expect(marking.peekTokens(ghost).map(tok => tok.value)).toEqual(['ghost']);
    });
  });
}

// Injection needs the executor's environment-place options + inject/drain API,
// so these construct the executors directly instead of going through `backends`.
for (const backendName of ['BitmapNetExecutor', 'PrecompiledNetExecutor'] as const) {
  describe(`unknown-place injection (${backendName})`, () => {
    it('token injected into an undeclared environment place is retained (CORE-072)', async () => {
      const input = place<string>('IN');
      const out = place<string>('OUT');
      // Registered as an environment place but never referenced by the net.
      const ghost = environmentPlace<string>('GHOST');

      const t = Transition.builder('T')
        .inputs(one(input))
        .outputs(outPlace(out))
        .action(async (ctx) => { ctx.output(out, ctx.input(input)); })
        .build();
      const net = PetriNet.builder('N').transition(t).build();
      const tokens = initialTokens([input, [tokenOf('go')]]);
      const options = { environmentPlaces: new Set([ghost]) };
      const executor = backendName === 'BitmapNetExecutor'
        ? new BitmapNetExecutor(net, tokens, options)
        : new PrecompiledNetExecutor(net, tokens, options);

      const runPromise = executor.run(5000);
      const accepted = await executor.inject(ghost, tokenOf('ghost'));
      executor.drain();
      const marking = await runPromise;

      expect(accepted).toBe(true);
      expect(marking.peekTokens(out).map(tok => tok.value)).toEqual(['go']);
      expect(marking.peekTokens(ghost.place).map(tok => tok.value)).toEqual(['ghost']);
    });
  });
}

// ==================== CORE-072 AC4: one warning per unknown place ====================

/** The contract's unknown-place diagnostic shape (CORE-072 AC4, EVT-013). */
function expectUnknownPlaceWarning(
  warning: LogMessage,
  placeName: string,
  transitionName: string,
): void {
  expect(warning.logger).toBe('libpetri.runtime');
  expect(warning.level).toBe('WARN');
  expect(warning.transitionName).toBe(transitionName);
  expect(warning.error).toBeNull();
  expect(warning.errorMessage).toBeNull();
  expect(warning.message).toBe(
    `unknown place '${placeName}': tokens are retained in the marking but inert `
    + '(the net declares no arc on it)',
  );
}

for (const backendName of ['BitmapNetExecutor', 'PrecompiledNetExecutor'] as const) {
  describe(`unknown-place diagnostic (${backendName})`, () => {
    it('warns once per distinct unknown place, not once per token (CORE-072 AC4)', async () => {
      const input = place<string>('IN');
      const out = place<string>('OUT');
      const ghost = place<string>('GHOST');
      const other = place<string>('OTHER');

      const t = Transition.builder('T')
        .inputs(one(input))
        .outputs(outPlace(out))
        .action(async (ctx) => {
          ctx.output(out, ctx.input(input));
          const allowed = (ctx as any).allowedOutputs as Set<string>;
          allowed.add(ghost.name);
          allowed.add(other.name);
          ctx.output(ghost, 'g1');
          ctx.output(ghost, 'g2');
          ctx.output(other, 'o1');
        })
        .build();
      const net = PetriNet.builder('N').transition(t).build();
      const store = new InMemoryEventStore();
      // Three firings x three unknown-place writes = nine writes, two places.
      const tokens = initialTokens([input, [tokenOf('a'), tokenOf('b'), tokenOf('c')]]);
      const executor = backendName === 'BitmapNetExecutor'
        ? new BitmapNetExecutor(net, tokens, { eventStore: store })
        : new PrecompiledNetExecutor(net, tokens, { eventStore: store });

      const marking = await executor.run(5000);

      const warnings = eventsOfType(store, 'log-message');
      expect(warnings.length).toBe(2);
      expectUnknownPlaceWarning(warnings[0]!, 'GHOST', 'T');
      expectUnknownPlaceWarning(warnings[1]!, 'OTHER', 'T');

      // The diagnostic does not gate retention (AC3 is a MUST, AC4 a SHOULD).
      expect(marking.peekTokens(ghost).map(tok => tok.value)).toEqual(
        ['g1', 'g2', 'g1', 'g2', 'g1', 'g2'],
      );
      expect(marking.peekTokens(other).length).toBe(3);
    });

    it('initial-marking and injection seams warn once with an empty transition name', async () => {
      const input = place<string>('IN');
      const out = place<string>('OUT');
      const orphan = place<string>('ORPHAN');
      const ghost = environmentPlace<string>('GHOST');

      const t = Transition.builder('T')
        .inputs(one(input))
        .outputs(outPlace(out))
        .action(async (ctx) => { ctx.output(out, ctx.input(input)); })
        .build();
      const net = PetriNet.builder('N').transition(t).build();
      const store = new InMemoryEventStore();
      const tokens = initialTokens(
        [input, [tokenOf('go')]],
        [orphan, [tokenOf('keep-1'), tokenOf('keep-2')]],
      );
      const options = { eventStore: store, environmentPlaces: new Set([ghost]) };
      const executor = backendName === 'BitmapNetExecutor'
        ? new BitmapNetExecutor(net, tokens, options)
        : new PrecompiledNetExecutor(net, tokens, options);

      const runPromise = executor.run(5000);
      await executor.inject(ghost, tokenOf('g1'));
      await executor.inject(ghost, tokenOf('g2'));
      executor.drain();
      const marking = await runPromise;

      const warnings = eventsOfType(store, 'log-message');
      expect(warnings.length).toBe(2);
      expectUnknownPlaceWarning(warnings[0]!, 'ORPHAN', '');
      expectUnknownPlaceWarning(warnings[1]!, 'GHOST', '');

      expect(marking.peekTokens(orphan).length).toBe(2);
      expect(marking.peekTokens(ghost.place).map(tok => tok.value)).toEqual(['g1', 'g2']);
    });
  });
}

// ==================== EXEC-002 / CONC-023: ready order within a priority ====================

// Deterministic test of the firing-order seam: both executors resolve
// same-priority conflicts by enablement time (FIFO), then declaration/tid order
// for equal timestamps. Wall-clock cannot deterministically place two
// transitions enabled in different cycles into the SAME firing pass (the wake
// timer targets the earlier ready time), so the test drives the internal
// fireReadyGeneral seam directly with synthetic enablement timestamps — the
// same technique as the Rust ready-queue tests.
describe('ready order within a priority level (EXEC-002, CONC-023)', () => {
  interface Scenario {
    net: PetriNet;
    tLate: Transition;
    tEarly: Transition;
    tokens: Map<Place<any>, Token<any>[]>;
  }

  /**
   * Two same-priority delayed transitions competing for one SHARED token.
   * tLate is declared FIRST (lower tid) — declaration order is deliberately
   * OPPOSITE to enablement order, so tid-order scheduling would pick tLate.
   */
  function conflictScenario(): Scenario {
    const shared = place<string>('SHARED');
    const pLate = place<string>('P_LATE');
    const pEarly = place<string>('P_EARLY');

    const tLate = Transition.builder('tLate')
      .inputs(one(pLate), one(shared))
      .timing(delayed(1))
      .action(async () => {})
      .build();
    const tEarly = Transition.builder('tEarly')
      .inputs(one(pEarly), one(shared))
      .timing(delayed(1))
      .action(async () => {})
      .build();

    const net = PetriNet.builder('N').transitions(tLate, tEarly).build();
    const tokens = initialTokens(
      [shared, [tokenOf('s')]],
      [pLate, [tokenOf('l')]],
      [pEarly, [tokenOf('e')]],
    );
    return { net, tLate, tEarly, tokens };
  }

  /**
   * Seeds executor internals with synthetic enablement timestamps and runs one
   * general firing pass; returns the names of the transitions that started.
   */
  function fireOnce(
    executor: BitmapNetExecutor | PrecompiledNetExecutor,
    store: InMemoryEventStore,
    scenario: Scenario,
    lateEnabledAtMs: number,
    earlyEnabledAtMs: number,
  ): string[] {
    const internals = executor as any;
    const compiled: CompiledNet = internals.compiled ?? internals.program.compiled;
    const lateTid = compiled.transitionId(scenario.tLate);
    const earlyTid = compiled.transitionId(scenario.tEarly);

    // Initialize the place-presence bitmap from the initial tokens.
    internals.initializeMarkingBitmap.call(executor);

    internals.enabledFlags[lateTid] = 1;
    internals.enabledFlags[earlyTid] = 1;
    internals.enabledTransitionCount = 2;
    internals.enabledAtMs[lateTid] = lateEnabledAtMs;
    internals.enabledAtMs[earlyTid] = earlyEnabledAtMs;

    // Both delayed(1) transitions are past their earliest at now=3000.
    internals.fireReadyGeneral(3000);

    return eventsOfType(store, 'transition-started').map(e => e.transitionName);
  }

  for (const backendName of ['BitmapNetExecutor', 'PrecompiledNetExecutor'] as const) {
    function makeExecutor(scenario: Scenario, store: InMemoryEventStore) {
      return backendName === 'BitmapNetExecutor'
        ? new BitmapNetExecutor(scenario.net, scenario.tokens, { eventStore: store })
        : new PrecompiledNetExecutor(scenario.net, scenario.tokens, { eventStore: store });
    }

    describe(backendName, () => {
      it('earlier-enabled transition wins the conflict despite higher tid', () => {
        const scenario = conflictScenario();
        const store = new InMemoryEventStore();
        const executor = makeExecutor(scenario, store);

        // tEarly (declared second, higher tid) became enabled in an EARLIER
        // cycle than tLate (declared first, lower tid).
        const started = fireOnce(executor, store, scenario, 2000, 1000);

        // tEarly fires first and takes the SHARED token; tLate is disabled.
        expect(started).toEqual(['tEarly']);
      });

      it('enablement-order win is symmetric (control: earlier-enabled lower tid wins)', () => {
        const scenario = conflictScenario();
        const store = new InMemoryEventStore();
        const executor = makeExecutor(scenario, store);

        const started = fireOnce(executor, store, scenario, 1000, 2000);

        expect(started).toEqual(['tLate']);
      });
    });
  }
});


// ==================== EXEC-001 / EXEC-003: same-cycle outputs are invisible intra-pass ====================

// Pins Rust differential-harness divergence #5. During one firing pass, the
// reference semantics recheck subsequent ready transitions against a
// post-consumption, PRE-output-deposit view of the marking: outputs deposit in
// loop step 1 of a later cycle (EXEC-001), and losers of a conflict are
// disabled by the winner's consumption (EXEC-003). A buggy executor that lets
// a same-cycle sync-action deposit become visible to the intra-pass recheck
// fires [t_high, t_low, t_high] instead of starving t_low entirely.
//
// Witness: a holds 3 tokens, b holds 1. t_high (priority 1) consumes one(a),
// resets b, and its action synchronously produces one token back to b. t_low
// (priority 0) consumes one(a) and reads b. Each pass fires t_high first; the
// recheck of t_low must see b EMPTY (reset applied, produced token not yet
// deposited), so t_high fires 3x and t_low never fires. In TypeScript this
// holds structurally on both loops: actions complete through the microtask
// queue into completionQueue, drained at the top of the NEXT cycle, and the
// recheck reads the firing-pass snapshot of the presence bitmap.
describe('same-cycle outputs invisible to intra-pass recheck (EXEC-001, EXEC-003)', () => {
  function witness() {
    const a = place<string>('a');
    const b = place<string>('b');
    const tLow = Transition.builder('t_low')
      .inputs(one(a))
      .read(b)
      .priority(0)
      .action(async () => {})
      .build();
    const tHigh = Transition.builder('t_high')
      .inputs(one(a))
      .reset(b)
      .outputs(outPlace(b))
      .priority(1)
      .action(async (ctx) => { ctx.output(b, 'produced'); })
      .build();
    const net = PetriNet.builder('N').transitions(tLow, tHigh).build();
    const tokens = initialTokens(
      [a, [tokenOf('a1'), tokenOf('a2'), tokenOf('a3')]],
      [b, [tokenOf('b1')]],
    );
    return { net, tokens, a, b };
  }

  /** Normalizes an event to a timestamp-free shape for cross-executor comparison. */
  function describeEvent(e: NetEvent): string {
    switch (e.type) {
      case 'transition-enabled': return `enabled:${e.transitionName}`;
      case 'transition-started': return `started:${e.transitionName}`;
      case 'transition-completed': return `completed:${e.transitionName}`;
      case 'token-added': return `+${e.placeName}:${String(e.token.value)}`;
      case 'token-removed': return `-${e.placeName}:${String(e.token.value)}`;
      default: return e.type;
    }
  }

  async function runWitness(backend: Backend) {
    const { net, tokens, a, b } = witness();
    const store = new InMemoryEventStore();
    const marking = await (backend.name === 'BitmapNetExecutor'
      ? new BitmapNetExecutor(net, tokens, { eventStore: store })
      : new PrecompiledNetExecutor(net, tokens, { eventStore: store })
    ).run(5000);
    return {
      started: eventsOfType(store, 'transition-started').map(e => e.transitionName),
      finalA: marking.peekTokens(a).map(tok => tok.value),
      finalB: marking.peekTokens(b).map(tok => tok.value),
      sequence: store.events().map(describeEvent),
    };
  }

  for (const backend of backends) {
    it(`${backend.name}: t_high fires 3x, t_low starved by pre-deposit recheck`, async () => {
      const result = await runWitness(backend);

      // The recheck after each t_high firing sees b empty (reset applied, the
      // produced token not yet deposited), so t_low never wins a pass.
      expect(result.started).toEqual(['t_high', 't_high', 't_high']);
      // a: all three tokens consumed by t_high. b: only the LAST produced
      // token survives (each firing's reset drains the previous deposit).
      expect(result.finalA).toEqual([]);
      expect(result.finalB).toEqual(['produced']);
    });
  }

  it('both executors emit the identical event sequence', async () => {
    const [bitmap, precompiled] = await Promise.all(backends.map(runWitness));
    expect(precompiled!.sequence).toEqual(bitmap!.sequence);
  });
});
