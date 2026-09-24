/**
 * **EXEC-042 — Terminal places**, over both executors, plus the termination reason they now
 * report ([EXEC-041] AC3), ENV-014 AC9 (a parked executor answers a read at once) and TIME-015
 * AC11 (an action's promise completed from inside the host's wait is admitted a cycle later).
 *
 * TypeScript separates a firing's start from its deposit: every action's outputs — a
 * synchronous action's included — land in the completion phase of a later cycle. So a
 * transition that was ready in the same pass as the one that marks a terminal place has
 * already *started* when the terminal deposit happens; what EXEC-042 strictness requires here
 * is that its result is never deposited and that nothing starts after the deposit. AC4 below
 * pins both halves.
 */
import { describe, it, expect } from 'vitest';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import type { BitmapNetExecutorOptions } from '../../src/runtime/bitmap-net-executor.js';
import { PrecompiledNetExecutor } from '../../src/runtime/precompiled-net-executor.js';
import { isComplete } from '../../src/runtime/petri-net-executor.js';
import type { Clock } from '../../src/runtime/clock.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, environmentPlace } from '../../src/core/place.js';
import type { Place, EnvironmentPlace } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace, and } from '../../src/core/out.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { Interface } from '../../src/core/interface.js';
import { FusionSet } from '../../src/core/fusion-set.js';
import { tokenOf } from '../../src/core/token.js';
import type { Token } from '../../src/core/token.js';
import type { TransitionContext } from '../../src/core/transition-context.js';
import { InMemoryEventStore, eventsOfType } from '../../src/event/event-store.js';

type Backend = 'bitmap' | 'precompiled';
const BACKENDS: Backend[] = ['bitmap', 'precompiled'];

function makeExecutor(
  backend: Backend,
  net: PetriNet,
  tokens: Map<Place<any>, Token<any>[]>,
  options: BitmapNetExecutorOptions = {},
): BitmapNetExecutor | PrecompiledNetExecutor {
  return backend === 'bitmap'
    ? new BitmapNetExecutor(net, tokens, options)
    : new PrecompiledNetExecutor(net, tokens, options);
}

function initial(...entries: [Place<any>, Token<any>[]][]): Map<Place<any>, Token<any>[]> {
  return new Map(entries);
}

/** A promise with its resolver, for an action whose completion the test controls. */
function deferred(): { promise: Promise<void>; resolve: () => void } {
  let resolve!: () => void;
  const promise = new Promise<void>(r => { resolve = r; });
  return { promise, resolve };
}

const tick = (ms = 5): Promise<void> => new Promise(r => setTimeout(r, ms));

/** Synchronous copy action: writes `value` to each of `places` and resolves at once. */
function writes(...places: Place<any>[]) {
  return async (ctx: TransitionContext): Promise<void> => {
    for (const p of places) ctx.output(p, 'v');
  };
}

describe('EXEC-042 — terminal places', () => {
  describe.each(BACKENDS)('%s backend', (backend) => {
    it('AC1: an initial marking that marks a terminal place fires nothing and ends terminal', async () => {
      const A = place<string>('A');
      const B = place<string>('B');
      const DONE = place<string>('DONE');
      const t = Transition.builder('t').inputs(one(A)).outputs(outPlace(B)).action(writes(B)).build();
      const net = PetriNet.builder('ac1').transition(t).terminal(DONE).build();
      const store = new InMemoryEventStore();
      const exec = makeExecutor(backend, net, initial([A, [tokenOf('a')]], [DONE, [tokenOf('d')]]),
        { eventStore: store });

      expect(exec.terminationReason()).toBe('running');
      const marking = await exec.run(1000);

      expect(exec.terminationReason()).toBe('terminal');
      expect(isComplete(exec.terminationReason())).toBe(true);
      expect(marking.tokenCount(A)).toBe(1);
      expect(marking.tokenCount(B)).toBe(0);
      expect(eventsOfType(store, 'transition-started')).toHaveLength(0);
    });

    it('AC2: a completion that marks a terminal place ends the run without waiting for the other arm', async () => {
      const START = place<string>('START');
      const FAST = place<string>('FAST');
      const SLOW = place<string>('SLOW');
      const DONE = place<string>('DONE');
      const LATE = place<string>('LATE');
      const gate = deferred();
      const fork = Transition.builder('fork').inputs(one(START)).outputs(and(outPlace(FAST), outPlace(SLOW)))
        .action(writes(FAST, SLOW)).build();
      const finish = Transition.builder('finish').inputs(one(FAST)).outputs(outPlace(DONE))
        .action(async (ctx) => { await tick(1); ctx.output(DONE, 'done'); }).build();
      const slow = Transition.builder('slow').inputs(one(SLOW)).outputs(outPlace(LATE))
        .action(async (ctx) => { await gate.promise; ctx.output(LATE, 'late'); }).build();
      const net = PetriNet.builder('ac2').transitions(fork, finish, slow).terminal(DONE).build();
      const exec = makeExecutor(backend, net, initial([START, [tokenOf('s')]]));

      // The slow arm never completes on its own: the run ending at all shows it was not awaited.
      const marking = await exec.run(2000);
      expect(exec.terminationReason()).toBe('terminal');
      expect(marking.tokenCount(DONE)).toBe(1);
      expect(marking.tokenCount(LATE)).toBe(0);
      // ENV-014: the abandoned arm still reports work in flight.
      expect(exec.snapshot().actionInFlight).toBe(true);

      // Its late result is discarded, never deposited.
      gate.resolve();
      await tick(10);
      expect(exec.getMarking().tokenCount(LATE)).toBe(0);
      expect(exec.snapshot().marking.get('LATE')).toBeUndefined();
    });

    it('AC3: an injection into a terminal environment place ends the run; an event queued behind it is refused', async () => {
      const IN = environmentPlace<string>('IN');
      const HALT = environmentPlace<string>('HALT');
      const OUT = place<string>('OUT');
      const t = Transition.builder('t').inputs(one(IN.place)).outputs(outPlace(OUT)).action(writes(OUT)).build();
      const net = PetriNet.builder('ac3').transition(t).place(HALT.place).terminal(HALT.place).build();
      const exec = makeExecutor(backend, net, new Map(),
        { environmentPlaces: new Set<EnvironmentPlace<any>>([IN, HALT]) });

      const done = exec.run(2000);
      await tick();
      const halted = exec.inject(HALT, tokenOf('halt'));
      const behind = exec.inject(IN, tokenOf('in'));
      const marking = await done;

      expect(await halted).toBe(true);
      expect(await behind).toBe(false);
      expect(exec.terminationReason()).toBe('terminal');
      expect(marking.tokenCount(HALT.place)).toBe(1);
      expect(marking.tokenCount(IN.place)).toBe(0);
      expect(marking.tokenCount(OUT)).toBe(0);
      // And nothing is accepted afterwards.
      expect(await exec.inject(IN, tokenOf('after'))).toBe(false);
    });

    it('AC4: a synchronous output that marks a terminal place stops the pass — the lower-priority result never lands and nothing starts after it', async () => {
      const A = place<string>('A');
      const B = place<string>('B');
      const X = place<string>('X');
      const Y = place<string>('Y');
      const OUT2 = place<string>('OUT2');
      const DONE = place<string>('DONE');
      const first = Transition.builder('first').priority(10).inputs(one(A))
        .outputs(and(outPlace(DONE), outPlace(X))).action(writes(DONE, X)).build();
      const second = Transition.builder('second').priority(0).inputs(one(B))
        .outputs(outPlace(OUT2)).action(writes(OUT2)).build();
      const downstream = Transition.builder('downstream').inputs(one(X))
        .outputs(outPlace(Y)).action(writes(Y)).build();
      const net = PetriNet.builder('ac4').transitions(first, second, downstream).terminal(DONE).build();
      const store = new InMemoryEventStore();
      const exec = makeExecutor(backend, net, initial([A, [tokenOf('a')]], [B, [tokenOf('b')]]),
        { eventStore: store });

      const marking = await exec.run(1000);

      expect(exec.terminationReason()).toBe('terminal');
      // The firing that made the deposit completes atomically: all its outputs land.
      expect(marking.tokenCount(DONE)).toBe(1);
      expect(marking.tokenCount(X)).toBe(1);
      // `second` was ready in the same pass. TS had already started it (its consumed token is
      // gone), but its result is queued behind the terminal deposit and is never admitted.
      expect(marking.tokenCount(OUT2)).toBe(0);
      expect(eventsOfType(store, 'transition-completed').map(e => e.transitionName)).toEqual(['first']);
      // Nothing starts after the deposit, although `downstream` is enabled by it.
      expect(marking.tokenCount(Y)).toBe(0);
      expect(eventsOfType(store, 'transition-started').map(e => e.transitionName))
        .not.toContain('downstream');
      // No diagnostic: the stop was designed ([EVT-013] AC5).
      expect(eventsOfType(store, 'log-message').filter(e => e.level === 'WARN')).toHaveLength(0);
    });

    it('AC4: same-priority immediate fast path stops the same way', async () => {
      const A = place<string>('A');
      const B = place<string>('B');
      const OUT2 = place<string>('OUT2');
      const DONE = place<string>('DONE');
      const first = Transition.builder('first').inputs(one(A)).outputs(outPlace(DONE)).action(writes(DONE)).build();
      const second = Transition.builder('second').inputs(one(B)).outputs(outPlace(OUT2)).action(writes(OUT2)).build();
      const net = PetriNet.builder('ac4-fast').transitions(first, second).terminal(DONE).build();
      const exec = makeExecutor(backend, net, initial([A, [tokenOf('a')]], [B, [tokenOf('b')]]));

      const marking = await exec.run(1000);
      expect(exec.terminationReason()).toBe('terminal');
      expect(marking.tokenCount(DONE)).toBe(1);
      expect(marking.tokenCount(OUT2)).toBe(0);
    });

    it('a net without terminals keeps ending quiescent', async () => {
      const A = place<string>('A');
      const B = place<string>('B');
      const t = Transition.builder('t').inputs(one(A)).outputs(outPlace(B)).action(writes(B)).build();
      const net = PetriNet.builder('plain').transition(t).build();
      const exec = makeExecutor(backend, net, initial([A, [tokenOf('a')]]));
      const marking = await exec.run(1000);
      expect(marking.tokenCount(B)).toBe(1);
      expect(exec.terminationReason()).toBe('quiescent');
      expect(isComplete('quiescent')).toBe(true);
    });
  });
});

describe('EXEC-041 AC3 — termination reasons', () => {
  describe.each(BACKENDS)('%s backend', (backend) => {
    it('close() ends the run closed, a truncation', async () => {
      const IN = environmentPlace<string>('IN');
      const OUT = place<string>('OUT');
      const t = Transition.builder('t').inputs(one(IN.place)).outputs(outPlace(OUT)).action(writes(OUT)).build();
      const net = PetriNet.builder('closed').transition(t).build();
      const exec = makeExecutor(backend, net, new Map(), { environmentPlaces: new Set([IN]) });
      const done = exec.run(2000);
      await tick();
      exec.close();
      await done;
      expect(exec.terminationReason()).toBe('closed');
      expect(isComplete(exec.terminationReason())).toBe(false);
    });

    it('an expired run budget still rejects, and reports stopped', async () => {
      const A = place<string>('A');
      const B = place<string>('B');
      const never = new Promise<void>(() => {});
      const t = Transition.builder('t').inputs(one(A)).outputs(outPlace(B))
        .action(async () => { await never; }).build();
      const net = PetriNet.builder('stopped').transition(t).build();
      const exec = makeExecutor(backend, net, initial([A, [tokenOf('a')]]));
      await expect(exec.run(20)).rejects.toThrow('Execution timed out');
      expect(exec.terminationReason()).toBe('stopped');
      expect(isComplete(exec.terminationReason())).toBe(false);
    });

    it('an expired budget under the close policy is still reported stopped', async () => {
      const A = place<string>('A');
      const B = place<string>('B');
      const gate = deferred();
      const t = Transition.builder('t').inputs(one(A)).outputs(outPlace(B))
        .action(async () => { await gate.promise; }).build();
      const net = PetriNet.builder('stopped-close').transition(t).build();
      const exec = makeExecutor(backend, net, initial([A, [tokenOf('a')]]));
      await expect(exec.run(20, 'close')).rejects.toThrow('Execution timed out');
      gate.resolve();
      await tick(10);
      expect(exec.terminationReason()).toBe('stopped');
    });
  });
});

describe('EXEC-042 — build and composition rules', () => {
  const T = place<string>('T');
  const A = place<string>('A');
  const B = place<string>('B');

  it('AC5: a terminal place that a transition consumes is rejected at build, naming both', () => {
    const t = Transition.builder('eats').inputs(one(T)).outputs(outPlace(B)).build();
    expect(() => PetriNet.builder('bad').transition(t).terminal(T).build())
      .toThrow(/terminal place 'T' is an input of transition 'eats'/);
  });

  it('AC5: a terminal place that a transition reads is rejected at build, naming both', () => {
    const t = Transition.builder('peeks').inputs(one(A)).read(T).outputs(outPlace(B)).build();
    expect(() => PetriNet.builder('bad').transition(t).terminal(T).build())
      .toThrow(/terminal place 'T' is a read-arc place of transition 'peeks'/);
  });

  it('an inhibitor or output arc on a terminal place is well-formed; the place joins the net', () => {
    const t = Transition.builder('t').inputs(one(A)).inhibitor(T).outputs(outPlace(B)).build();
    const net = PetriNet.builder('ok').transition(t).terminal(T).build();
    expect([...net.terminals].map(p => p.name)).toEqual(['T']);
    const standalone = PetriNet.builder('ok2').transition(
      Transition.builder('u').inputs(one(A)).outputs(outPlace(B)).build(),
    ).terminal(T).build();
    expect([...standalone.places].some(p => p.name === 'T')).toBe(true);
  });

  it('terminals keep declaration order and survive bindActions', () => {
    const U = place<string>('U');
    const t = Transition.builder('t').inputs(one(A)).outputs(outPlace(B)).build();
    const net = PetriNet.builder('order').transition(t).terminal(U).terminal(T).terminal(U).build();
    expect([...net.terminals].map(p => p.name)).toEqual(['U', 'T']);
    const bound = net.bindActions({ t: writes(B) });
    expect([...bound.terminals].map(p => p.name)).toEqual(['U', 'T']);
  });

  it('a fused terminal is remapped to the canonical place', () => {
    const canonical = place<string>('canonical');
    const member = place<string>('member');
    const t1 = Transition.builder('t1').inputs(one(A)).outputs(outPlace(canonical)).build();
    const t2 = Transition.builder('t2').inputs(one(B)).outputs(outPlace(member)).build();
    const net = PetriNet.builder('fused').transitions(t1, t2).terminal(member)
      .fuse(FusionSet.of('f', canonical, member)).build();
    expect([...net.terminals].map(p => p.name)).toEqual(['canonical']);
    expect([...net.places].some(p => p.name === 'member')).toBe(false);
  });

  it('a fused terminal that becomes an input is rejected', () => {
    const canonical = place<string>('canonical');
    const member = place<string>('member');
    const t1 = Transition.builder('t1').inputs(one(canonical)).outputs(outPlace(B)).build();
    const t2 = Transition.builder('t2').inputs(one(A)).outputs(outPlace(member)).build();
    expect(() => PetriNet.builder('fused').transitions(t1, t2).terminal(member)
      .fuse(FusionSet.of('f', canonical, member)).build())
      .toThrow(/terminal place 'canonical' is an input of transition 't1'/);
  });

  describe('AC6: a subnet body that declares terminals is rejected', () => {
    function terminalBody(): SubnetDef<void> {
      const t = Transition.builder('t').inputs(one(A)).outputs(outPlace(T)).build();
      const body = PetriNet.builder('Body').transition(t).terminal(T).build();
      return SubnetDef.fromNet(body, Interface.builder().build());
    }

    it('by compose(SubnetDef)', () => {
      expect(() => PetriNet.builder('host').compose(terminalBody()))
        .toThrow(/compose\(SubnetDef\): subnet 'Body' declares terminal place\(s\) 'T'/);
    });

    it('by instantiate', () => {
      expect(() => terminalBody().instantiate('one'))
        .toThrow(/instantiate: subnet 'Body' declares terminal place\(s\) 'T'/);
    });
  });
});

/**
 * A host clock whose `sleep` only resolves on abort, running a hook at a point where the
 * executor is provably parked in its wait.
 */
class HostClock implements Clock {
  monotonicMs = 0;
  onSleep: (() => void) | null = null;
  now(): number { return this.monotonicMs; }
  epochNow(): number { return 1_700_000_000_000 + this.monotonicMs; }
  sleep(_delayMs: number, _ready: () => boolean, signal: AbortSignal): Promise<void> {
    const hook = this.onSleep;
    this.onSleep = null;
    hook?.();
    return new Promise<void>(resolve => {
      if (signal.aborted) { resolve(); return; }
      signal.addEventListener('abort', () => resolve(), { once: true });
    });
  }
}

describe('ENV-014 AC9 — a parked executor answers a read at once', () => {
  describe.each(BACKENDS)('%s backend', (backend) => {
    it('snapshot()/getMarking() inside the host wait return the current marking', async () => {
      const IN = environmentPlace<string>('IN');
      const OUT = place<string>('OUT');
      const t = Transition.builder('t').inputs(one(IN.place)).outputs(outPlace(OUT)).action(writes(OUT)).build();
      const net = PetriNet.builder('parked').transition(t).build();
      const clock = new HostClock();
      const exec = makeExecutor(backend, net, new Map(),
        { environmentPlaces: new Set([IN]), clock, deadlineToleranceMs: 0 });

      const done = exec.run(2000);
      await tick();
      // Parked with nothing to do. Read the marking at the next park — synchronously, from
      // inside the host's own wait, as a deterministic host answering a query would.
      let seen: { out: number; inFlight: boolean; live: number } | null = null;
      exec.injectNoAwait(IN, 'x');
      await tick();
      clock.onSleep = () => {
        const snap = exec.snapshot();
        seen = {
          out: snap.marking.get('OUT')?.length ?? 0,
          inFlight: snap.actionInFlight,
          live: exec.getMarking().tokenCount(OUT),
        };
      };
      exec.injectNoAwait(IN, 'y');
      await tick();
      // The read ran inside the next wait, after the second token's firing had landed: it saw
      // the current marking, not an earlier published one, and was answered on the spot.
      expect(seen).toEqual({ out: 2, inFlight: false, live: 2 });
      exec.drain();
      await done;
    });

    it('a read between cycles while parked returns without waking the orchestrator', async () => {
      const IN = environmentPlace<string>('IN');
      const OUT = place<string>('OUT');
      const t = Transition.builder('t').inputs(one(IN.place)).outputs(outPlace(OUT)).action(writes(OUT)).build();
      const net = PetriNet.builder('parked2').transition(t).build();
      const store = new InMemoryEventStore();
      const exec = makeExecutor(backend, net, new Map(),
        { environmentPlaces: new Set([IN]), eventStore: store });
      const done = exec.run(2000);
      expect(await exec.inject(IN, tokenOf('x'))).toBe(true);
      await tick();
      const before = store.events().length;
      const snap = exec.snapshot();
      expect(snap.marking.get('OUT')?.length).toBe(1);
      expect(snap.actionInFlight).toBe(false);
      // Synchronous: no cycle ran to serve it.
      expect(store.events().length).toBe(before);
      exec.drain();
      await done;
    });
  });
});

describe('TIME-015 AC11 — an action promise completed inside the host wait', () => {
  describe.each(BACKENDS)('%s backend', (backend) => {
    it('is admitted in the following cycle\'s completion phase, not at the call', async () => {
      const A = place<string>('A');
      const OUT = place<string>('OUT');
      const gate = deferred();
      const t = Transition.builder('hosted').inputs(one(A)).outputs(outPlace(OUT))
        .action(async (ctx) => { await gate.promise; ctx.output(OUT, 'result'); }).build();
      const net = PetriNet.builder('hosted').transition(t).build();
      const clock = new HostClock();
      const store = new InMemoryEventStore();
      const exec = makeExecutor(backend, net, initial([A, [tokenOf('a')]]),
        { clock, eventStore: store, deadlineToleranceMs: 0 });

      let atCall: { out: number; inFlight: boolean; completed: number } | null = null;
      clock.onSleep = () => {
        // The host executes the action itself: it completes the action's promise here.
        gate.resolve();
        const snap = exec.snapshot();
        atCall = {
          out: snap.marking.get('OUT')?.length ?? 0,
          inFlight: snap.actionInFlight,
          completed: eventsOfType(store, 'transition-completed').length,
        };
      };

      const marking = await exec.run(2000);
      // Nothing was admitted at the call ...
      expect(atCall).toEqual({ out: 0, inFlight: true, completed: 0 });
      // ... and the outputs appeared in the following cycle's completion phase.
      expect(marking.tokenCount(OUT)).toBe(1);
      expect(eventsOfType(store, 'transition-completed').map(e => e.transitionName)).toEqual(['hosted']);
      expect(exec.terminationReason()).toBe('quiescent');
    });
  });
});
