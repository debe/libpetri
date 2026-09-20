/**
 * **TIME-015 — Injectable Clock.** The executor's time seam: a monotonic firing
 * clock, an epoch clock, and ownership of the wait for the next timing boundary.
 *
 * AC#1 ("with no clock supplied, every existing timing test passes unchanged") is
 * not a test here — it is the rest of the suite, which is why none of it changed.
 * AC#9 (the default path pays nothing measurable) is a benchmark, not an assertion.
 *
 * The clocks below are deliberately hostile in the ways the contract permits: one
 * never advances on its own, one resolves spuriously, one stands still entirely.
 * Each isolates a failure that is silent under a real clock.
 */
import { describe, it, expect } from 'vitest';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { PrecompiledNetExecutor } from '../../src/runtime/precompiled-net-executor.js';
import type { Clock } from '../../src/runtime/clock.js';
import { systemClock, seedToken } from '../../src/runtime/clock.js';
import type { PetriNetExecutor } from '../../src/runtime/petri-net-executor.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, environmentPlace } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace, xor, timeout, forwardInput } from '../../src/core/out.js';
import { delayed, window as windowTiming } from '../../src/core/timing.js';
import { tokenOf, tokenAt } from '../../src/core/token.js';
import type { Token } from '../../src/core/token.js';
import { InMemoryEventStore, eventsOfType } from '../../src/event/event-store.js';

const EPOCH_ORIGIN = 1_700_000_000_000;

function initial(...entries: [Place<any>, Token<any>[]][]): Map<Place<any>, Token<any>[]> {
  return new Map(entries);
}

/**
 * A host clock that advances only when the executor asks it to wait, by exactly the
 * interval asked for. The common shape: virtual time moves in jumps, never in real
 * time. `epochNow` is derived from the same logical source so the two agree across a
 * replay, which TIME-015 permits and recommends.
 */
class VirtualClock implements Clock {
  monotonicMs = 0;
  readonly sleeps: number[] = [];
  /** Resolve without advancing this many times first — contract 3's spurious completion. */
  spuriousLeft = 0;
  /** Invoked inside `sleep`, before it decides anything. */
  onSleep: (() => void) | null = null;

  now(): number {
    return this.monotonicMs;
  }

  epochNow(): number {
    return EPOCH_ORIGIN + this.monotonicMs;
  }

  async sleep(delayMs: number, ready: () => boolean, signal: AbortSignal): Promise<void> {
    this.sleeps.push(delayMs);
    this.onSleep?.();
    if (signal.aborted || ready()) return;
    if (this.spuriousLeft > 0) {
      this.spuriousLeft--;
      return; // contract 3: completed early, advanced nothing
    }
    if (!(delayMs < Infinity)) {
      // Nothing timed is pending: suspend. The executor races its own wake sources,
      // so resolving only on abort is correct here rather than a stall (contract 2).
      await new Promise<void>(resolve => {
        signal.addEventListener('abort', () => resolve(), { once: true });
      });
      return;
    }
    this.monotonicMs += delayMs; // contract 2: advance to the boundary
  }
}

/**
 * A clock whose `sleep` resolves *only* on abort — it never advances and never times
 * out. Anything this net achieves, it achieves through the executor's own wake
 * sources, which is exactly what TIME-015 AC#8 pins.
 */
class SuspendingClock implements Clock {
  monotonicMs = 0;
  readonly sleeps: number[] = [];
  /** Invoked inside `sleep`, i.e. at a point where the executor is provably parked. */
  onSleep: (() => void) | null = null;

  now(): number {
    return this.monotonicMs;
  }

  epochNow(): number {
    return EPOCH_ORIGIN + this.monotonicMs;
  }

  sleep(delayMs: number, _ready: () => boolean, signal: AbortSignal): Promise<void> {
    this.sleeps.push(delayMs);
    this.onSleep?.();
    return new Promise<void>(resolve => {
      if (signal.aborted) {
        resolve();
        return;
      }
      signal.addEventListener('abort', () => resolve(), { once: true });
    });
  }
}

type Backend = 'bitmap' | 'precompiled';
const BACKENDS: Backend[] = ['bitmap', 'precompiled'];

function makeExecutor(
  backend: Backend,
  net: PetriNet,
  tokens: Map<Place<any>, Token<any>[]>,
  options: Record<string, unknown>,
): PetriNetExecutor {
  return backend === 'bitmap'
    ? new BitmapNetExecutor(net, tokens, options)
    : new PrecompiledNetExecutor(net, tokens, options);
}

describe('TIME-015 — injectable clock', () => {
  describe.each(BACKENDS)('%s backend', (backend) => {
    it('AC#3: a delayed net quiesces on virtual time without the delay elapsing for real', async () => {
      const IN = place<string>('IN');
      const OUT = place<string>('OUT');
      const t = Transition.builder('Delayed')
        .inputs(one(IN))
        .outputs(outPlace(OUT))
        .timing(delayed(60_000)) // a minute of net time
        .action(async (ctx) => { ctx.output(OUT, ctx.input(IN)); })
        .build();
      const net = PetriNet.builder('N').transition(t).build();

      const clock = new VirtualClock();
      const executor = makeExecutor(backend, net, initial([IN, [tokenOf('go')]]), { clock });

      const startedReal = Date.now();
      const marking = await executor.run(5000);
      const realElapsed = Date.now() - startedReal;

      expect(marking.hasTokens(OUT)).toBe(true);
      // A full minute of net time passed...
      expect(clock.monotonicMs).toBeGreaterThanOrEqual(60_000);
      // ...in negligible real time. This is the whole point of the requirement.
      expect(realElapsed).toBeLessThan(2000);
    });

    it('AC#4: a spurious wait completion does not fire a transition before its earliest bound', async () => {
      const IN = place<string>('IN');
      const OUT = place<string>('OUT');
      const firedAt: number[] = [];
      const clock = new VirtualClock();
      const t = Transition.builder('Delayed')
        .inputs(one(IN))
        .outputs(outPlace(OUT))
        .timing(delayed(1000))
        .action(async (ctx) => {
          firedAt.push(clock.now());
          ctx.output(OUT, ctx.input(IN));
        })
        .build();
      const net = PetriNet.builder('N').transition(t).build();

      // The first three waits complete early having advanced nothing. The executor
      // must re-check the boundary each time rather than reading "the wait resolved"
      // as "the bound is reached".
      clock.spuriousLeft = 3;
      const executor = makeExecutor(backend, net, initial([IN, [tokenOf('go')]]), { clock });
      const marking = await executor.run(5000);

      expect(marking.hasTokens(OUT)).toBe(true);
      expect(firedAt).toHaveLength(1);
      expect(firedAt[0]).toBeGreaterThanOrEqual(1000);
      // The spurious completions really did happen — otherwise this asserts nothing.
      expect(clock.sleeps.length).toBeGreaterThan(3);
    });

    it('AC#7: a boundary already due advances on the next cycle instead of waiting — injected as by default', async () => {
      // The net from the existing regression: `window(50, 200)` with nothing in flight
      // and no environment place, so a due boundary that got waited on would sleep until
      // the run budget expired. The short-circuit must survive the seam, and must reach
      // the same outcome with and without a clock.
      const build = (): PetriNet => {
        const IN = place<string>('IN');
        const OUT = place<string>('OUT');
        const t = Transition.builder('Windowed')
          .inputs(one(IN))
          .outputs(outPlace(OUT))
          .timing(windowTiming(50, 200))
          .action(async (ctx) => { ctx.output(OUT, ctx.input(IN)); })
          .build();
        return PetriNet.builder('N').transition(t).build();
      };

      for (const clock of [undefined, new VirtualClock()]) {
        const net = build();
        const IN = [...net.places].find((p) => p.name === 'IN')! as Place<string>;
        const OUT = [...net.places].find((p) => p.name === 'OUT')! as Place<string>;
        const executor = makeExecutor(
          backend, net, initial([IN, [tokenOf('go')]]),
          clock === undefined ? {} : { clock },
        );
        const marking = await executor.run(5000);
        expect(marking.hasTokens(OUT)).toBe(true);
      }
    });

    it('AC#8: a completing action wakes the wait without the interval being waited out', async () => {
      // SuspendingClock never resolves a sleep on its own. The only way this net can
      // finish is the in-flight completion promise still being in the race — a seam
      // shaped as a bare duration would stall here while the default path ran fine.
      const IN = place<string>('IN');
      const MID = place<string>('MID');
      const OUT = place<string>('OUT');
      const first = Transition.builder('First')
        .inputs(one(IN))
        .outputs(outPlace(MID))
        .action(async (ctx) => {
          await Promise.resolve();
          await Promise.resolve();
          ctx.output(MID, ctx.input(IN));
        })
        .build();
      const second = Transition.builder('Second')
        .inputs(one(MID))
        .outputs(outPlace(OUT))
        .action(async (ctx) => { ctx.output(OUT, ctx.input(MID)); })
        .build();
      const net = PetriNet.builder('N').transitions(first, second).build();

      const clock = new SuspendingClock();
      const executor = makeExecutor(backend, net, initial([IN, [tokenOf('go')]]), { clock });
      const marking = await executor.run(5000);

      expect(marking.hasTokens(OUT)).toBe(true);
      expect(clock.monotonicMs).toBe(0); // no interval was ever waited out
    });

    it('AC#8: an injected external event wakes the wait', async () => {
      const ENV = environmentPlace(place<string>('ENV'));
      const OUT = place<string>('OUT');
      const t = Transition.builder('OnEvent')
        .inputs(one(ENV.place))
        .outputs(outPlace(OUT))
        .action(async (ctx) => { ctx.output(OUT, ctx.input(ENV.place)); })
        .build();
      const net = PetriNet.builder('N').place(ENV.place).transition(t).build();

      const clock = new SuspendingClock();
      const executor = makeExecutor(backend, net, initial(), {
        clock,
        environmentPlaces: new Set([ENV]),
      });

      // Drain from inside the wait. A bare `drain()` races the loop: `wakeUp()` is a
      // no-op unless the executor is parked, and `sleep` is the one place we know it is
      // (the executor assigns `wakeUpResolve` before calling us).
      let injectionDone = false;
      clock.onSleep = () => { if (injectionDone) executor.drain(); };

      const running = executor.run(5000);
      await executor.injectValue(ENV, 'hello');
      injectionDone = true;
      const marking = await running;

      expect(marking.hasTokens(OUT)).toBe(true);
      expect(clock.monotonicMs).toBe(0);
    });

    it('AC#5/AC#8: close aborts the wait, which resolves rather than failing, and the run terminates', async () => {
      const ENV = environmentPlace(place<string>('ENV'));
      const OUT = place<string>('OUT');
      const t = Transition.builder('OnEvent')
        .inputs(one(ENV.place))
        .outputs(outPlace(OUT))
        .action(async (ctx) => { ctx.output(OUT, ctx.input(ENV.place)); })
        .build();
      const net = PetriNet.builder('N').place(ENV.place).transition(t).build();

      const clock = new SuspendingClock();
      const executor = makeExecutor(backend, net, initial(), {
        clock,
        environmentPlaces: new Set([ENV]),
      });

      const running = executor.run(5000);
      // Let the loop reach the wait, then tear down from underneath it. A `sleep` that
      // rejected on abort would surface here as a rejected run — and in production as an
      // unhandled rejection on the teardown path, where nothing observes it.
      await new Promise<void>(r => setTimeout(r, 20));
      expect(clock.sleeps.length).toBeGreaterThan(0);
      executor.close();

      await expect(running).resolves.toBeDefined();
    });

    it('AC#11: inject() is legal from inside the wait and admits on a later cycle, never at the injection point', async () => {
      // The only admission path a clock-only host has: it is inside `sleep` when it
      // decides to publish an event. That must enqueue and return, with the tokens
      // entering through the executor's own external-events phase.
      const ENV = environmentPlace(place<string>('ENV'));
      const OUT = place<string>('OUT');
      let fired = false;
      const t = Transition.builder('OnEvent')
        .inputs(one(ENV.place))
        .outputs(outPlace(OUT))
        .action(async (ctx) => {
          fired = true;
          ctx.output(OUT, ctx.input(ENV.place));
        })
        .build();
      const net = PetriNet.builder('N').place(ENV.place).transition(t).build();

      const clock = new VirtualClock();
      const executor = makeExecutor(backend, net, initial(), {
        clock,
        environmentPlaces: new Set([ENV]),
      });

      let injected = false;
      let firedAtInjectionPoint: boolean | null = null;
      clock.onSleep = () => {
        if (injected) return;
        injected = true;
        // Inject and return. Awaiting admission here would suspend the orchestrator on a
        // promise only the orchestrator can settle — a silent self-deadlock (TIME-015).
        const pending = executor.injectValue(ENV, 'from-inside-the-wait');
        void pending.catch(() => {});
        // Reentrant inject only enqueues: the transition cannot have fired yet.
        firedAtInjectionPoint = fired;
        executor.drain();
      };

      const marking = await executor.run(5000);

      expect(injected).toBe(true);
      expect(firedAtInjectionPoint).toBe(false);
      expect(marking.hasTokens(OUT)).toBe(true);
      expect(marking.peekFirst(OUT)?.value).toBe('from-inside-the-wait');
    });

    it('AC#11: injectNoAwait has no admission signal to await, and still admits on a later cycle', async () => {
      // The SHOULD half of the admission rule: documenting the deadlock is the weak fix,
      // handing the host a form with no result to await is the stronger one. `inject` is
      // the footgun precisely because inject-and-confirm is what a host author writes first.
      const ENV = environmentPlace(place<string>('ENV'));
      const OUT = place<string>('OUT');
      let fired = false;
      const t = Transition.builder('OnEvent')
        .inputs(one(ENV.place))
        .outputs(outPlace(OUT))
        .action(async (ctx) => { fired = true; ctx.output(OUT, ctx.input(ENV.place)); })
        .build();
      const net = PetriNet.builder('N').place(ENV.place).transition(t).build();

      const clock = new VirtualClock();
      const executor = makeExecutor(backend, net, initial(), {
        clock,
        environmentPlaces: new Set([ENV]),
      });

      let injected = false;
      let firedAtInjectionPoint: boolean | null = null;
      clock.onSleep = () => {
        if (injected) {
          executor.drain();
          return;
        }
        injected = true;
        const result: void = executor.injectNoAwait(ENV, 'no-await');
        expect(result).toBeUndefined(); // nothing to await, by construction
        firedAtInjectionPoint = fired;
      };

      const marking = await executor.run(5000);

      expect(injected).toBe(true);
      expect(firedAtInjectionPoint).toBe(false);
      expect(marking.peekFirst(OUT)?.value).toBe('no-await');
    });

    it('AC#10: a clock that never advances still completes an immediate net, ties breaking by declaration order', async () => {
      // A host clock derived from millisecond wall time or a replay log returns the
      // same reading across many cycles. That is permitted — non-decreasing, not
      // strictly increasing — and it makes enablement-time ties the common case rather
      // than the rare one, so the EXEC-002 AC3 declaration-order tie-break carries them.
      const A = place<string>('A');
      const B = place<string>('B');
      const OUT = place<string>('OUT');
      const NEVER = place<string>('NEVER');
      const order: string[] = [];
      const first = Transition.builder('First')
        .inputs(one(A))
        .outputs(outPlace(OUT))
        .action(async (ctx) => { order.push('First'); ctx.output(OUT, ctx.input(A)); })
        .build();
      const second = Transition.builder('Second')
        .inputs(one(B))
        .outputs(outPlace(OUT))
        .action(async (ctx) => { order.push('Second'); ctx.output(OUT, ctx.input(B)); })
        .build();
      // Never enabled; present only to take `allImmediate` off and route the firing
      // through the general (sorting) path, which is where the tie-break lives. Pinning
      // fast-path order for a general-path net, or the reverse, is what TIME-015 warns
      // a virtual-clock suite against.
      const parked = Transition.builder('Parked')
        .inputs(one(NEVER))
        .timing(delayed(10))
        .action(async () => {})
        .build();
      const net = PetriNet.builder('N').place(NEVER).transitions(first, second, parked).build();

      const frozen: Clock = {
        now: () => 4242,
        epochNow: () => EPOCH_ORIGIN,
        sleep: async () => {},
      };
      const executor = makeExecutor(
        backend, net, initial([A, [tokenOf('a')], ], [B, [tokenOf('b')]]), { clock: frozen },
      );
      const marking = await executor.run(5000);

      expect(marking.tokenCount(OUT)).toBe(2);
      expect(order).toEqual(['First', 'Second']);
    });

    it('AC#12: the executor stamps what it mints from the epoch clock; host tokens keep their own', async () => {
      // Three token origins, three different rules. The seam reaches the first two and
      // deliberately does not reach the third — pinned here so the boundary is a
      // decision on record rather than an oversight.
      const ENV = environmentPlace(place<string>('ENV')); // executor-minted, nothing consumes it
      const SEED = place<string>('SEED');                 // host-minted, initial marking
      const SRC = place<string>('SRC');
      const OUT = place<string>('OUT');                   // action-minted via ctx.output
      const t = Transition.builder('Pass')
        .inputs(one(SRC))
        .outputs(outPlace(OUT))
        .action(async (ctx) => { ctx.output(OUT, ctx.input(SRC)); })
        .build();
      const net = PetriNet.builder('N').place(ENV.place).place(SEED).transition(t).build();

      const clock = new VirtualClock();
      // A host token carrying a timestamp of its own — restored from a snapshot, say.
      const preserved = tokenAt('kept', 12_345);
      const executor = makeExecutor(
        backend, net,
        initial([SEED, [seedToken(clock, 'seeded'), preserved]], [SRC, [tokenOf('src')]]),
        { clock, environmentPlaces: new Set([ENV]) },
      );

      // Driven entirely from inside the wait, so there is no race between the test and
      // the loop: park #1 injects, park #2 (after admission) drains. A `drain()` issued
      // from outside is a no-op unless the executor happens to be parked.
      let injected = false;
      clock.onSleep = () => {
        if (!injected) {
          injected = true;
          void executor.injectValue(ENV, 'injected').catch(() => {});
        } else {
          executor.drain();
        }
      };

      const wallBefore = Date.now();
      const marking = await executor.run(5000);
      const wallAfter = Date.now();

      const seeded = marking.peekTokens(SEED);
      // seedToken stamps from the injected epoch clock, not the wall clock (AC#12).
      expect(seeded[0]!.createdAt).toBe(EPOCH_ORIGIN);
      // The host's own token passes through untouched. Re-stamping it would defeat
      // exactly the createdAt preservation a CORE-073 restore exists for.
      expect(seeded[1]!.createdAt).toBe(12_345);

      // injectValue mints inside the executor, so it follows the injected epoch clock.
      expect(marking.peekTokens(ENV.place)[0]!.createdAt).toBe(EPOCH_ORIGIN);

      // ...and ctx.output, the case that looks host-side and is not: the action supplies a
      // *value*, libpetri chooses the createdAt, so the token is executor-produced and
      // follows the clock (AC#13). Reading this the other way leaves the bulk of a run's
      // tokens on wall time under a virtual clock — defeating the requirement while
      // appearing to satisfy it.
      const produced = marking.peekTokens(OUT)[0]!;
      expect(produced.createdAt).toBe(EPOCH_ORIGIN);
      // Which is emphatically not wall time: the run really did happen just now.
      expect(wallBefore).toBeGreaterThan(EPOCH_ORIGIN);
      expect(wallAfter).toBeGreaterThan(EPOCH_ORIGIN);
    });
  });

  it('AC#15: an absent boundary suspends — the documented clock reaches quiescence without spinning', async () => {
    // The clock below is a transcription of the `Clock` @example in clock.ts, whose only
    // addition is the call counter. AC#15 covers "every clock in its own documentation",
    // and the example is what a host copies — so the doc is what this pins.
    //
    // The earlier version of that example returned on `Infinity` instead of suspending.
    // Measured, on this net: no output in 30s, a 200ms setTimeout never fired, and the
    // run budget never fired either. A loop of already-resolved promises never yields to
    // the macrotask queue, so the executor starves the very event loop it is waiting on —
    // which is why the assertions below are about the event loop, not just the result.
    //
    // Bounded by `sleep` entry count rather than by a timeout, deliberately: the spin
    // starves timers, so an enclosing timeout is exactly what cannot fire. A test written
    // that way wedges the run instead of failing it. (Flipping the branch back here does
    // not hang forever under vitest's fork pool — the worker OOMs, because each cycle
    // registers a wake-up promise on a queue starvation never drains. That accumulation is
    // this runtime's failure surface, not the defect's: the same bug in Rust holds RSS flat
    // and simply never finishes. Don't generalise either shape into the other.)
    class DocumentedVirtualClock implements Clock {
      private t = 0;
      sleepCalls = 0;
      now(): number { return this.t; }
      epochNow(): number { return EPOCH_ORIGIN + this.t; }
      sleep(delayMs: number, ready: () => boolean, signal: AbortSignal): Promise<void> {
        this.sleepCalls++;
        if (ready()) return Promise.resolve();
        if (delayMs === Infinity) {
          return new Promise(resolve => {
            signal.addEventListener('abort', () => resolve(), { once: true });
          });
        }
        this.t += delayMs;
        return Promise.resolve();
      }
    }

    const IN = place<string>('IN');
    const OUT = place<string>('OUT');
    // An action that only completes on a real timer: the orchestrator parks on it with
    // nothing timed pending, so the executor asks the clock to wait `Infinity`. If the
    // clock returns instead of suspending, this timer never gets to fire.
    const t = Transition.builder('Slow')
      .inputs(one(IN))
      .outputs(outPlace(OUT))
      .action(async (ctx) => {
        await new Promise<void>(r => setTimeout(r, 30));
        ctx.output(OUT, ctx.input(IN));
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const clock = new DocumentedVirtualClock();
    const executor = new BitmapNetExecutor(net, initial([IN, [tokenOf('go')]]), { clock });
    const running = executor.run(5000);

    // The event loop still belongs to everyone: a macrotask queued while the orchestrator
    // is parked must still run. Under the old example this never resolved.
    const macrotaskRan = await new Promise<boolean>(r => setTimeout(() => r(true), 50));
    expect(macrotaskRan).toBe(true);

    const marking = await running;
    expect(marking.hasTokens(OUT)).toBe(true);
    // Suspended rather than spun. A returning clock is re-entered every cycle and would
    // count in the thousands; a suspending one is entered a handful of times.
    expect(clock.sleepCalls).toBeLessThan(10);
  });

  it('AC#15: systemClock() suspends on an absent boundary too', async () => {
    // "Every clock the implementation itself ships" — systemClock is the only one.
    const IN = place<string>('IN');
    const OUT = place<string>('OUT');
    const t = Transition.builder('Slow')
      .inputs(one(IN))
      .outputs(outPlace(OUT))
      .action(async (ctx) => {
        await new Promise<void>(r => setTimeout(r, 30));
        ctx.output(OUT, ctx.input(IN));
      })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const executor = new BitmapNetExecutor(net, initial([IN, [tokenOf('go')]]), {
      clock: systemClock(),
    });
    const running = executor.run(5000);
    expect(await new Promise<boolean>(r => setTimeout(() => r(true), 50))).toBe(true);
    expect((await running).hasTokens(OUT)).toBe(true);
  });

  it('AC#14: run identifiers are not clock readings', async () => {
    // Contract point 1 forbids treating a reading as a unique key, and the execution id was
    // exactly that: `startMs.toString(16)`. Under performance.now() it was unique by accident
    // — two executors practically never shared a reading. A host clock removes the accident.
    const frozen: Clock = {
      now: () => 1000,          // every executor built here starts at the same instant
      epochNow: () => EPOCH_ORIGIN,
      sleep: async () => {},
    };
    const net = PetriNet.builder('N').place(place<string>('P')).build();

    // Deliberately one of each backend: they draw from one shared counter, so a bitmap and a
    // precompiled executor in the same process cannot both be the first id.
    const ids = [
      new BitmapNetExecutor(net, initial(), { clock: frozen }).executionId(),
      new PrecompiledNetExecutor(net, initial(), { clock: frozen }).executionId(),
      new BitmapNetExecutor(net, initial(), { clock: frozen }).executionId(),
    ];

    expect(new Set(ids).size).toBe(3);
    for (const id of ids) expect(id).not.toBe((1000).toString(16));
  });

  it('AC#13: action-timeout recovery outputs carry the injected clock too', async () => {
    // The third executor-produced origin. These tokens never pass through action code at
    // all — the executor synthesises them after severing the context — but they reach the
    // marking through the same per-firing collector, so stamping the collector covers them.
    // Pinned because it is the origin easiest to forget: nobody writes it.
    const IN = place<string>('IN');
    const OK = place<string>('OK');
    const RETRY = place<string>('RETRY');
    const t = Transition.builder('Slow')
      .inputs(one(IN))
      .outputs(xor(outPlace(OK), timeout(10, forwardInput(IN, RETRY))))
      // Never resolves: the timeout branch is the only way out.
      .action(() => new Promise<void>(() => {}))
      .build();
    const net = PetriNet.builder('N').place(OK).transition(t).build();

    const clock = new VirtualClock();
    const executor = new BitmapNetExecutor(net, initial([IN, [tokenOf('payload')]]), { clock });
    const marking = await executor.run(5000);

    expect(marking.hasTokens(RETRY)).toBe(true);
    expect(marking.peekFirst(RETRY)?.value).toBe('payload');
    // Stamped from the injected epoch clock, not wall time.
    expect(marking.peekTokens(RETRY)[0]!.createdAt).toBe(EPOCH_ORIGIN);
  });

  it('AC#2: two executors on two clocks in one process do not observe each other', async () => {
    const build = (): { net: PetriNet; IN: Place<string>; OUT: Place<string> } => {
      const IN = place<string>('IN');
      const OUT = place<string>('OUT');
      const t = Transition.builder('Delayed')
        .inputs(one(IN))
        .outputs(outPlace(OUT))
        .timing(delayed(5000))
        .action(async (ctx) => { ctx.output(OUT, ctx.input(IN)); })
        .build();
      return { net: PetriNet.builder('N').transition(t).build(), IN, OUT };
    };

    const a = build();
    const b = build();
    const clockA = new VirtualClock();
    const clockB = new VirtualClock();

    // Deliberately one of each backend: independence is of the clocks, not the engines.
    const execA = new BitmapNetExecutor(a.net, initial([a.IN, [tokenOf('a')]]), { clock: clockA });
    const execB = new PrecompiledNetExecutor(b.net, initial([b.IN, [tokenOf('b')]]), { clock: clockB });

    const markingA = await execA.run(5000);
    expect(markingA.hasTokens(a.OUT)).toBe(true);
    expect(clockA.monotonicMs).toBeGreaterThanOrEqual(5000);
    // B has not run: advancing A advanced nothing of B's.
    expect(clockB.monotonicMs).toBe(0);

    const markingB = await execB.run(5000);
    expect(markingB.hasTokens(b.OUT)).toBe(true);
    expect(clockB.monotonicMs).toBeGreaterThanOrEqual(5000);
  });

  it('AC#6: with tolerance 0 a window is reaped one millisecond past its bound, and not at it', async () => {
    // Wall time cannot ask this question: the 5ms default band exists precisely because
    // real jitter makes "exactly at the bound" unobservable. Under a host clock the
    // jitter is gone, so the boundary is exact — which is why TIME-015 tells a host
    // verifying deadlines to set the tolerance to 0.
    const run = async (advanceTo: number): Promise<{ reaped: number; produced: boolean }> => {
      const IN = place<string>('IN');
      const OUT = place<string>('OUT');
      const GO = place<string>('GO');
      const GO_OUT = place<string>('GO_OUT');
      const clock = new VirtualClock();

      const windowed = Transition.builder('Windowed')
        .inputs(one(IN))
        .outputs(outPlace(OUT))
        .timing(windowTiming(100, 150))
        .action(async (ctx) => { ctx.output(OUT, ctx.input(IN)); })
        .build();
      // Fires first (higher priority) and advances the host clock while in flight —
      // the deterministic stand-in for the busy event loop that starves a window in
      // the wall-clock version of this test.
      const blocker = Transition.builder('Blocker')
        .inputs(one(GO))
        .outputs(outPlace(GO_OUT))
        .priority(100)
        .action(async (ctx) => {
          clock.monotonicMs = advanceTo;
          ctx.output(GO_OUT, ctx.input(GO));
        })
        .build();
      const net = PetriNet.builder('N').transitions(windowed, blocker).build();

      const eventStore = new InMemoryEventStore();
      const executor = new BitmapNetExecutor(
        net,
        initial([IN, [tokenOf('val')]], [GO, [tokenOf('go')]]),
        { clock, eventStore, deadlineToleranceMs: 0 },
      );
      const marking = await executor.run(5000);
      return {
        reaped: eventsOfType(eventStore, 'transition-timed-out').length,
        produced: marking.hasTokens(OUT),
      };
    };

    // Exactly at the bound: elapsed === latest is still inside the window.
    const atBound = await run(150);
    expect(atBound.reaped).toBe(0);
    expect(atBound.produced).toBe(true);

    // One millisecond past: force-disabled, nothing produced.
    const pastBound = await run(151);
    expect(pastBound.reaped).toBe(1);
    expect(pastBound.produced).toBe(false);
  });

  it('systemClock() reproduces the default behaviour it stands in for', async () => {
    const IN = place<string>('IN');
    const OUT = place<string>('OUT');
    const t = Transition.builder('Delayed')
      .inputs(one(IN))
      .outputs(outPlace(OUT))
      .timing(delayed(10))
      .action(async (ctx) => { ctx.output(OUT, ctx.input(IN)); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    const explicit = new BitmapNetExecutor(
      net, initial([IN, [tokenOf('go')]]), { clock: systemClock() },
    );
    expect((await explicit.run(5000)).hasTokens(OUT)).toBe(true);

    const implicit = new BitmapNetExecutor(net, initial([IN, [tokenOf('go')]]), {});
    expect((await implicit.run(5000)).hasTokens(OUT)).toBe(true);
  });

  it('the two time bases stay separate: a virtual firing clock does not move wall-clock event stamps', async () => {
    // The origins are unrelated, so conflating them is silent rather than loud. Here the
    // firing clock jumps a minute while the epoch clock is pinned, and the event
    // timestamps must follow the epoch clock alone.
    const IN = place<string>('IN');
    const OUT = place<string>('OUT');
    const t = Transition.builder('Delayed')
      .inputs(one(IN))
      .outputs(outPlace(OUT))
      .timing(delayed(60_000))
      .action(async (ctx) => { ctx.output(OUT, ctx.input(IN)); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();

    let monotonic = 0;
    const split: Clock = {
      now: () => monotonic,
      epochNow: () => EPOCH_ORIGIN, // pinned: wall time is standing still
      sleep: async (delayMs) => { if (delayMs < Infinity) monotonic += delayMs; },
    };
    const eventStore = new InMemoryEventStore();
    const executor = new BitmapNetExecutor(
      net, initial([IN, [tokenOf('go')]]), { clock: split, eventStore },
    );
    const marking = await executor.run(5000);

    expect(marking.hasTokens(OUT)).toBe(true);
    expect(monotonic).toBeGreaterThanOrEqual(60_000);
    for (const event of eventStore.events()) {
      expect(event.timestamp).toBe(EPOCH_ORIGIN);
    }
  });
});
