/**
 * **CORE-073** (marking snapshot and restore), **ENV-014** (mid-execution snapshot) and
 * **NU-011** (resume-safe ν-name minting).
 *
 * These three land together by construction: CORE-073's status line says an implementation that
 * gains restore also acquires NU-011, because a resumed execution seeded from a restored marking
 * re-mints names that marking already holds — and a [NU-020] join correlates on name equality
 * alone, so the collision never surfaces as an error. It silently merges tokens from different
 * run segments.
 *
 * The snapshot form is normative as of this revision. It was not before, which is why Python
 * built one shape, Rust had an in-process `Clone` that was mistaken for one, and Java and
 * TypeScript built nothing.
 */
import { describe, it, expect, vi } from 'vitest';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import type { BitmapNetExecutorOptions } from '../../src/runtime/bitmap-net-executor.js';
import { PrecompiledNetExecutor } from '../../src/runtime/precompiled-net-executor.js';
import { Marking } from '../../src/runtime/marking.js';
import type { MarkingSnapshotForm } from '../../src/runtime/marking.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, environmentPlace } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { delayed, deadline } from '../../src/core/timing.js';
import { andPlaces } from '../../src/core/out.js';
import { nameId } from '../../src/core/name.js';
import type { NameId } from '../../src/core/name.js';
import { tokenOf, tokenAt } from '../../src/core/token.js';
import type { Token } from '../../src/core/token.js';
import { InMemoryEventStore, eventsOfType } from '../../src/event/event-store.js';
import type { EventStore } from '../../src/event/event-store.js';
import type { SnapshotResult } from '../../src/runtime/petri-net-executor.js';
import { convertMarking } from '../../src/debug/net-event-converter.js';
import { compareCodePoints } from '../../src/core/internal/code-point-order.js';
import * as staticLib from '../../src/index.js';
import * as runtimeLib from '../../src/runtime/index.js';

function initial(...entries: [Place<any>, Token<any>[]][]): Map<Place<any>, Token<any>[]> {
  return new Map(entries);
}

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

describe('CORE-073 — marking snapshot and restore', () => {
  it('AC#1: value and createdAt round-trip unchanged', () => {
    const P = place<string>('P');
    const m = Marking.from(initial([P, [tokenAt('a', 111), tokenAt('b', 222)]]));

    const snap = m.snapshot();
    const restored = Marking.fromSnapshot(snap);

    expect(restored.peekTokens(P).map(t => t.value)).toEqual(['a', 'b']);
    expect(restored.peekTokens(P).map(t => t.createdAt)).toEqual([111, 222]);
  });

  it('AC#6: FIFO order survives, and the first firing consumes the first token', async () => {
    // Order is data, not presentation: it decides which token a firing takes. A snapshot that
    // lost it would still "round-trip" by value and fail the only test that matters.
    const P = place<string>('P');
    const OUT = place<string>('OUT');
    const m = Marking.from(initial([P, [tokenAt('A', 1), tokenAt('B', 2), tokenAt('C', 3)]]));
    const snap = m.snapshot();

    expect(snap.get('P')!.map(t => t.value)).toEqual(['A', 'B', 'C']);

    const t = Transition.builder('T')
      .inputs(one(P))
      .outputs(outPlace(OUT))
      .action(async (ctx) => { ctx.output(OUT, ctx.input(P)); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const marking = await new BitmapNetExecutor(net, new Map(), { restore: snap }).run(5000);

    // A is consumed first, so it is the one that reached OUT first.
    expect(marking.peekTokens(OUT).map(t => t.value)).toEqual(['A', 'B', 'C']);
  });

  it('AC#7: present-but-empty and omitted restore identically', () => {
    const P = place<string>('P');
    const withEmpty: MarkingSnapshotForm = new Map([['P', []]]);
    const omitted: MarkingSnapshotForm = new Map();

    const a = Marking.fromSnapshot(withEmpty);
    const b = Marking.fromSnapshot(omitted);

    expect(a.tokenCount(P)).toBe(0);
    expect(b.tokenCount(P)).toBe(0);
    expect(a.hasTokens(P)).toBe(false);
    expect(b.hasTokens(P)).toBe(false);
  });

  it('an emitted snapshot omits empty places — drained, or restored empty', () => {
    // One emission rule, so that two implementations snapshotting one marking agree key for key
    // (AC#12): Java, Rust and the precompiled executor all omit. A restore still accepts both
    // forms (AC#7, above); only what is *emitted* is pinned.
    const P = place<string>('P');
    const Q = place<string>('Q');
    const m = Marking.from(initial([P, [tokenAt('a', 1)]], [Q, [tokenAt('q', 2)]]));
    m.removeFirst(P); // declared and drained

    expect([...m.snapshot().keys()]).toEqual(['Q']);

    const restoredEmpty = Marking.fromSnapshot(new Map([['P', []], ['Q', [tokenAt('q', 2)]]]));
    expect([...restoredEmpty.snapshot().keys()]).toEqual(['Q']);
  });

  it('AC#7: a place the receiving net does not declare is retained, not dropped', async () => {
    // The point of keying a snapshot by name: a snapshot must survive a round-trip through a
    // net that has since lost a place. There is no Place to construct for a name the net never
    // declared, which is why the form cannot be keyed by Place.
    const KNOWN = place<string>('KNOWN');
    const GONE = place<string>('GONE');
    const OUT = place<string>('OUT');
    const snap: MarkingSnapshotForm = new Map([
      ['KNOWN', [tokenAt('k', 10)]],
      ['GONE', [tokenAt('g', 20)]],
    ]);

    const t = Transition.builder('T')
      .inputs(one(KNOWN))
      .outputs(outPlace(OUT))
      .action(async (ctx) => { ctx.output(OUT, ctx.input(KNOWN)); })
      .build();
    const net = PetriNet.builder('N').transition(t).build(); // declares KNOWN and OUT only
    const marking = await new BitmapNetExecutor(net, new Map(), { restore: snap }).run(5000);

    expect(marking.hasTokens(OUT)).toBe(true);
    // Retained and inert, per CORE-072 — and with its original timestamp.
    expect(marking.tokenCount(GONE)).toBe(1);
    expect(marking.peekFirst(GONE)?.value).toBe('g');
    expect(marking.peekTokens(GONE)[0]!.createdAt).toBe(20);
  });

  it('AC#8: no codec is imposed — a closure and a class instance round-trip untouched', async () => {
    // The engine must not require values to be serializable, because only the host knows what
    // its values are. Deliberately unserializable values: JSON.stringify drops the function and
    // flattens the instance, so anything that encoded on the way through would be caught here.
    class Handle {
      constructor(readonly id: number) {}
      describe(): string { return `handle-${this.id}`; }
    }
    const fn = (x: number): number => x * 3;
    const handle = new Handle(7);

    const P = place<unknown>('P');
    const OUT = place<unknown>('OUT');
    const m = Marking.from(initial([P, [tokenOf(fn), tokenOf(handle)]]));

    const restored = Marking.fromSnapshot(m.snapshot());
    const [a, b] = restored.peekTokens(P);

    // Identity, not equality: the very same objects came back.
    expect(a!.value).toBe(fn);
    expect(b!.value).toBe(handle);
    expect((a!.value as typeof fn)(5)).toBe(15);
    expect((b!.value as Handle).describe()).toBe('handle-7');
    expect(b!.value).toBeInstanceOf(Handle);

    // And they survive an executor round-trip, not just a Marking one.
    const t = Transition.builder('T')
      .inputs(one(P))
      .outputs(outPlace(OUT))
      .action(async (ctx) => { ctx.output(OUT, ctx.input(P)); })
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const marking = await new BitmapNetExecutor(net, new Map(), { restore: m.snapshot() }).run(5000);
    expect(marking.peekTokens(OUT).map(t2 => t2.value)).toContain(fn);
  });

  it('the documented persistence walk round-trips through JSON and keeps canonical order', () => {
    // `Marking.snapshot`'s doc tells a durable host to store an **array of entries** —
    // `JSON.stringify([...snapshot])` — and come back with `new Map(JSON.parse(stored))`.
    // Tested rather than asserted, because a documented walk that does not work is precisely
    // the defect this project found in its own clock example — guidance a host copies is
    // guidance that needs a test.
    //
    // Place names here are integer-like on purpose: what a host naming places after node ids
    // produces, and the case the previously documented `Object.fromEntries` walk got wrong.
    const names = ['9', '10', '1', '-1', 'a', '__proto__'];
    const m = Marking.from(initial(
      ...names.map((n, i): [Place<any>, Token<any>[]] =>
        [place<{ step: string }>(n), [tokenAt({ step: n }, 100 + i), tokenAt({ step: `${n}'` }, 200 + i)]]),
    ));
    const canonical = [...names].sort(compareCodePoints);
    expect(canonical).toEqual(['-1', '1', '10', '9', '__proto__', 'a']);
    expect([...m.snapshot().keys()]).toEqual(canonical);

    const stored = JSON.stringify([...m.snapshot()]);
    const parsed = new Map(JSON.parse(stored)) as MarkingSnapshotForm;

    // The stored artefact is still in canonical order, so two captures of one marking are
    // byte-identical and comparable without normalising.
    expect([...parsed.keys()]).toEqual(canonical);
    expect(JSON.stringify([...Marking.fromSnapshot(parsed).snapshot()])).toBe(stored);
    const restored = Marking.fromSnapshot(parsed);
    for (const n of names) {
      expect(restored.peekTokens(place(n)).map(t => t.value)).toEqual([{ step: n }, { step: `${n}'` }]);
    }
    expect(restored.peekTokens(place('9')).map(t => t.createdAt)).toEqual([100, 200]);

    // Why not a plain object: JavaScript hoists integer-like keys in numeric order, so the
    // object walk loses the canonical order (and `__proto__` with it).
    const viaObject = Object.keys(JSON.parse(JSON.stringify(Object.fromEntries(m.snapshot()))) as object);
    expect(viaObject).not.toEqual(canonical);
    expect(viaObject.slice(0, 3)).toEqual(['1', '9', '10']);
  });

  it('a place named __proto__ round-trips, which is why the form is a Map', () => {
    // Reachable input rather than a hypothetical: a host compiling place names from
    // user-supplied step identifiers can be handed this. A plain object would put the tokens
    // on the prototype instead of in the snapshot.
    const hostile = place<string>('__proto__');
    const m = Marking.from(initial([hostile, [tokenAt('payload', 7)]]));

    const snap = m.snapshot();
    expect(snap.get('__proto__')!.map(t => t.value)).toEqual(['payload']);

    const restored = Marking.fromSnapshot(snap);
    expect(restored.peekTokens(hostile).map(t => t.value)).toEqual(['payload']);
    expect(restored.peekTokens(hostile).map(t => t.createdAt)).toEqual([7]);
  });

  it('AC#12: place order is deterministic, and a restore ignores the order presented', () => {
    // The form is a mapping, so only the per-place sequence is ordered — but a host that
    // persists a snapshot will diff, hash or content-address it, and an unstable key order
    // makes two captures of one marking look different. Emitted in code-point order, which is
    // also Rust's `BTreeMap<str>` order, so the two languages agree key for key.
    const Z = place<string>('zeta');
    const A = place<string>('alpha');
    const M = place<string>('mid');
    const m = Marking.from(initial(
      [Z, [tokenAt('z', 1)]], [A, [tokenAt('a', 2)]], [M, [tokenAt('m', 3)]],
    ));

    // Twice over the same marking: identical order, and it is sorted rather than insertion order.
    expect([...m.snapshot().keys()]).toEqual([...m.snapshot().keys()]);
    expect([...m.snapshot().keys()]).toEqual(['alpha', 'mid', 'zeta']);

    // Code-point order, not the default sort's UTF-16 code-unit order. The two agree on every
    // name above, so those cannot tell them apart; this pair can. U+1F600 is stored as the
    // surrogates D83D DE00, which sort *below* U+E000 by code unit and *above* it by code
    // point — and code point is what Rust's `str` and the requirement use.
    const HIGH_BMP = place<string>('\u{E000}-private-use');
    const ASTRAL = place<string>('\u{1F600}-astral');
    expect([HIGH_BMP.name, ASTRAL.name].sort()).toEqual([ASTRAL.name, HIGH_BMP.name]); // the trap
    const unicode = Marking.from(initial([ASTRAL, [tokenAt('x', 1)]], [HIGH_BMP, [tokenAt('y', 2)]]));
    expect([...unicode.snapshot().keys()]).toEqual([HIGH_BMP.name, ASTRAL.name]);

    // And the restore side does not care what order it is handed.
    const forward = m.snapshot();
    const reversed: MarkingSnapshotForm = new Map([...forward].reverse());
    const fromForward = Marking.fromSnapshot(forward);
    const fromReversed = Marking.fromSnapshot(reversed);
    for (const place_ of [Z, A, M]) {
      const asPairs = (mk: Marking): unknown[] =>
        mk.peekTokens(place_).map(t => [t.value, t.createdAt]);
      expect(asPairs(fromReversed)).toEqual(asPairs(fromForward));
    }
  });

  describe.each(BACKENDS)('%s backend', (backend) => {
    it('AC#2/AC#10: a restored marking pre-populates places, and the net consumes those tokens', async () => {
      const P = place<string>('P');
      const OUT = place<string>('OUT');
      const t = Transition.builder('T')
        .inputs(one(P))
        .outputs(outPlace(OUT))
        .action(async (ctx) => { ctx.output(OUT, ctx.input(P)); })
        .build();
      const net = PetriNet.builder('N').transition(t).build();

      const snap = Marking.from(initial([P, [tokenAt('x', 42)]])).snapshot();
      const marking = await makeExecutor(backend, net, new Map(), { restore: snap }).run(5000);

      // AC#10: the restored tokens are the ones the net's own transitions consumed — not
      // merely present in the marking. TypeScript reaches this unaided because `Place` is
      // name-only at runtime, so a name rebuilds a usable key; an implementation with
      // structural (name, tokenType) equality must resolve names against the receiving net
      // instead, and its restore takes the net as a second input ([MOD-024]).
      expect(marking.hasTokens(OUT)).toBe(true);
      expect(marking.peekFirst(OUT)?.value).toBe('x');
      expect(marking.tokenCount(P)).toBe(0); // consumed, not left sitting
    });

    it('AC#7: a restored token on an undeclared place is reported once, as from initialTokens', async () => {
      // CORE-072 AC#4 on the restore seam. The reference executor walked `initialTokens` for
      // this report — which a resume leaves empty — so only the production executor warned.
      const K = place<string>('K');
      const net = PetriNet.builder('N').place(K).build();
      const store = new InMemoryEventStore();
      const restore: MarkingSnapshotForm = new Map([
        ['GONE', [tokenAt('g', 1), tokenAt('h', 2)]], ['EMPTY-GONE', []],
      ]);
      await makeExecutor(backend, net, new Map(), { restore, eventStore: store }).run(5000);

      const warnings = eventsOfType(store, 'log-message').filter(e => e.level === 'WARN');
      expect(warnings.map(e => e.message)).toEqual([expect.stringContaining("unknown place 'GONE'")]);
    });

    it('AC#3: a Delayed transition waits its full interval from the resuming enablement', async () => {
      // The clocks do not come back. A token stamped in 1970 does not shortcut delayed(60_000).
      const P = place<string>('P');
      const OUT = place<string>('OUT');
      const firedAt: number[] = [];
      let monotonic = 0;
      const clock = {
        now: () => monotonic,
        epochNow: () => 1_700_000_000_000 + monotonic,
        sleep: async (delayMs: number, ready: () => boolean, signal: AbortSignal) => {
          if (ready()) return;
          if (delayMs === Infinity) {
            await new Promise<void>(r => signal.addEventListener('abort', () => r(), { once: true }));
            return;
          }
          monotonic += delayMs;
        },
      };
      const t = Transition.builder('T')
        .inputs(one(P))
        .outputs(outPlace(OUT))
        .timing(delayed(60_000))
        .action(async (ctx) => { firedAt.push(clock.now()); ctx.output(OUT, ctx.input(P)); })
        .build();
      const net = PetriNet.builder('N').transition(t).build();

      // createdAt far in the past — older than the delay by decades.
      const snap: MarkingSnapshotForm = new Map([['P', [tokenAt('ancient', 0)]]]);
      const marking = await makeExecutor(backend, net, new Map(), { restore: snap, clock }).run(5000);

      expect(marking.hasTokens(OUT)).toBe(true);
      // Waited the whole interval from this executor's enablement, not from createdAt.
      expect(firedAt[0]).toBeGreaterThanOrEqual(60_000);
    });

    it('AC#4: a Deadline gets a fresh budget — the original bound does not survive', async () => {
      // The asymmetry worth pinning: re-waiting a lower bound is still sound, re-granting an
      // upper bound is not. A deadline the net promised can be silently missed across a restore,
      // which is why a hard bound belongs in the payload or in an action timeout instead.
      const P = place<string>('P');
      const OUT = place<string>('OUT');
      const store = new InMemoryEventStore();
      const t = Transition.builder('T')
        .inputs(one(P))
        .outputs(outPlace(OUT))
        .timing(deadline(50_000))
        .action(async (ctx) => { ctx.output(OUT, ctx.input(P)); })
        .build();
      const net = PetriNet.builder('N').transition(t).build();

      // Stamped long enough ago that the original budget would be exhausted many times over.
      const snap: MarkingSnapshotForm = new Map([['P', [tokenAt('old', 1)]]]);
      const marking = await makeExecutor(
        backend, net, new Map(), { restore: snap, eventStore: store, deadlineToleranceMs: 0 },
      ).run(5000);

      // It fires rather than being reaped, and nothing is emitted for the elapsed original budget.
      expect(marking.hasTokens(OUT)).toBe(true);
      expect(eventsOfType(store, 'transition-timed-out')).toHaveLength(0);
    });

    it('AC#9: the engine does not re-stamp, including under an injected epoch clock', async () => {
      // Restore is the one path where the engine hands back a timestamp it did not choose.
      // The clock below would stamp everything at a fixed instant if anything re-stamped.
      const P = place<string>('P');
      const SIT = place<string>('SIT');
      const OUT = place<string>('OUT');
      const clock = {
        now: () => 0,
        epochNow: () => 9_999_999,
        sleep: async () => {},
      };
      const t = Transition.builder('T')
        .inputs(one(P))
        .outputs(outPlace(OUT))
        .action(async (ctx) => { ctx.output(OUT, ctx.input(P)); })
        .build();
      const net = PetriNet.builder('N').place(SIT).transition(t).build();

      const snap: MarkingSnapshotForm = new Map([
        ['P', [tokenAt('moved', 111)]],
        ['SIT', [tokenAt('still', 222)]],
      ]);
      const marking = await makeExecutor(backend, net, new Map(), { restore: snap, clock }).run(5000);

      // Untouched token keeps its own stamp...
      expect(marking.peekTokens(SIT)[0]!.createdAt).toBe(222);
      // ...and the token the action *produced* is executor-minted, so it does follow the clock
      // (TIME-015 AC#13). The two rules coexist: restore preserves, production stamps.
      expect(marking.peekTokens(OUT)[0]!.createdAt).toBe(9_999_999);
    });

    it('AC#11: restore and a non-empty initialTokens are rejected, not merged', () => {
      const P = place<string>('P');
      const net = PetriNet.builder('N').place(P).build();
      expect(() => makeExecutor(
        backend, net, initial([P, [tokenOf('from-args')]]),
        { restore: new Map([['P', [tokenAt('from-snapshot', 1)]]]) },
      )).toThrow('CORE-073');
    });
  });
});

describe('ENV-014 — mid-execution snapshot', () => {
  describe.each(BACKENDS)('%s backend', (backend) => {
    it('AC#1/#2/#3: snapshots a running net, keeps running, and the copy is independent', async () => {
      const ENV = environmentPlace<string>('ENV');
      const OUT = place<string>('OUT');
      const t = Transition.builder('T')
        .inputs(one(ENV.place))
        .outputs(outPlace(OUT))
        .action(async (ctx) => { ctx.output(OUT, ctx.input(ENV.place)); })
        .build();
      const net = PetriNet.builder('N').place(ENV.place).transition(t).build();
      const executor = makeExecutor(backend, net, new Map(), {
        environmentPlaces: new Set([ENV]),
      });

      const running = executor.run(5000);
      await executor.injectValue(ENV, 'first');
      await new Promise<void>(r => setTimeout(r, 20));

      const taken = executor.snapshot();
      expect(taken.marking.get('OUT')!.map(t2 => t2.value)).toEqual(['first']);

      // The net kept running: a second injection still lands.
      await executor.injectValue(ENV, 'second');
      await new Promise<void>(r => setTimeout(r, 20));
      executor.drain();
      const final = await running;

      expect(final.tokenCount(OUT)).toBe(2);
      // The earlier capture is an owned copy — later firings did not reach into it.
      expect(taken.marking.get('OUT')!).toHaveLength(1);
    });

    it('AC#4: rejected once drained or closed', async () => {
      const ENV = environmentPlace<string>('ENV');
      const net = PetriNet.builder('N').place(ENV.place).build();
      const executor = makeExecutor(backend, net, new Map(), {
        environmentPlaces: new Set([ENV]),
      });
      const running = executor.run(5000);
      executor.drain();
      await running;
      expect(() => executor.snapshot()).toThrow('ENV-014');
    });

    it('AC#5/#6: a snapshot taken with an action in flight says so, and shows the gap', async () => {
      // The case the flag exists for: the firing's inputs are already consumed and its outputs
      // have not landed, so those tokens are in neither place. The marking is a valid
      // observation and an invalid restore point, and the caller can tell which.
      const P = place<string>('P');
      const OUT = place<string>('OUT');
      let release!: () => void;
      const gate = new Promise<void>(r => { release = r; });
      const t = Transition.builder('T')
        .inputs(one(P))
        .outputs(outPlace(OUT))
        .action(async (ctx) => { await gate; ctx.output(OUT, ctx.input(P)); })
        .build();
      const net = PetriNet.builder('N').transition(t).build();
      const executor = makeExecutor(backend, net, initial([P, [tokenOf('x')]]));

      const running = executor.run(5000);
      await new Promise<void>(r => setTimeout(r, 20));

      const midFlight = executor.snapshot();
      expect(midFlight.actionInFlight).toBe(true);
      // AC#6: the consumed token is in neither place — this is the gap that makes it unusable
      // as a restore point.
      expect(midFlight.marking.get('P') ?? []).toHaveLength(0);
      expect(midFlight.marking.get('OUT') ?? []).toHaveLength(0);

      release();
      const final = await running;
      expect(final.hasTokens(OUT)).toBe(true);
    });

    it('AC#1/#2: a second snapshot sees the progress made since the first', async () => {
      // The checkpoint-saver shape: one executor, snapshotted repeatedly. A capture served from
      // a cache filled by the first call returns the first marking forever, flagged as a valid
      // restore point — every ENV-014 test that takes a single snapshot cannot see that.
      const ENV = environmentPlace<string>('ENV');
      const OUT = place<string>('OUT');
      const t = Transition.builder('T')
        .inputs(one(ENV.place))
        .outputs(outPlace(OUT))
        .action(async (ctx) => { ctx.output(OUT, ctx.input(ENV.place)); })
        .build();
      const net = PetriNet.builder('N').place(ENV.place).transition(t).build();
      const executor = makeExecutor(backend, net, new Map(), { environmentPlaces: new Set([ENV]) });

      const running = executor.run(5000);
      await executor.injectValue(ENV, 'first');
      await new Promise<void>(r => setTimeout(r, 20));
      const s1 = executor.snapshot();

      await executor.injectValue(ENV, 'second');
      await new Promise<void>(r => setTimeout(r, 20));
      const s2 = executor.snapshot();

      expect(s1.marking.get('OUT')!.map(tk => tk.value)).toEqual(['first']);
      expect(s2.marking.get('OUT')!.map(tk => tk.value)).toEqual(['first', 'second']);
      expect(s2.actionInFlight).toBe(false);

      executor.drain();
      await running;
    });

    it('getMarking() mid-run follows the net, with no snapshot() in between to refresh it', async () => {
      // The staleness snapshot() inherited lived in getMarking(): the precompiled executor
      // materialises a Marking lazily and used to keep the first one for the rest of the run.
      // Kept apart from the test above on purpose — snapshot() re-syncs as a side effect, so a
      // getMarking() assertion next to one passes whether or not getMarking() itself is fixed.
      const ENV = environmentPlace<string>('ENV');
      const OUT = place<string>('OUT');
      const t = Transition.builder('T')
        .inputs(one(ENV.place))
        .outputs(outPlace(OUT))
        .action(async (ctx) => { ctx.output(OUT, ctx.input(ENV.place)); })
        .build();
      const net = PetriNet.builder('N').place(ENV.place).transition(t).build();
      const executor = makeExecutor(backend, net, new Map(), { environmentPlaces: new Set([ENV]) });

      const running = executor.run(5000);
      await executor.injectValue(ENV, 'first');
      await new Promise<void>(r => setTimeout(r, 20));
      expect(executor.getMarking().tokenCount(OUT)).toBe(1);

      await executor.injectValue(ENV, 'second');
      await new Promise<void>(r => setTimeout(r, 20));
      expect(executor.getMarking().tokenCount(OUT)).toBe(2);

      executor.drain();
      const final = await running;
      // Once the run is over the view is stable again: the object run() resolved with.
      expect(executor.getMarking()).toBe(final);
    });

    it('AC#4: rejected once closed, not only once drained', async () => {
      const ENV = environmentPlace<string>('ENV');
      const net = PetriNet.builder('N').place(ENV.place).build();
      const executor = makeExecutor(backend, net, new Map(), { environmentPlaces: new Set([ENV]) });
      const running = executor.run(5000);
      await new Promise<void>(r => setTimeout(r, 20));
      expect(() => executor.snapshot()).not.toThrow(); // positive control: it is available first
      executor.close();
      await running;
      expect(() => executor.snapshot()).toThrow('ENV-014');
    });

    it('AC#7: an accepted but un-injected external event counts as work in flight', async () => {
      // inject() accepts the token at the call and deposits it on a following cycle. Between
      // the two it is in no place, so a snapshot taken there is not a restore point: resuming
      // from it loses an event the host was told nothing bad about.
      const ENV = environmentPlace<string>('ENV');
      const net = PetriNet.builder('N').place(ENV.place).build();
      const executor = makeExecutor(backend, net, new Map(), { environmentPlaces: new Set([ENV]) });
      const running = executor.run(5000);
      await new Promise<void>(r => setTimeout(r, 20));

      const admitted = executor.inject(ENV, tokenOf('queued')); // accepted, deliberately not awaited
      const between = executor.snapshot();
      expect(between.marking.get('ENV') ?? []).toHaveLength(0);
      expect(between.actionInFlight).toBe(true);

      expect(await admitted).toBe(true);
      const after = executor.snapshot();
      expect(after.marking.get('ENV')!.map(tk => tk.value)).toEqual(['queued']);
      expect(after.actionInFlight).toBe(false);

      // The fire-and-forget form queues through the same path.
      executor.injectNoAwait(ENV, 'queued-2');
      expect(executor.snapshot().actionInFlight).toBe(true);
      await new Promise<void>(r => setTimeout(r, 20));
      const settled = executor.snapshot();
      expect(settled.marking.get('ENV')).toHaveLength(2);
      expect(settled.actionInFlight).toBe(false);

      executor.drain();
      await running;
    });

    it('AC#7: mid-deposit of a batch of external events, the ones not yet deposited still count', async () => {
      // Two events accepted before the orchestrator's next external-events phase, observed from
      // the token-added emit of each. After the first deposit one accepted event is still in no
      // place; after the second none is, and the capture is a restore point again.
      const ENV = environmentPlace<string>('ENV');
      const seen: SnapshotResult[] = [];
      const holder: { executor?: BitmapNetExecutor | PrecompiledNetExecutor } = {};
      const inner = new InMemoryEventStore();
      const store: EventStore = {
        append(event) {
          inner.append(event);
          if (event.type === 'token-added') seen.push(holder.executor!.snapshot());
        },
        events: () => inner.events(),
        isEnabled: () => true,
        size: () => inner.size(),
        isEmpty: () => inner.isEmpty(),
      };
      const net = PetriNet.builder('N').place(ENV.place).build();
      holder.executor = makeExecutor(backend, net, new Map(), {
        environmentPlaces: new Set([ENV]), eventStore: store,
      });
      const running = holder.executor.run(5000);
      await new Promise<void>(r => setTimeout(r, 20));

      const both = [holder.executor.inject(ENV, tokenOf('e1')), holder.executor.inject(ENV, tokenOf('e2'))];
      expect(await Promise.all(both)).toEqual([true, true]);

      expect(seen.map(r => [r.marking.get('ENV')?.length, r.actionInFlight])).toEqual([[1, true], [2, false]]);

      holder.executor.drain();
      await running;
    });

    it('AC#8: a snapshot requested by the running action is flagged — from its synchronous prefix and after it has suspended', async () => {
      // A net-native checkpoint transition. Both halves of AC#8, because they are reported by
      // different machinery: before the action's first await the firing is not yet registered
      // in flight (only consumed), after it the orchestrator has moved on and the firing is an
      // ordinary in-flight action. Either way the inputs are consumed and the outputs have not
      // landed, so the token is in neither place.
      //
      // Bounded by the calls returning, not by patience: TypeScript's snapshot() is synchronous,
      // so "does not park the orchestrator against itself" is the action reaching its output
      // at all — a self-deadlock would surface as run()'s 5 s timeout rejecting.
      const P = place<string>('P');
      const OUT = place<string>('OUT');
      let inPrefix: SnapshotResult | undefined;
      let afterSuspend: SnapshotResult | undefined;
      const holder: { executor?: BitmapNetExecutor | PrecompiledNetExecutor } = {};
      const t = Transition.builder('T')
        .inputs(one(P))
        .outputs(outPlace(OUT))
        .action(async (ctx) => {
          inPrefix = holder.executor!.snapshot();
          await new Promise<void>(r => setTimeout(r, 10));
          afterSuspend = holder.executor!.snapshot();
          ctx.output(OUT, ctx.input(P));
        })
        .build();
      const net = PetriNet.builder('N').transition(t).build();
      holder.executor = makeExecutor(backend, net, initial([P, [tokenOf('x')]]));

      const final = await holder.executor.run(5000);

      expect(final.tokenCount(OUT)).toBe(1);
      for (const seen of [inPrefix, afterSuspend]) {
        expect(seen).toBeDefined();
        expect(seen!.marking.get('P') ?? []).toHaveLength(0);
        expect(seen!.marking.get('OUT') ?? []).toHaveLength(0);
        expect(seen!.actionInFlight).toBe(true);
        expect(staticLib.isRestorePoint(seen!)).toBe(false);
      }
    });

    it('AC#6: a snapshot taken from an event-store callback mid-cycle is flagged while tokens are in neither place', async () => {
      // Observability rides the event store, so a checkpoint saver written as a store decorator
      // is the expected pattern — and `append` is called synchronously from inside the cycle:
      // after the inputs are consumed (token-removed, transition-started) and between the
      // deposits of one firing's outputs (token-added). `transition-completed` is the settled
      // instant, and the one a saver should key on.
      const P = place<string>('P');
      const A = place<string>('A');
      const B = place<string>('B');
      const seen: [string, SnapshotResult][] = [];
      const holder: { executor?: BitmapNetExecutor | PrecompiledNetExecutor } = {};
      const inner = new InMemoryEventStore();
      const store: EventStore = {
        append(event) {
          inner.append(event);
          const probe = event.type === 'token-removed' || event.type === 'transition-started'
            || event.type === 'token-added' || event.type === 'transition-completed';
          if (probe) seen.push([event.type, holder.executor!.snapshot()]);
        },
        events: () => inner.events(),
        isEnabled: () => true,
        size: () => inner.size(),
        isEmpty: () => inner.isEmpty(),
      };
      const t = Transition.builder('T')
        .inputs(one(P))
        .outputs(andPlaces(A, B))
        .action(async (ctx) => { const v = ctx.input(P); ctx.output(A, v); ctx.output(B, v); })
        .build();
      const net = PetriNet.builder('N').transition(t).build();
      holder.executor = makeExecutor(backend, net, initial([P, [tokenOf('x')]]), { eventStore: store });

      await holder.executor.run(5000);

      const count = (r: SnapshotResult): number =>
        [...r.marking.values()].reduce((n, tokens) => n + tokens.length, 0);
      const by = (type: string): SnapshotResult[] => seen.filter(([ty]) => ty === type).map(([, r]) => r);

      // Inputs consumed, outputs not landed: zero tokens anywhere, and the flag says so.
      for (const type of ['token-removed', 'transition-started']) {
        expect(by(type)).toHaveLength(1);
        expect(count(by(type)[0]!)).toBe(0);
        expect(by(type)[0]!.actionInFlight).toBe(true);
      }
      // First of two deposits: one token of the two this firing owes. Not a restore point.
      const added = by('token-added');
      expect(added).toHaveLength(2);
      expect(count(added[0]!)).toBe(1);
      expect(added[0]!.actionInFlight).toBe(true);
      // Every output landed and nothing else is running: settled, and reported as such.
      const completed = by('transition-completed');
      expect(completed).toHaveLength(1);
      expect(count(completed[0]!)).toBe(2);
      expect(completed[0]!.actionInFlight).toBe(false);
    });

    it('AC#5: isRestorePoint() answers the question a checkpointing caller asks, on a live result', async () => {
      // The free-function twin of Java's `SnapshotResult.isRestorePoint()` and Rust/Python's
      // `is_restore_point` — SnapshotResult is a plain interface here, so there is no method to
      // hang it on. Exported from the runtime entry point and from the package root, and they
      // are one function, not two that could drift.
      expect(typeof runtimeLib.isRestorePoint).toBe('function');
      expect(runtimeLib.isRestorePoint).toBe(staticLib.isRestorePoint);
      const { isRestorePoint } = staticLib;

      const P = place<string>('P');
      const OUT = place<string>('OUT');
      const ENV = environmentPlace<string>('ENV');
      let release!: () => void;
      const gate = new Promise<void>(r => { release = r; });
      const t = Transition.builder('T')
        .inputs(one(P))
        .outputs(outPlace(OUT))
        .action(async (ctx) => { await gate; ctx.output(OUT, ctx.input(P)); })
        .build();
      const net = PetriNet.builder('N').place(ENV.place).transition(t).build();
      const executor = makeExecutor(backend, net, initial([P, [tokenOf('x')]]), {
        environmentPlaces: new Set([ENV]),
      });
      const running = executor.run(5000);
      await new Promise<void>(r => setTimeout(r, 20));

      // An action in flight: an observation, not a restore point.
      const midFlight = executor.snapshot();
      expect(midFlight.actionInFlight).toBe(true);
      expect(isRestorePoint(midFlight)).toBe(false);

      release();
      await new Promise<void>(r => setTimeout(r, 20));
      const settled = executor.snapshot();
      expect(settled.actionInFlight).toBe(false);
      expect(isRestorePoint(settled)).toBe(true);

      // The second thing the flag covers (AC#7): an accepted, un-injected event.
      executor.injectNoAwait(ENV, 'queued');
      expect(isRestorePoint(executor.snapshot())).toBe(false);
      await new Promise<void>(r => setTimeout(r, 20));
      const again = executor.snapshot();
      expect(isRestorePoint(again)).toBe(true);

      // And a result that says it is one really does restore to the same marking (CORE-073).
      executor.drain();
      await running;
      expect([...Marking.fromSnapshot(again.marking).snapshot()]).toEqual([...again.marking]);
    });

    it('AC#5: a snapshot taken with nothing in flight reports that', async () => {
      const ENV = environmentPlace<string>('ENV');
      const SIT = place<string>('SIT');
      const net = PetriNet.builder('N').place(ENV.place).place(SIT).build();
      const executor = makeExecutor(backend, net, initial([SIT, [tokenOf('quiet')]]), {
        environmentPlaces: new Set([ENV]),
      });

      const running = executor.run(5000);
      await new Promise<void>(r => setTimeout(r, 20));

      const taken = executor.snapshot();
      expect(taken.actionInFlight).toBe(false);
      expect(taken.marking.get('SIT')!.map(t => t.value)).toEqual(['quiet']);

      executor.drain();
      await running;
    });
  });
});

describe('CORE-073 AC#12 — the reference and production executors snapshot key for key', () => {
  // Bitmap keeps a Marking whose drained places linger as empty queues; Precompiled rebuilds
  // one from non-empty ring buffers. Same net, same inputs, and until the emission rule was
  // pinned two different artefacts — which a host that hashes or content-addresses its
  // checkpoints sees as two different states.
  const render = (r: SnapshotResult): [string, unknown[]][] =>
    [...r.marking].map(([name, tokens]) => [name, tokens.map(tk => tk.value)]);

  const scenario = async (backend: Backend): Promise<{ mid: SnapshotResult; final: MarkingSnapshotForm }> => {
    const ENV = environmentPlace<string>('ENV');
    const P = place<string>('P');
    const OUT = place<string>('OUT');
    const viaEnv = Transition.builder('viaEnv')
      .inputs(one(ENV.place)).outputs(outPlace(OUT))
      .action(async (ctx) => { ctx.output(OUT, ctx.input(ENV.place)); })
      .build();
    const viaP = Transition.builder('viaP')
      .inputs(one(P)).outputs(outPlace(OUT))
      .action(async (ctx) => { ctx.output(OUT, ctx.input(P)); })
      .build();
    const net = PetriNet.builder('N').transitions(viaEnv, viaP).build();
    // P is restored with a token and drained by the run; EMPTY and GONE arrive empty, one
    // declared nowhere; GONE2 is undeclared and retained (CORE-072).
    const restore: MarkingSnapshotForm = new Map([
      ['P', [tokenAt('p', 1)]], ['EMPTY', []], ['GONE', []], ['GONE2', [tokenAt('g', 2)]],
    ]);
    const executor = makeExecutor(backend, net, new Map(), { restore, environmentPlaces: new Set([ENV]) });
    const running = executor.run(5000);
    await executor.inject(ENV, tokenAt('e', 3));
    await new Promise<void>(r => setTimeout(r, 20));
    const mid = executor.snapshot();
    executor.drain();
    return { mid, final: (await running).snapshot() };
  };

  it('mid-run and final snapshots are identical across backends, with no empty place in either', async () => {
    const bitmap = await scenario('bitmap');
    const precompiled = await scenario('precompiled');

    expect(render(bitmap.mid)).toEqual([['GONE2', ['g']], ['OUT', ['p', 'e']]]);
    expect(render(bitmap.mid)).toEqual(render(precompiled.mid));
    expect(bitmap.mid.actionInFlight).toBe(precompiled.mid.actionInFlight);
    expect([...bitmap.final.keys()]).toEqual(['GONE2', 'OUT']);
    expect([...bitmap.final.keys()]).toEqual([...precompiled.final.keys()]);
  });
});

describe('EVT-014 AC#4 / CORE-073 AC#12 on the event path — canonical order where a snapshot is rendered', () => {
  // The rule follows the form: it applies wherever a marking snapshot reaches an ordered
  // medium, not only to the value handed back to a host. These emit in place-*id* order
  // before the fix — deterministic within TypeScript and arbitrary relative to Java and Rust,
  // which is the quiet version of the defect Java hit loudly with a randomising immutable map.
  //
  // Pinned rather than left true by construction: "passes by design" and "passes by luck" look
  // identical from the test, and only one survives a refactor that touches iteration order.
  describe.each(BACKENDS)('%s backend', (backend) => {
    it('EVT-014 AC#4: a marking-snapshot event carries places in code-point order, not declaration order', async () => {
      // Declared deliberately out of order, so place-id order and name order disagree.
      const Z = place<string>('zeta');
      const A = place<string>('alpha');
      const M = place<string>('mid');
      // The pair that tells code-point order from UTF-16 code-unit order (see the Marking
      // test above); declared astral-first so neither declaration order nor the default
      // sort produces the right answer by accident.
      const ASTRAL = place<string>('\u{1F600}-astral');
      const HIGH_BMP = place<string>('\u{E000}-private-use');
      const SINK = place<string>('sink');
      const t = Transition.builder('T')
        .inputs(one(Z))
        .outputs(outPlace(SINK))
        .action(async (ctx) => { ctx.output(SINK, ctx.input(Z)); })
        .build();
      const net = PetriNet.builder('N')
        .place(Z).place(ASTRAL).place(A).place(HIGH_BMP).place(M).transition(t).build();

      const store = new InMemoryEventStore();
      await makeExecutor(backend, net, initial(
        [Z, [tokenOf('z')]], [ASTRAL, [tokenOf('u')]], [A, [tokenOf('a')]],
        [HIGH_BMP, [tokenOf('h')]], [M, [tokenOf('m')]],
      ), { eventStore: store }).run(5000);

      const snapshots = eventsOfType(store, 'marking-snapshot');
      expect(snapshots.length).toBeGreaterThan(0);
      for (const snap of snapshots) {
        const names = [...snap.marking.keys()];
        // compareCodePoints, not `<`: the two disagree above U+FFFF, and code-point order is
        // what the requirement specifies and what Rust's `str` ordering gives.
        expect(names).toEqual([...names].sort(compareCodePoints));
        // And concretely on the first one, where all three places are still marked.
      }
      expect([...snapshots[0]!.marking.keys()]).toEqual(
        ['alpha', 'mid', 'zeta', HIGH_BMP.name, ASTRAL.name]);
    });
  });

  it('convertMarking keeps a place named __proto__ instead of silently dropping it', () => {
    // An ordinary object literal assigned at `__proto__` sets the prototype: the entry vanishes
    // and the marking serializes as `{}`. Verified before the fix — this is data loss on the
    // archive path, not an ordering nit.
    const marking = new Map<string, readonly Token<unknown>[]>([
      ['__proto__', [tokenAt('payload', 7)]],
      ['ordinary', [tokenAt('other', 8)]],
    ]);

    const converted = convertMarking(marking);

    expect(Object.keys(converted)).toContain('__proto__');
    expect(converted['__proto__']).toHaveLength(1);
    // And it survives the serialization the archive actually performs.
    const round = JSON.parse(JSON.stringify(converted)) as Record<string, unknown[]>;
    expect(round['__proto__']).toHaveLength(1);
    expect(round['ordinary']).toHaveLength(1);
  });
});

describe('NU-011 — resume-safe fresh-name minting', () => {
  interface NuMsg { readonly cid: NameId; }

  /** The exports a fork/join net is built from — swappable for a freshly loaded module graph. */
  type Lib = typeof import('../../src/index.js');

  /** A fork that mints a ν-name and stamps both branches with it. */
  function forkNet(lib: Pick<Lib, 'place' | 'Transition' | 'PetriNet' | 'one' | 'andPlaces' | 'outPlace' | 'matchSpec' | 'matchKey'> = staticLib): {
    net: PetriNet; SRC: Place<string>; A: Place<NuMsg>; B: Place<NuMsg>; MERGED: Place<string>;
  } {
    const SRC = lib.place<string>('src');
    const A = lib.place<NuMsg>('branchA');
    const B = lib.place<NuMsg>('branchB');
    const MERGED = lib.place<string>('merged');
    const fork = lib.Transition.builder('fork')
      .inputs(lib.one(SRC))
      .outputs(lib.andPlaces(A, B))
      .action(async (ctx) => {
        const id = ctx.freshName();
        ctx.output(A, { cid: id });
        ctx.output(B, { cid: id });
      })
      .build();
    const join = lib.Transition.builder('join')
      .inputs(lib.one(A), lib.one(B))
      .match(lib.matchSpec(
        lib.matchKey(A, (m: NuMsg) => m.cid),
        lib.matchKey(B, (m: NuMsg) => m.cid),
      ))
      .outputs(lib.outPlace(MERGED))
      .action(async (ctx) => { ctx.output(MERGED, String(ctx.input(A).cid)); })
      .build();
    return { net: lib.PetriNet.builder('N').transitions(fork, join).build(), SRC, A, B, MERGED };
  }

  /**
   * Splits a minted name `<transition>#<scope>:<n>`. With `:` and `#` both banned from a scope
   * the parse is unique: the last `:` splits off the counter, then the last `#` before it
   * splits off the scope — a transition name may itself contain either character.
   */
  function parseMinted(name: string): { transition: string; scope: string; n: number } {
    const colon = name.lastIndexOf(':');
    const hash = name.lastIndexOf('#', colon);
    return { transition: name.slice(0, hash), scope: name.slice(hash + 1, colon), n: Number(name.slice(colon + 1)) };
  }

  describe.each(BACKENDS)('%s backend', (backend) => {
    it('AC#5: the default scope is 128 random bits — per executor, and not the execution id, which stays a counter', async () => {
      // Two different values since R1: executionId() is reproducible for a fixed construction
      // order (TIME-015 AC#14), which is exactly what makes it useless as a collision-safe
      // scope across processes — every process's first executor is `0`.
      const { net, SRC, MERGED } = forkNet();
      const executor = makeExecutor(backend, net, initial([SRC, [tokenOf('a'), tokenOf('b')]]));
      const minted = (await executor.run(5000)).peekTokens(MERGED).map(t => parseMinted(String(t.value)));

      expect(minted).toHaveLength(2);
      for (const m of minted) {
        expect(m.transition).toBe('fork');
        expect(m.scope).toMatch(/^[0-9a-f]{32}$/);
        expect(m.scope).not.toBe(executor.executionId());
      }
      // One scope per executor; within it `<n>` is the per-executor counter from 0 — the
      // randomness never reaches the sequence.
      expect(new Set(minted.map(m => m.scope)).size).toBe(1);
      expect(minted.map(m => m.n).sort()).toEqual([0, 1]);

      // "Different for every executor" — inside one process too, not only across them. A scope
      // drawn once per process would pass the fresh-process test below and still hand two
      // executions restored side by side (AC#4) the same names.
      const sibling = makeExecutor(backend, net, initial([SRC, [tokenOf('c')]]));
      const siblingMinted = (await sibling.run(5000)).peekTokens(MERGED).map(t => parseMinted(String(t.value)));
      expect(siblingMinted).toHaveLength(1);
      expect(siblingMinted[0]!.scope).toMatch(/^[0-9a-f]{32}$/);
      expect(siblingMinted[0]!.scope).not.toBe(minted[0]!.scope);
    });

    it('AC#5 (AC#1/AC#4 across processes): the first executor of two fresh processes do not mint the same name', async () => {
      // The durable-restart case, which is what restore is for. Each "process" is a freshly
      // loaded module graph, so every process-local counter starts again at zero — under a
      // counter-derived default scope both executors are `0` and both mint `fork#0:0`, and a
      // NU-020 join then pairs a restored token from one segment with a fresh one from another.
      const mintedInFreshProcess = async (): Promise<string[]> => {
        vi.resetModules();
        const lib = await import('../../src/index.js');
        const { net, SRC, MERGED } = forkNet(lib);
        const tokens = new Map([[SRC, [lib.tokenOf('go')]]]);
        const executor = backend === 'bitmap'
          ? new lib.BitmapNetExecutor(net, tokens) : new lib.PrecompiledNetExecutor(net, tokens);
        // Control: this really is a fresh process as far as the counter is concerned.
        expect(executor.executionId()).toBe('0');
        return (await executor.run(5000)).peekTokens(MERGED).map(t => String(t.value));
      };

      const first = await mintedInFreshProcess();
      const second = await mintedInFreshProcess();
      expect(first).toHaveLength(1);
      expect(second).toHaveLength(1);
      expect(second).not.toEqual(first);
    });

    it('AC#1: a resumed execution does not re-mint a name present in the restored marking', async () => {
      // The whole hazard: counting firings from zero re-mints `fork#…:0`, which is already live in
      // the restored marking. Because a NU-020 join correlates on name equality alone, the
      // collision never raises — it silently merges segments.
      const { net, SRC, MERGED } = forkNet();

      // Minted names are read from MERGED, which carries the cid as its value: the join drains
      // branchA/branchB, so a completed fork leaves no trace of its name there.
      const first = await makeExecutor(backend, net, initial([SRC, [tokenOf('one')]])).run(5000);
      const mintedBefore = first.peekTokens(MERGED).map(t => String(t.value));
      expect(mintedBefore).toHaveLength(1);

      // Resume from that marking, with fresh work so the resumed segment mints at least as many.
      const snap = new Map(first.snapshot());
      snap.set('src', [tokenAt('two', 1)]);
      const resumed = await makeExecutor(backend, net, new Map(), { restore: snap }).run(5000);

      const mintedAfter = resumed.peekTokens(MERGED).map(t => String(t.value));
      // The restored name is still there, exactly once, and one new name joined it.
      expect(mintedAfter).toHaveLength(2);
      expect(mintedAfter.filter(n => n === mintedBefore[0]!)).toHaveLength(1);
      // Compared structurally: both segments started their counter at 0, so the scope is the
      // only thing keeping the names apart.
      const fresh = parseMinted(mintedAfter.find(n => n !== mintedBefore[0]!)!);
      expect(fresh.n).toBe(parseMinted(mintedBefore[0]!).n);
      expect(fresh.scope).not.toBe(parseMinted(mintedBefore[0]!).scope);
    });

    it('AC#2: a restored token awaiting a sibling is not correlated with a fresh one', async () => {
      // The silent failure NU-011 exists to prevent. Restore a marking holding a half-finished
      // fork — a token on branchA with no sibling — then run a fresh fork. If the resumed segment
      // re-minted the same name, the join would pair the restored orphan with a new branchB token
      // and produce a merge across run segments.
      //
      // Scopes are pinned so the orphan's name is known without depending on which executor
      // the process happened to construct first.
      const orphanName = 'fork#segment-1:0';
      const resume = async (executionScope: string | undefined): Promise<Marking> => {
        const { net } = forkNet();
        const snap: MarkingSnapshotForm = new Map([
          ['branchA', [tokenAt({ cid: nameId(orphanName) }, 1)]],
          ['src', [tokenAt('fresh', 2)]],
        ]);
        return makeExecutor(backend, net, new Map(), { restore: snap, executionScope }).run(5000);
      };
      const { A, B, MERGED } = forkNet();

      for (const scope of ['segment-2', undefined]) {
        const marking = await resume(scope);
        // The fresh fork's pair joined with **each other**, exactly once...
        expect(marking.tokenCount(MERGED)).toBe(1);
        // ...and the merged token carries the *fresh* name, not the restored orphan's...
        expect(marking.peekFirst(MERGED)?.value).not.toBe(orphanName);
        // ...and the orphan is still waiting, alone and uncorrelated.
        expect(marking.tokenCount(A)).toBe(1);
        expect(String((marking.peekFirst(A)?.value as NuMsg).cid)).toBe(orphanName);
        expect(marking.tokenCount(B)).toBe(0);
      }

      // Negative control — what the assertions above discriminate against. Resume under the
      // *same* scope and the collision happens: the join takes the orphan (FIFO, it is older)
      // with the fresh sibling, and the fresh branchA token is the one left stranded.
      const collided = await resume('segment-1');
      expect(collided.peekFirst(MERGED)?.value).toBe(orphanName);
      expect(collided.tokenCount(A)).toBe(1);
    });

    it('AC#3: a pinned scope makes the minted sequence reproducible', async () => {
      const mintedIn = async (executionScope: string): Promise<string[]> => {
        const { net, SRC, MERGED } = forkNet();
        const m = await makeExecutor(
          backend, net, initial([SRC, [tokenOf('go'), tokenOf('again')]]), { executionScope },
        ).run(5000);
        return m.peekTokens(MERGED).map(t => String(t.value)).sort();
      };

      // Same scope, same firing order → identical names. This is what makes a segment replayable.
      expect(await mintedIn('run-a')).toEqual(['fork#run-a:0', 'fork#run-a:1']);
      expect(await mintedIn('run-a')).toEqual(await mintedIn('run-a'));
      // A different scope changes them, which is what makes a resume collision-safe.
      expect(await mintedIn('run-b')).toEqual(['fork#run-b:0', 'fork#run-b:1']);
    });

    it('AC#4: two executions restored from the same snapshot mint disjoint name sets', async () => {
      const snap: MarkingSnapshotForm = new Map([['src', [tokenAt('go', 1)]]]);
      const mintedFrom = async (): Promise<string[]> => {
        const { net, MERGED } = forkNet();
        const m = await makeExecutor(backend, net, new Map(), { restore: snap }).run(5000);
        return m.peekTokens(MERGED).map(t => String(t.value));
      };

      const [left, right] = await Promise.all([mintedFrom(), mintedFrom()]);
      expect(left.length).toBeGreaterThan(0);
      // Disjoint because each executor draws its own random default scope.
      expect(left.filter(n => right.includes(n))).toEqual([]);
    });

    it('AC#6: the scope is validated: empty, or containing the `:` or `#` a minted name is parsed on', () => {
      const { net, SRC } = forkNet();
      const tokens = initial([SRC, [tokenOf('go')]]);
      for (const executionScope of ['', 'a:b', 'a#b', ':', '#']) {
        expect(() => makeExecutor(backend, net, tokens, { executionScope })).toThrow('NU-011');
      }
      // Length zero is what is rejected — not "blank". Whitespace is a legal, if odd, scope.
      expect(() => makeExecutor(backend, net, tokens, { executionScope: ' ' })).not.toThrow();
    });

    it('AC#6: a transition name containing # and : still parses, because the scope holds neither', async () => {
      const SRC = place<string>('src');
      const OUT = place<string>('out');
      const t = Transition.builder('odd#name:1')
        .inputs(one(SRC)).outputs(outPlace(OUT))
        .action(async (ctx) => { ctx.output(OUT, String(ctx.freshName())); })
        .build();
      const net = PetriNet.builder('N').transition(t).build();
      const m = await makeExecutor(backend, net, initial([SRC, [tokenOf('go')]]), { executionScope: 'pinned' }).run(5000);

      expect(parseMinted(String(m.peekFirst(OUT)!.value))).toEqual({ transition: 'odd#name:1', scope: 'pinned', n: 0 });
    });
  });
});
