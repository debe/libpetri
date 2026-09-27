import { describe, it, expect } from 'vitest';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { PrecompiledNetExecutor } from '../../src/runtime/precompiled-net-executor.js';
import type { Marking } from '../../src/runtime/marking.js';
import { InMemoryEventStore } from '../../src/event/event-store.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, type Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { andPlaces, forwardInput, outPlace, timeout, xor } from '../../src/core/out.js';
import { tokenAt, type Token } from '../../src/core/token.js';
import { nameId } from '../../src/core/name.js';
import { matchKey, matchSpec, relayKey } from '../../src/core/match-spec.js';
import { SubnetDef } from '../../src/core/subnet-def.js';

/**
 * [NU-054] join relay: the declaration and its build-time rejections (AC1), the runtime check
 * that every token a join writes into a relay target carries the matched name (AC2, both
 * executors), and composition remapping the targets like the keys.
 */

interface Msg {
  readonly cid: string;
  readonly tag?: string;
}
const byCid = (m: Msg) => nameId(m.cid);
/** A projection that yields no name for a token without `cid`, as a user key may. */
const byCidOrNone = (m: Msg) => (m.cid === '' ? (null as unknown as ReturnType<typeof nameId>) : nameId(m.cid));

describe('NU-054 relay declaration (AC1)', () => {
  const a = place<Msg>('A');
  const b = place<Msg>('B');
  const c = place<Msg>('C');
  const other = place<Msg>('other');

  it('matchSpec keeps relay targets apart from the keys', () => {
    const spec = matchSpec(matchKey(a, byCid), relayKey(c, byCid), matchKey(b, byCid));
    expect(spec.keys.map(k => k.place.name)).toEqual(['A', 'B']);
    expect(spec.relays.map(k => k.place.name)).toEqual(['C']);
  });

  it('a relay target does not count towards the two correlated inputs', () => {
    expect(() => matchSpec(matchKey(a, byCid), relayKey(c, byCid))).toThrow(
      'MatchSpec must correlate at least 2 input places, got 1',
    );
  });

  it('rejects a relay target that is not an output, naming the transition and the place', () => {
    const build = () => Transition.builder('j')
      .inputs(one(a), one(b))
      .outputs(outPlace(c))
      .match(matchSpec(matchKey(a, byCid), matchKey(b, byCid), relayKey(other, byCid)))
      .build();
    expect(build).toThrow("Transition 'j': relay target 'other' is not an output of the transition (NU-054)");
  });

  it('rejects a relay target declared twice, naming the transition and the place', () => {
    const build = () => Transition.builder('j')
      .inputs(one(a), one(b))
      .outputs(outPlace(c))
      .match(matchSpec(matchKey(a, byCid), matchKey(b, byCid), relayKey(c, byCid), relayKey(c, byCid)))
      .build();
    expect(build).toThrow("Transition 'j': relay target 'C' is declared twice (NU-054)");
  });

  it('accepts a target on one XOR branch only, and a target that is also a key (self-loop)', () => {
    expect(() => Transition.builder('j')
      .inputs(one(a), one(b))
      .outputs(xor(outPlace(c), outPlace(other)))
      .match(matchSpec(matchKey(a, byCid), matchKey(b, byCid), relayKey(c, byCid)))
      .build()).not.toThrow();
    expect(() => Transition.builder('j')
      .inputs(one(a), one(b))
      .outputs(andPlaces(a, c))
      .match(matchSpec(matchKey(a, byCid), matchKey(b, byCid), relayKey(a, byCid)))
      .build()).not.toThrow();
  });

  it('a MatchSpec written as a literal { keys } (the pre-NU-054 shape) has no relay targets', async () => {
    const t = Transition.builder('j')
      .inputs(one(a), one(b))
      .outputs(outPlace(c))
      .match({ keys: [matchKey(a, byCid), matchKey(b, byCid)] })
      .action(async ctx => { ctx.output(c, ctx.input(a)); })
      .build();
    expect(t.matchSpec!.relays).toEqual([]);
    // Both executors read `relays` on every completion of a join.
    const net = PetriNet.builder('literal').transition(t).build();
    for (const exec of [
      new BitmapNetExecutor(net, new Map([[a, [tokenAt({ cid: 'x' }, 0)]], [b, [tokenAt({ cid: 'x' }, 0)]]])),
      new PrecompiledNetExecutor(net, new Map([[a, [tokenAt({ cid: 'x' }, 0)]], [b, [tokenAt({ cid: 'x' }, 0)]]])),
    ]) {
      const marking = await exec.run(1_000);
      expect(marking.peekTokens(c).length).toBe(1);
    }
  });

  it('composition remaps relay targets like keys (instance prefix and port binding)', () => {
    const inA = place<Msg>('inA');
    const inB = place<Msg>('inB');
    const mid = place<Msg>('mid');
    const def = SubnetDef.builder('sub')
      .inputPort('a', inA)
      .inputPort('b', inB)
      .outputPort('out', mid)
      .transition(Transition.builder('j')
        .inputs(one(inA), one(inB))
        .outputs(outPlace(mid))
        .match(matchSpec(matchKey(inA, byCid), matchKey(inB, byCid), relayKey(mid, byCid)))
        .build())
      .build();
    const hostOut = place<Msg>('hostOut');
    const inst = def.instantiate('s');
    const net = PetriNet.builder('host')
      .compose(inst, { out: hostOut })
      .build();
    const j = [...net.transitions].find(t => t.name === 's/j')!;
    expect(j.matchSpec!.keys.map(k => k.place.name)).toEqual(['s/inA', 's/inB']);
    expect(j.matchSpec!.relays.map(k => k.place.name)).toEqual(['hostOut']);
  });
});

/** Both executors expose the same `new Executor(net, tokens, { eventStore })` + `run(ms)` API. */
interface Backend {
  readonly name: string;
  make(
    net: PetriNet,
    tokens: Map<Place<any>, Token<any>[]>,
    store: InMemoryEventStore,
    skipOutputValidation?: boolean,
  ): { run(ms: number): Promise<Marking> };
}

const backends: Backend[] = [
  { name: 'BitmapNetExecutor', make: (net, t, eventStore) => new BitmapNetExecutor(net, t, { eventStore }) },
  {
    name: 'PrecompiledNetExecutor',
    make: (net, t, eventStore, skipOutputValidation) =>
      new PrecompiledNetExecutor(net, t, { eventStore, skipOutputValidation }),
  },
];

for (const backend of backends) {
  describe(`NU-054 relay check at run time (AC2, ${backend.name})`, () => {
    const a = place<Msg>('A');
    const b = place<Msg>('B');
    const c = place<Msg>('C');
    const log = place<string>('log');

    /** A join on A, B relaying to C; `write` decides what lands in C. */
    function relayNet(write: (matched: string) => Msg, out = outPlace(c), key = byCid) {
      const j = Transition.builder('j')
        .inputs(one(a), one(b))
        .outputs(out)
        .match(matchSpec(matchKey(a, byCid), matchKey(b, byCid), relayKey(c, key)))
        .action(async ctx => { ctx.output(c, write(ctx.input(a).cid)); })
        .build();
      return PetriNet.builder('relay').transition(j).build();
    }

    async function fire(net: PetriNet, skip = false, extra: [Place<any>, Token<any>[]][] = []) {
      const store = new InMemoryEventStore();
      const tokens = new Map<Place<any>, Token<any>[]>([
        [a, [tokenAt({ cid: 'x' }, 0)]],
        [b, [tokenAt({ cid: 'x' }, 0)]],
        ...extra,
      ]);
      const marking = await backend.make(net, tokens, store, skip).run(2000);
      const failed = store.events().filter(e => e.type === 'transition-failed');
      const warnings = store.events().filter(e => e.type === 'log-message' && e.level === 'WARN');
      return { marking, failed, warnings };
    }

    it('a conforming action fires normally', async () => {
      const { marking, failed } = await fire(relayNet(cid => ({ cid, tag: 'relayed' })));
      expect(failed).toEqual([]);
      expect([...marking.peekTokens(c)].map(t => t.value.cid)).toEqual(['x']);
    });

    it('a token of another name fails the firing, naming transition, place and both names', async () => {
      const { marking, failed } = await fire(relayNet(() => ({ cid: 'y' })));
      expect(failed).toHaveLength(1);
      expect((failed[0] as { errorMessage: string }).errorMessage).toBe(
        "'j': relay target 'C' received a token with name 'y', but the join matched name 'x' (NU-054)",
      );
      expect(marking.peekTokens(c)).toHaveLength(0);
    });

    it('a token projecting to no name fails the firing', async () => {
      const { failed } = await fire(relayNet(() => ({ cid: '' }), outPlace(c), byCidOrNone));
      expect(failed).toHaveLength(1);
      expect((failed[0] as { errorMessage: string }).errorMessage).toBe(
        "'j': relay target 'C' received a token with no name, but the join matched name 'x' (NU-054)",
      );
    });

    it('an absent value has no name, and the projection is not called on it', async () => {
      // byCid dereferences its argument, so calling it on null would throw its own TypeError.
      const { failed } = await fire(relayNet(() => null as unknown as Msg));
      expect(failed).toHaveLength(1);
      expect((failed[0] as { errorMessage: string }).errorMessage).toBe(
        "'j': relay target 'C' received a token with no name, but the join matched name 'x' (NU-054)",
      );
    });

    it('checks what an Out.timeout branch deposits, forwarded input included (IO-014)', async () => {
      const z = place<Msg>('Z');
      const slow = (from: Place<Msg>) => Transition.builder('j')
        .inputs(one(a), one(b), one(z))
        .outputs(timeout(10, forwardInput(from, c)))
        .match(matchSpec(matchKey(a, byCid), matchKey(b, byCid), relayKey(c, byCid)))
        .action(() => new Promise<void>(r => setTimeout(r, 500)))
        .build();
      const extra: [Place<any>, Token<any>[]] = [z, [tokenAt({ cid: 'q' }, 0)]];
      // Forwarding the matched key token conforms.
      const ok = await fire(PetriNet.builder('fwdKey').transition(slow(a)).build(), false, [extra]);
      expect(ok.failed).toEqual([]);
      expect([...ok.marking.peekTokens(c)].map(t => t.value.cid)).toEqual(['x']);
      // Forwarding the non-key input's token (name 'q') is caught like an action's write.
      const bad = await fire(PetriNet.builder('fwdOther').transition(slow(z)).build(), false, [extra]);
      expect(bad.failed).toHaveLength(1);
      expect((bad.failed[0] as { errorMessage: string }).errorMessage).toBe(
        "'j': relay target 'C' received a token with name 'q', but the join matched name 'x' (NU-054)",
      );
    });

    it('checks every token in the target: one of another name beside a conforming one fails', async () => {
      const j = Transition.builder('j')
        .inputs(one(a), one(b))
        .outputs(andPlaces(c, log))
        .match(matchSpec(matchKey(a, byCid), matchKey(b, byCid), relayKey(c, byCid)))
        .action(async ctx => {
          ctx.output(c, { cid: 'x' });
          ctx.output(c, { cid: 'z' });
          ctx.output(log, 'done');
        })
        .build();
      const bad = await fire(PetriNet.builder('two').transition(j).build());
      expect(bad.failed).toHaveLength(1);
      expect((bad.failed[0] as { errorMessage: string }).errorMessage).toContain("name 'z'");
    });

    it('a key function that throws projects no name: the firing fails with the relay error', async () => {
      const throwing = (m: Msg) => {
        if (m.tag === 'boom') throw new Error('projection exploded');
        return nameId(m.cid);
      };
      const { marking, failed } = await fire(relayNet(cid => ({ cid, tag: 'boom' }), outPlace(c), throwing));
      expect(failed).toHaveLength(1);
      expect((failed[0] as { errorMessage: string }).errorMessage).toBe(
        "'j': relay target 'C' received a token with no name, but the join matched name 'x' (NU-054)",
      );
      expect(marking.peekTokens(c)).toHaveLength(0);
    });

    it.each([
      ['a single named place', outPlace(c), false],
      ['a composite spec', andPlaces(c, log), true],
    ])('the relay check runs before the IO-016 multiplicity WARN (%s)', async (_kind, out, writesLog) => {
      const j = Transition.builder('j')
        .inputs(one(a), one(b))
        .outputs(out)
        .match(matchSpec(matchKey(a, byCid), matchKey(b, byCid), relayKey(c, byCid)))
        .action(async ctx => {
          ctx.output(c, { cid: 'x' });
          ctx.output(c, { cid: 'z' });
          if (writesLog) ctx.output(log, 'done');
        })
        .build();
      const { failed, warnings } = await fire(PetriNet.builder('order').transition(j).build());
      expect(failed).toHaveLength(1);
      expect((failed[0] as { errorMessage: string }).errorMessage).toContain("name 'z'");
      expect(warnings).toEqual([]);
    });

    it('does not check a place that is not a relay target', async () => {
      const j = Transition.builder('j')
        .inputs(one(a), one(b))
        .outputs(andPlaces(c, log))
        .match(matchSpec(matchKey(a, byCid), matchKey(b, byCid), relayKey(c, byCid)))
        .action(async ctx => { ctx.output(c, { cid: 'x' }); ctx.output(log, 'anything'); })
        .build();
      const { failed } = await fire(PetriNet.builder('other').transition(j).build());
      expect(failed).toEqual([]);
    });

    if (backend.name === 'PrecompiledNetExecutor') {
      it('is skipped exactly where output validation is (CONC-026)', async () => {
        const { marking, failed } = await fire(relayNet(() => ({ cid: 'y' })), true);
        expect(failed).toEqual([]);
        expect([...marking.peekTokens(c)].map(t => t.value.cid)).toEqual(['y']);
      });
    }
  });
}
