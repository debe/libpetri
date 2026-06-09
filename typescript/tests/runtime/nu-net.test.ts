import { describe, it, expect } from 'vitest';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { PrecompiledNetExecutor } from '../../src/runtime/precompiled-net-executor.js';
import type { Marking } from '../../src/runtime/marking.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace, andPlaces } from '../../src/core/out.js';
import { tokenOf, tokenAt } from '../../src/core/token.js';
import type { Token } from '../../src/core/token.js';
import { nameId } from '../../src/core/name.js';
import { matchSpec, matchKey } from '../../src/core/match-spec.js';

interface NuMsg {
  cid: string;
}

/** Both executors expose the same `new Executor(net, tokens)` + `run(ms)` API. */
interface Backend {
  readonly name: string;
  make(net: PetriNet, tokens: Map<Place<any>, Token<any>[]>): { run(ms: number): Promise<Marking> };
}

const backends: Backend[] = [
  { name: 'BitmapNetExecutor', make: (net, t) => new BitmapNetExecutor(net, t) },
  { name: 'PrecompiledNetExecutor', make: (net, t) => new PrecompiledNetExecutor(net, t) },
];

const correlateOnCid = (a: Place<NuMsg>, b: Place<NuMsg>) =>
  matchSpec(
    matchKey(a, (m: NuMsg) => nameId(m.cid)),
    matchKey(b, (m: NuMsg) => nameId(m.cid)),
  );

for (const backend of backends) {
  describe(`ν-net fork/join (${backend.name})`, () => {
    // NU-020: a join correlates by name equality, NOT FIFO. Reversed arrival
    // order would make a FIFO join pair X with Y; the name match must pair X-X.
    it('join matches by name, not FIFO', async () => {
      const a = place<NuMsg>('branchA');
      const b = place<NuMsg>('branchB');
      const merged = place<string>('merged');

      const join = Transition.builder('join')
        .inputs(one(a), one(b))
        .match(correlateOnCid(a, b))
        .outputs(outPlace(merged))
        .action(async (ctx) => {
          ctx.output(merged, `${ctx.input(a).cid}+${ctx.input(b).cid}`);
        })
        .build();

      const net = PetriNet.builder('nuJoin').transition(join).build();
      const tokens = new Map<Place<any>, Token<any>[]>([
        [a, [tokenAt({ cid: 'X' }, 0), tokenAt({ cid: 'Y' }, 1)]],
        [b, [tokenAt({ cid: 'Y' }, 0), tokenAt({ cid: 'X' }, 1)]],
      ]);

      const marking = await backend.make(net, tokens).run(2000);
      const vals = [...marking.peekTokens(merged)].map(t => t.value as string).sort();
      expect(vals).toEqual(['X+X', 'Y+Y']);
      for (const v of vals) {
        const [l, r] = v.split('+');
        expect(l).toBe(r);
      }
    });

    // NU-020: no name in both inputs → join never enabled; tokens stay put.
    it('join blocks without a matching name', async () => {
      const a = place<NuMsg>('branchA');
      const b = place<NuMsg>('branchB');
      const merged = place<string>('merged');

      const join = Transition.builder('join')
        .inputs(one(a), one(b))
        .match(correlateOnCid(a, b))
        .outputs(outPlace(merged))
        .action(async (ctx) => {
          ctx.output(merged, `${ctx.input(a).cid}+${ctx.input(b).cid}`);
        })
        .build();

      const net = PetriNet.builder('nuJoinBlock').transition(join).build();
      const tokens = new Map<Place<any>, Token<any>[]>([
        [a, [tokenOf({ cid: 'X' })]],
        [b, [tokenOf({ cid: 'Y' })]],
      ]);

      const marking = await backend.make(net, tokens).run(500);
      expect(marking.hasTokens(merged)).toBe(false);
      expect(marking.hasTokens(a)).toBe(true);
      expect(marking.hasTokens(b)).toBe(true);
    });

    // NU-010 + NU-020 end to end: fork mints a fresh id per firing and stamps
    // both siblings; the join re-merges exactly the siblings sharing an id.
    it('fork mints unique ids, then join re-merges', async () => {
      const source = place<number>('source');
      const a = place<NuMsg>('branchA');
      const b = place<NuMsg>('branchB');
      const merged = place<string>('merged');

      const fork = Transition.builder('fork')
        .inputs(one(source))
        .outputs(andPlaces(a, b))
        .action(async (ctx) => {
          const id = ctx.freshName();
          ctx.output(a, { cid: id });
          ctx.output(b, { cid: id });
        })
        .build();

      const join = Transition.builder('join')
        .inputs(one(a), one(b))
        .match(correlateOnCid(a, b))
        .outputs(outPlace(merged))
        .action(async (ctx) => {
          const ma = ctx.input(a);
          const mb = ctx.input(b);
          if (ma.cid !== mb.cid) throw new Error(`join saw mismatched ids: ${ma.cid} vs ${mb.cid}`);
          ctx.output(merged, ma.cid);
        })
        .build();

      const net = PetriNet.builder('nuScatterGather').transitions(fork, join).build();
      const tokens = new Map<Place<any>, Token<any>[]>([
        [source, [tokenOf(0), tokenOf(0), tokenOf(0)]],
      ]);

      const marking = await backend.make(net, tokens).run(2000);
      const vals = [...marking.peekTokens(merged)].map(t => t.value as string);
      expect(vals).toHaveLength(3);
      expect(new Set(vals).size).toBe(3); // fresh_name mints a unique id per fork firing
    });

    // NU-040: a bounded `budget` place caps live fork groups (the decidability
    // lever); the budget token returned by each join lets all work still
    // complete — serialized at k = 1.
    it('budget bounds concurrency', async () => {
      const source = place<number>('source');
      const budget = place<number>('budget');
      const a = place<NuMsg>('branchA');
      const b = place<NuMsg>('branchB');
      const merged = place<string>('merged');

      const fork = Transition.builder('fork')
        .inputs(one(source), one(budget))
        .outputs(andPlaces(a, b))
        .action(async (ctx) => {
          const id = ctx.freshName();
          ctx.output(a, { cid: id });
          ctx.output(b, { cid: id });
        })
        .build();

      const join = Transition.builder('join')
        .inputs(one(a), one(b))
        .match(correlateOnCid(a, b))
        .outputs(andPlaces(merged, budget))
        .action(async (ctx) => {
          const ma = ctx.input(a);
          const mb = ctx.input(b);
          if (ma.cid !== mb.cid) throw new Error(`join saw mismatched ids: ${ma.cid} vs ${mb.cid}`);
          ctx.output(merged, ma.cid);
          ctx.output(budget, 0);
        })
        .build();

      const net = PetriNet.builder('nuBudget').transitions(fork, join).build();
      const tokens = new Map<Place<any>, Token<any>[]>([
        [source, [tokenOf(0), tokenOf(0), tokenOf(0)]],
        [budget, [tokenOf(0)]],
      ]);

      const marking = await backend.make(net, tokens).run(2000);
      expect([...marking.peekTokens(merged)]).toHaveLength(3);
      expect([...marking.peekTokens(budget)]).toHaveLength(1);
      expect([...marking.peekTokens(source)]).toHaveLength(0);
    });
  });
}
