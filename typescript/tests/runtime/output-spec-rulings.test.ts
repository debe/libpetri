/**
 * Executor-level acceptance criteria of the output-spec rulings:
 *
 * - CORE-034 AC4: a reset arc on an output place neither adds a deposit nor removes one.
 * - CORE-036 AC2/AC3: deposits compare per place; two tokens into one claimed place conform, and
 *   the order of the writes does not matter.
 * - CONC-026 AC4-AC6: the precompiled executor's `skipOutputValidation` covers a single-leaf
 *   spec, a partial `And` write and the IO-016 AC4 warning, but not a write to an undeclared
 *   place (CORE-063) and not the build-time IO-012 check.
 */
import { describe, expect, it } from 'vitest';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { PrecompiledNetExecutor } from '../../src/runtime/precompiled-net-executor.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { and, outPlace, xor, xorPlaces } from '../../src/core/out.js';
import { tokenOf } from '../../src/core/token.js';
import type { Token } from '../../src/core/token.js';
import { InMemoryEventStore, eventsOfType } from '../../src/event/event-store.js';

const backends = [
  { name: 'BitmapNetExecutor', make: (net: PetriNet, t: Map<Place<any>, Token<any>[]>) => new BitmapNetExecutor(net, t) },
  { name: 'PrecompiledNetExecutor', make: (net: PetriNet, t: Map<Place<any>, Token<any>[]>) => new PrecompiledNetExecutor(net, t) },
];

for (const backend of backends) {
  describe(`CORE-034 AC4: a reset arc changes no deposit (${backend.name})`, () => {
    it.each([
      [false, true], [false, false], [true, true], [true, false],
    ])('reset %s, action writes b %s', async (withReset, writeB) => {
      const a = place<number>('a');
      const b = place<number>('b');
      const c = place<number>('c');
      let builder = Transition.builder('t')
        .inputs(one(a))
        .outputs(xor(outPlace(b), outPlace(c)))
        .action(async (ctx) => { ctx.output(writeB ? b : c, 7); });
      if (withReset) builder = builder.reset(b);
      const net = PetriNet.builder('N').transition(builder.build()).build();
      const marking = await backend.make(net, new Map<Place<any>, Token<any>[]>([
        [a, [tokenOf(1)]], [b, [tokenOf(1), tokenOf(2)]],
      ])).run(5000);
      expect(marking.tokenCount(a)).toBe(0);
      expect(marking.tokenCount(b)).toBe((withReset ? 0 : 2) + (writeB ? 1 : 0));
      expect(marking.tokenCount(c)).toBe(writeB ? 0 : 1);
    });
  });

  describe(`CORE-036 AC2/AC3: deposits compare per place (${backend.name})`, () => {
    it.each([[['b', 'b', 'c']], [['c', 'b', 'b']]])('writes %j', async (order) => {
      const a = place<number>('a');
      const b = place<number>('b');
      const c = place<number>('c');
      const byName = { b, c } as Record<string, Place<number>>;
      const t = Transition.builder('t')
        .inputs(one(a))
        .outputs(and(outPlace(b), outPlace(c)))
        .action(async (ctx) => { for (const p of order) ctx.output(byName[p]!, 1); })
        .build();
      const net = PetriNet.builder('N').transition(t).build();
      const marking = await backend.make(net, new Map<Place<any>, Token<any>[]>([[a, [tokenOf(1)]]])).run(5000);
      expect(marking.tokenCount(a)).toBe(0);
      expect(marking.tokenCount(b)).toBe(2);
      expect(marking.tokenCount(c)).toBe(1);
    });
  });
}

describe('CONC-026 AC4-AC6: skipOutputValidation', () => {
  it('covers the leaf, a partial And and the IO-016 warning, but not an undeclared write', async () => {
    const go = (n: string) => place<number>(n);
    const [go1, go2, go3, go4] = ['GO1', 'GO2', 'GO3', 'GO4'].map(go);
    const p = go('P');
    const a = go('A');
    const b = go('B');
    const many = go('MANY');
    const silent = Transition.builder('silent').inputs(one(go1!)).outputs(outPlace(p))
      .action(async () => {}).build();
    const half = Transition.builder('half').inputs(one(go2!)).outputs(and(outPlace(a), outPlace(b)))
      .action(async (ctx) => { ctx.output(a, 1); }).build();
    const twice = Transition.builder('twice').inputs(one(go3!)).outputs(outPlace(many))
      .action(async (ctx) => { ctx.output(many, 1); ctx.output(many, 2); }).build();
    const undeclared = Transition.builder('undeclared').inputs(one(go4!)).outputs(outPlace(p))
      .action(async (ctx) => { ctx.output(a, 9); }).build();
    const net = PetriNet.builder('skip').transitions(silent, half, twice, undeclared).build();
    const store = new InMemoryEventStore();
    const tokens = new Map<Place<any>, Token<any>[]>(
      [go1!, go2!, go3!, go4!].map(g => [g, [tokenOf(0)]] as [Place<any>, Token<any>[]]));
    const marking = await new PrecompiledNetExecutor(net, tokens, { eventStore: store, skipOutputValidation: true })
      .run(5000);
    expect(marking.tokenCount(p)).toBe(0);
    expect(marking.tokenCount(a)).toBe(1);
    expect(marking.tokenCount(b)).toBe(0);
    expect(marking.tokenCount(many)).toBe(2);
    expect(eventsOfType(store, 'log-message')).toEqual([]);
    expect(eventsOfType(store, 'transition-failed').map(e => e.transitionName)).toEqual(['undeclared']);
  });

  it('does not reach the build-time IO-012 check', () => {
    const p = place<number>('P');
    expect(() => Transition.builder('t').inputs(one(place('GO'))).outputs(xorPlaces(p, p)).build())
      .toThrowError(/is ambiguous: output branches 0 and 1 both claim \{P\}/);
  });
});
