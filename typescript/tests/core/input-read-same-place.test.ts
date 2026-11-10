import { describe, it, expect } from 'vitest';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { FusionSet } from '../../src/core/fusion-set.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import type { Place } from '../../src/core/place.js';
import { place } from '../../src/core/place.js';
import { one, all, exactly, atLeast, type In } from '../../src/core/in.js';
import { outPlace, and, xor } from '../../src/core/out.js';
import { delayed, MAX_DURATION_MS } from '../../src/core/timing.js';

/**
 * EXEC-012 (D15): a transition with an input arc and a read arc on the same place is rejected
 * when it is built. The message is byte-identical across implementations. The check runs after
 * every input-arc check (CORE-030, IO-002, IO-004) and before the timing check (TIME-001) and
 * the output-spec checks (IO-011 to IO-014), and names the first read arc in declaration order
 * whose place is an input place.
 */

const message = (t: string, p: string) =>
  `Transition '${t}' declares an input arc and a read arc on place '${p}'. `
  + 'A read of a place the same firing consumes from has no coherent semantics and is rejected '
  + '(EXEC-012). Remove the read arc: the input arc already hands the consumed tokens to the action.';

const p = place<string>('p');
const a = place<string>('a');
const b = place<string>('b');
const out = place<string>('out');

function thrown(build: () => unknown): string {
  try {
    build();
  } catch (e) {
    return (e as Error).message;
  }
  throw new Error('expected the build to fail');
}

describe('input arc and read arc on one place (EXEC-012)', () => {
  it('AC2: rejects one(), all(), exactly(2) and atLeast(1) with a read on the same place', () => {
    const inputs: In[] = [one(p), all(p), exactly(2, p), atLeast(1, p)];
    for (const input of inputs) {
      expect(thrown(() => Transition.builder('t').inputs(input).read(p).build()))
        .toBe(message('t', 'p'));
    }
  });

  it('AC2: rejects regardless of the order the arcs are declared in', () => {
    expect(thrown(() => Transition.builder('t').read(p).inputs(one(p)).build()))
      .toBe(message('t', 'p'));
  });

  it('AC3: names the first read arc in declaration order whose place is an input place', () => {
    expect(thrown(() =>
      Transition.builder('t').inputs(one(a), one(b)).reads(b, a).build(),
    )).toBe(message('t', 'b'));
    expect(thrown(() =>
      Transition.builder('t').inputs(one(a), one(b)).read(out).read(a).read(b).build(),
    )).toBe(message('t', 'a'));
  });

  it('AC3: two input arcs on p plus a read on p gives the CORE-030 message', () => {
    expect(thrown(() => Transition.builder('t').inputs(one(p), one(p)).read(p).build()))
      .toContain('declares two input arcs on place \'p\'');
  });

  it('runs after the IO-002 zero-count check', () => {
    const zero: In = { type: 'exactly', place: p, count: 0 };
    expect(thrown(() => Transition.builder('t').inputs(zero).read(p).build()))
      .toContain("input 'p' of transition 't' requires 0 tokens");
  });

  it('runs before the TIME-001 timing check and the output-spec checks', () => {
    expect(thrown(() =>
      Transition.builder('t')
        .inputs(one(p))
        .read(p)
        .timing({ type: 'delayed', afterMs: MAX_DURATION_MS + 1 })
        .build(),
    )).toBe(message('t', 'p'));
    expect(thrown(() =>
      Transition.builder('t')
        .inputs(one(p))
        .read(p)
        .outputs(xor(and(outPlace(out), outPlace(out)), outPlace(out)))
        .build(),
    )).toBe(message('t', 'p'));
  });

  it('AC4: input and read on different places, and read plus reset on one place, build', () => {
    const t1 = Transition.builder('t1').inputs(one(a)).read(b).outputs(outPlace(out))
      .timing(delayed(5)).build();
    expect(t1.reads.map(r => r.place.name)).toEqual(['b']);
    const t2 = Transition.builder('t2').read(p).reset(p).build();
    expect(t2.reads.map(r => r.place.name)).toEqual(['p']);
    expect(t2.resets.map(r => r.place.name)).toEqual(['p']);
  });

  it('rejects at net build when fusion (MOD-061) puts an input and a read on one place', () => {
    const t = Transition.builder('t').inputs(one(a)).read(b).build();
    expect(thrown(() =>
      PetriNet.builder('Fused').transitions(t).fuse(FusionSet.of('ab', a, b)).build(),
    )).toBe(message('t', 'a'));
  });

  it('rejects at compose when an input port and a read port are bound to one place (MOD-020)', () => {
    const def = SubnetDef.builder('Peek')
      .transition(Transition.builder('peek').inputs(one(a)).read(b).outputs(outPlace(out)).build())
      .inputPort('a', a)
      .inputPort('b', b)
      .build();
    const x = place<string>('X');
    expect(thrown(() =>
      PetriNet.builder('host')
        .compose(def.instantiate('s'), { a: x as Place<unknown>, b: x as Place<unknown> })
        .build(),
    )).toBe(message('s/peek', 'X'));
  });
});
