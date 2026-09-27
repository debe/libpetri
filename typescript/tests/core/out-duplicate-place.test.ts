import { describe, expect, it } from 'vitest';
import { PetriNet } from '../../src/core/petri-net.js';
import { place, type Place } from '../../src/core/place.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { Transition } from '../../src/core/transition.js';
import { one } from '../../src/core/in.js';
import { and, andPlaces, outPlace, xor, xorPlaces, type Out } from '../../src/core/out.js';

/**
 * [IO-011]: outputs are sets ([IO-015]), so one output branch — one choice at every XOR, nested
 * ANDs flattened — naming a place twice is rejected rather than collapsed. [MOD-020]: composition
 * that produces the duplicate by binding two output ports to one place says so.
 */

const P = place<string>('P');
const Q = place<string>('Q');
const A = place<string>('A');
const B = place<string>('B');
const IN = place<string>('in');

const message = (t: string, p: string) =>
  `output spec of transition '${t}' names place '${p}' twice in one AND branch; outputs are sets (IO-015) ` +
  '— a weighted output is not supported, add a second place or a follow-up transition';

function build(out: Out): Transition {
  return Transition.builder('t').inputs(one(IN)).outputs(out).build();
}

describe('a place named twice in one AND branch (IO-011 AC4)', () => {
  it('And(P, P) is rejected, naming the transition and the place', () => {
    expect(() => build(andPlaces(P, P))).toThrowError(message('t', 'P'));
  });

  it('And(P, And(Q, P)) is rejected: nested ANDs are one branch', () => {
    expect(() => build(and(outPlace(P), andPlaces(Q, P)))).toThrowError(message('t', 'P'));
  });

  it('Xor(A, And(P, P)) is rejected: the duplicate sits inside one alternative', () => {
    expect(() => build(xor(outPlace(A), andPlaces(P, P)))).toThrowError(message('t', 'P'));
  });

  it('And(P, Xor(P, Q)) is rejected: the P alternative puts P in the branch twice', () => {
    expect(() => build(and(outPlace(P), xorPlaces(P, Q)))).toThrowError(message('t', 'P'));
  });

  it('Xor(And(P, A), And(P, B)) is accepted: each alternative names P once', () => {
    const t = build(xor(andPlaces(P, A), andPlaces(P, B)));
    expect(t.outputSpec).not.toBeNull();
  });
});

/** `split` writes ports `a` and `b` in one branch (AND), or one of them (XOR). */
function splitDef(out: (a: Place<string>, b: Place<string>) => Out): SubnetDef<void> {
  const input = place<string>('in');
  const a = place<string>('a');
  const b = place<string>('b');
  return SubnetDef.builder('Split')
    .transition(Transition.builder('split').inputs(one(input)).outputs(out(a, b)).build())
    .inputPort('in', input)
    .outputPort('a', a)
    .outputPort('b', b)
    .build();
}

describe('output-port collision at compose (MOD-020 AC8)', () => {
  it('two output ports one AND branch writes, bound to one host place, are rejected naming the binding', () => {
    const x = place<string>('X');
    const s = splitDef((a, b) => andPlaces(a, b)).instantiate('s');
    expect(() => PetriNet.builder('host').compose(s, { a: x as Place<unknown>, b: x as Place<unknown> }))
      .toThrowError(
        "ports 'a' and 'b' of instance 's' are both bound to host place 'X'; transition 's/split' would " +
        "produce into 'X' twice in one AND branch. Outputs are sets (IO-015); bind them to distinct places " +
        'or use one port.',
      );
  });

  it('the same binding is accepted when the ports are XOR alternatives', () => {
    const x = place<string>('X');
    const s = splitDef((a, b) => xorPlaces(a, b)).instantiate('s');
    const net = PetriNet.builder('host').compose(s, { a: x as Place<unknown>, b: x as Place<unknown> }).build();
    expect([...net.places].map(p => p.name)).toContain('X');
  });
});
