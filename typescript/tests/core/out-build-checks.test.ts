import { describe, expect, it } from 'vitest';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { and, andPlaces, forwardInput, outPlace, timeout, xor, xorPlaces, type Out } from '../../src/core/out.js';

/**
 * The build-time output-spec checks of [IO-011] (which duplicate is named), [IO-012] (ambiguous
 * alternatives), [IO-013] (at most one Timeout node, no Xor in its child) and [IO-014]
 * (ForwardInput only inside a Timeout child). The messages are byte-identical across
 * implementations, and the first failing check wins in the order IO-011, IO-013 count, IO-013
 * Xor in Timeout, IO-014 placement, IO-014 AC3, IO-012.
 */

const P = place<string>('P');
const Q = place<string>('Q');
const A = place<string>('A');
const B = place<string>('B');
const C = place<string>('C');
const E = place<string>('E');
const X = place<string>('X');
const a = place<string>('a');
const b = place<string>('b');
const c = place<string>('c');
const e = place<string>('e');

function build(out: Out): Transition {
  return Transition.builder('t').inputs(one(a)).outputs(out).build();
}

const ambiguous = (i: number, j: number, places: string) =>
  `output spec of transition 't' is ambiguous: output branches ${i} and ${j} both claim {${places}}; ` +
  'no write can tell them apart (IO-012)';
const timeouts = (n: number) =>
  `output spec of transition 't' has ${n} Timeout nodes; an output spec has at most one, nested or not (IO-013)`;
const xorInTimeout =
  "output spec of transition 't' has a Xor node inside the child of its Timeout node; " +
  'the timeout outcome deposits one fixed set of places (IO-013)';
const duplicate = (name: string) =>
  `output spec of transition 't' names place '${name}' twice in one AND branch; outputs are sets (IO-015) ` +
  '— a weighted output is not supported, add a second place or a follow-up transition';
const bareForward = (from: string, to: string) =>
  `output spec of transition 't' uses ForwardInput('${from}', '${to}') outside the child of a Timeout node; ` +
  'a forward deposits only on the timeout outcome (IO-014)';

describe('IO-012 AC5: two alternatives claiming the same set do not build', () => {
  it.each<[string, () => Out, number, number, string]>([
    ['Xor(P, P)', () => xorPlaces(P, P), 0, 1, 'P'],
    ['Xor(And(A, B), And(B, A))', () => xor(andPlaces(A, B), andPlaces(B, A)), 0, 1, 'A, B'],
    ['Xor(A, Xor(A, B))', () => xor(outPlace(A), xorPlaces(A, B)), 0, 1, 'A'],
    ['And(Q, Xor(P, P))', () => and(outPlace(Q), xorPlaces(P, P)), 0, 1, 'Q, P'],
    ['Xor(And(A, Xor(B, C)), And(A, B))', () => xor(and(outPlace(A), xorPlaces(B, C)), andPlaces(A, B)), 0, 2, 'A, B'],
    ['Xor(P, Timeout(d, P))', () => xor(outPlace(P), timeout(10, outPlace(P))), 0, 1, 'P'],
    ['Xor(B, Timeout(d, ForwardInput(a, B)))', () => xor(outPlace(B), timeout(10, forwardInput(a, B))), 0, 1, 'B'],
  ])('%s is rejected', (_name, spec, i, j, places) => {
    expect(() => build(spec())).toThrowError(ambiguous(i, j, places));
  });

  it.each<[string, () => Out]>([
    ['Xor(And(A, B, C), And(A, B))', () => xor(andPlaces(A, B, C), andPlaces(A, B))],
    ['Xor(And(P, A), And(P, B))', () => xor(andPlaces(P, A), andPlaces(P, B))],
    ['Xor(A, Timeout(d, B))', () => xor(outPlace(A), timeout(10, outPlace(B)))],
  ])('%s builds', (_name, spec) => {
    expect(build(spec()).outputSpec).not.toBeNull();
  });

  it('the same node object in two alternatives is still two alternatives', () => {
    const leaf = outPlace(P);
    expect(() => build(xor(leaf, leaf))).toThrowError(ambiguous(0, 1, 'P'));
  });

  it('reports the first colliding branch j, and the first earlier branch i with its set', () => {
    // Branches: 0 {A,X}, 1 {B,X}, 2 {C}, 3 {B,X}. The collision is 3 with 1.
    const spec = xor(and(xorPlaces(A, B), outPlace(X)), outPlace(C), andPlaces(X, B));
    expect(() => build(spec)).toThrowError(ambiguous(1, 3, 'B, X'));
  });

  it('a collision past 2^20 branches is found without enumerating them', () => {
    // And(Xor(P, P), Xor(A0, B0), ..., Xor(A19, B19)): branch 2^20 repeats branch 0.
    const pairs = Array.from({ length: 20 }, (_, k) => xorPlaces(place(`A${k}`), place(`B${k}`)));
    const spec = and(xorPlaces(P, P), ...pairs);
    const names = ['P', ...Array.from({ length: 20 }, (_, k) => `A${k}`)].join(', ');
    expect(() => build(spec)).toThrowError(ambiguous(0, 2 ** 20, names));
  });

  it('an And of 64 two-way Xors builds without enumerating its 2^64 branches', () => {
    const pairs = Array.from({ length: 64 }, (_, k) => xorPlaces(place(`A${k}`), place(`B${k}`)));
    const start = performance.now();
    build(and(...pairs));
    expect(performance.now() - start).toBeLessThan(1000);
  });

  it('a cross-alternative collision deep in a large alternative is reported exactly', () => {
    // Alternative 0 is And(Xor(A_k, B_k) for k < 12); alternative 1 names one of its sets,
    // B0..B11 = the last branch of alternative 0, index 2^12 - 1. Branch 2^12 repeats it.
    const pairs = Array.from({ length: 12 }, (_, k) => xorPlaces(place(`A${k}`), place(`B${k}`)));
    const last = andPlaces(...Array.from({ length: 12 }, (_, k) => place<string>(`B${k}`)));
    const names = Array.from({ length: 12 }, (_, k) => `B${k}`).join(', ');
    expect(() => build(xor(and(...pairs), last))).toThrowError(ambiguous(2 ** 12 - 1, 2 ** 12, names));
  });
});

describe('IO-012: the reported pair and places match the other implementations', () => {
  const D = place<string>('D');
  const Y = place<string>('Y');

  it('reports the first pair in branch order, at And strides and deep in an Xor', () => {
    // Branches [X,A] [X,B] [X,A'] [Y,A] [Y,B] [Y,A'] with A' = A: (0, 2).
    expect(() => build(and(xorPlaces(X, Y), xorPlaces(A, B, A)))).toThrowError(ambiguous(0, 2, 'X, A'));
    // A repeat in the first child shows at stride 3: (0, 3).
    expect(() => build(and(xorPlaces(X, X), xorPlaces(A, B, C)))).toThrowError(ambiguous(0, 3, 'X, A'));
    // A later alternative that repeats a deep branch of an earlier one: (3, 5).
    expect(() => build(xor(and(xorPlaces(A, B), xorPlaces(C, D)), outPlace(E), andPlaces(D, B))))
      .toThrowError(ambiguous(3, 5, 'B, D'));
  });

  it('two alternatives sharing one place are compared only within each other\'s places', () => {
    const side = (x: string, y: string) =>
      and(outPlace(P), ...Array.from({ length: 40 }, (_, k) => xorPlaces(place(`${x}${k}`), place(`${y}${k}`))));
    const start = performance.now();
    build(xor(side('x', 'y'), side('u', 'v')));
    expect(performance.now() - start).toBeLessThan(1000);
  });

  it('two empty Ands written as object literals claim the same empty set', () => {
    const empty = { type: 'and', children: [] } as unknown as Out;
    expect(() => build(xor(empty, { type: 'and', children: [] } as unknown as Out)))
      .toThrowError(ambiguous(0, 1, ''));
  });
});

describe('IO-013 AC7: more than one Timeout node does not build', () => {
  it.each<[string, () => Out]>([
    ['Timeout(d, Timeout(e, P))', () => timeout(10, timeout(5, outPlace(P)))],
    ['Xor(Timeout(d, A), Timeout(e, B))', () => xor(timeout(10, outPlace(A)), timeout(20, outPlace(B)))],
    ['And(Timeout(d, A), Xor(B, Timeout(e, C)))', () => and(timeout(10, outPlace(A)), xor(outPlace(B), timeout(20, outPlace(C))))],
  ])('%s is rejected with n = 2', (_name, spec) => {
    expect(() => build(spec())).toThrowError(timeouts(2));
  });

  it('three Timeout nodes report n = 3', () => {
    expect(() => build(xor(timeout(1, outPlace(A)), timeout(2, outPlace(B)), timeout(3, outPlace(C)))))
      .toThrowError(timeouts(3));
  });

  it.each<[string, () => Out]>([
    ['Xor(A, Timeout(d, B))', () => xor(outPlace(A), timeout(10, outPlace(B)))],
    ['Timeout(d, And(A, B))', () => timeout(10, andPlaces(A, B))],
  ])('%s builds', (_name, spec) => {
    expect(build(spec()).outputSpec).not.toBeNull();
  });
});

describe('IO-013 AC8: an Xor inside the Timeout child does not build', () => {
  const D = place<string>('D');
  it.each<[string, () => Out]>([
    ['Timeout(d, Xor(A, B))', () => timeout(10, xorPlaces(A, B))],
    ['Xor(C, Timeout(d, And(A, Xor(B, D))))', () => xor(outPlace(C), timeout(10, and(outPlace(A), xorPlaces(B, D))))],
  ])('%s is rejected', (_name, spec) => {
    expect(() => build(spec())).toThrowError(xorInTimeout);
  });

  it.each<[string, () => Out]>([
    ['Xor(A, Timeout(d, B))', () => xor(outPlace(A), timeout(10, outPlace(B)))],
    ['Timeout(d, And(A, ForwardInput(a, B)))', () => timeout(10, and(outPlace(A), forwardInput(a, B)))],
  ])('%s builds', (_name, spec) => {
    expect(build(spec()).outputSpec).not.toBeNull();
  });
});

describe('IO-011 AC5: the walk names the place every implementation names', () => {
  it('And(Xor(A, B), Xor(B, A)) names B, not A', () => {
    expect(() => build(and(xorPlaces(A, B), xorPlaces(B, A)))).toThrowError(duplicate('B'));
  });
});

describe('IO-014 AC7: a ForwardInput outside the child of a Timeout node does not build', () => {
  it.each<[string, () => Out]>([
    ['ForwardInput(a, b)', () => forwardInput(a, b)],
    ['Xor(c, ForwardInput(a, b))', () => xor(outPlace(c), forwardInput(a, b))],
    ['And(c, Xor(e, ForwardInput(a, b)))', () => and(outPlace(c), xor(outPlace(e), forwardInput(a, b)))],
  ])('%s is rejected', (_name, spec) => {
    expect(() => build(spec())).toThrowError(bareForward('a', 'b'));
  });

  it.each<[string, () => Out]>([
    ['Timeout(d, ForwardInput(a, b))', () => timeout(10, forwardInput(a, b))],
    ['Xor(c, Timeout(d, And(e, ForwardInput(a, b))))', () => xor(outPlace(c), timeout(10, and(outPlace(e), forwardInput(a, b))))],
  ])('%s builds', (_name, spec) => {
    expect(build(spec()).outputSpec).not.toBeNull();
  });

  it('names the first bare forward in pre-order', () => {
    const z = place<string>('z');
    const spec = xor(timeout(10, forwardInput(a, b)), forwardInput(a, c), forwardInput(a, z));
    expect(() => build(spec)).toThrowError(bareForward('a', 'c'));
  });
});

describe('check order: the first failing check wins', () => {
  it('IO-011 before IO-014 placement', () => {
    expect(() => build(and(outPlace(b), forwardInput(a, b)))).toThrowError(
      "output spec of transition 't' names place 'b' twice in one AND branch; outputs are sets (IO-015) " +
      '— a weighted output is not supported, add a second place or a follow-up transition',
    );
  });

  it('IO-011 before IO-013 Xor in Timeout', () => {
    expect(() => build(timeout(10, and(outPlace(A), xorPlaces(A, B))))).toThrowError(duplicate('A'));
  });

  it('IO-013 Timeout count before IO-013 Xor in Timeout', () => {
    expect(() => build(xor(timeout(1, xorPlaces(A, B)), timeout(2, outPlace(C))))).toThrowError(timeouts(2));
  });

  it('IO-013 Xor in Timeout before IO-014 placement', () => {
    expect(() => build(xor(timeout(10, xorPlaces(A, B)), forwardInput(a, c)))).toThrowError(xorInTimeout);
  });

  it('IO-013 Xor in Timeout before IO-014 AC3 and IO-012', () => {
    expect(() => build(xor(outPlace(b), timeout(10, xor(forwardInput(E, b), outPlace(C))))))
      .toThrowError(xorInTimeout);
  });

  it('IO-013 before IO-014 placement', () => {
    expect(() => build(xor(timeout(1, outPlace(A)), timeout(2, outPlace(B)), forwardInput(a, c))))
      .toThrowError(timeouts(2));
  });

  it('IO-014 placement before IO-014 AC3 (non-input from)', () => {
    expect(() => build(forwardInput(E, b))).toThrowError(bareForward('E', 'b'));
  });

  it('IO-014 AC3 (non-input from) before IO-012', () => {
    expect(() => build(xor(outPlace(b), timeout(10, forwardInput(E, b))))).toThrowError(
      "Transition 't': ForwardInput references non-input place 'E'",
    );
  });
});
