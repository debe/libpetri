import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, type Place } from '../../src/core/place.js';
import { all, one } from '../../src/core/in.js';
import { andPlaces, outPlace } from '../../src/core/out.js';
import { matchKey, matchSpec } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import type { FlatNet } from '../../src/verification/encoding/flat-net.js';
import { flatTransition, type FlatTransition } from '../../src/verification/encoding/flat-transition.js';
import { IncidenceMatrix } from '../../src/verification/encoding/incidence-matrix.js';
import { computePSemiflows, validateInvariantsExact } from '../../src/verification/invariant/p-invariant-computer.js';
import type { PInvariant } from '../../src/verification/invariant/p-invariant.js';
import { declaredMints, type FragmentMode } from '../../src/verification/analysis/name-fragment.js';
import { buildColouredPlan, encodeColoured, type ColouredPlan } from '../../src/verification/z3/name-coloured-encoder.js';
import {
  checkCover, checkedSlotBound, presolve, Rational, slotBoundK, slotBoundReportLine, SlotTableau,
  solveSlotBound, solveSlotBoundCounted, SLOT_LP_MAX_PLACES,
  type LpAnswer, type ScaledCover, type SlotBound,
} from '../../src/verification/z3/slot-bound-lp.js';
import { placeBound } from '../../src/verification/smt-property.js';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { resolveZ3, runZ3Text } from '../../src/verification/z3/z3-process.js';
import { runZ3Spacer } from '../../src/verification/z3/spacer-runner.js';
import { describeZ3 } from '../fixtures/z3.js';
import { FIG_12C_ROWS, JOIN_CHAIN_ROWS, JOIN_CHAIN_SPLIT_ROWS, N1_CORR_ROWS, pnidNet, UNION_ROWS } from '../fixtures/pnid-nets.js';
import { produces } from '../fixtures/producing-actions.js';

/**
 * The colour-slot linear program of [NU-053] (`slot-bound-lp`): the exact simplex core, the
 * checker, the shared parity cases written by the Rust reference, and differential tests
 * against the state space, against the semiflow bound it replaced, against z3 as an
 * independent optimiser, and through `buildColouredPlan` with deliberately wrong answers,
 * which the exact re-check must refuse. Mirrors the Rust `slot_bound_lp` tests.
 */

const q = (n: bigint, d: bigint = 1n): Rational => Rational.of(n, d);
const big = (xs: readonly number[]): bigint[] => xs.map(x => BigInt(x));

// ---- synthetic flat nets ----

/** A transition only for `FlatTransition.source`; the LP reads the vectors and the name. */
const STUB = { name: 'stub' } as unknown as Transition;

interface VectorRow {
  readonly name: string;
  readonly pre: readonly number[];
  readonly post: readonly number[];
  readonly reset?: readonly number[];
  readonly all?: readonly number[];
}

function flatFromVectors(names: readonly string[], rows: readonly VectorRow[]): FlatNet {
  const places = names.map(n => place(n));
  const n = names.length;
  const transitions = rows.map(r => {
    const consumeAll = new Array<boolean>(n).fill(false);
    for (const p of r.all ?? []) consumeAll[p] = true;
    return flatTransition(r.name, STUB, -1, [...r.pre], [...r.post], [], [], [...(r.reset ?? [])], consumeAll);
  });
  return {
    places,
    placeIndex: new Map(names.map((p, i) => [p, i] as const)),
    transitions,
    environmentBounds: new Map(),
    environmentInjection: new Map(),
  };
}

/** Places `names` in this order, rows `[name, pre, post]` as place → count maps. */
function flat(
  names: readonly string[],
  rows: readonly (readonly [string, Record<string, number>, Record<string, number>])[],
): FlatNet {
  const idx = (p: string): number => {
    const i = names.indexOf(p);
    if (i < 0) throw new Error(`unknown place ${p}`);
    return i;
  };
  return flatFromVectors(names, rows.map(([name, pre, post]) => {
    const pv = new Array<number>(names.length).fill(0);
    const qv = new Array<number>(names.length).fill(0);
    for (const [p, c] of Object.entries(pre)) pv[idx(p)]! += c;
    for (const [p, c] of Object.entries(post)) qv[idx(p)]! += c;
    return { name, pre: pv, post: qv };
  }));
}

function marking(net: FlatNet, tokens: Record<string, number>): MarkingState {
  const m = MarkingState.builder();
  for (const [p, k] of Object.entries(tokens)) m.tokens(net.places[net.placeIndex.get(p)!]!, k);
  return m.build();
}

function bound(net: FlatNet, m0: MarkingState, coloured: readonly number[]): SlotBound {
  return checkedSlotBound(net, m0, coloured, solveSlotBound(net, m0, coloured));
}

function cover(weights: readonly number[], d: number): ScaledCover {
  return { weights: big(weights), denominator: BigInt(d) };
}

function reasonOf(check: ReturnType<typeof checkCover>): string {
  if (check.ok) throw new Error(`accepted with k=${check.cover.k}`);
  return check.reason;
}

// ---- the simplex core ----

/**
 * Beale's example (1955) in its original rational data: maximise
 * `3/4 x4 − 20 x5 + 1/2 x6 − 6 x7` subject to `1/4 x4 − 8 x5 − x6 + 9 x7 ≤ 0`,
 * `1/2 x4 − 12 x5 − 1/2 x6 + 3 x7 ≤ 0`, `x6 ≤ 1`.
 */
function beale(): SlotTableau {
  return SlotTableau.standard(
    [
      [q(1n, 4n), q(-8n), q(-1n), q(9n)],
      [q(1n, 2n), q(-12n), q(-1n, 2n), q(3n)],
      [q(0n), q(0n), q(1n), q(0n)],
    ],
    [q(0n), q(0n), q(1n)],
    [q(3n, 4n), q(-20n), q(1n, 2n), q(-6n)],
  );
}

describe('the exact simplex core', () => {
  it("Bland's rule solves Beale's cycling example in 6 pivots", () => {
    const t = beale();
    expect(t.run('bland', 1000)).toBe('optimal');
    expect(t.objValue.toString()).toBe('5/4');
    expect(t.pivots).toBe(6);
  });

  it("the largest-coefficient rule revisits a basis on Beale's example", () => {
    // This is what Bland's rule is there for: the other rule never terminates.
    const t = beale();
    const key = (b: readonly number[]) => [...b].sort((x, y) => x - y).join(',');
    const seen = new Set([key(t.basis)]);
    let revisited: number | null = null;
    for (let step = 1; step <= 50; step++) {
      const e = t.entering('largest');
      expect(e, 'not optimal yet').not.toBeNull();
      const r = t.leaving('largest', e!);
      expect(r, 'bounded').not.toBeNull();
      t.pivot(r!, e!);
      if (seen.has(key(t.basis))) {
        revisited = step;
        break;
      }
      seen.add(key(t.basis));
    }
    expect(revisited).toBe(6);
    expect(t.objValue.isZero()).toBe(true);
  });

  it('breaks a ratio tie toward the row whose basic column is smallest', () => {
    // After the first pivot x0 is basic in row 1, and x1 then ties rows 0 (basic s2) and 1
    // (basic x0) at ratio 0. Bland's rule takes row 1, so x0 leaves; the lowest row would let
    // s2 leave and end in the basis [1, 0, 4, 5].
    const t = SlotTableau.standard(
      [[q(-1n), q(2n)], [q(2n), q(2n)], [q(-1n), q(0n)], [q(0n), q(2n)]],
      [q(0n), q(0n), q(1n), q(1n)],
      [q(1n), q(2n)],
    );
    expect(t.run('bland', 100)).toBe('optimal');
    expect([t.pivots, t.basis, t.objValue.toString()]).toEqual([2, [2, 1, 4, 5], '0']);
  });

  it('polls the pivot limit and the stop before a pivot', () => {
    const limited = beale();
    expect(limited.run('bland', 3)).toBe('pivot-limit');
    expect(limited.pivots).toBe(3);
    const stopped = beale();
    expect(stopped.run('bland', 1000, () => true)).toBe('stopped');
    expect(stopped.pivots).toBe(0);
  });

  it('rationals stay in lowest terms with a positive denominator', () => {
    expect(q(6n, -4n).toString()).toBe('-3/2');
    expect(q(4n, 2n).toString()).toBe('2');
    expect(q(1n, 3n).add(q(1n, 6n)).toString()).toBe('1/2');
    expect(q(2n, 3n).mul(q(9n, 4n)).toString()).toBe('3/2');
    expect(q(2n, 3n).div(q(-4n, 9n)).toString()).toBe('-3/2');
    expect(q(1n, 3n).cmp(q(1n, 2n))).toBeLessThan(0);
    expect(() => q(1n, 0n)).toThrow();
  });
});

// ---- the program, the checker and their reasons ----

/**
 * An `exactly(3)` fork into the keys `a`, `b` and a join that refunds one budget token:
 * optimum `14/3` at budget 7, `2/3` at budget 1.
 */
function fractionalFork(): FlatNet {
  return flat(['a', 'b', 'budget'], [
    ['mint', { budget: 3 }, { a: 1, b: 1 }],
    ['join', { a: 1, b: 1 }, { budget: 1 }],
  ]);
}

describe('the colour-slot program (NU-053)', () => {
  it('floors a fractional optimum after the re-check', () => {
    const net = fractionalFork();
    const m0 = marking(net, { budget: 7 });
    const answer = solveSlotBound(net, m0, [0, 1]);
    expect(answer.type).toBe('optimal');
    if (answer.type !== 'optimal') return;
    expect([answer.places, answer.rows]).toEqual([3, 2]);
    expect(answer.cover.denominator).toBe(3n);
    expect(answer.cover.weights).toEqual([3n, 3n, 2n]);
    const b = checkedSlotBound(net, m0, [0, 1], answer);
    expect(b.type).toBe('bound');
    expect(slotBoundK(b)).toBe(4);
    expect(b.type === 'bound' && b.value.toString()).toBe('14/3');
    expect(slotBoundReportLine(b)).toBe(
      '  Colour-slot bound: LP optimum 14/3 over 3 places and 2 transitions, so k=4 (re-checked in exact arithmetic)',
    );
    // One budget token: below one coloured token, so the exact zero-slot plan.
    expect(slotBoundK(bound(net, marking(net, { budget: 1 }), [0, 1]))).toBe(0);
  });

  it("enters by Bland's rule, the smallest column, not the largest coefficient", () => {
    // The dual maximises σ0 + 2·σ1 under σ0 + σ1 ≤ 1. Bland's rule enters σ0 first and swaps
    // it for σ1 in a second pivot; the largest coefficient would take σ1 in one.
    const net = flat(['a', 'budget'], [
      ['one', { budget: 1 }, { a: 1 }],
      ['two', { budget: 1 }, { a: 2 }],
    ]);
    const m0 = marking(net, { budget: 1 });
    const { answer, pivots } = solveSlotBoundCounted(net, m0, [0]);
    expect(pivots).toBe(2);
    expect(answer.type === 'optimal' && answer.cover.weights).toEqual([1n, 2n]);
    expect(slotBoundK(checkedSlotBound(net, m0, [0], answer))).toBe(2);
  });

  it('gives k = 0 without a budget token and refuses an inflating join as infeasible', () => {
    const conserving = flat(['a', 'b', 'budget'], [
      ['mint', { budget: 1 }, { a: 1, b: 1 }],
      ['join', { a: 1, b: 1 }, { budget: 1 }],
    ]);
    expect(slotBoundK(bound(conserving, marking(conserving, {}), [0, 1]))).toBe(0);
    expect(slotBoundK(bound(conserving, marking(conserving, { budget: 3 }), [0, 1]))).toBe(6);
    // The join refunds two tokens, one to each budget place: the colours multiply.
    const inflating = flat(['a', 'b', 'budget1', 'budget2'], [
      ['mint1', { budget1: 1 }, { a: 1, b: 1 }],
      ['mint2', { budget2: 1 }, { a: 1, b: 1 }],
      ['join', { a: 1, b: 1 }, { budget1: 1, budget2: 1 }],
    ]);
    const b = bound(inflating, marking(inflating, { budget1: 1 }), [0, 1]);
    expect(b).toEqual({ type: 'infeasible', places: 4, rows: 3 });
    expect(slotBoundReportLine(b)).toBe(
      '  Colour-slot bound: none (LP infeasible over 4 places and 3 transitions: no weighting bounds the coloured tokens)',
    );
  });

  it('keeps the upstream cone in the presolve and drops duplicate rows', () => {
    // A row producing into the cone with an entry outside it, a duplicate restricted row, a
    // consume-only row and an unrelated cycle.
    const net = flat(['a', 'budget', 'log', 'x', 'y'], [
      ['mint', { budget: 1 }, { a: 1, log: 1 }],
      ['mint_again', { budget: 1 }, { a: 1 }],
      ['consume', { a: 1 }, {}],
      ['cycle', { x: 1 }, { y: 1 }],
      ['back', { y: 1 }, { x: 1 }],
    ]);
    const m0 = marking(net, { budget: 2, x: 1 });
    const p = presolve(net, [true, false, false, false, false]);
    expect(p.places).toEqual([0, 1]);
    expect(p.rows).toEqual([[[0, 1n], [1, -1n]]]);
    const b = bound(net, m0, [0]);
    expect(b.type === 'bound' && [b.k, b.value.toString(), b.places, b.rows]).toEqual([2, '2', 2, 1]);
    // m' = 0: nothing produces into the coloured place.
    const empty = flat(['a', 'b'], [['t', { a: 1 }, { b: 1 }]]);
    expect(presolve(empty, [true, false]).rows.length).toBe(0);
    expect(slotBoundK(bound(empty, marking(empty, { b: 4 }), [0]))).toBe(0);
  });

  it('keeps big counts and denominators exact', () => {
    // A mint that turns 2^50 budget tokens into 2^50 − 1 keys, with 2^30 budget tokens: the
    // optimum (2^50 − 1)·2^30 / 2^50 has a numerator far outside a double's exact range.
    const two50 = 2 ** 50;
    const net = flat(['a', 'budget'], [
      ['mint', { budget: two50 }, { a: two50 - 1 }],
      ['join', { a: 1 }, { budget: 1 }],
    ]);
    const m0 = marking(net, { budget: 2 ** 30 });
    const answer = solveSlotBound(net, m0, [0]);
    expect(answer.type).toBe('optimal');
    if (answer.type !== 'optimal') return;
    expect(answer.cover.denominator).toBe(2n ** 50n);
    expect(answer.cover.weights).toEqual([2n ** 50n, 2n ** 50n - 1n]);
    const b = checkedSlotBound(net, m0, [0], answer);
    const expected = Rational.of((2n ** 50n - 1n) * 2n ** 30n, 2n ** 50n);
    expect(expected.toString()).toBe('1125899906842623/1048576');
    expect(b.type === 'bound' && b.value.equals(expected)).toBe(true);
    expect(slotBoundK(b)).toBe(2 ** 30 - 1);
  });

  it('decides the size limit before any pivot', () => {
    // One row consuming from 4096 places into the coloured one puts all 4097 in the cone.
    const n = SLOT_LP_MAX_PLACES + 1;
    const names = Array.from({ length: n }, (_, i) => `p${String(i).padStart(5, '0')}`);
    const pre = new Array<number>(n).fill(1);
    pre[0] = 0;
    const post = new Array<number>(n).fill(0);
    post[0] = 1;
    const net = flatFromVectors(names, [{ name: 'gather', pre, post }]);
    const m0 = MarkingState.empty();
    const { answer, pivots } = solveSlotBoundCounted(net, m0, [0]);
    expect(answer).toEqual({ type: 'too-large', places: n, rows: 1 });
    expect(pivots).toBe(0);
    expect(slotBoundReportLine(checkedSlotBound(net, m0, [0], answer))).toBe(
      '  Colour-slot bound: none (LP over 4097 places and 1 transitions exceeds the limit of 4096 places and 16384 transitions)',
    );
  });

  it('refuses each clause of the checker with its reason, in order', () => {
    const net = fractionalFork();
    const m0 = marking(net, { budget: 7 });
    const check = (c: ScaledCover) => checkCover(net, m0, [0, 1], c);
    const ok = check(cover([3, 3, 2], 3));
    expect(ok.ok && [ok.cover.k, ok.cover.value.toString()]).toEqual([4, '14/3']);
    expect(reasonOf(check(cover([3, 3], 3)))).toBe('weighting has 2 entries for 3 places');
    expect(reasonOf(check(cover([3, 3, 2], 0)))).toBe('denominator 0 is not positive');
    expect(reasonOf(check(cover([-3, -3, -2], -3)))).toBe('denominator -3 is not positive');
    expect(reasonOf(check(cover([3, 3, -2], 3)))).toBe("place 'budget' has negative weight -2");
    expect(reasonOf(check(cover([3, 2, 2], 3)))).toBe("coloured place 'b' has weight 2 below the denominator 3");
    // Keys at 1 and the budget at 0: the mint raises the weighted sum by 2.
    expect(reasonOf(check(cover([1, 1, 0], 1)))).toBe("transition 'mint' increases the weighted sum by 2");
    // Feasible and above the cap: k = 7·2^31 / 3 > 2147483647.
    const w = 2 ** 31;
    expect(reasonOf(check(cover([w * 3 / 2, w * 3 / 2, w], 3)))).toBe(`k=${(7n * 2n ** 31n) / 3n} exceeds 2147483647`);
    // A feasible weighting that is not optimal is accepted, with its larger k.
    const loose = check(cover([1, 1, 1], 1));
    expect(loose.ok && loose.cover.k).toBe(7);
  });

  it('checks rows the presolve dropped', () => {
    // `spill` only consumes from the cone, so it has no positive entry there and never reaches
    // the simplex, but a weighting that is negative on its output must still fail.
    const net = flat(['a', 'budget', 'z'], [
      ['mint', { budget: 1 }, { a: 1 }],
      ['join', { a: 1 }, { budget: 1 }],
      ['spill', { a: 1 }, { z: 2 }],
    ]);
    const m0 = marking(net, { budget: 1 });
    expect(presolve(net, [true, false, false]).rows.length).toBe(2);
    // z = 1: spill raises the sum by 2·1 − 1 = 1.
    expect(reasonOf(checkCover(net, m0, [0], cover([1, 1, 1], 1)))).toBe("transition 'spill' increases the weighted sum by 1");
    expect(slotBoundK(bound(net, m0, [0]))).toBe(1);
  });

  it('gives no bound for every answer without a weighting', () => {
    const net = fractionalFork();
    const m0 = marking(net, {});
    const limited = checkedSlotBound(net, m0, [0, 1], { type: 'pivot-limit', limit: 250 });
    expect(slotBoundK(limited)).toBeNull();
    expect(slotBoundReportLine(limited)).toBe('  Colour-slot bound: none (no LP optimum within the pivot limit of 250)');
    const stopped = checkedSlotBound(net, m0, [0, 1], { type: 'stopped' });
    expect(slotBoundK(stopped)).toBeNull();
    expect(slotBoundReportLine(stopped)).toBeNull();
    const short = checkedSlotBound(net, m0, [0, 1], { type: 'optimal', cover: cover([1, 1], 1), places: 3, rows: 2 });
    expect(slotBoundReportLine(short)).toBe(
      '  Colour-slot bound: none (LP weighting failed the exact re-check: weighting has 2 entries for 3 places)',
    );
  });
});

// ---- the shared parity cases ----

interface JsonRow {
  readonly name: string;
  readonly pre?: Record<string, number>;
  readonly post?: Record<string, number>;
  readonly reset?: readonly string[];
  readonly consumeAll?: readonly string[];
}

interface JsonCase {
  readonly id: string;
  readonly places: readonly string[];
  readonly coloured: readonly string[];
  readonly marking?: Record<string, number>;
  readonly rows: readonly JsonRow[];
  readonly expected: {
    readonly status: string;
    readonly places?: number;
    readonly rows?: number;
    readonly pivots: number;
    readonly optimum?: string;
    readonly k?: number;
    readonly weights?: Record<string, string>;
    readonly denominator?: string;
  };
}

/** One LP subject: a flat net, its initial marking and its coloured places (ascending). */
interface Subject {
  readonly id: string;
  readonly flat: FlatNet;
  readonly initial: MarkingState;
  readonly coloured: readonly number[];
}

const here = dirname(fileURLToPath(import.meta.url));
const LP_CASES: readonly JsonCase[] = JSON.parse(
  readFileSync(resolve(here, '../../../spec/verification-fixtures/slot-bound-lp.json'), 'utf8'),
).cases;

function buildCase(c: JsonCase): Subject {
  const index = new Map(c.places.map((p, i) => [p, i] as const));
  const at = (p: string): number => {
    const i = index.get(p);
    if (i === undefined) throw new Error(`[${c.id}] unknown place '${p}'`);
    return i;
  };
  const counts = (m: Record<string, number> | undefined): number[] => {
    const v = new Array<number>(c.places.length).fill(0);
    for (const [p, k] of Object.entries(m ?? {})) v[at(p)]! += k;
    return v;
  };
  const net = flatFromVectors(c.places, c.rows.map(r => ({
    name: r.name,
    pre: counts(r.pre),
    post: counts(r.post),
    reset: (r.reset ?? []).map(at),
    all: (r.consumeAll ?? []).map(at),
  })));
  return {
    id: c.id,
    flat: net,
    initial: marking(net, c.marking ?? {}),
    coloured: c.coloured.map(at).sort((x, y) => x - y),
  };
}

const paritySubjects = (): Subject[] => LP_CASES.map(buildCase);

describe('the shared colour-slot LP cases (spec/verification-fixtures/slot-bound-lp.json)', () => {
  it('lists cases', () => {
    expect(LP_CASES.length).toBeGreaterThanOrEqual(16);
  });

  for (const c of LP_CASES) {
    it(`${c.id}: the same status, sizes, pivots, optimum, k and weighting as Rust`, () => {
      const s = buildCase(c);
      const { answer, pivots } = solveSlotBoundCounted(s.flat, s.initial, s.coloured);
      const status = answer.type;
      const actual: Record<string, unknown> = { status };
      if (answer.type === 'optimal' || answer.type === 'infeasible' || answer.type === 'too-large') {
        actual.places = answer.places;
        actual.rows = answer.rows;
      }
      actual.pivots = pivots;
      if (answer.type === 'optimal') {
        const b = checkedSlotBound(s.flat, s.initial, s.coloured, answer);
        expect(b.type, `[${c.id}] the simplex's weighting failed the re-check: ${slotBoundReportLine(b)}`).toBe('bound');
        if (b.type === 'bound') {
          actual.optimum = b.value.toString();
          actual.k = b.k;
        }
        const weights: Record<string, string> = {};
        answer.cover.weights.forEach((w, p) => { if (w !== 0n) weights[s.flat.places[p]!.name] = w.toString(); });
        actual.weights = weights;
        actual.denominator = answer.cover.denominator.toString();
      }
      expect(actual).toEqual(c.expected);
    });
  }

  it('solves the seeded composed workflow (255 x 341) to optimum 6 in few pivots', () => {
    const s = paritySubjects().find(x => x.id === 'composed-workflow-7')!;
    expect([s.flat.places.length, s.flat.transitions.length]).toEqual([255, 341]);
    const t0 = performance.now();
    const { answer, pivots } = solveSlotBoundCounted(s.flat, s.initial, s.coloured);
    const elapsed = performance.now() - t0;
    expect(answer.type).toBe('optimal');
    if (answer.type !== 'optimal') return;
    expect(pivots).toBeLessThanOrEqual(2 * (answer.places + answer.rows));
    expect(slotBoundK(checkedSlotBound(s.flat, s.initial, s.coloured, answer))).toBe(6);
    // A generous ceiling for a loaded CI machine; the solve takes tens of milliseconds.
    expect(elapsed).toBeLessThan(2_000);
  });
});

// ---- the differential corpus ----

/** The coloured places `buildColouredPlan` hands the slot bound, or null when a structural refusal comes first. */
function planColoured(
  net: PetriNet, flatNet: FlatNet, initial: MarkingState, budgets: readonly string[], carriers: readonly string[],
  mode: FragmentMode,
): number[] | null {
  let seen: number[] | null = null;
  buildColouredPlan(
    net, flatNet, initial, declaredMints(net, new Set(budgets), new Set()), mode, new Set(carriers),
    c => {
      seen = [...c];
      return solveSlotBound(flatNet, initial, c);
    },
  );
  return seen;
}

/** The PNID relay nets at budgets 1 and 2, with the coloured set their plan computes. */
function relaySubjects(): Subject[] {
  const nets: [string, Parameters<typeof pnidNet>[1], string, readonly string[]][] = [
    ['fig12c', FIG_12C_ROWS, 'R', ['P1', 'B1', 'B2', 'C1', 'D1']],
    ['n1', N1_CORR_ROWS, 'SUPPLY', []],
    ['s-union', UNION_ROWS, 'SUPPLY', ['q']],
    ['join-chain', JOIN_CHAIN_ROWS, 'S', []],
    ['join-chain-split', JOIN_CHAIN_SPLIT_ROWS, 'S', []],
  ];
  const out: Subject[] = [];
  for (const [name, rows, budget, carriers] of nets) {
    const { net, places } = pnidNet(name, rows);
    const flatNet = flatten(net);
    for (const scale of [1, 2]) {
      const m = MarkingState.builder().tokens(places.get(budget)!, scale);
      if (name === 'join-chain-split') m.tokens(places.get('S2')!, scale);
      const initial = m.build();
      const coloured = planColoured(net, flatNet, initial, [budget], carriers, 'extended');
      if (coloured === null) continue;
      out.push({ id: `${name}@${scale}`, flat: flatNet, initial, coloured });
    }
  }
  return out;
}

const MASK = (1n << 64n) - 1n;

/** xorshift64*, as the Rust corpus draws it, so both languages build the same nets. */
class Rng {
  private s: bigint;
  constructor(seed: number) {
    this.s = ((BigInt(seed) * 0x9E3779B97F4A7C15n) & MASK) | 1n;
  }
  next(): bigint {
    this.s ^= this.s >> 12n;
    this.s ^= (this.s << 25n) & MASK;
    this.s ^= this.s >> 27n;
    return (this.s * 0x2545F4914F6CDD1Dn) & MASK;
  }
  below(n: number): number {
    return Number(this.next() % BigInt(n));
  }
  chance(percent: number): boolean {
    return this.below(100) < percent;
  }
}

/**
 * A seeded small ν-like flat net: two keys (sometimes a third coloured carrier), a budget, a
 * few uncoloured places, mints into the keys, joins out of them, a coloured drain now and then,
 * and uncoloured rows, some with a reset or consume-all arc on an uncoloured place. Coloured
 * places start empty. The draws follow the Rust `random_subject` one for one.
 */
function randomSubject(seed: number): Subject {
  const rng = new Rng(seed);
  const carrier = rng.chance(30);
  const extra = 1 + rng.below(3);
  const names = ['a', 'b', 'budget'];
  if (carrier) names.push('c');
  for (let i = 0; i < extra; i++) names.push(`u${i}`);
  names.sort();
  const n = names.length;
  const idx = (p: string): number => names.indexOf(p);
  const keys = carrier ? [idx('a'), idx('b'), idx('c')] : [idx('a'), idx('b')];
  const carrierPlace = carrier ? idx('c') : null;
  const unc = names.map((_, p) => p).filter(p => !keys.includes(p));
  const rows: VectorRow[] = [];
  const zeros = () => new Array<number>(n).fill(0);
  const anyUnc = () => unc[rng.below(unc.length)]!;
  const mints = 1 + rng.below(2);
  for (let m = 0; m < mints; m++) {
    const pre = zeros();
    const post = zeros();
    pre[idx('budget')] = 1 + rng.below(3);
    if (rng.chance(30)) pre[anyUnc()]! += 1;
    for (const k of keys) if (rng.chance(85) || k === idx('a')) post[k] = 1;
    if (rng.chance(30)) post[anyUnc()]! += 1;
    rows.push({ name: `mint${m}`, pre, post });
  }
  const joins = 1 + rng.below(2);
  for (let j = 0; j < joins; j++) {
    const pre = zeros();
    const post = zeros();
    for (const k of keys) if (k !== carrierPlace || rng.chance(50)) pre[k] = 1;
    post[idx('budget')] = rng.below(3);
    if (rng.chance(50)) post[anyUnc()]! += 1;
    rows.push({ name: `join${j}`, pre, post });
  }
  if (rng.chance(30)) {
    const pre = zeros();
    const post = zeros();
    pre[keys[rng.below(keys.length)]!] = 1;
    post[anyUnc()] = 1;
    rows.push({ name: 'drain', pre, post });
  }
  const sides = rng.below(4);
  for (let t = 0; t < sides; t++) {
    const pre = zeros();
    const post = zeros();
    const from = anyUnc();
    const to = anyUnc();
    pre[from] = 1 + rng.below(2);
    post[to]! += 1 + rng.below(2);
    const reset: number[] = [];
    const allPlaces: number[] = [];
    const side = anyUnc();
    const arm = rng.below(6);
    if (arm === 0 && side !== from) reset.push(side);
    else if (arm === 1) {
      pre[from] = 1;
      allPlaces.push(from);
    }
    rows.push({ name: `side${t}`, pre, post, reset, all: allPlaces });
  }
  const net = flatFromVectors(names, rows);
  const m = MarkingState.builder().tokens(net.places[idx('budget')]!, rng.below(4));
  for (const u of unc) {
    if (names[u] !== 'budget' && rng.chance(40)) m.tokens(net.places[u]!, 1 + rng.below(2));
  }
  return { id: `random-${seed}`, flat: net, initial: m.build(), coloured: keys };
}

let corpusCache: Subject[] | null = null;
function corpus(): Subject[] {
  corpusCache ??= [...paritySubjects(), ...relaySubjects(), ...Array.from({ length: 300 }, (_, i) => randomSubject(i))];
  return corpusCache;
}

/** The simplex's checked bound. */
const lpBound = (s: Subject): SlotBound => bound(s.flat, s.initial, s.coloured);

const STATE_CAP = 5_000;

const m0Of = (s: Subject): number[] => s.flat.places.map(p => s.initial.tokens(p));
const isReset = (t: FlatTransition, p: number): boolean => t.resetPlaces.includes(p) || t.consumeAll[p] === true;

/**
 * Fires a row as Lean `fireAD` does: a reset or consume-all place ends at the row's deposit,
 * every other place at `m − pre + post`. Inhibitor and read arcs are ignored, which only adds
 * markings.
 */
function fireAD(t: FlatTransition, m: readonly number[]): number[] | null {
  for (let p = 0; p < m.length; p++) if (t.preVector[p]! > m[p]!) return null;
  return m.map((v, p) => isReset(t, p) ? t.postVector[p]! : v - t.preVector[p]! + t.postVector[p]!);
}

/** The largest coloured token count over the `fireAD` state space, and whether it closed. */
function maxColouredTokens(s: Subject): { tokens: number; closed: boolean } {
  const m0 = m0Of(s);
  const seen = new Set([m0.join(',')]);
  const queue = [m0];
  let best = 0;
  for (let head = 0; head < queue.length; head++) {
    const m = queue[head]!;
    best = Math.max(best, s.coloured.reduce((acc, p) => acc + m[p]!, 0));
    for (const t of s.flat.transitions) {
      const next = fireAD(t, m);
      if (next === null) continue;
      if (seen.size >= STATE_CAP) return { tokens: best, closed: false };
      const key = next.join(',');
      if (!seen.has(key)) {
        seen.add(key);
        queue.push(next);
      }
    }
  }
  return { tokens: best, closed: true };
}

/**
 * The name semantics of the flat rows: a row consuming coloured places takes one name from all
 * of them and writes it into its coloured outputs; a row writing coloured places without
 * consuming one writes a fresh name. The largest number of names live at once and the largest
 * coloured token count, and whether the space closed.
 */
function maxLiveNames(s: Subject): { live: number; tokens: number; closed: boolean } {
  const n = s.flat.places.length;
  const isCol = (p: number): boolean => s.coloured.includes(p);
  type Tok = readonly [number, number];
  type State = { unc: number[]; col: Tok[] };
  const cmpTok = (x: Tok, y: Tok): number => x[0] - y[0] || x[1] - y[1];
  // Names renamed by first appearance, so the space stays finite.
  const normal = ({ unc, col }: State): State => {
    const sorted = [...col].sort(cmpTok);
    const map = new Map<number, number>();
    const renamed = sorted.map(([p, x]) => {
      if (!map.has(x)) map.set(x, map.size);
      return [p, map.get(x)!] as const;
    });
    return { unc, col: renamed.sort(cmpTok) };
  };
  const keyOf = (st: State): string => `${st.unc.join(',')}|${st.col.map(([p, x]) => `${p}:${x}`).join(',')}`;
  const start = normal({ unc: m0Of(s), col: [] });
  const seen = new Set([keyOf(start)]);
  const queue = [start];
  let live = 0;
  let tokens = 0;
  const push = (next: State): boolean => {
    if (seen.size >= STATE_CAP) return false;
    const key = keyOf(next);
    if (!seen.has(key)) {
      seen.add(key);
      queue.push(next);
    }
    return true;
  };
  for (let head = 0; head < queue.length; head++) {
    const { unc, col } = queue[head]!;
    const names = new Set(col.map(e => e[1]));
    live = Math.max(live, names.size);
    tokens = Math.max(tokens, col.length);
    for (const t of s.flat.transitions) {
      let uncOk = true;
      for (let p = 0; p < n; p++) if (!isCol(p) && t.preVector[p]! > unc[p]!) uncOk = false;
      if (!uncOk) continue;
      const firedUnc = unc.map((v, p) =>
        isCol(p) ? 0 : isReset(t, p) ? t.postVector[p]! : v - t.preVector[p]! + t.postVector[p]!);
      const colIn = s.coloured.filter(p => t.preVector[p]! > 0);
      const colOut = s.coloured.filter(p => t.postVector[p]! > 0);
      if (colIn.length === 0 && colOut.length === 0) {
        if (!push(normal({ unc: firedUnc, col: [...col] }))) return { live, tokens, closed: false };
        continue;
      }
      let candidates: number[];
      if (colIn.length === 0) {
        let fresh = 0;
        while (names.has(fresh)) fresh++;
        candidates = [fresh];
      } else {
        candidates = [...names].sort((x, y) => x - y).filter(x =>
          colIn.every(p => col.filter(e => e[0] === p && e[1] === x).length >= t.preVector[p]!));
      }
      for (const x of candidates) {
        const c: Tok[] = [...col];
        for (const p of colIn) {
          for (let i = 0; i < t.preVector[p]!; i++) c.splice(c.findIndex(e => e[0] === p && e[1] === x), 1);
        }
        for (const p of colOut) for (let i = 0; i < t.postVector[p]!; i++) c.push([p, x]);
        if (!push(normal({ unc: [...firedUnc], col: c }))) return { live, tokens, closed: false };
      }
    }
  }
  return { live, tokens, closed: true };
}

/** Verbatim port of the colour-slot bound before the linear program (Rust `old_slot_bound.rs`). */
function oldColourSlotBound(coloured: readonly number[], semiflows: readonly PInvariant[]): number | null {
  const w = (inv: PInvariant, pid: number): number => inv.weights[pid] ?? 0;
  const isSemiflow = (inv: PInvariant): boolean => inv.weights.every(x => x >= 0);
  let single: number | null = null;
  for (const inv of semiflows) {
    if (isSemiflow(inv) && coloured.every(pid => w(inv, pid) >= 1)) {
      if (single === null || inv.constant < single) single = inv.constant;
    }
  }
  if (single !== null) return single;
  const covered = new Array<boolean>(coloured.length).fill(false);
  for (const inv of semiflows) {
    if (!isSemiflow(inv) || inv.constant !== 0) continue;
    coloured.forEach((pid, i) => { if (w(inv, pid) >= 1) covered[i] = true; });
  }
  const free = [...covered];
  let sumConst = 0;
  for (const inv of semiflows) {
    if (!isSemiflow(inv) || inv.constant === 0) continue;
    if (!coloured.some((pid, i) => !free[i] && w(inv, pid) >= 1)) continue;
    coloured.forEach((pid, i) => { if (w(inv, pid) >= 1) covered[i] = true; });
    sumConst += inv.constant;
  }
  return covered.every(c => c) ? sumConst : null;
}

/**
 * The weighting behind {@link oldColourSlotBound}: the covering semiflow it picked (the first of
 * least constant), or the sum of the semiflows its fallback added.
 */
function oldColourSlotWeighting(n: number, coloured: readonly number[], semiflows: readonly PInvariant[]): number[] | null {
  const w = (inv: PInvariant, pid: number): number => inv.weights[pid] ?? 0;
  const nonNeg = semiflows.filter(inv => inv.weights.every(x => x >= 0));
  let best: PInvariant | null = null;
  for (const inv of nonNeg) {
    if (coloured.every(pid => w(inv, pid) >= 1) && (best === null || inv.constant < best.constant)) best = inv;
  }
  if (best !== null) return Array.from({ length: n }, (_, p) => w(best!, p));
  const free = coloured.map(pid => nonNeg.some(inv => inv.constant === 0 && w(inv, pid) >= 1));
  const sum = new Array<number>(n).fill(0);
  const covered = [...free];
  for (const inv of nonNeg) {
    const take = inv.constant === 0
      ? coloured.some(pid => w(inv, pid) >= 1)
      : coloured.some((pid, i) => !free[i] && w(inv, pid) >= 1);
    if (!take) continue;
    coloured.forEach((pid, i) => { if (w(inv, pid) >= 1) covered[i] = true; });
    for (let p = 0; p < n; p++) sum[p]! += w(inv, p);
  }
  return covered.every(c => c) ? sum : null;
}

/** The gate-validated semiflows the old bound read, computed as the verifier did. */
function validatedSemiflows(flatNet: FlatNet, initial: MarkingState): readonly PInvariant[] {
  const matrix = IncidenceMatrix.from(flatNet);
  return validateInvariantsExact(matrix, computePSemiflows(matrix, flatNet, initial), flatNet, initial).valid;
}

describe('the colour-slot program against the state space and the semiflow bound', () => {
  it('LP k bounds the largest coloured token count, which bounds the live names', () => {
    let checked = 0;
    let tight = 0;
    for (const s of corpus()) {
      const b = lpBound(s);
      if (b.type !== 'bound') continue;
      const { tokens, closed } = maxColouredTokens(s);
      const names = maxLiveNames(s);
      expect(tokens, `[${s.id}] ${tokens} coloured tokens reachable above k=${b.k}`).toBeLessThanOrEqual(b.k);
      expect(names.live, `[${s.id}]`).toBeLessThanOrEqual(names.tokens);
      if (closed && names.closed) expect(names.tokens, `[${s.id}] name semantics beyond fireAD`).toBeLessThanOrEqual(tokens);
      checked++;
      if (tokens === b.k) tight++;
    }
    expect(checked, `checked ${checked}, tight ${tight}`).toBeGreaterThanOrEqual(200);
    expect(tight, `checked ${checked}, tight ${tight}`).toBeGreaterThanOrEqual(100);
  }, 120_000);

  it('LP k never exceeds the semiflow bound, and an infeasible program means it had none', () => {
    let compared = 0;
    let smaller = 0;
    let admitted = 0;
    for (const s of corpus()) {
      const old = oldColourSlotBound(s.coloured, validatedSemiflows(s.flat, s.initial));
      const b = lpBound(s);
      if (b.type === 'bound') {
        if (old === null) {
          admitted++;
        } else {
          expect(b.k, `[${s.id}] LP k=${b.k} above the semiflow bound ${old}`).toBeLessThanOrEqual(old);
          compared++;
          if (b.k < old) smaller++;
        }
      } else {
        expect(b.type, `[${s.id}] unexpected answer`).toBe('infeasible');
        expect(old, `[${s.id}] LP infeasible but a covering semiflow exists`).toBeNull();
      }
    }
    const summary = `compared ${compared}, smaller ${smaller}, admitted ${admitted}`;
    expect(compared, summary).toBeGreaterThanOrEqual(40);
    expect(smaller, summary).toBeGreaterThanOrEqual(10);
    expect(admitted, summary).toBeGreaterThanOrEqual(10);
  }, 120_000);
});

/** A `QF_LRA` question about the program: `extra` conjoined to its constraints. */
function lraScript(s: Subject, extra: string): string {
  const n = s.flat.places.length;
  const out: string[] = ['(set-logic QF_LRA)'];
  for (let p = 0; p < n; p++) out.push(`(declare-const y${p} Real)`, `(assert (>= y${p} 0.0))`);
  for (const p of s.coloured) out.push(`(assert (>= y${p} 1.0))`);
  const real = (v: number): string => v < 0 ? `(- ${-v}.0)` : `${v}.0`;
  const sum = (terms: string[]): string => terms.length === 0 ? '0.0' : `(+ 0.0 ${terms.join(' ')})`;
  for (const t of s.flat.transitions) {
    const terms: string[] = [];
    for (let p = 0; p < n; p++) {
      const v = t.postVector[p]! - t.preVector[p]!;
      if (v !== 0) terms.push(`(* ${real(v)} y${p})`);
    }
    out.push(`(assert (<= ${sum(terms)} 0.0))`);
  }
  const objective: string[] = [];
  s.flat.places.forEach((pl, p) => {
    const m = s.initial.tokens(pl);
    if (m !== 0) objective.push(`(* ${real(m)} y${p})`);
  });
  out.push(extra.replace('OBJ', sum(objective)), '(check-sat)');
  return out.join('\n') + '\n';
}

async function z3Answer(script: string): Promise<string> {
  const reply = await runZ3Text(resolveZ3(), script, 'slot-bound-lp-test', 60_000);
  return reply.stdout.split('\n')[0]!.trim();
}

describeZ3('the colour-slot optimum against z3 over the reals', () => {
  it('is satisfiable at the LP optimum, unsatisfiable strictly below it, and infeasible alike', async () => {
    const agree = async (s: Subject): Promise<void> => {
      const b = lpBound(s);
      if (b.type === 'bound') {
        const v = `(/ ${b.value.num}.0 ${b.value.den}.0)`;
        expect(await z3Answer(lraScript(s, `(assert (<= OBJ ${v}))`)), `[${s.id}]`).toBe('sat');
        expect(await z3Answer(lraScript(s, `(assert (< OBJ ${v}))`)), `[${s.id}] ${b.value}`).toBe('unsat');
      } else {
        expect(b.type, `[${s.id}] unexpected answer`).toBe('infeasible');
        expect(await z3Answer(lraScript(s, '')), `[${s.id}]`).toBe('unsat');
      }
    };
    // Eight z3 processes at a time: each query is independent.
    const subjects = corpus();
    for (let i = 0; i < subjects.length; i += 8) await Promise.all(subjects.slice(i, i + 8).map(agree));
  }, 300_000);
});

// ---- the re-check cannot be bypassed ----

/** The scatter-gather ν-net, optionally with `archive: merged → archived`, a row the presolve drops. */
function scatterGather(archive: boolean): { net: PetriNet; initial: MarkingState } {
  const [source, budget, pending, a, b, merged, archived] =
    ['source', 'budget', 'pending', 'branchA', 'branchB', 'merged', 'archived'].map(n => place<string>(n)) as Place<string>[];
  const key = (s: string) => nameId(s);
  const fork = Transition.builder('fork')
    .inputs(one(source!), one(budget!)).outputs(andPlaces(a!, b!, pending!)).action(produces()).build();
  const join = Transition.builder('join')
    .inputs(one(a!), one(b!), one(pending!))
    .match(matchSpec(matchKey(a!, key), matchKey(b!, key)))
    .outputs(andPlaces(merged!, budget!)).action(produces()).build();
  const ts = [fork, join];
  if (archive) ts.push(Transition.builder('archive').inputs(one(merged!)).outputs(outPlace(archived!)).action(produces()).build());
  const net = PetriNet.builder(archive ? 'scatter_gather_archive' : 'nuScatterGather').transitions(...ts).build();
  return { net, initial: MarkingState.builder().tokens(source!, 3).tokens(budget!, 2).build() };
}

/** `buildColouredPlan` with the simplex replaced by `answer`, and the bound it reported. */
function planWith(
  net: PetriNet, initial: MarkingState, answer: (flatNet: FlatNet) => LpAnswer,
): { plan: ColouredPlan | null; reported: SlotBound; flatNet: FlatNet } {
  const flatNet = flatten(net);
  let reported: SlotBound | null = null;
  const plan = buildColouredPlan(
    net, flatNet, initial, declaredMints(net, new Set(['budget']), new Set()), 'base', new Set(),
    () => answer(flatNet), b => { reported = b; },
  );
  expect(reported, 'the sink is called once the plan reaches the bound').not.toBeNull();
  return { plan, reported: reported!, flatNet };
}

/** Weights by place name, every other place 0. */
function weights(flatNet: FlatNet, byName: readonly (readonly [string, number])[], d: number): LpAnswer {
  const w = new Array<bigint>(flatNet.places.length).fill(0n);
  for (const [p, v] of byName) w[flatNet.placeIndex.get(p)!] = BigInt(v);
  return { type: 'optimal', cover: { weights: w, denominator: BigInt(d) }, places: 5, rows: 2 };
}

describe('buildColouredPlan takes k only from a weighting the re-check accepts', () => {
  const { net, initial } = scatterGather(true);
  const optimal = [['branchA', 1], ['branchB', 1], ['budget', 2]] as const;

  it('takes k = 4 from the simplex', () => {
    const { plan, reported } = planWith(net, initial, f =>
      solveSlotBound(f, initial, [f.placeIndex.get('branchA')!, f.placeIndex.get('branchB')!].sort((x, y) => x - y)));
    expect(plan?.k, slotBoundReportLine(reported) ?? reported.type).toBe(4);
  });

  const refused: [readonly (readonly [string, number])[], number, string][] = [
    [[...optimal, ['pending', -1]], 1, "place 'pending' has negative weight -1"],
    [[['branchA', 2], ['branchB', 1], ['budget', 6]], 2, "coloured place 'branchB' has weight 1 below the denominator 2"],
    [[...optimal, ['archived', 1]], 1, "transition 'archive' increases the weighted sum by 1"],
    [optimal, 0, 'denominator 0 is not positive'],
    [optimal, -1, 'denominator -1 is not positive'],
    [[...optimal, ['source', 2 ** 31]], 1, 'k=6442450948 exceeds 2147483647'],
  ];
  for (const [w, d, reason] of refused) {
    it(`refuses: ${reason}`, () => {
      const { plan, reported } = planWith(net, initial, f => weights(f, w, d));
      expect(plan).toBeNull();
      expect(reported).toEqual({ type: 'check-failed', reason });
      expect(slotBoundReportLine(reported)).toBe(`  Colour-slot bound: none (LP weighting failed the exact re-check: ${reason})`);
    });
  }

  it('accepts a feasible weighting that is not optimal, with its larger k', () => {
    const { plan } = planWith(net, initial, f => weights(f, [...optimal, ['source', 1]], 1));
    expect(plan?.k).toBe(7);
  });

  it('refuses the plan on every answer without a weighting', () => {
    const answers: LpAnswer[] = [
      { type: 'infeasible', places: 5, rows: 2 }, { type: 'pivot-limit', limit: 350 }, { type: 'stopped' },
    ];
    for (const a of answers) expect(planWith(net, initial, () => a).plan, a.type).toBeNull();
  });
});

// ---- verdict invariance, the report and the deadline ----

describeZ3('the colour-slot bound in the verifier', () => {
  it('gives the same verdicts with the LP k as with the old semiflow k (scatter-gather, 10 -> 4)', async () => {
    // Spacer may run out of time on the larger encoding (unknown); it must never answer the
    // other way.
    const { net, initial } = scatterGather(false);
    const flatNet = flatten(net);
    const coloured = ['branchA', 'branchB'].map(p => flatNet.placeIndex.get(p)!).sort((x, y) => x - y);
    const old = oldColourSlotWeighting(flatNet.places.length, coloured, validatedSemiflows(flatNet, initial));
    expect(old, 'the scatter-gather net has a covering semiflow').not.toBeNull();
    const oldAnswer: LpAnswer = { type: 'optimal', cover: { weights: big(old!), denominator: 1n }, places: 0, rows: 0 };
    const oldPlan = planWith(net, initial, () => oldAnswer).plan!;
    const lpPlan = planWith(net, initial, f => solveSlotBound(f, initial, coloured)).plan!;
    expect([oldPlan.k, lpPlan.k]).toEqual([10, 4]);
    const p = (name: string) => flatNet.places[flatNet.placeIndex.get(name)!]!;
    const queries: [string, number, 'proven' | 'violated'][] = [
      ['budget', 2, 'proven'], ['branchA', 2, 'proven'], ['branchA', 1, 'violated'],
      ['merged', 2, 'violated'], ['pending', 2, 'proven'],
    ];
    const solver = resolveZ3();
    const spacer = (plan: ColouredPlan, placeName: string, k: number): Promise<string> => {
      const enc = encodeColoured(plan, flatNet, initial, placeBound(p(placeName), k), [], new Set());
      expect(enc).not.toBeNull();
      return runZ3Spacer(solver, 20_000, enc!.smt2, 'slot-bound-lp-test').then(r => r.type);
    };
    // Every query in parallel: they are independent z3 processes.
    const replies = await Promise.all(queries.map(([placeName, k]) =>
      Promise.all([spacer(oldPlan, placeName, k), spacer(lpPlan, placeName, k)])));
    let decided = 0;
    for (const [i, [placeName, k, expected]] of queries.entries()) {
      const answers = replies[i]!;
      expect(answers[1], `LP k: placeBound(${placeName}, ${k})`).toBe(expected);
      expect([expected, 'unknown'], `old k: placeBound(${placeName}, ${k}) ${answers}`).toContain(answers[0]);
      if (answers[0] === expected) decided++;
    }
    expect(decided, `the old k decided only ${decided} queries`).toBeGreaterThanOrEqual(3);
  }, 180_000);

  it('builds the coloured plan without enumerating a semiflow (VER-007 AC2)', async () => {
    // A draining loop whose semiflows fail the H1 gate sits beside the scatter-gather ν-net:
    // the enumeration would report them as `Dropped semiflow:` lines, as the union run shows.
    // With the option off the plan is built and no such line appears. The semiflow slot bound
    // that preceded the linear program enumerated them here and wrote those lines.
    const { net: nu } = scatterGather(false);
    const [loopBudget, queue, work, sink] = ['loopBudget', 'queue', 'work', 'sink'].map(n => place<number>(n)) as Place<number>[];
    const take = Transition.builder('take')
      .inputs(one(loopBudget!), all(queue!)).outputs(outPlace(work!)).action(produces()).build();
    const done = Transition.builder('done')
      .inputs(one(work!)).outputs(andPlaces(loopBudget!, sink!)).action(produces()).build();
    const net = PetriNet.builder('drain_beside_scatter_gather').transitions(...nu.transitions, take, done).build();
    const byName = new Map([...net.places].map(pl => [pl.name, pl] as const));
    const run = (union: boolean) => SmtVerifier.forNet(net)
      .enumerationMaxClasses(0)
      .linearBound(false)
      .initialMarking(m => m
        .tokens(byName.get('source')!, 3).tokens(byName.get('budget')!, 2)
        .tokens(loopBudget!, 1).tokens(queue!, 2))
      .property(placeBound(byName.get('merged')!, 3))
      .budgetPlaces(byName.get('budget')!)
      .semiflowInvariants(union)
      .timeout(30_000)
      .verify();
    const off = await run(false);
    expect(off.report).toContain('ν-encoding: name-coloured (colour-slot bound k=4;');
    expect(off.report).toContain('  Colour-slot bound: LP optimum 4 over 5 places and 2 transitions, so k=4');
    expect(off.report, 'the plan must not enumerate semiflows').not.toContain('Dropped semiflow:');
    const on = await run(true);
    expect(on.report, 'the net must have semiflows the gate drops').toContain('Dropped semiflow:');
    expect(on.report).toContain('ν-encoding: name-coloured (colour-slot bound k=4;');
  }, 60_000);

  it('polls the deadline before every pivot: a stop inside the solve is charged to its own step (VER-013)', async () => {
    // The signal reports itself aborted only when read from inside the simplex, so nothing
    // before the solve sees it, and the step's own entry poll does not either. Only the
    // per-pivot poll can turn it into the verdict.
    const signal = {
      get aborted() { return (new Error().stack ?? '').includes('solveSlotBoundCounted'); },
      addEventListener() {},
      removeEventListener() {},
    } as unknown as AbortSignal;
    const { net, initial } = scatterGather(false);
    const byName = new Map([...net.places].map(pl => [pl.name, pl] as const));
    const result = await SmtVerifier.forNet(net)
      .enumerationMaxClasses(0)
      .linearBound(false)
      .initialMarking(initial)
      .property(placeBound(byName.get('merged')!, 3))
      .budgetPlaces(byName.get('budget')!)
      .signal(signal)
      .timeout(30_000)
      .verify();
    expect(result.verdict, result.report).toEqual({ type: 'unknown', reason: 'verification cancelled during colour-slot bound' });
    // A stop writes no slot-bound line: the budget machinery reports it.
    expect(result.report).not.toContain('Colour-slot bound: ');
  }, 60_000);
});
