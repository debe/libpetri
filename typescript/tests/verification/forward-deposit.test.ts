import { describe, expect, it } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { placeBound } from '../../src/verification/smt-property.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { all, atLeast, exactly, one, type In } from '../../src/core/in.js';
import { and, forwardInput, outPlace, timeout, xor } from '../../src/core/out.js';
import { drainedForward, outcomes, type Outcome } from '../../src/verification/analysis/branch-outcomes.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { StateClassGraph } from '../../src/verification/analysis/state-class-graph.js';
import { fork } from '../../src/core/transition-action.js';
import { describeZ3 } from '../fixtures/z3.js';

/**
 * [IO-014]: a timeout `ForwardInput(from, to)` deposits one token in `to` per token the firing
 * consumed from `from`. The analyses deposited one per forward, so on
 * `t: exactly(2, a) -> xor(c, timeout(50, forwardInput(a, b)))` from `a = 2` every route
 * proved `placeBound(b, 1)` while the executor ends at `b = 2`.
 */

const a = place<number>('a');
const b = place<number>('b');
const c = place<number>('c');

function forwardNet(input: In): PetriNet {
  const t = Transition.builder('t')
    .inputs(input)
    .outputs(xor(outPlace(c), timeout(50, forwardInput(a, b))))
    .action(fork())
    .build();
  return PetriNet.builder('forward').transition(t).build();
}

const m0 = () => MarkingState.builder().tokens(a, 2).build();

const deposits = (o: Outcome) => o.deposits.map(d => [
  d.place.name,
  d.deposit.type === 'tokens' ? d.deposit.count : `drained(${d.deposit.from.name})`,
]);

describe('branch outcomes (IO-013, IO-014, IO-016)', () => {
  it('an exactly(2) forward deposits two', () => {
    const got = outcomes([...forwardNet(exactly(2, a)).transitions][0]!);
    expect(got.map(deposits)).toEqual([
      [['c', 1]],
      // The action may write the forward's target itself: one token ([IO-016]).
      [['b', 1]],
      // The timeout forwards both consumed tokens ([IO-014]).
      [['b', 2]],
    ]);
  });

  it('a one forward adds no outcome', () => {
    expect(outcomes([...forwardNet(one(a)).transitions][0]!)).toHaveLength(2);
  });

  it('a timeout does not write its siblings (IO-013 AC5)', () => {
    const t = Transition.builder('t').inputs(one(a)).outputs(and(outPlace(c), timeout(50, outPlace(b))))
      .action(fork()).build();
    expect(outcomes(t).map(deposits)).toEqual([[['b', 1], ['c', 1]], [['b', 1]]]);
  });

  it.each([
    ['all', () => all(a)],
    ['atLeast', () => atLeast(2, a)],
  ] as const)('a drained forward is marking-dependent and found (%s)', (_name, input) => {
    const net = forwardNet(input());
    expect(deposits(outcomes([...net.transitions][0]!)[2]!)).toEqual([['b', 'drained(a)']]);
    expect(drainedForward(net)).toEqual({ transition: 't', from: 'a', to: 'b' });
  });

  it('no output spec is one empty outcome', () => {
    const t = Transition.builder('t').inputs(one(a)).build();
    expect(outcomes(t).map(deposits)).toEqual([[]]);
  });
});

describe('the flattener deposits every consumed token (IO-014)', () => {
  it('flatten forward deposits every consumed token', () => {
    const flat = flatten(forwardNet(exactly(2, a)));
    expect(flat.transitions.map(t => t.name)).toEqual(['t_b0', 't_b1', 't_b2']);
    const [ia, ib, ic] = ['a', 'b', 'c'].map(n => flat.placeIndex.get(n)!);
    expect(flat.transitions.every(t => t.preVector[ia!] === 2)).toBe(true);
    expect(flat.transitions.map(t => [t.postVector[ib!], t.postVector[ic!]])).toEqual([[0, 1], [1, 0], [2, 0]]);
  });
});

describe('the state-class graph deposits every consumed token (IO-014)', () => {
  const bCounts = (graph: StateClassGraph) =>
    [...new Set(graph.stateClasses().map(sc => sc.marking.tokens(b)))].sort((x, y) => x - y);

  it('an exactly(2) forward deposits two in the state space', () => {
    const graph = StateClassGraph.build(forwardNet(exactly(2, a)), m0(), 100);
    expect(graph.isComplete()).toBe(true);
    expect(bCounts(graph)).toEqual([0, 1, 2]);
  });

  it('an all forward deposits the drained batch in the state space', () => {
    const graph = StateClassGraph.build(forwardNet(all(a)), m0(), 100);
    expect(graph.isComplete()).toBe(true);
    expect(bCounts(graph)).toEqual([0, 1, 2]);
  });
});

describeZ3('a timeout forward deposits every consumed token (IO-014)', () => {
  // (budget, linear bound, VER-018/VER-019 phases): the last SMT arm leaves the CHC/IC3
  // fixpoint alone to decide.
  it.each([
    [0, true, true, 'smt'],
    [0, false, true, 'smt'],
    [0, false, false, 'smt'],
    [50_000, true, true, 'enumeration'],
  ] as const)(
    'a forward of two consumed tokens violates a bound of one (budget %i, linear bound %s, phases %s)',
    async (budget, linearBound, phases, route) => {
      const result = await SmtVerifier.forNet(forwardNet(exactly(2, a)))
        .initialMarking(m0())
        .property(placeBound(b, 1))
        .enumerationMaxClasses(budget)
        .linearBound(linearBound)
        .stateEquationPhase(phases)
        .firingBound(phases)
        .verify();
      expect(result.verdict.type, result.report).toBe('violated');
      expect(result.route, result.report).toBe(route);
      expect(result.counterexampleTransitions, result.report).toHaveLength(1);
      const last = result.counterexampleTrace[result.counterexampleTrace.length - 1]!;
      expect([last.tokens(a), last.tokens(b)], result.report).toEqual([0, 2]);
    },
    30_000,
  );
});

describe('a forward of a drained input (IO-014)', () => {
  // The deposit of a drained batch is marking-dependent: no flat encoding can hold it, so the
  // linear routes refuse the net ([VER-003] AC5), while the enumeration ([VER-017]) counts the
  // drained batch exactly as the executor does and decides it: `b` reaches 2, never 3.
  const verify = (input: In, bound: number, budget: number) =>
    SmtVerifier.forNet(forwardNet(input))
      .initialMarking(m0())
      .property(placeBound(b, bound))
      .enumerationMaxClasses(budget)
      .verify();

  it.each([
    ['all', () => all(a)],
    ['atLeast', () => atLeast(1, a)],
  ] as const)('is refused by the linear routes and decided by the graph (%s)', async (_name, input) => {
    // Enumeration off: only the linear routes are left, and each refuses.
    const refused = await verify(input(), 1, 0);
    expect(refused.verdict.type, refused.report).toBe('unknown');
    if (refused.verdict.type === 'unknown') {
      expect(refused.verdict.reason).toContain("forwards its All/AtLeast input 'a' to 'b'");
      expect(refused.verdict.reason).toContain('refusing to certify on the linear routes');
    }
    expect(refused.route).toBe('unavailable');

    // The enumeration decides both directions.
    const violated = await verify(input(), 1, 50_000);
    expect(violated.verdict.type, violated.report).toBe('violated');
    expect(violated.route).toBe('enumeration');
    expect(violated.counterexampleTransitions, violated.report).toHaveLength(1);
    const last = violated.counterexampleTrace[violated.counterexampleTrace.length - 1]!;
    expect([last.tokens(a), last.tokens(b)], violated.report).toEqual([0, 2]);

    const proven = await verify(input(), 2, 50_000);
    expect(proven.verdict.type, proven.report).toBe('proven');
    expect(proven.route).toBe('enumeration');
  }, 30_000);
});
