import { describe, it, expect } from 'vitest';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import {
  enabledA, fireA, injectA, successors, satisfiesBad, replayCounterexample,
  vectorize, toMarkingState, stepName,
} from '../../src/verification/z3/abstract-replayer.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import {
  deadlockFree, mutualExclusion, placeBound, terminatesAtSink, unreachable,
} from '../../src/verification/smt-property.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, environmentPlace } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one, all, atLeast } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { alwaysAvailable, bounded } from '../../src/verification/analysis/environment-analysis-mode.js';

// Pure abstract-semantics tests (Basic.lean enabledA/fireA mirror) — no Z3.

const NO_SINKS: ReadonlySet<Place<any>> = new Set();

/** Builds a state vector from {placeName: count} using the flat net's indexing. */
function state(flat: ReturnType<typeof flatten>, counts: Record<string, number>): number[] {
  const s = new Array<number>(flat.places.length).fill(0);
  for (const [name, count] of Object.entries(counts)) {
    const idx = flat.placeIndex.get(name);
    if (idx == null) throw new Error(`unknown place ${name}`);
    s[idx] = count;
  }
  return s;
}

describe('abstract-replayer: enabledA / fireA (Basic.lean mirror)', () => {
  it('consume-all (all): fireA empties the place regardless of count', () => {
    const p0 = place('P0');
    const p1 = place('P1');
    const t = Transition.builder('T').inputs(all(p0)).outputs(outPlace(p1)).build();
    const flat = flatten(PetriNet.builder('N').transitions(t).build());
    const ft = flat.transitions[0]!;

    expect(enabledA(state(flat, { P0: 2 }), ft)).toBe(true);
    expect(enabledA(state(flat, { P0: 0 }), ft)).toBe(false); // all() requires >= 1

    // fireA on M = (P0: 5): consume-all arm sets P0' = post[P0] = 0, P1' = P1 + 1.
    const next = fireA(state(flat, { P0: 5 }), ft);
    expect(next[flat.placeIndex.get('P0')!]).toBe(0);
    expect(next[flat.placeIndex.get('P1')!]).toBe(1);
  });

  it('consume-all (atLeast): pre gates on the minimum, fire drains everything', () => {
    const p0 = place('P0');
    const p1 = place('P1');
    const t = Transition.builder('T').inputs(atLeast(2, p0)).outputs(outPlace(p1)).build();
    const flat = flatten(PetriNet.builder('N').transitions(t).build());
    const ft = flat.transitions[0]!;

    expect(enabledA(state(flat, { P0: 1 }), ft)).toBe(false);
    expect(enabledA(state(flat, { P0: 2 }), ft)).toBe(true);
    const next = fireA(state(flat, { P0: 3 }), ft);
    expect(next[flat.placeIndex.get('P0')!]).toBe(0); // drained, not decremented by 2
    expect(next[flat.placeIndex.get('P1')!]).toBe(1);
  });

  it('reset: fireA sets the place to post[p] (0 unless produced into)', () => {
    const a = place('A');
    const b = place('B');
    const r = place('R');
    const t = Transition.builder('T').inputs(one(a)).outputs(outPlace(b)).reset(r).build();
    const flat = flatten(PetriNet.builder('N').transitions(t).build());
    const ft = flat.transitions[0]!;

    // Reset arcs do not gate enablement (CORE-034).
    expect(enabledA(state(flat, { A: 1, R: 7 }), ft)).toBe(true);
    const next = fireA(state(flat, { A: 1, R: 7 }), ft);
    expect(next[flat.placeIndex.get('R')!]).toBe(0);
    expect(next[flat.placeIndex.get('A')!]).toBe(0);
    expect(next[flat.placeIndex.get('B')!]).toBe(1);
  });

  it('inhibitor: blocks when the place is non-empty', () => {
    const a = place('A');
    const b = place('B');
    const blk = place('BLK');
    const t = Transition.builder('T').inputs(one(a)).outputs(outPlace(b)).inhibitor(blk).build();
    const flat = flatten(PetriNet.builder('N').transitions(t).build());
    const ft = flat.transitions[0]!;

    expect(enabledA(state(flat, { A: 1, BLK: 1 }), ft)).toBe(false);
    expect(enabledA(state(flat, { A: 1, BLK: 0 }), ft)).toBe(true);
  });

  it('read: requires a token but does not consume it', () => {
    const a = place('A');
    const b = place('B');
    const g = place('G');
    const t = Transition.builder('T').inputs(one(a)).outputs(outPlace(b)).read(g).build();
    const flat = flatten(PetriNet.builder('N').transitions(t).build());
    const ft = flat.transitions[0]!;

    expect(enabledA(state(flat, { A: 1, G: 0 }), ft)).toBe(false);
    expect(enabledA(state(flat, { A: 1, G: 1 }), ft)).toBe(true);
    const next = fireA(state(flat, { A: 1, G: 1 }), ft);
    expect(next[flat.placeIndex.get('G')!]).toBe(1); // untouched
  });

  it('injection: adds one token; successors gate on the bound (VER-006)', () => {
    const e = environmentPlace('E');
    const out = place('OUT');
    const t = Transition.builder('T').inputs(one(e.place)).outputs(outPlace(out)).build();
    const net = PetriNet.builder('N').transitions(t).build();

    const boundedFlat = flatten(net, new Set([e]), bounded(2));
    const idxE = boundedFlat.placeIndex.get('E')!;
    expect(injectA(state(boundedFlat, { E: 1 }), idxE)[idxE]).toBe(2);

    // Below the bound: injection successor present; at the bound: absent.
    const below = successors(state(boundedFlat, { E: 1 }), boundedFlat);
    expect(below.some(s => s.step.kind === 'inject' && s.step.place === 'E')).toBe(true);
    const atCap = successors(state(boundedFlat, { E: 2 }), boundedFlat);
    expect(atCap.some(s => s.step.kind === 'inject')).toBe(false);

    // AlwaysAvailable: never gated.
    const alwaysFlat = flatten(net, new Set([e]), alwaysAvailable());
    const many = successors(state(alwaysFlat, { E: 50 }), alwaysFlat);
    expect(many.some(s => s.step.kind === 'inject' && stepName(s.step) === 'inject(E)')).toBe(true);
  });
});

describe('abstract-replayer: environment post-caps (encodeStepRelation mirror)', () => {
  // bounded(1) on E. `A -> E` is enabled at {A:2, E:1} but its successor holds
  // E = 2, which the encoder's envBounds(M') conjunct forbids — and the only
  // other route to E = 2 is a second injection, which the M[E] < 1 guard
  // forbids. So E = 2 is unreachable in the encoded system and replay must not
  // chain through it.
  function cappedNet() {
    const e = environmentPlace('E');
    const a = place('A');
    const t = Transition.builder('AtoE').inputs(one(a)).outputs(outPlace(e.place)).build();
    const net = PetriNet.builder('Capped').transitions(t).build();
    return { e, a, flat: flatten(net, new Set([e]), bounded(1)) };
  }

  it('successors drops a firing whose M-prime breaches the environment cap', () => {
    const { flat } = cappedNet();
    const idxE = flat.placeIndex.get('E')!;

    // Under the cap: the firing is a genuine step.
    expect(successors(state(flat, { A: 2, E: 0 }), flat)
      .some(s => s.step.kind === 'fire' && s.step.transition === 'AtoE')).toBe(true);
    // At the cap: firing would make E = 2 > 1, and a second injection is gated.
    const atCap = successors(state(flat, { A: 2, E: 1 }), flat);
    expect(atCap.some(s => s.step.kind === 'fire')).toBe(false);
    expect(atCap.some(s => s.step.kind === 'inject')).toBe(false);
    for (const s of successors(state(flat, { A: 2, E: 0 }), flat)) {
      expect(s.state[idxE]!).toBeLessThanOrEqual(1);
    }
  });

  it('replay does not confirm a violation only reachable past the cap', () => {
    const { e, flat } = cappedNet();
    const m0 = state(flat, { A: 2 });
    const outcome = replayCounterexample(
      flat, m0, [m0], placeBound(e.place, 1), NO_SINKS,
    );
    expect(outcome.kind).toBe('no-chain');
  });
});

describe('abstract-replayer: satisfiesBad (encodePropertyViolation mirror)', () => {
  it('deadlock: relax-env treats injectable inputs as satisfiable', () => {
    const e = environmentPlace('E');
    const out = place('OUT');
    const t = Transition.builder('T').inputs(one(e.place)).outputs(outPlace(out)).build();
    const net = PetriNet.builder('N').transitions(t).build();

    // A token rests in the non-sink OUT so quiescence is observable under the strict
    // VER-002 predicate: only a STRANDED token is a DeadlockFree violation.
    // AlwaysAvailable: E=0 is NOT a deadlock — injection could re-enable T.
    const alwaysFlat = flatten(net, new Set([e]), alwaysAvailable());
    expect(satisfiesBad(state(alwaysFlat, { OUT: 1 }), alwaysFlat, deadlockFree(), NO_SINKS)).toBe(false);

    // Bounded(0): T can never be enabled by injection — genuine deadlock.
    const starvedFlat = flatten(net, new Set([e]), bounded(0));
    expect(satisfiesBad(state(starvedFlat, { OUT: 1 }), starvedFlat, deadlockFree(), NO_SINKS)).toBe(true);
  });

  it('deadlock: a token outside the declared sinks is stranded (VER-002 AC3)', () => {
    const a = place('A');
    const done = place('DONE');
    const stuck = place('STUCK');
    const t = Transition.builder('T').inputs(one(a)).outputs(outPlace(done)).build();
    const u = Transition.builder('U').inputs(one(a)).outputs(outPlace(stuck)).build();
    const flat = flatten(PetriNet.builder('N').transitions(t, u).build());

    // Only DONE marked and declared a sink: nothing is stranded.
    expect(satisfiesBad(state(flat, { DONE: 1 }), flat, deadlockFree(), new Set([done]))).toBe(false);
    // STUCK is marked and is not a sink: the marked sink does not excuse it (AC3).
    const mixed = state(flat, { DONE: 1, STUCK: 1 });
    expect(satisfiesBad(mixed, flat, deadlockFree(), new Set([done]))).toBe(true);
    // With no sinks declared every marked place strands.
    expect(satisfiesBad(state(flat, { DONE: 1 }), flat, deadlockFree(), NO_SINKS)).toBe(true);
  });

  it('deadlock and terminates-at-sink invert on the empty marking (VER-002 AC4/AC6)', () => {
    const a = place('A');
    const done = place('DONE');
    // A sink transition: firing it drains the net completely.
    const t = Transition.builder('T').inputs(one(a)).build();
    const flat = flatten(PetriNet.builder('N').places(done).transitions(t).build());

    const drained = state(flat, {});
    const sinks = new Set<Place<any>>([done]);
    // AC4: the empty quiescent marking strands nothing.
    expect(satisfiesBad(drained, flat, deadlockFree(), sinks)).toBe(false);
    // AC6: ... but it reached no declared sink.
    expect(satisfiesBad(drained, flat, terminatesAtSink(), sinks)).toBe(true);
    // AC5: a marked sink satisfies TerminatesAtSink whatever else is marked.
    expect(satisfiesBad(state(flat, { DONE: 1 }), flat, terminatesAtSink(), sinks)).toBe(false);
  });

  it('mutual-exclusion, place-bound, unreachable evaluate on raw counts', () => {
    const a = place('A');
    const b = place('B');
    const t = Transition.builder('T').inputs(one(a)).outputs(outPlace(b)).build();
    const flat = flatten(PetriNet.builder('N').transitions(t).build());

    expect(satisfiesBad(state(flat, { A: 1, B: 1 }), flat, mutualExclusion(a, b), NO_SINKS)).toBe(true);
    expect(satisfiesBad(state(flat, { A: 1 }), flat, mutualExclusion(a, b), NO_SINKS)).toBe(false);
    expect(satisfiesBad(state(flat, { B: 2 }), flat, placeBound(b, 1), NO_SINKS)).toBe(true);
    expect(satisfiesBad(state(flat, { B: 1 }), flat, placeBound(b, 1), NO_SINKS)).toBe(false);
    expect(satisfiesBad(state(flat, { A: 1, B: 1 }), flat, unreachable(new Set([a, b])), NO_SINKS)).toBe(true);
    expect(satisfiesBad(state(flat, { B: 1 }), flat, unreachable(new Set([a, b])), NO_SINKS)).toBe(false);
  });

  it('unreachable: a property whose places all fail to resolve is never violated', () => {
    const a = place('A');
    const b = place('B');
    const t = Transition.builder('T').inputs(one(a)).outputs(outPlace(b)).build();
    const flat = flatten(PetriNet.builder('N').transitions(t).build());
    // Neither place is in this net; with every place skipped the conjunction
    // would be vacuously true and EVERY marking would count as violating.
    const foreign = unreachable(new Set([place('X'), place('Y')]));

    expect(satisfiesBad(state(flat, {}), flat, foreign, NO_SINKS)).toBe(false);
    expect(satisfiesBad(state(flat, { A: 1 }), flat, foreign, NO_SINKS)).toBe(false);
    // One resolvable place still decides normally.
    const mixed = unreachable(new Set([b, place('X')]));
    expect(satisfiesBad(state(flat, { B: 1 }), flat, mixed, NO_SINKS)).toBe(true);
    expect(satisfiesBad(state(flat, { A: 1 }), flat, mixed, NO_SINKS)).toBe(false);
  });
});

describe('abstract-replayer: replayCounterexample', () => {
  /** A -> B -> C -> D -> E chain net with M0 = {A: 1}. */
  function chainNet(...names: string[]) {
    const places = names.map(n => place(n));
    const transitions = [];
    for (let i = 0; i + 1 < places.length; i++) {
      transitions.push(
        Transition.builder(`T${i}`).inputs(one(places[i]!)).outputs(outPlace(places[i + 1]!)).build(),
      );
    }
    const flat = flatten(PetriNet.builder('Chain').transitions(...transitions).build());
    return { places, flat };
  }

  it('confirms a chain and re-emits it in firing order', () => {
    const { places, flat } = chainNet('A', 'B', 'C');
    const m0 = state(flat, { A: 1 });
    // Decoded set deliberately shuffled — order-free by contract.
    const decoded = [state(flat, { C: 1 }), m0, state(flat, { B: 1 })];

    const outcome = replayCounterexample(flat, m0, decoded, placeBound(places[2]!, 0), NO_SINKS);
    expect(outcome.kind).toBe('confirmed');
    if (outcome.kind === 'confirmed') {
      expect(outcome.states.map(s => [...s].join(','))).toEqual([
        state(flat, { A: 1 }).join(','),
        state(flat, { B: 1 }).join(','),
        state(flat, { C: 1 }).join(','),
      ]);
      expect(outcome.steps.map(stepName)).toEqual(['T0', 'T1']);
    }
  });

  it('bridges up to 3 steps between decoded anchors', () => {
    // Only M0 and the state 3 steps later are decoded; the two intermediates
    // must be found by the bounded BFS.
    const { places, flat } = chainNet('A', 'B', 'C', 'D');
    const m0 = state(flat, { A: 1 });
    const outcome = replayCounterexample(
      flat, m0, [m0], placeBound(places[3]!, 0), NO_SINKS,
    );
    expect(outcome.kind).toBe('confirmed');
    if (outcome.kind === 'confirmed') {
      expect(outcome.steps.map(stepName)).toEqual(['T0', 'T1', 'T2']);
    }
  });

  it('exhausted: the bad state lies beyond the segment budget of every anchor', () => {
    // Bad state E is 4 steps from M0 and no intermediate waypoint was decoded,
    // so the segment budget (3) truncates the search — truncation is NOT
    // evidence that no chain exists, so this must not be `no-chain`.
    const { places, flat } = chainNet('A', 'B', 'C', 'D', 'E');
    const m0 = state(flat, { A: 1 });
    const outcome = replayCounterexample(flat, m0, [m0], placeBound(places[4]!, 0), NO_SINKS);
    expect(outcome.kind).toBe('exhausted');
    if (outcome.kind === 'exhausted') {
      expect(outcome.reason).toContain('within 3 abstract step(s) of a decoded state');
    }
  });

  it('confirms across a long chain once the intermediates are decoded anchors', () => {
    // Same net, but D is decoded too: the segment counter resets there, so the
    // search reaches E without raising the budget.
    const { places, flat } = chainNet('A', 'B', 'C', 'D', 'E');
    const m0 = state(flat, { A: 1 });
    const outcome = replayCounterexample(
      flat, m0, [m0, state(flat, { D: 1 })], placeBound(places[4]!, 0), NO_SINKS,
    );
    expect(outcome.kind).toBe('confirmed');
    if (outcome.kind === 'confirmed') {
      expect(outcome.steps.map(stepName)).toEqual(['T0', 'T1', 'T2', 'T3']);
    }
  });

  it('no-chain: a completed search that reaches no violating state', () => {
    // A -> B and nothing else; placeBound(B, 5) can never be violated, and the
    // whole reachable set is explored without hitting either budget.
    const { places, flat } = chainNet('A', 'B');
    const m0 = state(flat, { A: 1 });
    const outcome = replayCounterexample(flat, m0, [m0], placeBound(places[1]!, 5), NO_SINKS);
    expect(outcome.kind).toBe('no-chain');
  });

  it('exhausted: the initial marking must be among the decoded states', () => {
    const { places, flat } = chainNet('A', 'B', 'C');
    const m0 = state(flat, { A: 1 });
    const outcome = replayCounterexample(
      flat, m0, [state(flat, { B: 1 })], placeBound(places[2]!, 0), NO_SINKS,
    );
    expect(outcome.kind).toBe('exhausted');
    if (outcome.kind === 'exhausted') {
      expect(outcome.reason).toContain('initial marking is not among the decoded states');
    }
  });

  it('exhausted: the node budget caps the search', () => {
    const { places, flat } = chainNet('A', 'B', 'C');
    const m0 = state(flat, { A: 1 });
    const outcome = replayCounterexample(
      flat, m0, [m0, state(flat, { B: 1 }), state(flat, { C: 1 })],
      placeBound(places[2]!, 0), NO_SINKS, { nodeBudget: 1 },
    );
    expect(outcome.kind).toBe('exhausted');
    if (outcome.kind === 'exhausted') {
      expect(outcome.reason).toContain('budget exhausted');
    }
  });

  it('an initial marking that already violates confirms with an empty chain', () => {
    const { places, flat } = chainNet('A', 'B');
    const m0 = state(flat, { A: 1 });
    const outcome = replayCounterexample(flat, m0, [m0], placeBound(places[0]!, 0), NO_SINKS);
    expect(outcome.kind).toBe('confirmed');
    if (outcome.kind === 'confirmed') {
      expect(outcome.states).toHaveLength(1);
      expect(outcome.steps).toHaveLength(0);
    }
  });

  it('vectorize/toMarkingState round-trip on the flat indexing', () => {
    const { flat } = chainNet('A', 'B', 'C');
    const marking = MarkingState.builder()
      .tokens(place('A'), 2)
      .tokens(place('C'), 1)
      .build();
    const vec = vectorize(marking, flat);
    const back = toMarkingState(vec, flat);
    expect(back.toString()).toBe(marking.toString());
  });
});
