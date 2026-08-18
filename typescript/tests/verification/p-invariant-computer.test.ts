import { describe, it, expect } from 'vitest';
import { computePInvariants, computePSemiflows, isCoveredByInvariants, validateInvariantsExact } from '../../src/verification/invariant/p-invariant-computer.js';
import { pInvariant } from '../../src/verification/invariant/p-invariant.js';
import { IncidenceMatrix } from '../../src/verification/encoding/incidence-matrix.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { all, atLeast, exactly, one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';

describe('PInvariantComputer', () => {
  it('circular net finds conservation invariant', () => {
    const pA = place('A');
    const pB = place('B');
    const t1 = Transition.builder('T1')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const t2 = Transition.builder('T2')
      .inputs(one(pB))
      .outputs(outPlace(pA))
      .build();
    const net = PetriNet.builder('N').transitions(t1, t2).build();
    const flatNet = flatten(net);
    const matrix = IncidenceMatrix.from(flatNet);

    const initialMarking = MarkingState.builder()
      .tokens(pA, 1)
      .build();

    const invariants = computePInvariants(matrix, flatNet, initialMarking);

    expect(invariants.length).toBeGreaterThan(0);

    // Should find: A + B = 1
    const inv = invariants[0]!;
    expect(inv.constant).toBe(1);

    // Both places should be in support
    expect(inv.support.size).toBe(2);

    // Weights should be equal (both 1)
    const idxA = flatNet.placeIndex.get('A')!;
    const idxB = flatNet.placeIndex.get('B')!;
    expect(inv.weights[idxA]).toBe(inv.weights[idxB]);
  });

  it('pipeline net finds invariant', () => {
    const pA = place('A');
    const pB = place('B');
    const pC = place('C');
    const t1 = Transition.builder('T1')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const t2 = Transition.builder('T2')
      .inputs(one(pB))
      .outputs(outPlace(pC))
      .build();
    const net = PetriNet.builder('N').transitions(t1, t2).build();
    const flatNet = flatten(net);
    const matrix = IncidenceMatrix.from(flatNet);

    const initialMarking = MarkingState.builder()
      .tokens(pA, 2)
      .build();

    const invariants = computePInvariants(matrix, flatNet, initialMarking);

    // For a pipeline A→B→C with initial A=2:
    // invariant: A + B + C = 2
    expect(invariants.length).toBeGreaterThan(0);
    const inv = invariants[0]!;
    expect(inv.constant).toBe(2);
    expect(inv.support.size).toBe(3);
  });

  it('isCoveredByInvariants true for conserving net', () => {
    const pA = place('A');
    const pB = place('B');
    const t1 = Transition.builder('T1')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const t2 = Transition.builder('T2')
      .inputs(one(pB))
      .outputs(outPlace(pA))
      .build();
    const net = PetriNet.builder('N').transitions(t1, t2).build();
    const flatNet = flatten(net);
    const matrix = IncidenceMatrix.from(flatNet);

    const initialMarking = MarkingState.builder()
      .tokens(pA, 1)
      .build();

    const invariants = computePInvariants(matrix, flatNet, initialMarking);
    expect(isCoveredByInvariants(invariants, flatNet.places.length)).toBe(true);
  });

  it('empty net returns no invariants', () => {
    const net = PetriNet.builder('Empty').build();
    const flatNet = flatten(net);
    const matrix = IncidenceMatrix.from(flatNet);
    const initialMarking = MarkingState.empty();

    const invariants = computePInvariants(matrix, flatNet, initialMarking);
    expect(invariants).toHaveLength(0);
  });

  it('isCoveredByInvariants false when a place is uncovered', () => {
    // Net with a source transition (produces to B but doesn't consume from B)
    // A → B → C, but add B → D (no transition consumes D)
    // D is a "sink" place with no further transitions
    // This should NOT be fully covered by invariants
    const pA = place('A');
    const pB = place('B');
    const pD = place('D');
    const t1 = Transition.builder('T1')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const t2 = Transition.builder('T2')
      .inputs(one(pB))
      .outputs(outPlace(pD))
      .build();
    // Note: D is a sink — no transition consumes from it
    const net = PetriNet.builder('N').transitions(t1, t2).build();
    const flatNet = flatten(net);
    const matrix = IncidenceMatrix.from(flatNet);
    const initialMarking = MarkingState.builder().tokens(pA, 1).build();

    const invariants = computePInvariants(matrix, flatNet, initialMarking);
    // In a pipeline, all places are covered by the conservation invariant A+B+D=1
    // because every token taken from A eventually ends up in D
    expect(isCoveredByInvariants(invariants, flatNet.places.length)).toBe(true);
  });
});

describe('validateInvariantsExact', () => {
  function circularFixture() {
    const pA = place('A');
    const pB = place('B');
    const t1 = Transition.builder('T1')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const t2 = Transition.builder('T2')
      .inputs(one(pB))
      .outputs(outPlace(pA))
      .build();
    const net = PetriNet.builder('N').transitions(t1, t2).build();
    const flatNet = flatten(net);
    const matrix = IncidenceMatrix.from(flatNet);
    const initialMarking = MarkingState.builder().tokens(pA, 1).build();
    return { flatNet, matrix, initialMarking };
  }

  it('valid invariants pass through unchanged', () => {
    const { flatNet, matrix, initialMarking } = circularFixture();
    const invariants = computePInvariants(matrix, flatNet, initialMarking);
    expect(invariants.length).toBeGreaterThan(0);

    const { valid, dropped } = validateInvariantsExact(matrix, invariants, flatNet, initialMarking);

    expect(dropped).toHaveLength(0);
    expect(valid).toEqual(invariants);
    // Pass-through, not a rewrite: the exact same invariant objects come back.
    expect(valid[0]).toBe(invariants[0]);
  });

  it('drops a fabricated invariant with a nonzero y·C component, with a reason', () => {
    const { flatNet, matrix, initialMarking } = circularFixture();
    const idxA = flatNet.placeIndex.get('A')!;
    const idxB = flatNet.placeIndex.get('B')!;
    // A + 2B is NOT a conservation law of A⇄B: firing T1 changes the sum by +1.
    const weights = new Array<number>(flatNet.places.length).fill(0);
    weights[idxA] = 1;
    weights[idxB] = 2;
    const bogus = pInvariant(weights, 1, new Set([idxA, idxB]));

    const { valid, dropped } = validateInvariantsExact(matrix, [bogus], flatNet, initialMarking);

    expect(valid).toHaveLength(0);
    expect(dropped).toHaveLength(1);
    expect(dropped[0]!.invariant).toBe(bogus);
    expect(dropped[0]!.reason).toContain('y·C');
  });

  it('drops an invariant with a weight outside the safe-integer range', () => {
    const { flatNet, matrix, initialMarking } = circularFixture();
    const idxA = flatNet.placeIndex.get('A')!;
    const idxB = flatNet.placeIndex.get('B')!;
    // 2^53 is the first integer `number` can no longer represent adjacently.
    const weights = new Array<number>(flatNet.places.length).fill(0);
    weights[idxA] = 2 ** 53;
    weights[idxB] = 2 ** 53;
    const bogus = pInvariant(weights, 2 ** 53, new Set([idxA, idxB]));

    const { valid, dropped } = validateInvariantsExact(matrix, [bogus], flatNet, initialMarking);

    expect(valid).toHaveLength(0);
    expect(dropped).toHaveLength(1);
    expect(dropped[0]!.reason).toContain('safe-integer');
  });

  it('drops an invariant whose constant disagrees with the exact y·M0', () => {
    const { flatNet, matrix, initialMarking } = circularFixture();
    const invariants = computePInvariants(matrix, flatNet, initialMarking);
    const good = invariants[0]!;
    const bogus = pInvariant([...good.weights], good.constant + 1, new Set(good.support));

    const { valid, dropped } = validateInvariantsExact(matrix, [bogus], flatNet, initialMarking);

    expect(valid).toHaveLength(0);
    expect(dropped).toHaveLength(1);
    expect(dropped[0]!.reason).toContain('y·M0');
  });

  it('skips the constant re-check when net and marking are not supplied', () => {
    const { flatNet, matrix, initialMarking } = circularFixture();
    const invariants = computePInvariants(matrix, flatNet, initialMarking);
    const good = invariants[0]!;
    const staleConstant = pInvariant([...good.weights], good.constant + 1, new Set(good.support));

    // Without M0 the constant cannot be re-derived; y·C and safe-integer checks still run.
    const withoutMarking = validateInvariantsExact(matrix, [staleConstant]);
    expect(withoutMarking.dropped).toHaveLength(0);
    expect(withoutMarking.valid).toHaveLength(1);
  });

  it('keeps the good and drops the bad in a mixed batch', () => {
    const { flatNet, matrix, initialMarking } = circularFixture();
    const invariants = computePInvariants(matrix, flatNet, initialMarking);
    const good = invariants[0]!;
    const idxA = flatNet.placeIndex.get('A')!;
    const badWeights = new Array<number>(flatNet.places.length).fill(0);
    badWeights[idxA] = 1; // A alone is not conserved by A⇄B
    const bogus = pInvariant(badWeights, 1, new Set([idxA]));

    const { valid, dropped } = validateInvariantsExact(matrix, [good, bogus], flatNet, initialMarking);

    expect(valid).toEqual([good]);
    expect(dropped).toHaveLength(1);
    expect(dropped[0]!.invariant).toBe(bogus);
  });
});

describe('validateInvariantsExact H1 linearity guard', () => {
  // The H1 witness from Strengthening.lean (consume_all_hypothesis_is_necessary):
  // T: all(P0) -> P1 with M0 = (2, 0). The linearized column is (-1, +1), so the
  // Farkas elimination finds y = (1, 1) with constant 2 and the y·C = 0 gate alone
  // would accept it — but the real firing drains BOTH tokens (y·M drops 2 -> 1),
  // so the invariant is false on the net and the guard must drop it.
  function witnessFixture() {
    const p0 = place('P0');
    const p1 = place('P1');
    const t = Transition.builder('T')
      .inputs(all(p0))
      .outputs(outPlace(p1))
      .build();
    const net = PetriNet.builder('H1Witness').transitions(t).build();
    const flatNet = flatten(net);
    const matrix = IncidenceMatrix.from(flatNet);
    const initialMarking = MarkingState.builder().tokens(p0, 2).build();
    return { flatNet, matrix, initialMarking };
  }

  it('drops the Lean witness invariant on the consume-all place', () => {
    const { flatNet, matrix, initialMarking } = witnessFixture();
    const invariants = computePInvariants(matrix, flatNet, initialMarking);
    expect(invariants.length).toBeGreaterThan(0); // Farkas finds y = (1, 1)

    const { valid, dropped } = validateInvariantsExact(matrix, invariants, flatNet, initialMarking);

    expect(valid).toHaveLength(0);
    expect(dropped.length).toBeGreaterThan(0);
    expect(dropped[0]!.reason).toContain('non-linear consumption');
    expect(dropped[0]!.reason).toContain('Strengthening.lean H1');
    expect(dropped[0]!.reason).toContain("'P0'");
  });

  it('drops the witness semiflow through the same validator (bound-path symmetry)', () => {
    const { flatNet, matrix, initialMarking } = witnessFixture();
    const semiflows = computePSemiflows(matrix, flatNet, initialMarking);
    expect(semiflows.length).toBeGreaterThan(0);

    const { valid, dropped } = validateInvariantsExact(matrix, semiflows, flatNet, initialMarking);

    expect(valid).toHaveLength(0);
    expect(dropped[0]!.reason).toContain('Strengthening.lean H1');
  });

  it('drops an invariant weighting a reset place', () => {
    // Reset analogue: reset places never enter pre/post at all, so the column is
    // again (-1, +1) and Farkas finds y = (1, 1) — false because firing clears P0.
    const p0 = place('P0');
    const p1 = place('P1');
    const t = Transition.builder('T')
      .inputs(one(p0))
      .reset(p0)
      .outputs(outPlace(p1))
      .build();
    const net = PetriNet.builder('H1Reset').transitions(t).build();
    const flatNet = flatten(net);
    expect(flatNet.transitions[0]!.resetPlaces).toContain(flatNet.placeIndex.get('P0')!);
    const matrix = IncidenceMatrix.from(flatNet);
    const initialMarking = MarkingState.builder().tokens(p0, 2).build();

    const invariants = computePInvariants(matrix, flatNet, initialMarking);
    expect(invariants.length).toBeGreaterThan(0);

    const { valid, dropped } = validateInvariantsExact(matrix, invariants, flatNet, initialMarking);

    expect(valid).toHaveLength(0);
    expect(dropped[0]!.reason).toContain("consume-all/reset place 'P0'");
    expect(dropped[0]!.reason).toContain('Strengthening.lean H1');
  });

  it('drops an invariant weighting an at-least place (at-least consumes ALL, not n)', () => {
    // atLeast(n) is NOT linear in this codebase: it waits for n tokens but then
    // consumes all available (consumptionCount in core/in.ts returns `available`),
    // which is why the flattener flags it in consumeAll alongside `all` and why
    // Lean's Card.consumesAll models both. With atLeast(1) === all, keeping such
    // invariants would reopen the witness's false PROVEN.
    const p0 = place('P0');
    const p1 = place('P1');
    const t = Transition.builder('T')
      .inputs(atLeast(2, p0))
      .outputs(outPlace(p1))
      .build();
    const net = PetriNet.builder('H1AtLeast').transitions(t).build();
    const flatNet = flatten(net);
    expect(flatNet.transitions[0]!.consumeAll[flatNet.placeIndex.get('P0')!]).toBe(true);
    const matrix = IncidenceMatrix.from(flatNet);
    const initialMarking = MarkingState.builder().tokens(p0, 2).build();

    const invariants = computePInvariants(matrix, flatNet, initialMarking);
    expect(invariants.length).toBeGreaterThan(0);

    const { valid, dropped } = validateInvariantsExact(matrix, invariants, flatNet, initialMarking);

    expect(valid).toHaveLength(0);
    expect(dropped[0]!.reason).toContain("consume-all/reset place 'P0'");
  });

  it('keeps an invariant over an exactly(n) input (genuinely linear)', () => {
    // exactly(n) consumes exactly n tokens, so the linearized column is truthful
    // and the y = (1, 2) law of T: exactly(2, P0) -> P1 is a real invariant.
    const p0 = place('P0');
    const p1 = place('P1');
    const t = Transition.builder('T')
      .inputs(exactly(2, p0))
      .outputs(outPlace(p1))
      .build();
    const net = PetriNet.builder('H1Exactly').transitions(t).build();
    const flatNet = flatten(net);
    expect(flatNet.transitions[0]!.consumeAll.every((f) => !f)).toBe(true);
    const matrix = IncidenceMatrix.from(flatNet);
    const initialMarking = MarkingState.builder().tokens(p0, 2).build();

    const invariants = computePInvariants(matrix, flatNet, initialMarking);
    expect(invariants.length).toBeGreaterThan(0);

    const { valid, dropped } = validateInvariantsExact(matrix, invariants, flatNet, initialMarking);

    expect(dropped).toHaveLength(0);
    expect(valid).toEqual(invariants);
  });

  it('is support-local: the linear component survives while the drained one drops', () => {
    const pA = place('A');
    const pB = place('B');
    const pX = place('X');
    const pY = place('Y');
    const t1 = Transition.builder('T1')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const t2 = Transition.builder('T2')
      .inputs(one(pB))
      .outputs(outPlace(pA))
      .build();
    const tAll = Transition.builder('TAll')
      .inputs(all(pX))
      .outputs(outPlace(pY))
      .build();
    const net = PetriNet.builder('H1Mixed').transitions(t1, t2, tAll).build();
    const flatNet = flatten(net);
    const matrix = IncidenceMatrix.from(flatNet);
    const initialMarking = MarkingState.builder().tokens(pA, 3).tokens(pX, 2).build();

    const invariants = computePInvariants(matrix, flatNet, initialMarking);
    const { valid, dropped } = validateInvariantsExact(matrix, invariants, flatNet, initialMarking);

    const idxA = flatNet.placeIndex.get('A')!;
    const idxX = flatNet.placeIndex.get('X')!;
    expect(valid.some((inv) => inv.weights[idxA] !== 0)).toBe(true);
    expect(valid.every((inv) => inv.weights[idxX] === 0)).toBe(true);
    expect(dropped.some(({ reason }) => reason.includes("'X'"))).toBe(true);
  });
});
