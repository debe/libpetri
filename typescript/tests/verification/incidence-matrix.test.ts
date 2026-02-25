import { describe, it, expect } from 'vitest';
import { IncidenceMatrix } from '../../src/verification/encoding/incidence-matrix.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';

describe('IncidenceMatrix', () => {
  it('simple net incidence matrix correct', () => {
    const pA = place('A');
    const pB = place('B');
    const t = Transition.builder('T')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const flatNet = flatten(net);
    const matrix = IncidenceMatrix.from(flatNet);

    expect(matrix.numTransitions()).toBe(1);
    expect(matrix.numPlaces()).toBe(2);

    const idxA = flatNet.placeIndex.get('A')!;
    const idxB = flatNet.placeIndex.get('B')!;

    // Pre: A consumed (1), B not consumed (0)
    expect(matrix.pre()[0]![idxA]).toBe(1);
    expect(matrix.pre()[0]![idxB]).toBe(0);

    // Post: A not produced (0), B produced (1)
    expect(matrix.post()[0]![idxA]).toBe(0);
    expect(matrix.post()[0]![idxB]).toBe(1);

    // Incidence: A = 0-1 = -1, B = 1-0 = +1
    expect(matrix.incidence()[0]![idxA]).toBe(-1);
    expect(matrix.incidence()[0]![idxB]).toBe(1);
  });

  it('transposed incidence dimensions correct', () => {
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

    const ct = matrix.transposedIncidence();
    // C^T should be P×T
    expect(ct.length).toBe(matrix.numPlaces());
    expect(ct[0]!.length).toBe(matrix.numTransitions());
  });

  it('circular net incidence sums to zero per place', () => {
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

    const ct = matrix.transposedIncidence();
    // For each place (row), sum of incidence across transitions should be 0
    for (let p = 0; p < matrix.numPlaces(); p++) {
      let sum = 0;
      for (let t = 0; t < matrix.numTransitions(); t++) {
        sum += ct[p]![t]!;
      }
      expect(sum).toBe(0);
    }
  });

  it('pipeline net incidence matrix', () => {
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

    expect(matrix.numTransitions()).toBe(2);
    expect(matrix.numPlaces()).toBe(3);
  });
});
