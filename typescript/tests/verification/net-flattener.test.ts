import { describe, it, expect } from 'vitest';
import { flatten, bounded } from '../../src/verification/encoding/net-flattener.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, environmentPlace } from '../../src/core/place.js';
import { one, exactly, all, atLeast } from '../../src/core/in.js';
import { outOne, outExactly, and, xor, andPlaces, xorPlaces } from '../../src/core/out.js';

describe('NetFlattener', () => {
  it('assigns stable place indices sorted by name', () => {
    const pC = place('C');
    const pA = place('A');
    const pB = place('B');
    const t = Transition.builder('T')
      .inputs(one(pC), one(pA))
      .outputs(outOne(pB))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const flatNet = flatten(net);

    // Places should be sorted by name: A, B, C
    expect(flatNet.places[0]!.name).toBe('A');
    expect(flatNet.places[1]!.name).toBe('B');
    expect(flatNet.places[2]!.name).toBe('C');

    // Reverse lookup consistent
    for (let i = 0; i < flatNet.places.length; i++) {
      expect(flatNet.placeIndex.get(flatNet.places[i]!.name)).toBe(i);
    }
  });

  it('flattenTransition pre-vector correct for one()', () => {
    const input = place('IN');
    const output = place('OUT');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outOne(output))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const flatNet = flatten(net);

    expect(flatNet.transitions).toHaveLength(1);
    const ft = flatNet.transitions[0]!;
    const inIdx = flatNet.placeIndex.get('IN')!;
    const outIdx = flatNet.placeIndex.get('OUT')!;

    expect(ft.preVector[inIdx]).toBe(1);
    expect(ft.postVector[outIdx]).toBe(1);
    expect(ft.preVector[outIdx]).toBe(0);
    expect(ft.postVector[inIdx]).toBe(0);
  });

  it('flattenTransition pre-vector correct for exactly()', () => {
    const input = place('IN');
    const output = place('OUT');
    const t = Transition.builder('T')
      .inputs(exactly(3, input))
      .outputs(outOne(output))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const flatNet = flatten(net);
    const ft = flatNet.transitions[0]!;
    const inIdx = flatNet.placeIndex.get('IN')!;
    expect(ft.preVector[inIdx]).toBe(3);
  });

  it('flattenTransition consumeAll flag for all()', () => {
    const input = place('IN');
    const output = place('OUT');
    const t = Transition.builder('T')
      .inputs(all(input))
      .outputs(outOne(output))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const flatNet = flatten(net);
    const ft = flatNet.transitions[0]!;
    const inIdx = flatNet.placeIndex.get('IN')!;
    expect(ft.preVector[inIdx]).toBe(1);
    expect(ft.consumeAll[inIdx]).toBe(true);
  });

  it('flattenTransition consumeAll flag for atLeast()', () => {
    const input = place('IN');
    const output = place('OUT');
    const t = Transition.builder('T')
      .inputs(atLeast(3, input))
      .outputs(outOne(output))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const flatNet = flatten(net);
    const ft = flatNet.transitions[0]!;
    const inIdx = flatNet.placeIndex.get('IN')!;
    expect(ft.preVector[inIdx]).toBe(3);
    expect(ft.consumeAll[inIdx]).toBe(true);
  });

  it('flattenTransition records inhibitor and read arcs', () => {
    const input = place('IN');
    const output = place('OUT');
    const inh = place('INH');
    const rd = place('RD');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outOne(output))
      .inhibitor(inh)
      .read(rd)
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const flatNet = flatten(net);
    const ft = flatNet.transitions[0]!;

    expect(ft.inhibitorPlaces).toContain(flatNet.placeIndex.get('INH'));
    expect(ft.readPlaces).toContain(flatNet.placeIndex.get('RD'));
  });

  it('flattenTransition records reset arcs', () => {
    const input = place('IN');
    const output = place('OUT');
    const rst = place('RST');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outOne(output))
      .reset(rst)
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const flatNet = flatten(net);
    const ft = flatNet.transitions[0]!;
    expect(ft.resetPlaces).toContain(flatNet.placeIndex.get('RST'));
  });

  it('XOR outputs expand to separate flat transitions', () => {
    const input = place('IN');
    const outA = place('A');
    const outB = place('B');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(xorPlaces(outA, outB))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const flatNet = flatten(net);

    expect(flatNet.transitions).toHaveLength(2);
    expect(flatNet.transitions[0]!.name).toBe('T_b0');
    expect(flatNet.transitions[1]!.name).toBe('T_b1');
    expect(flatNet.transitions[0]!.branchIndex).toBe(0);
    expect(flatNet.transitions[1]!.branchIndex).toBe(1);

    // Each branch should produce to exactly one output
    const idxA = flatNet.placeIndex.get('A')!;
    const idxB = flatNet.placeIndex.get('B')!;
    expect(flatNet.transitions[0]!.postVector[idxA]).toBe(1);
    expect(flatNet.transitions[0]!.postVector[idxB]).toBe(0);
    expect(flatNet.transitions[1]!.postVector[idxA]).toBe(0);
    expect(flatNet.transitions[1]!.postVector[idxB]).toBe(1);
  });

  it('non-XOR transition maps 1:1', () => {
    const input = place('IN');
    const output = place('OUT');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outOne(output))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const flatNet = flatten(net);

    expect(flatNet.transitions).toHaveLength(1);
    expect(flatNet.transitions[0]!.name).toBe('T');
    expect(flatNet.transitions[0]!.branchIndex).toBe(-1);
  });

  it('AND outputs produce to all places', () => {
    const input = place('IN');
    const outA = place('A');
    const outB = place('B');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(andPlaces(outA, outB))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const flatNet = flatten(net);

    expect(flatNet.transitions).toHaveLength(1);
    const ft = flatNet.transitions[0]!;
    expect(ft.postVector[flatNet.placeIndex.get('A')!]).toBe(1);
    expect(ft.postVector[flatNet.placeIndex.get('B')!]).toBe(1);
  });

  it('sink transition with no outputs has empty post-vector', () => {
    const input = place('IN');
    const t = Transition.builder('T')
      .inputs(one(input))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const flatNet = flatten(net);

    expect(flatNet.transitions).toHaveLength(1);
    const ft = flatNet.transitions[0]!;
    expect(ft.postVector.every(v => v === 0)).toBe(true);
  });

  it('environment bounds applied in bounded mode', () => {
    const envP = environmentPlace<string>('ENV');
    const input = envP.place;
    const output = place('OUT');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outOne(output))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const flatNet = flatten(net, new Set([envP]), bounded(3));

    expect(flatNet.environmentBounds.get('ENV')).toBe(3);
  });

  it('multiple transitions flatten correctly', () => {
    const p1 = place('P1');
    const p2 = place('P2');
    const p3 = place('P3');

    const t1 = Transition.builder('T1')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .build();
    const t2 = Transition.builder('T2')
      .inputs(one(p2))
      .outputs(outOne(p3))
      .build();

    const net = PetriNet.builder('Pipeline').transitions(t1, t2).build();
    const flatNet = flatten(net);

    expect(flatNet.places).toHaveLength(3);
    expect(flatNet.transitions).toHaveLength(2);
  });

  // ==================== Multiplicity (IO-018, IO-019) ====================

  it('Out.and(P, P, P) post-vector reflects count 3', () => {
    const input = place('Input');
    const output = place('Output');
    const t = Transition.builder('Triple')
      .inputs(one(input))
      .outputs(andPlaces(output, output, output))
      .build();
    const net = PetriNet.builder('RepeatedAndNet').transition(t).build();
    const flatNet = flatten(net);

    expect(flatNet.transitions).toHaveLength(1);
    const ft = flatNet.transitions[0]!;
    const outIdx = flatNet.placeIndex.get(output.name)!;
    expect(ft.postVector[outIdx]).toBe(3);
  });

  it('Out.exactly(5, P) post-vector equals count', () => {
    const input = place('Input');
    const output = place('Output');
    const t = Transition.builder('Five')
      .inputs(one(input))
      .outputs(outExactly(5, output))
      .build();
    const net = PetriNet.builder('ExactlyNet').transition(t).build();
    const flatNet = flatten(net);

    const ft = flatNet.transitions[0]!;
    const outIdx = flatNet.placeIndex.get(output.name)!;
    expect(ft.postVector[outIdx]).toBe(5);
  });

  it('AND of two exactly accumulates counts', () => {
    const input = place('Input');
    const output = place('Output');
    const t = Transition.builder('Sum')
      .inputs(one(input))
      .outputs(and(outExactly(2, output), outExactly(3, output)))
      .build();
    const net = PetriNet.builder('SumNet').transition(t).build();
    const flatNet = flatten(net);

    const ft = flatNet.transitions[0]!;
    const outIdx = flatNet.placeIndex.get(output.name)!;
    expect(ft.postVector[outIdx]).toBe(5);
  });

  it('XOR with different counts: each branch carries its own count', () => {
    const input = place('Input');
    const output = place('Output');
    const t = Transition.builder('Choice')
      .inputs(one(input))
      .outputs(xor(outOne(output), outExactly(3, output)))
      .build();
    const net = PetriNet.builder('XorCountsNet').transition(t).build();
    const flatNet = flatten(net);

    expect(flatNet.transitions).toHaveLength(2);
    const outIdx = flatNet.placeIndex.get(output.name)!;
    expect(flatNet.transitions[0]!.postVector[outIdx]).toBe(1);
    expect(flatNet.transitions[1]!.postVector[outIdx]).toBe(3);
  });
});
