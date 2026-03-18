import { describe, it, expect } from 'vitest';
import { CompiledNet, setBit, clearBit, testBit, containsAll, intersects } from '../../src/runtime/compiled-net.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one, exactly, all, atLeast } from '../../src/core/in.js';
import { outPlace, andPlaces, xorPlaces } from '../../src/core/out.js';

describe('Bitmap Helpers', () => {
  it('setBit and testBit', () => {
    const arr = new Uint32Array(2);
    expect(testBit(arr, 0)).toBe(false);
    setBit(arr, 0);
    expect(testBit(arr, 0)).toBe(true);
    setBit(arr, 33);
    expect(testBit(arr, 33)).toBe(true);
    expect(testBit(arr, 1)).toBe(false);
  });

  it('clearBit', () => {
    const arr = new Uint32Array(1);
    setBit(arr, 5);
    expect(testBit(arr, 5)).toBe(true);
    clearBit(arr, 5);
    expect(testBit(arr, 5)).toBe(false);
  });

  it('containsAll', () => {
    const snapshot = new Uint32Array(2);
    setBit(snapshot, 0);
    setBit(snapshot, 5);
    setBit(snapshot, 33);

    const mask = new Uint32Array(2);
    setBit(mask, 0);
    setBit(mask, 5);
    expect(containsAll(snapshot, mask)).toBe(true);

    setBit(mask, 10);
    expect(containsAll(snapshot, mask)).toBe(false);
  });

  it('intersects', () => {
    const snapshot = new Uint32Array(2);
    setBit(snapshot, 3);
    setBit(snapshot, 40);

    const mask1 = new Uint32Array(2);
    setBit(mask1, 3);
    expect(intersects(snapshot, mask1)).toBe(true);

    const mask2 = new Uint32Array(2);
    setBit(mask2, 10);
    expect(intersects(snapshot, mask2)).toBe(false);
  });

  it('containsAll with empty mask', () => {
    const snapshot = new Uint32Array(1);
    const mask = new Uint32Array(1);
    expect(containsAll(snapshot, mask)).toBe(true);
  });

  it('containsAll with bit 31 (sign bit) set', () => {
    const snapshot = new Uint32Array(1);
    setBit(snapshot, 31);
    const mask = new Uint32Array(1);
    setBit(mask, 31);
    expect(containsAll(snapshot, mask)).toBe(true);

    // bit 31 not in snapshot → false
    const empty = new Uint32Array(1);
    expect(containsAll(empty, mask)).toBe(false);
  });

  it('intersects with bit 31 (sign bit) set', () => {
    const snapshot = new Uint32Array(1);
    setBit(snapshot, 31);
    const mask = new Uint32Array(1);
    setBit(mask, 31);
    expect(intersects(snapshot, mask)).toBe(true);

    const noSign = new Uint32Array(1);
    setBit(noSign, 0);
    expect(intersects(noSign, mask)).toBe(false);
  });

  it('containsAll with bit 31 in both words (multi-word)', () => {
    const snapshot = new Uint32Array(2);
    setBit(snapshot, 31); // sign bit of word 0
    setBit(snapshot, 63); // sign bit of word 1
    const mask = new Uint32Array(2);
    setBit(mask, 31);
    setBit(mask, 63);
    expect(containsAll(snapshot, mask)).toBe(true);

    // missing bit 63 → false
    const partial = new Uint32Array(2);
    setBit(partial, 31);
    expect(containsAll(partial, mask)).toBe(false);
  });
});

describe('CompiledNet', () => {
  it('compiles a simple net', () => {
    const p1 = place<number>('P1');
    const p2 = place<number>('P2');
    const t = Transition.builder('T').inputs(one(p1)).outputs(outPlace(p2)).build();
    const net = PetriNet.builder('N').transition(t).build();
    const compiled = CompiledNet.compile(net);

    expect(compiled.placeCount).toBe(2);
    expect(compiled.transitionCount).toBe(1);
    expect(compiled.wordCount).toBe(1);
  });

  it('assigns correct place IDs', () => {
    const p1 = place('P1');
    const p2 = place('P2');
    const p3 = place('P3');
    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(andPlaces(p2, p3))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const compiled = CompiledNet.compile(net);

    const pid1 = compiled.placeId(p1);
    const pid2 = compiled.placeId(p2);
    const pid3 = compiled.placeId(p3);
    expect(new Set([pid1, pid2, pid3]).size).toBe(3);
  });

  it('throws for unknown place', () => {
    const p1 = place('P1');
    const p2 = place('P2');
    const t = Transition.builder('T').inputs(one(p1)).outputs(outPlace(p2)).build();
    const net = PetriNet.builder('N').transition(t).build();
    const compiled = CompiledNet.compile(net);
    expect(() => compiled.placeId(place('UNKNOWN'))).toThrow('Unknown place');
  });

  it('canEnableBitmap with input place marked', () => {
    const p1 = place('P1');
    const p2 = place('P2');
    const t = Transition.builder('T').inputs(one(p1)).outputs(outPlace(p2)).build();
    const net = PetriNet.builder('N').transition(t).build();
    const compiled = CompiledNet.compile(net);

    const marking = new Uint32Array(compiled.wordCount);
    const tid = compiled.transitionId(t);

    expect(compiled.canEnableBitmap(tid, marking)).toBe(false);
    setBit(marking, compiled.placeId(p1));
    expect(compiled.canEnableBitmap(tid, marking)).toBe(true);
  });

  it('canEnableBitmap blocked by inhibitor', () => {
    const input = place('IN');
    const output = place('OUT');
    const inhibitor = place('BLOCKER');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .inhibitor(inhibitor)
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const compiled = CompiledNet.compile(net);

    const marking = new Uint32Array(compiled.wordCount);
    setBit(marking, compiled.placeId(input));
    const tid = compiled.transitionId(t);

    expect(compiled.canEnableBitmap(tid, marking)).toBe(true);
    setBit(marking, compiled.placeId(inhibitor));
    expect(compiled.canEnableBitmap(tid, marking)).toBe(false);
  });

  it('canEnableBitmap requires read arcs', () => {
    const input = place('IN');
    const output = place('OUT');
    const readPlace = place('RD');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .read(readPlace)
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const compiled = CompiledNet.compile(net);

    const marking = new Uint32Array(compiled.wordCount);
    const tid = compiled.transitionId(t);

    setBit(marking, compiled.placeId(input));
    expect(compiled.canEnableBitmap(tid, marking)).toBe(false);
    setBit(marking, compiled.placeId(readPlace));
    expect(compiled.canEnableBitmap(tid, marking)).toBe(true);
  });

  it('affectedTransitions tracks reverse index', () => {
    const p1 = place('P1');
    const p2 = place('P2');
    const p3 = place('P3');
    const t1 = Transition.builder('T1').inputs(one(p1)).outputs(outPlace(p2)).build();
    const t2 = Transition.builder('T2').inputs(one(p1)).outputs(outPlace(p3)).build();
    const net = PetriNet.builder('N').transitions(t1, t2).build();
    const compiled = CompiledNet.compile(net);

    const pid1 = compiled.placeId(p1);
    const affected = compiled.affectedTransitions(pid1);
    expect(affected.length).toBe(2);
  });

  it('cardinality check for exactly()', () => {
    const p1 = place('P1');
    const p2 = place('P2');
    const t = Transition.builder('T')
      .inputs(exactly(3, p1))
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const compiled = CompiledNet.compile(net);
    const tid = compiled.transitionId(t);

    const check = compiled.cardinalityCheck(tid);
    expect(check).not.toBeNull();
    expect(check!.requiredCounts[0]).toBe(3);
  });

  it('no cardinality check for one()', () => {
    const p1 = place('P1');
    const p2 = place('P2');
    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const compiled = CompiledNet.compile(net);
    const tid = compiled.transitionId(t);

    expect(compiled.cardinalityCheck(tid)).toBeNull();
  });

  it('consumption place IDs include inputs and resets', () => {
    const input = place('IN');
    const output = place('OUT');
    const resetPlace = place('RST');
    const t = Transition.builder('T')
      .inputs(one(input))
      .outputs(outPlace(output))
      .reset(resetPlace)
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const compiled = CompiledNet.compile(net);
    const tid = compiled.transitionId(t);

    const consumptionPids = compiled.consumptionPlaceIds(tid);
    expect(consumptionPids).toContain(compiled.placeId(input));
    expect(consumptionPids).toContain(compiled.placeId(resetPlace));
  });

  it('handles net with many places (multi-word bitmap)', () => {
    // Create 40 places to force 2 Uint32 words
    const places = Array.from({ length: 40 }, (_, i) => place(`P${i}`));
    const transitions = places.slice(0, 39).map((p, i) =>
      Transition.builder(`T${i}`).inputs(one(p)).outputs(outPlace(places[i + 1]!)).build()
    );
    const net = PetriNet.builder('BigNet').transitions(...transitions).build();
    const compiled = CompiledNet.compile(net);

    expect(compiled.placeCount).toBe(40);
    expect(compiled.wordCount).toBe(2);
    expect(compiled.transitionCount).toBe(39);
  });
});
