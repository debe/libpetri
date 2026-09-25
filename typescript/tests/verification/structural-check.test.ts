import { describe, it, expect } from 'vitest';
import { structuralCheck, findMinimalSiphons, findMaximalTrapIn } from '../../src/verification/invariant/structural-check.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { and, outPlace } from '../../src/core/out.js';

describe('StructuralCheck', () => {
  it('circular net is deadlock-free', () => {
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
    const marking = MarkingState.builder().tokens(pA, 1).build();

    const result = structuralCheck(flatNet, marking);
    expect(result.type).toBe('no-potential-deadlock');
  });

  it('empty net is deadlock-free', () => {
    const net = PetriNet.builder('Empty').build();
    const flatNet = flatten(net);
    const marking = MarkingState.empty();

    const result = structuralCheck(flatNet, marking);
    expect(result.type).toBe('no-potential-deadlock');
  });

  it('pipeline net with no initial marking has potential deadlock', () => {
    const pA = place('A');
    const pB = place('B');
    const t = Transition.builder('T')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const flatNet = flatten(net);
    const marking = MarkingState.empty(); // No tokens!

    const result = structuralCheck(flatNet, marking);
    // Without tokens, the siphon {A} cannot have a marked trap
    expect(result.type).toBe('potential-deadlock');
  });

  it('pipeline net with initial marking has potential deadlock (sink place)', () => {
    const pA = place('A');
    const pB = place('B');
    const t = Transition.builder('T')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const net = PetriNet.builder('N').transition(t).build();
    const flatNet = flatten(net);
    const marking = MarkingState.builder().tokens(pA, 1).build();

    const result = structuralCheck(flatNet, marking);
    // Pipeline A→B: siphon {A} has no trap (A consumed by T but T outputs to B, not A)
    // So once A is consumed, the net deadlocks with tokens stuck in B
    expect(result.type).toBe('potential-deadlock');
  });

  it('findMinimalSiphons finds siphons', () => {
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

    const siphons = findMinimalSiphons(flatNet);
    // Circular net should have one siphon containing both places
    expect(siphons.length).toBeGreaterThan(0);
    // The siphon should contain both A and B
    const siphon = siphons[0]!;
    expect(siphon.size).toBe(2);
  });

  it('findMaximalTrapIn finds trap', () => {
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

    const allPlaces = new Set([0, 1]);
    const trap = findMaximalTrapIn(flatNet, allPlaces);
    // Both places form a trap in a circular net
    expect(trap.size).toBe(2);
  });

  const guardedRing = () => {
    const g = place('g'), h = place('h'), x = place('x'), y = place('y');
    const t1 = Transition.builder('t1').inputs(one(g), one(x)).outputs(and(outPlace(y), outPlace(g))).build();
    const t2 = Transition.builder('t2').inputs(one(h), one(y)).outputs(and(outPlace(x), outPlace(h))).build();
    return { flatNet: flatten(PetriNet.builder('N').transitions(t1, t2).build()), g, h, x };
  };

  it('finds a siphon that only a second input reaches', () => {
    const { flatNet, g, h, x } = guardedRing();
    const names = findMinimalSiphons(flatNet).map(s => [...s].map(i => flatNet.places[i]!.name).sort().join(','));
    expect(names.sort()).toEqual(['g', 'h', 'x,y']);
    expect(structuralCheck(flatNet, MarkingState.builder().tokens(g, 1).tokens(h, 1).build()).type)
      .toBe('potential-deadlock');
    expect(structuralCheck(flatNet, MarkingState.builder().tokens(g, 1).tokens(h, 1).tokens(x, 1).build()).type)
      .toBe('no-potential-deadlock');
  });

  it('an exhausted search is inconclusive', () => {
    expect(findMinimalSiphons(guardedRing().flatNet, 1)).toBeNull();
  });

  it('does not pad a siphon with every input of a producer', () => {
    // t1: a + c -> b + c, t2: b -> a. The minimal siphon {a, b} is empty at {c:1}.
    const a = place('a'), b = place('b'), c = place('c');
    const t1 = Transition.builder('t1').inputs(one(a), one(c)).outputs(and(outPlace(b), outPlace(c))).build();
    const t2 = Transition.builder('t2').inputs(one(b)).outputs(outPlace(a)).build();
    const flatNet = flatten(PetriNet.builder('N').transitions(t1, t2).build());
    expect(structuralCheck(flatNet, MarkingState.builder().tokens(c, 1).build()).type).toBe('potential-deadlock');
  });
});
