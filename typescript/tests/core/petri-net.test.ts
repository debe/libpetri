import { describe, it, expect } from 'vitest';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace, andPlaces } from '../../src/core/out.js';
import type { TransitionAction } from '../../src/core/transition-action.js';

describe('PetriNet', () => {
  const p1 = place<string>('P1');
  const p2 = place<number>('P2');
  const p3 = place<string>('P3');

  it('creates net with builder', () => {
    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();

    const net = PetriNet.builder('TestNet')
      .transition(t)
      .build();

    expect(net.name).toBe('TestNet');
    expect(net.transitions.size).toBe(1);
    // Places auto-collected from transitions
    expect(net.places.size).toBe(2);
  });

  it('auto-collects places from transitions', () => {
    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(andPlaces(p2, p3))
      .inhibitor(p3)
      .build();

    const net = PetriNet.builder('Net')
      .transition(t)
      .build();

    const placeNames = [...net.places].map(p => p.name).sort();
    expect(placeNames).toContain('P1');
    expect(placeNames).toContain('P2');
    expect(placeNames).toContain('P3');
  });

  it('allows explicit places', () => {
    const orphan = place('Orphan');
    const net = PetriNet.builder('Net')
      .place(orphan)
      .build();

    expect(net.places.has(orphan)).toBe(true);
  });

  it('bindActions replaces action by transition name', () => {
    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();

    const net = PetriNet.builder('Net')
      .transition(t)
      .build();

    let called = false;
    const action: TransitionAction = async () => { called = true; };

    const bound = net.bindActions({ T: action });

    // Original net unchanged
    const origT = [...net.transitions][0]!;
    expect(origT.action).not.toBe(action);

    // Bound net has new action
    const boundT = [...bound.transitions][0]!;
    expect(boundT.action).toBe(action);
    expect(boundT.name).toBe('T');
    // Structure preserved
    expect(boundT.inputSpecs).toHaveLength(1);
  });

  it('bindActions with Map', () => {
    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();

    const net = PetriNet.builder('Net').transition(t).build();

    const action: TransitionAction = async () => {};
    const bound = net.bindActions(new Map([['T', action]]));
    const boundT = [...bound.transitions][0]!;
    expect(boundT.action).toBe(action);
  });

  it('bindActions preserves unbound transitions', () => {
    const t1 = Transition.builder('T1').build();
    const t2 = Transition.builder('T2').build();

    const net = PetriNet.builder('Net')
      .transitions(t1, t2)
      .build();

    const action: TransitionAction = async () => {};
    const bound = net.bindActions({ T1: action });

    const boundTransitions = [...bound.transitions];
    const boundT1 = boundTransitions.find(t => t.name === 'T1')!;
    const boundT2 = boundTransitions.find(t => t.name === 'T2')!;

    expect(boundT1.action).toBe(action);
    // T2 should get passthrough (default for unbound)
    expect(boundT2).toBeDefined();
  });

  it('bindActions preserves all arc specs', () => {
    const inh = place('INH');
    const rd = place('RD');
    const rst = place('RST');

    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .inhibitor(inh)
      .read(rd)
      .reset(rst)
      .priority(5)
      .build();

    const net = PetriNet.builder('Net').transition(t).build();

    const action: TransitionAction = async () => {};
    const bound = net.bindActions({ T: action });
    const boundT = [...bound.transitions][0]!;

    expect(boundT.inhibitors).toHaveLength(1);
    expect(boundT.reads).toHaveLength(1);
    expect(boundT.resets).toHaveLength(1);
    expect(boundT.priority).toBe(5);
    expect(boundT.inputSpecs).toHaveLength(1);
    expect(boundT.outputSpec).not.toBeNull();
  });

  it('bindActionsWithResolver binds via resolver function', () => {
    const t1 = Transition.builder('T1')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();
    const t2 = Transition.builder('T2')
      .inputs(one(p2))
      .outputs(outPlace(p3))
      .build();

    const net = PetriNet.builder('Net').transitions(t1, t2).build();

    const actions: Record<string, TransitionAction> = {};
    const action1: TransitionAction = async () => {};
    const action2: TransitionAction = async () => {};
    actions['T1'] = action1;
    actions['T2'] = action2;

    const bound = net.bindActionsWithResolver((name) => actions[name]!);

    const boundTransitions = [...bound.transitions];
    const boundT1 = boundTransitions.find(t => t.name === 'T1')!;
    const boundT2 = boundTransitions.find(t => t.name === 'T2')!;

    expect(boundT1.action).toBe(action1);
    expect(boundT2.action).toBe(action2);
    // Structure preserved
    expect(boundT1.inputSpecs).toHaveLength(1);
    expect(boundT2.outputSpec).not.toBeNull();
  });

  it('multiple transitions', () => {
    const t1 = Transition.builder('T1')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();
    const t2 = Transition.builder('T2')
      .inputs(one(p2))
      .outputs(outPlace(p3))
      .build();

    const net = PetriNet.builder('Pipeline')
      .transitions(t1, t2)
      .build();

    expect(net.transitions.size).toBe(2);
    expect(net.places.size).toBe(3);
  });
});
