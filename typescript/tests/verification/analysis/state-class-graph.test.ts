import { describe, it, expect } from 'vitest';
import { StateClassGraph } from '../../../src/verification/analysis/state-class-graph.js';
import { MarkingState } from '../../../src/verification/marking-state.js';
import { Transition } from '../../../src/core/transition.js';
import { PetriNet } from '../../../src/core/petri-net.js';
import { place, environmentPlace } from '../../../src/core/place.js';
import { one } from '../../../src/core/in.js';
import { outPlace, xorPlaces } from '../../../src/core/out.js';
import { immediate, delayed, window } from '../../../src/core/timing.js';
import { alwaysAvailable, ignore } from '../../../src/verification/analysis/environment-analysis-mode.js';

describe('StateClassGraph', () => {
  it('builds graph for simple circular net', () => {
    const pA = place('A');
    const pB = place('B');

    const t1 = Transition.builder('t1')
      .inputs(one(pA)).outputs(outPlace(pB)).build();
    const t2 = Transition.builder('t2')
      .inputs(one(pB)).outputs(outPlace(pA)).build();

    const net = PetriNet.builder('circular')
      .transitions(t1, t2).build();

    const marking = MarkingState.builder().tokens(pA, 1).build();
    const scg = StateClassGraph.build(net, marking, 100);

    expect(scg.size()).toBeGreaterThanOrEqual(2);
    expect(scg.isComplete()).toBe(true);
    expect(scg.edgeCount()).toBeGreaterThanOrEqual(2);

    // Initial class should have t1 enabled
    const initialEnabled = scg.enabledTransitions(scg.initialClass);
    expect(initialEnabled.has(t1)).toBe(true);
    expect(initialEnabled.has(t2)).toBe(false);
  });

  it('reachable markings covers both states', () => {
    const pA = place('A');
    const pB = place('B');

    const t1 = Transition.builder('t1')
      .inputs(one(pA)).outputs(outPlace(pB)).build();
    const t2 = Transition.builder('t2')
      .inputs(one(pB)).outputs(outPlace(pA)).build();

    const net = PetriNet.builder('circular')
      .transitions(t1, t2).build();

    const marking = MarkingState.builder().tokens(pA, 1).build();
    const scg = StateClassGraph.build(net, marking, 100);

    const markings = scg.reachableMarkings();
    expect(markings.size).toBe(2);
  });

  it('builds graph for timed net', () => {
    const pA = place('A');
    const pB = place('B');

    const t1 = Transition.builder('t1')
      .inputs(one(pA)).outputs(outPlace(pB))
      .timing(delayed(1000)) // 1 second delay
      .build();
    const t2 = Transition.builder('t2')
      .inputs(one(pB)).outputs(outPlace(pA))
      .timing(window(500, 2000))
      .build();

    const net = PetriNet.builder('timed')
      .transitions(t1, t2).build();

    const marking = MarkingState.builder().tokens(pA, 1).build();
    const scg = StateClassGraph.build(net, marking, 100);

    expect(scg.isComplete()).toBe(true);
    expect(scg.size()).toBeGreaterThanOrEqual(2);

    // Verify DBM constraints exist
    const initial = scg.initialClass;
    expect(initial.firingDomain.isEmpty()).toBe(false);
  });

  it('handles XOR branch expansion', () => {
    const p0 = place('start');
    const pA = place('branchA');
    const pB = place('branchB');
    const pEnd = place('end');

    const tChoice = Transition.builder('choice')
      .inputs(one(p0)).outputs(xorPlaces(pA, pB)).build();
    const tA = Transition.builder('fromA')
      .inputs(one(pA)).outputs(outPlace(pEnd)).build();
    const tB = Transition.builder('fromB')
      .inputs(one(pB)).outputs(outPlace(pEnd)).build();

    const net = PetriNet.builder('xor')
      .transitions(tChoice, tA, tB).build();

    const marking = MarkingState.builder().tokens(p0, 1).build();
    const scg = StateClassGraph.build(net, marking, 100);

    expect(scg.isComplete()).toBe(true);

    // The choice transition should produce branch edges
    const branchEdges = scg.branchEdges(scg.initialClass, tChoice);
    expect(branchEdges.length).toBe(2);
    expect(branchEdges[0]!.branchIndex).toBe(0);
    expect(branchEdges[1]!.branchIndex).toBe(1);
  });

  it('truncates when maxClasses exceeded', () => {
    const pA = place('A');
    const pB = place('B');

    const t1 = Transition.builder('t1')
      .inputs(one(pA)).outputs(outPlace(pB)).build();
    const t2 = Transition.builder('t2')
      .inputs(one(pB)).outputs(outPlace(pA)).build();

    const net = PetriNet.builder('circular')
      .transitions(t1, t2).build();

    const marking = MarkingState.builder().tokens(pA, 1).build();
    const scg = StateClassGraph.build(net, marking, 1);

    expect(scg.isComplete()).toBe(false);
    expect(scg.size()).toBeLessThanOrEqual(1);
  });

  it('supports environment places with always-available mode', () => {
    const env = environmentPlace<string>('env_input');
    const pOut = place('output');

    const t1 = Transition.builder('process')
      .inputs(one(env.place)).outputs(outPlace(pOut)).build();

    const net = PetriNet.builder('env-net')
      .transitions(t1).build();

    const marking = MarkingState.empty();
    const scg = StateClassGraph.build(
      net, marking, 100,
      new Set([env]),
      alwaysAvailable(),
    );

    // With always-available, t1 should be enabled even without tokens
    expect(scg.size()).toBeGreaterThanOrEqual(1);
    const initialEnabled = scg.enabledTransitions(scg.initialClass);
    expect(initialEnabled.has(t1)).toBe(true);
  });

  it('deadend net has no outgoing transitions from final state', () => {
    const pA = place('A');
    const pB = place('B');

    const t1 = Transition.builder('t1')
      .inputs(one(pA)).outputs(outPlace(pB)).build();

    const net = PetriNet.builder('deadend')
      .transitions(t1).build();

    const marking = MarkingState.builder().tokens(pA, 1).build();
    const scg = StateClassGraph.build(net, marking, 100);

    expect(scg.isComplete()).toBe(true);
    expect(scg.size()).toBe(2);

    // Find the deadend state class
    const deadendClasses = scg.stateClasses().filter(sc => scg.successors(sc).size === 0);
    expect(deadendClasses.length).toBe(1);
  });

  it('predecessors are correctly tracked', () => {
    const pA = place('A');
    const pB = place('B');

    const t1 = Transition.builder('t1')
      .inputs(one(pA)).outputs(outPlace(pB)).build();
    const t2 = Transition.builder('t2')
      .inputs(one(pB)).outputs(outPlace(pA)).build();

    const net = PetriNet.builder('circular')
      .transitions(t1, t2).build();

    const marking = MarkingState.builder().tokens(pA, 1).build();
    const scg = StateClassGraph.build(net, marking, 100);

    // Every non-initial class should have at least one predecessor
    for (const sc of scg.stateClasses()) {
      if (sc !== scg.initialClass) {
        expect(scg.predecessors(sc).size).toBeGreaterThan(0);
      }
    }
  });
});
