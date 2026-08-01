import { describe, it, expect } from 'vitest';
import { StateClassGraph } from '../../../src/verification/analysis/state-class-graph.js';
import { MarkingState } from '../../../src/verification/marking-state.js';
import { Transition } from '../../../src/core/transition.js';
import { PetriNet } from '../../../src/core/petri-net.js';
import { place, environmentPlace } from '../../../src/core/place.js';
import { one, all, atLeast } from '../../../src/core/in.js';
import { outPlace, xorPlaces } from '../../../src/core/out.js';
import { immediate, delayed, window } from '../../../src/core/timing.js';
import { alwaysAvailable, ignore } from '../../../src/verification/analysis/environment-analysis-mode.js';
import { produces } from '../../fixtures/producing-actions.js';

describe('StateClassGraph', () => {
  it('builds graph for simple circular net', () => {
    const pA = place('A');
    const pB = place('B');

    const t1 = Transition.builder('t1')
      .inputs(one(pA)).outputs(outPlace(pB)).action(produces()).build();
    const t2 = Transition.builder('t2')
      .inputs(one(pB)).outputs(outPlace(pA)).action(produces()).build();

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
      .inputs(one(pA)).outputs(outPlace(pB)).action(produces()).build();
    const t2 = Transition.builder('t2')
      .inputs(one(pB)).outputs(outPlace(pA)).action(produces()).build();

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
      .inputs(one(pA)).outputs(outPlace(pB)).action(produces())
      .timing(delayed(1000)) // 1 second delay
      .build();
    const t2 = Transition.builder('t2')
      .inputs(one(pB)).outputs(outPlace(pA)).action(produces())
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
      .inputs(one(p0)).outputs(xorPlaces(pA, pB)).action(produces()).build();
    const tA = Transition.builder('fromA')
      .inputs(one(pA)).outputs(outPlace(pEnd)).action(produces()).build();
    const tB = Transition.builder('fromB')
      .inputs(one(pB)).outputs(outPlace(pEnd)).action(produces()).build();

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
      .inputs(one(pA)).outputs(outPlace(pB)).action(produces()).build();
    const t2 = Transition.builder('t2')
      .inputs(one(pB)).outputs(outPlace(pA)).action(produces()).build();

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
      .inputs(one(env.place)).outputs(outPlace(pOut)).action(produces()).build();

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
      .inputs(one(pA)).outputs(outPlace(pB)).action(produces()).build();

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
      .inputs(one(pA)).outputs(outPlace(pB)).action(produces()).build();
    const t2 = Transition.builder('t2')
      .inputs(one(pB)).outputs(outPlace(pA)).action(produces()).build();

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

  // Regression: IO-007 draining semantics. `all` and `at-least` consume EVERY
  // available token in the executor. The SCG once modelled them as consuming
  // the minimum, which left phantom residual tokens that kept inhibitor arcs
  // unsatisfied and suppressed genuinely reachable successors — a false
  // "unreachable", i.e. an unsound Proven verdict from nu-scg-verifier.
  describe('draining input semantics (IO-007)', () => {
    it('all(p) drains p, so an inhibitor on p becomes satisfied', () => {
      const p = place<number>('p');
      const g = place<number>('g');
      const out = place<number>('out');
      const bad = place<number>('bad');

      // t fires once (g holds the single token) and drains all 3 tokens of p.
      const t = Transition.builder('t')
        .inputs(all(p), one(g))
        .outputs(outPlace(out))
        .action(produces())
        .build();

      // u needs p to be EMPTY. Only reachable if t truly drained p.
      const u = Transition.builder('u')
        .inputs(one(out))
        .inhibitor(p)
        .outputs(outPlace(bad))
        .action(produces())
        .build();

      const net = PetriNet.builder('drain-all').transitions(t, u).build();
      const marking = MarkingState.builder().tokens(p, 3).tokens(g, 1).build();
      const scg = StateClassGraph.build(net, marking, 100);

      expect(scg.isComplete()).toBe(true);

      // p must be fully drained somewhere in the reachable state space.
      expect(scg.stateClasses().some(sc => sc.marking.tokens(p) === 0)).toBe(true);

      // p is only ever 3 (before t) or 0 (after t) — never a residue like 2.
      const pCounts = new Set(scg.stateClasses().map(sc => sc.marking.tokens(p)));
      expect([...pCounts].sort((a, b) => a - b)).toEqual([0, 3]);

      // The whole point: `bad` IS reachable.
      expect(scg.stateClasses().some(sc => sc.marking.tokens(bad) > 0)).toBe(true);
    });

    it('atLeast(2, p) consumes all 5 tokens, leaving no residue', () => {
      const p = place<number>('p');
      const out = place<number>('out');

      const t = Transition.builder('t')
        .inputs(atLeast(2, p))
        .outputs(outPlace(out))
        .action(produces())
        .build();

      const net = PetriNet.builder('drain-at-least').transitions(t).build();
      const marking = MarkingState.builder().tokens(p, 5).build();
      const scg = StateClassGraph.build(net, marking, 100);

      expect(scg.isComplete()).toBe(true);

      // p is 5 (initial) or 0 (fully drained) — never 3, which is what
      // "consume minimum" would have produced.
      const pCounts = [...new Set(scg.stateClasses().map(sc => sc.marking.tokens(p)))]
        .sort((a, b) => a - b);
      expect(pCounts).toEqual([0, 5]);

      // t fires exactly once; it cannot re-enable on a residue.
      expect(scg.stateClasses().some(sc => sc.marking.tokens(out) === 1)).toBe(true);
      expect(scg.stateClasses().every(sc => sc.marking.tokens(out) <= 1)).toBe(true);
    });
  });
});

// CORE-043: the state-class graph reads token production from the Out spec, so a net whose
// action produces nothing would be analysed as something it cannot be at run time.
describe('StateClassGraph — CORE-043', () => {
  it('rejects an output-declaring transition still on passthrough', () => {
    const pA = place('A');
    const pB = place('B');
    const net = PetriNet.builder('inert')
      .transition(Transition.builder('t').inputs(one(pA)).outputs(outPlace(pB)).build())
      .build();
    const marking = MarkingState.builder().tokens(pA, 1).build();

    expect(() => StateClassGraph.build(net, marking, 100))
      .toThrow(/Transition 't' declares an output spec/);
  });

  it('a sink transition may still carry passthrough', () => {
    const pA = place('A');
    const net = PetriNet.builder('sink')
      .transition(Transition.builder('drain').inputs(one(pA)).build())
      .build();
    const marking = MarkingState.builder().tokens(pA, 1).build();

    expect(() => StateClassGraph.build(net, marking, 100)).not.toThrow();
  });
});
