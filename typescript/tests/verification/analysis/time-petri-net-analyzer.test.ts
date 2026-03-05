import { describe, it, expect } from 'vitest';
import { TimePetriNetAnalyzer } from '../../../src/verification/analysis/time-petri-net-analyzer.js';
import { StateClassGraph } from '../../../src/verification/analysis/state-class-graph.js';
import { MarkingState } from '../../../src/verification/marking-state.js';
import { Transition } from '../../../src/core/transition.js';
import { PetriNet } from '../../../src/core/petri-net.js';
import { place, environmentPlace } from '../../../src/core/place.js';
import { one } from '../../../src/core/in.js';
import { outPlace, xorPlaces } from '../../../src/core/out.js';
import { immediate, delayed, window } from '../../../src/core/timing.js';
import { alwaysAvailable, bounded, ignore } from '../../../src/verification/analysis/environment-analysis-mode.js';

describe('TimePetriNetAnalyzer', () => {
  describe('goal liveness', () => {
    it('verifies goal liveness for circular net', () => {
      const pA = place('A');
      const pB = place('B');

      const t1 = Transition.builder('t1')
        .inputs(one(pA)).outputs(outPlace(pB)).build();
      const t2 = Transition.builder('t2')
        .inputs(one(pB)).outputs(outPlace(pA)).build();

      const net = PetriNet.builder('circular')
        .transitions(t1, t2).build();

      const result = TimePetriNetAnalyzer.forNet(net)
        .initialMarking(MarkingState.builder().tokens(pA, 1).build())
        .goalPlaces(pB)
        .maxClasses(100)
        .build()
        .analyze();

      expect(result.isGoalLive).toBe(true);
      expect(result.isComplete).toBe(true);
      expect(result.stateClassGraph.size()).toBeGreaterThanOrEqual(2);
      expect(result.report).toContain('GOAL LIVENESS VERIFIED');
    });

    it('detects goal liveness violation for dead-end net', () => {
      const pA = place('A');
      const pB = place('B');
      const pGoal = place('Goal');

      // A → B, no path to Goal
      const t1 = Transition.builder('t1')
        .inputs(one(pA)).outputs(outPlace(pB)).build();

      const net = PetriNet.builder('deadend')
        .transitions(t1).place(pGoal).build();

      const result = TimePetriNetAnalyzer.forNet(net)
        .initialMarking(MarkingState.builder().tokens(pA, 1).build())
        .goalPlaces(pGoal)
        .maxClasses(100)
        .build()
        .analyze();

      expect(result.isGoalLive).toBe(false);
      expect(result.report).toContain('GOAL LIVENESS VIOLATION');
    });
  });

  describe('L4 liveness', () => {
    it('verifies L4 liveness for circular net', () => {
      const pA = place('A');
      const pB = place('B');

      const t1 = Transition.builder('t1')
        .inputs(one(pA)).outputs(outPlace(pB)).build();
      const t2 = Transition.builder('t2')
        .inputs(one(pB)).outputs(outPlace(pA)).build();

      const net = PetriNet.builder('circular')
        .transitions(t1, t2).build();

      const result = TimePetriNetAnalyzer.forNet(net)
        .initialMarking(MarkingState.builder().tokens(pA, 1).build())
        .goalPlaces(pA)
        .maxClasses(100)
        .build()
        .analyze();

      expect(result.isL4Live).toBe(true);
      expect(result.report).toContain('CLASSICAL LIVENESS (L4) VERIFIED');
    });

    it('detects L4 violation for dead-end', () => {
      const pA = place('A');
      const pB = place('B');

      const t1 = Transition.builder('t1')
        .inputs(one(pA)).outputs(outPlace(pB)).build();

      const net = PetriNet.builder('deadend')
        .transitions(t1).build();

      const result = TimePetriNetAnalyzer.forNet(net)
        .initialMarking(MarkingState.builder().tokens(pA, 1).build())
        .goalPlaces(pB)
        .maxClasses(100)
        .build()
        .analyze();

      expect(result.isL4Live).toBe(false);
    });
  });

  describe('environment places', () => {
    it('always-available mode enables transitions without tokens', () => {
      const env = environmentPlace<string>('input');
      const pReady = place('ready');
      const pOut = place('output');

      // ready → process (consumes ready, env always available) → output
      // output → reset → ready (cycle back)
      const t1 = Transition.builder('process')
        .inputs(one(pReady), one(env.place)).outputs(outPlace(pOut)).build();
      const t2 = Transition.builder('reset')
        .inputs(one(pOut)).outputs(outPlace(pReady)).build();

      const net = PetriNet.builder('env-net')
        .transitions(t1, t2).build();

      const result = TimePetriNetAnalyzer.forNet(net)
        .initialMarking(MarkingState.builder().tokens(pReady, 1).build())
        .goalPlaces(pOut)
        .environmentPlaces(env)
        .environmentMode(alwaysAvailable())
        .maxClasses(100)
        .build()
        .analyze();

      expect(result.isGoalLive).toBe(true);
      expect(result.report).toContain('Environment places');
    });

    it('ignore mode treats env places as regular', () => {
      const env = environmentPlace<string>('input');
      const pOut = place('output');

      const t1 = Transition.builder('process')
        .inputs(one(env.place)).outputs(outPlace(pOut)).build();

      const net = PetriNet.builder('env-net')
        .transitions(t1).build();

      const result = TimePetriNetAnalyzer.forNet(net)
        .initialMarking(MarkingState.empty())
        .goalPlaces(pOut)
        .environmentPlaces(env)
        .environmentMode(ignore())
        .maxClasses(100)
        .build()
        .analyze();

      // No tokens in env place + ignore = not enabled → no goal reached
      expect(result.isGoalLive).toBe(false);
    });

    it('bounded mode limits environment tokens', () => {
      const env = environmentPlace<string>('input');
      const pReady = place('ready');
      const pOut = place('output');

      const t1 = Transition.builder('process')
        .inputs(one(pReady), one(env.place)).outputs(outPlace(pOut)).build();
      const t2 = Transition.builder('reset')
        .inputs(one(pOut)).outputs(outPlace(pReady)).build();

      const net = PetriNet.builder('env-net')
        .transitions(t1, t2).build();

      const result = TimePetriNetAnalyzer.forNet(net)
        .initialMarking(MarkingState.builder().tokens(pReady, 1).build())
        .goalPlaces(pOut)
        .environmentPlaces(env)
        .environmentMode(bounded(1))
        .maxClasses(100)
        .build()
        .analyze();

      expect(result.isComplete).toBe(true);
    });
  });

  describe('XOR branch analysis', () => {
    it('identifies XOR branches and coverage', () => {
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
      const analysis = TimePetriNetAnalyzer.analyzeXorBranches(scg);

      expect(analysis.transitionBranches.size).toBe(1);
      expect(analysis.transitionBranches.has(tChoice)).toBe(true);

      const info = analysis.transitionBranches.get(tChoice)!;
      expect(info.totalBranches).toBe(2);
      expect(info.takenBranches.size).toBe(2);
      expect(info.untakenBranches.size).toBe(0);

      expect(analysis.isXorComplete()).toBe(true);
      expect(analysis.unreachableBranches().size).toBe(0);
    });

    it('report generation', () => {
      const p0 = place('start');
      const pA = place('branchA');
      const pB = place('branchB');

      const tChoice = Transition.builder('choice')
        .inputs(one(p0)).outputs(xorPlaces(pA, pB)).build();

      const net = PetriNet.builder('xor')
        .transitions(tChoice).build();

      const marking = MarkingState.builder().tokens(p0, 1).build();
      const scg = StateClassGraph.build(net, marking, 100);
      const analysis = TimePetriNetAnalyzer.analyzeXorBranches(scg);

      const report = analysis.report();
      expect(report).toContain('XOR Branch Coverage');
      expect(report).toContain('choice');
    });

    it('reports no XOR when none present', () => {
      const pA = place('A');
      const pB = place('B');

      const t1 = Transition.builder('t1')
        .inputs(one(pA)).outputs(outPlace(pB)).build();

      const net = PetriNet.builder('no-xor')
        .transitions(t1).build();

      const marking = MarkingState.builder().tokens(pA, 1).build();
      const scg = StateClassGraph.build(net, marking, 100);
      const analysis = TimePetriNetAnalyzer.analyzeXorBranches(scg);

      expect(analysis.report()).toBe('No XOR transitions in net.');
    });
  });

  describe('builder validation', () => {
    it('throws when no goal places specified', () => {
      const pA = place('A');
      const t1 = Transition.builder('t1').inputs(one(pA)).build();
      const net = PetriNet.builder('test').transitions(t1).build();

      expect(() =>
        TimePetriNetAnalyzer.forNet(net)
          .initialMarking(MarkingState.empty())
          .build()
      ).toThrow('At least one goal place');
    });
  });

  describe('report generation', () => {
    it('generates comprehensive report', () => {
      const pA = place('A');
      const pB = place('B');

      const t1 = Transition.builder('t1')
        .inputs(one(pA)).outputs(outPlace(pB)).build();
      const t2 = Transition.builder('t2')
        .inputs(one(pB)).outputs(outPlace(pA)).build();

      const net = PetriNet.builder('circular')
        .transitions(t1, t2).build();

      const result = TimePetriNetAnalyzer.forNet(net)
        .initialMarking(MarkingState.builder().tokens(pA, 1).build())
        .goalPlaces(pA)
        .maxClasses(100)
        .build()
        .analyze();

      expect(result.report).toContain('TIME PETRI NET FORMAL ANALYSIS');
      expect(result.report).toContain('Berthomieu-Diaz');
      expect(result.report).toContain('State classes:');
      expect(result.report).toContain('Terminal SCCs:');
      expect(result.report).toContain('ANALYSIS RESULT');
    });
  });
});
