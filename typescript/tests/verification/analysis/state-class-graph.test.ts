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

// VER-010: a class is identified by its marking and zone, not by the order in
// which its transitions became enabled.
describe('StateClassGraph — canonical class identity', () => {
  /**
   * Two independent chains a→c→e and b→d→f. From {c, d} the enabled set is {u, v}
   * whichever chain moved first, but fireTransition lays clocks out
   * persistent-then-new, so the two arrivals used to carry the orders [u, v] and
   * [v, u] and count as two classes. Untimed, every zone is `[0, ∞)` per clock, so
   * the marking is the whole identity: 3 × 3 = 9 markings, 9 classes.
   */
  function twoChains(timed: boolean) {
    const a = place('a'), b = place('b'), c = place('c'), d = place('d'), e = place('e'), f = place('f');
    const t = (name: string, from: ReturnType<typeof place>, to: ReturnType<typeof place>) => {
      const builder = Transition.builder(name).inputs(one(from)).outputs(outPlace(to)).action(produces());
      return (timed ? builder.timing(window(0, 2000)) : builder).build();
    };
    const net = PetriNet.builder('two-chains')
      .transitions(t('tx', a, c), t('ty', b, d), t('u', c, e), t('v', d, f))
      .build();
    const marking = MarkingState.builder().tokens(a, 1).tokens(b, 1).build();
    return { net, marking, c, d };
  }

  it('counts one marking once, whatever the enabling order (untimed)', () => {
    const { net, marking, c, d } = twoChains(false);
    const scg = StateClassGraph.build(net, marking, 1000);
    expect(scg.isComplete()).toBe(true);
    expect(scg.reachableMarkings().size).toBe(9);
    expect(scg.size()).toBe(9);
    const atCD = scg.classesWithMarking(MarkingState.builder().tokens(c, 1).tokens(d, 1).build());
    expect(atCD).toHaveLength(1);
    expect(atCD[0]!.firingDomain.clockNames).toEqual(['u', 'v']);
  });

  it('keeps clocks, enabled list and earliest-ready times aligned after reordering', () => {
    const { net, marking, c, d } = twoChains(true);
    const scg = StateClassGraph.build(net, marking, 1000);
    expect(scg.isComplete()).toBe(true);
    // Same zone from both paths (v and u are each fresh when enabled), so one class.
    const atCD = scg.classesWithMarking(MarkingState.builder().tokens(c, 1).tokens(d, 1).build());
    expect(atCD).toHaveLength(1);
    const sc = atCD[0]!;
    expect(sc.enabledTransitions.map(t => t.name)).toEqual(sc.firingDomain.clockNames);
    expect(sc.readyEarliest).toHaveLength(sc.enabledTransitions.length);
    for (const t of sc.enabledTransitions) {
      expect(sc.canFire(t)).toBe(true);
    }
  });

  it('orders the initial class canonically too', () => {
    const b = place('b'), a = place('a'), x = place('x');
    // Declared in the order tz, ty — the initial clocks come out ty, tz.
    const tz = Transition.builder('tz').inputs(one(b)).outputs(outPlace(x)).action(produces()).build();
    const ty = Transition.builder('ty').inputs(one(a)).outputs(outPlace(x)).action(produces()).build();
    const net = PetriNet.builder('initial-order').transitions(tz, ty).build();
    const marking = MarkingState.builder().tokens(a, 1).tokens(b, 1).build();
    const scg = StateClassGraph.build(net, marking, 100);
    expect(scg.initialClass.firingDomain.clockNames).toEqual(['ty', 'tz']);
    expect(scg.initialClass.enabledTransitions.map(t => t.name)).toEqual(['ty', 'tz']);
  });
});

// TIME-012 / VER-010 AC4: clock persistence is decided on the intermediate marking M - Pre(t).
// Refresh takes the timer token and puts one back, which leaves CloseSession disabled in
// between, so CloseSession starts a fresh interval in the successor class. A surplus token
// keeps it enabled throughout, and its clock persists.
describe('StateClassGraph — intermediate-marking clock persistence (TIME-012)', () => {
  /** CloseSession's earliest-ready time on a fresh clock: `delayed(200)`, in seconds. */
  const FRESH = 0.2;

  function refreshNet(shape: 'input' | 'read' | 'reset' | 'surplus') {
    const activity = place('activity');
    const timer = place('timer');
    const armed = place('armed');
    const closed = place('closed');
    const refreshBuilder = Transition.builder('Refresh').outputs(outPlace(timer)).action(produces());
    const refresh = (shape === 'reset'
      ? refreshBuilder.inputs(one(activity)).reset(timer)
      : refreshBuilder.inputs(one(activity), one(timer))
    ).build();
    const closeBuilder = Transition.builder('CloseSession')
      .outputs(outPlace(closed)).action(produces()).timing(delayed(200));
    const close = (shape === 'read'
      ? closeBuilder.inputs(one(armed)).read(timer)
      : closeBuilder.inputs(one(timer))
    ).build();
    const net = PetriNet.builder(`refresh-${shape}`).transitions(refresh, close).build();
    const marking = MarkingState.builder()
      .tokens(activity, 1)
      .tokens(timer, shape === 'surplus' ? 2 : 1)
      .tokens(armed, shape === 'read' ? 1 : 0)
      .build();
    return { net, marking, refresh, close };
  }

  /** CloseSession's earliest-ready time in the class Refresh leads to from the initial class. */
  function closeReadyAfterRefresh(shape: 'input' | 'read' | 'reset' | 'surplus'): number {
    const { net, marking, refresh, close } = refreshNet(shape);
    const scg = StateClassGraph.build(net, marking, 100);
    expect(scg.isComplete()).toBe(true);
    const initial = scg.initialClass;
    expect(initial.readyEarliest[initial.enabledTransitions.indexOf(close)]).toBeCloseTo(FRESH, 9);

    const edges = scg.branchEdges(initial, refresh);
    expect(edges).toHaveLength(1);
    const successor = edges[0]!.target;
    const k = successor.enabledTransitions.indexOf(close);
    expect(k).toBeGreaterThanOrEqual(0);
    return successor.readyEarliest[k]!;
  }

  it('consume-and-redeposit: the input-arc dependent is newly enabled with a fresh interval', () => {
    expect(closeReadyAfterRefresh('input')).toBeCloseTo(FRESH, 9);
  });

  it('consume-and-redeposit: the read-arc dependent is newly enabled with a fresh interval', () => {
    expect(closeReadyAfterRefresh('read')).toBeCloseTo(FRESH, 9);
  });

  it('reset refilled by the outputs: the dependent is newly enabled with a fresh interval', () => {
    expect(closeReadyAfterRefresh('reset')).toBeCloseTo(FRESH, 9);
  });

  it('surplus token: the dependent stays enabled throughout, so its clock persists', () => {
    // Refresh may fire at any time before CloseSession's, so the persistent clock may be ready at once.
    expect(closeReadyAfterRefresh('surplus')).toBe(0);
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
