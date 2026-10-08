import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { StateSpaceCache } from '../../src/verification/state-space-cache.js';
import { stateSpaceBuildCount } from '../../src/verification/scg-verifier.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import {
  deadlockFree, mutualExclusion, placeBound, unreachable, type SmtProperty,
} from '../../src/verification/smt-property.js';
import { NameStateClassGraph } from '../../src/verification/analysis/name-state-class-graph.js';
import { classify } from '../../src/verification/analysis/name-fragment.js';
import { ignore } from '../../src/verification/analysis/environment-analysis-mode.js';
import { counterexamplePath, decide, verifyViaNameScg } from '../../src/verification/nu-scg-verifier.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, type Place } from '../../src/core/place.js';
import { andPlaces, outPlace } from '../../src/core/out.js';
import { one } from '../../src/core/in.js';
import { delayed } from '../../src/core/timing.js';
import { produces } from '../fixtures/producing-actions.js';
import { describeZ3 } from '../fixtures/z3.js';
import {
  FIG_11B_ROWS, FIG_12C_ROWS, JOIN_CHAIN_ROWS, N1_CORR_ROWS, pnidNet,
} from '../fixtures/pnid-nets.js';
import { allMints } from '../fixtures/all-mints.js';

/**
 * [VER-012] AC3, [VER-017], [VER-023]: a graph route that truncates still decides a violation
 * found in its explored prefix — every stored class is reachable — and never proves anything
 * from it. Frontier classes, stored but never expanded, never count as quiescent.
 */

const PREFIX = 'the violation was found in the explored prefix';

function fig11b() {
  const { net, places } = pnidNet('P-Fig11b-not-exclusive', FIG_11B_ROWS);
  const m0 = MarkingState.builder().tokens(places.get('clerk')!, 2).build();
  return { net, places, m0 };
}

describe('Route B decides on its explored prefix (VER-012 AC3)', () => {
  it('PNID Fig. 11(b): placeBound(order_clerk, 2) stops at the first violating class, a depth-3 trace', async () => {
    // Default cap (100 000): the build stops at the violation instead of filling the cap, which
    // took 1.8 s at 20 000 classes before the early stop.
    const { net, places, m0 } = fig11b();
    const result = await SmtVerifier.forNet(net).mintTransitions(...allMints(net)).initialMarking(m0)
      .property(placeBound(places.get('order_clerk')!, 2)).verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.route).toBe('nu-scg');
    expect(result.counterexampleTransitions).toEqual(['create_order', 'create_order', 'create_order']);
    expect(result.counterexampleTrace).toHaveLength(4);
    const classes = Number(/Name-partition state classes: (\d+)/.exec(result.report)![1]);
    expect(classes).toBeLessThan(50);
    expect(result.report).toContain(`Route B stopped at the first violating class after ${classes} classes (VER-012).`);
    expect(result.report).not.toContain('truncated at');
  }, 60_000);

  it('a quiescence property on the same net still explores to the cap', async () => {
    const { net, m0 } = fig11b();
    const result = await SmtVerifier.forNet(net).mintTransitions(...allMints(net)).initialMarking(m0)
      .property(deadlockFree()).nuMaxClasses(50).verify();
    expect(result.verdict.type, result.report).toBe('unknown');
    expect(result.route).toBe('nu-scg');
    expect(Number(/Name-partition state classes: (\d+)/.exec(result.report)![1])).toBeGreaterThanOrEqual(50);
    expect(result.report).not.toContain('stopped at the first violating class');
  });

  it('a frontier class never looks dead: deadlockFree stays unknown on the truncated graph', async () => {
    // create_order is always enabled, so no reachable class is quiescent; the unexpanded
    // frontier has no successors recorded only because nobody looked.
    const { net, m0 } = fig11b();
    const result = await SmtVerifier.forNet(net).mintTransitions(...allMints(net)).initialMarking(m0)
      .property(deadlockFree()).nuMaxClasses(50).verify();
    expect(result.verdict.type, result.report).toBe('unknown');
    expect(result.route).toBe('nu-scg');
  });

  it('a prefix never proves: a property the prefix does not violate stays unknown', async () => {
    const { net, places, m0 } = fig11b();
    const result = await SmtVerifier.forNet(net).mintTransitions(...allMints(net)).initialMarking(m0)
      .property(placeBound(places.get('order_clerk')!, 100)).nuMaxClasses(50).verify();
    expect(result.verdict.type, result.report).toBe('unknown');
  });
});

/** `mint` reads `c` and adds a token to `p` forever: an untimed net whose graph never closes. */
function unboundedChain() {
  const c = place('c');
  const p = place('p');
  const t = Transition.builder('mint').read(c).outputs(outPlace(p)).action(produces());
  const net = PetriNet.builder('unbounded').transition(t.build()).build();
  return { net, c, p, m0: MarkingState.builder().tokens(c, 1).build() };
}

describe('VER-017 enumeration decides on its explored prefix', () => {
  it('a violation among the explored classes is decided on the enumeration route', async () => {
    const { net, p, m0 } = unboundedChain();
    const result = await SmtVerifier.forNet(net).mintTransitions(...allMints(net)).initialMarking(m0)
      .property(placeBound(p, 2)).enumerationMaxClasses(10).verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.route).toBe('enumeration');
    expect(result.counterexampleTransitions).toEqual(['mint', 'mint', 'mint']);
    expect(result.counterexampleConfirmed).toBe(true);
    expect(result.report).toContain('truncated at 10 classes');
    expect(result.report).toContain(PREFIX);
  });

  it('a cached truncation keeps its prefix: a later query at that budget decides without building', async () => {
    const { net, c, p, m0 } = unboundedChain();
    const cache = new StateSpaceCache();
    const q = (property: ReturnType<typeof placeBound>) => SmtVerifier.forNet(net).linearBound(false).mintTransitions(...allMints(net)).initialMarking(m0)
      .property(property).stateSpaceCache(cache).enumerationMaxClasses(10);
    // Nothing in the first query's prefix violates it: it builds, records the truncation and falls
    // through to the SMT pipeline (a linear bound, or unknown without z3 — only the build matters).
    const before = stateSpaceBuildCount();
    const first = await q(placeBound(c, 1)).verify();
    expect(first.route).not.toBe('enumeration');
    expect(stateSpaceBuildCount() - before).toBe(1);
    const second = await q(placeBound(p, 2)).verify();
    expect(stateSpaceBuildCount() - before).toBe(1);
    expect(second.verdict.type, second.report).toBe('violated');
    expect(second.route).toBe('enumeration');
    expect(second.counterexampleTransitions).toEqual(['mint', 'mint', 'mint']);
    expect(second.report).toContain('cached truncation at 10 classes');
  });
});

describeZ3('VER-023 timed check decides on its explored prefix', () => {
  it('VER-023 AC4: an unbounded timed producer confirms the counterexample in its prefix', async () => {
    // gen: G → G, A at delayed(1), one token on G: the timed graph never closes.
    const G = place('G');
    const A = place('A');
    const gen = Transition.builder('gen').inputs(one(G)).outputs(andPlaces(G, A)).timing(delayed(1))
      .action(produces()).build();
    const net = PetriNet.builder('timed-producer').transition(gen).build();
    const result = await SmtVerifier.forNet(net).mintTransitions(...allMints(net)).initialMarking(m => m.tokens(G, 1))
      .property(placeBound(A, 2)).enumerationMaxClasses(50).timedCounterexampleCheck(true)
      .timeout(30_000).verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleTiming, result.report).toBe('timed-confirmed');
    expect(result.counterexampleTransitions).toEqual(['gen', 'gen', 'gen']);
    expect(result.report).toContain('truncated at 50 classes');
    expect(result.report).toContain('explored prefix');
  });
});

describe('Route B early stop returns the full-graph witness (VER-012)', () => {
  interface Case {
    readonly name: string;
    readonly rows: Parameters<typeof pnidNet>[1];
    readonly marking: ReadonlyArray<readonly [string, number]>;
    readonly property: (p: (n: string) => Place<any>) => SmtProperty;
    readonly carriers?: readonly string[];
  }
  const CASES: Case[] = [
    { name: 'Fig. 11(b) placeBound(order_clerk, 2)', rows: FIG_11B_ROWS, marking: [['clerk', 2]],
      property: p => placeBound(p('order_clerk'), 2) },
    { name: 'Fig. 11(b) mutualExclusion(order, send_done)', rows: FIG_11B_ROWS, marking: [['clerk', 1]],
      property: p => mutualExclusion(p('order'), p('send_done')) },
    { name: 'Fig. 12(c) placeBound(OR, 1)', rows: FIG_12C_ROWS, marking: [['R', 2]],
      property: p => placeBound(p('OR'), 1), carriers: ['P1', 'B1', 'B2', 'C1', 'D1'] },
    { name: 'N1 unreachable(E_done)', rows: N1_CORR_ROWS, marking: [['SUPPLY', 2]],
      property: p => unreachable(new Set([p('E_done')])) },
    { name: 'join chain unreachable(done)', rows: JOIN_CHAIN_ROWS, marking: [['S', 2]],
      property: p => unreachable(new Set([p('done')])) },
  ];
  for (const c of CASES) {
    it(c.name, () => {
      const { net, places } = pnidNet(c.name, c.rows);
      const p = (n: string) => places.get(n)!;
      const m = MarkingState.builder();
      for (const [n, k] of c.marking) m.tokens(p(n), k);
      const m0 = m.build();
      const property = c.property(p);
      const carriers = new Set(c.carriers ?? []);
      const fragment = classify(net, 'extended', carriers, allMints(net))!;

      const full = NameStateClassGraph.build(net, m0, fragment, 2_000, new Set(), undefined, 'none', null, null);
      const target = decide(full, property, new Set(), []);
      expect(target).toBeGreaterThanOrEqual(0);
      const [trace, transitions] = counterexamplePath(full, target);
      expect(transitions.length).toBeGreaterThan(0);

      const early = verifyViaNameScg(
        net, m0, property, new Set(), new Set(), ignore(), 2_000, 'extended', carriers, allMints(net), 'none')!;
      expect(early.verdict.type).toBe('violated');
      expect(early.note).toContain('stopped at the first violating class');
      expect(early.classCount).toBe(target + 1);
      expect(early.transitions).toEqual(transitions);
      expect(early.trace.map(t => t.toString())).toEqual(trace.map(t => t.toString()));
    });
  }
});
