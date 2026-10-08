import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { deadlockFree, placeBound, unreachable } from '../../src/verification/smt-property.js';
import { arrivals, bounded } from '../../src/verification/analysis/environment-analysis-mode.js';
import { StateClassGraph } from '../../src/verification/analysis/state-class-graph.js';
import { closeArrivals } from '../../src/verification/open-net/closure.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { environmentPlace, place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { andPlaces, outPlace } from '../../src/core/out.js';
import { matchKey, matchSpec } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { produces } from '../fixtures/producing-actions.js';
import { describeZ3 } from '../fixtures/z3.js';

/**
 * [VER-006] `arrivals(k)`: at most `k` tokens injected into each environment place over the whole
 * run, by the [VER-022] optional closure rewrite (`env:optional[i]` holding `k`,
 * `env:arrive?[i]:P`, `env:decline[i]`).
 */

const IN = place<string>('IN');
const OUT = place<string>('OUT');
const ENV_IN = environmentPlace<string>('IN');

/** `env IN → T → OUT`. */
function forward(): PetriNet {
  return PetriNet.builder('forward')
    .transition(Transition.builder('T').inputs(one(IN)).outputs(outPlace(OUT)).action(produces()).build())
    .build();
}

const verifier = (k: number) => SmtVerifier.forNet(forward()).environmentPlaces(ENV_IN).environmentMode(arrivals(k));

describe('arrivals(k) (VER-006 AC9)', () => {
  it('placeBound(OUT, k) is proven: the total injected is k', async () => {
    const result = await verifier(2).property(placeBound(OUT, 2)).verify();
    expect(result.verdict.type, result.report).toBe('proven');
    // The closed net is untimed, so the linear bound runs ahead of the enumeration (VER-015 AC7).
    expect(result.route).toBe('structural');
    expect(result.report).toContain('arrivals(2)');
    expect(result.report).toContain('env:arrive?[0]:IN from env:optional[0] (at most 2)');
  });

  it('placeBound(OUT, k - 1) is violated by k arrivals, each named in the trace', async () => {
    const result = await verifier(2).property(placeBound(OUT, 1)).verify();
    expect(result.verdict.type, result.report).toBe('violated');
    const steps = result.counterexampleTransitions;
    expect(steps.filter(t => t === 'env:arrive?[0]:IN')).toHaveLength(2);
    expect(steps.filter(t => t === 'T')).toHaveLength(2);
  });

  it('deadlockFree with OUT a sink is decided without the always-available vacuity note', async () => {
    const result = await verifier(2).property(deadlockFree()).sinkPlaces(OUT).verify();
    expect(result.verdict.type, result.report).toBe('proven');
    expect(result.report).not.toContain('vacuous');
  });

  it('a run may rest after fewer than k arrivals: quiescence means at most k, not exactly k', async () => {
    // OUT holds exactly 2 at rest only if every arrival happened; with declines a run can rest
    // after 0 or 1 arrival, so "OUT is 2 at quiescence" is violated.
    const { quiescentCount } = await import('../../src/verification/smt-property.js');
    const result = await verifier(2).property(quiescentCount(new Set([OUT]), 2, 2)).verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.counterexampleTransitions).toContain('env:decline[0]');
    expect(result.counterexampleTransitions.filter(t => t === 'env:arrive?[0]:IN').length).toBeLessThan(2);
  });

  it('arrivals(k, k) is exact: every arrival happens before the net rests', async () => {
    const { quiescentCount } = await import('../../src/verification/smt-property.js');
    const exact = SmtVerifier.forNet(forward()).environmentPlaces(ENV_IN).environmentMode(arrivals(2, 2));
    const result = await exact.property(quiescentCount(new Set([OUT]), 2, 2)).sinkPlaces(OUT).verify();
    expect(result.verdict.type, result.report).toBe('proven');
    expect(result.report).toContain(
      'Environment: arrivals(2..2) — net closed before any route: env:arrive[0]:IN from env:arrivals[0] (exactly 2) (VER-006)',
    );
  });

  it('arrivals(min, max): min mandatory, max - min optional', async () => {
    const { quiescentCount } = await import('../../src/verification/smt-property.js');
    const between = () => SmtVerifier.forNet(forward()).environmentPlaces(ENV_IN).environmentMode(arrivals(1, 3));
    const atLeastOne = await between().property(quiescentCount(new Set([OUT]), 1, 3)).sinkPlaces(OUT).verify();
    expect(atLeastOne.verdict.type, atLeastOne.report).toBe('proven');
    expect(atLeastOne.report).toContain(
      'Environment: arrivals(1..3) — net closed before any route: env:arrive[0]:IN from env:arrivals[0] (exactly 1), ' +
      'env:arrive?[0]:IN from env:optional[0] (at most 2) (VER-006)',
    );
    const three = await between().property(quiescentCount(new Set([OUT]), 3, 3)).sinkPlaces(OUT).verify();
    expect(three.verdict.type, three.report).toBe('violated');
    expect(three.counterexampleTransitions).toContain('env:decline[0]');
  });

  it('arrivals(k) is arrivals(0, k); bad bounds are refused', () => {
    expect(arrivals(3)).toEqual(arrivals(0, 3));
    expect(() => arrivals(-1, 2)).toThrow(/0 <= minTokens <= maxTokens/);
    expect(() => arrivals(3, 2)).toThrow(/0 <= minTokens <= maxTokens/);
    expect(() => arrivals(1.5, 2)).toThrow(/whole bounds/);
  });

  it('the (min, max) rewrite omits an empty source with its transitions', () => {
    const exact = closeArrivals(forward(), MarkingState.empty(), [IN], 2, 2);
    expect([...exact.net.transitions].map(t => t.name).sort()).toEqual(['T', 'env:arrive[0]:IN']);
    expect(exact.initialMarking.placesWithTokens().map(p => [p.name, exact.initialMarking.tokens(p)]))
      .toEqual([['env:arrivals[0]', 2]]);
    const mixed = closeArrivals(forward(), MarkingState.empty(), [IN], 1, 3);
    expect([...mixed.net.transitions].map(t => t.name).sort())
      .toEqual(['T', 'env:arrive?[0]:IN', 'env:arrive[0]:IN', 'env:decline[0]']);
    expect(mixed.initialMarking.placesWithTokens().map(p => [p.name, mixed.initialMarking.tokens(p)]))
      .toEqual([['env:arrivals[0]', 1], ['env:optional[0]', 2]]);
  });

  it('arrivals(0) injects nothing', async () => {
    const result = await verifier(0).property(unreachable(new Set([OUT]))).verify();
    expect(result.verdict.type, result.report).toBe('proven');
  });

  it('the rewrite is the VER-022 closure: a source per environment place, in registration order', () => {
    const a = place('A');
    const b = place('B');
    const net = PetriNet.builder('two')
      .transition(Transition.builder('t').inputs(one(a), one(b)).outputs(outPlace(OUT)).action(produces()).build())
      .build();
    const closed = closeArrivals(net, MarkingState.empty(), [b, a], 3);
    const names = [...closed.net.transitions].map(t => t.name).sort();
    expect(names).toEqual(['env:arrive?[0]:B', 'env:arrive?[1]:A', 'env:decline[0]', 'env:decline[1]', 't']);
    const sources = closed.initialMarking.placesWithTokens().map(p => [p.name, closed.initialMarking.tokens(p)]);
    expect(sources).toEqual([['env:optional[0]', 3], ['env:optional[1]', 3]]);
  });

  it('the graph builders refuse the mode: only the verifier applies the rewrite', () => {
    expect(() => StateClassGraph.build(forward(), MarkingState.empty(), 100, new Set([ENV_IN]), arrivals(1)))
      .toThrow(/arrivals\(k\) is a net rewrite/);
  });
});

describeZ3('arrivals(k) against bounded(k) (VER-006 AC9)', () => {
  it('bounded(k) caps the resident tokens only, so both bounds are violated', async () => {
    for (const bound of [2, 1]) {
      const result = await SmtVerifier.forNet(forward()).environmentPlaces(ENV_IN).environmentMode(bounded(2))
        .property(placeBound(OUT, bound)).timeout(30_000).verify();
      expect(result.verdict.type, result.report).toBe('violated');
    }
  });
});

describe('arrivals(k) into a coloured place (VER-006 AC10)', () => {
  it('no ν route treats an arrival as a mint: Route B declines naming the place', async () => {
    // Environment place `a` is a match key of `join`: an injected token's name is unknown, so
    // two arrivals may share one — a mint would make them distinct and hide the join.
    const a = place<string>('a');
    const envA = environmentPlace<string>('a');
    const src = place<string>('src');
    const b = place<string>('b');
    const merged = place<string>('merged');
    const key = (p: typeof a) => matchKey(p, (v: string) => nameId(v));
    const net = PetriNet.builder('coloured-arrival')
      .transition(Transition.builder('fork').inputs(one(src)).outputs(andPlaces(b)).action(produces()).build())
      .transition(Transition.builder('join').inputs(one(a), one(b)).outputs(outPlace(merged))
        .match(matchSpec(key(a), key(b))).action(produces()).build())
      .build();
    const result = await SmtVerifier.forNet(net).initialMarking(m => m.tokens(src, 1))
      .environmentPlaces(envA).environmentMode(arrivals(1))
      .property(deadlockFree()).sinkPlaces(merged).verify();
    expect(result.verdict.type, result.report).toBe('unknown');
    expect(result.route).toBe('nu-scg');
    expect((result.verdict as { reason: string }).reason).toContain("environment place 'a'");
    expect((result.verdict as { reason: string }).reason).toContain('not a fresh mint');
  });
});
