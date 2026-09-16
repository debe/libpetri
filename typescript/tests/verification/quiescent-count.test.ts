import { describe, it, expect } from 'vitest';
import { describeZ3 } from '../fixtures/z3.js';
import { produces } from '../fixtures/producing-actions.js';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { propertyDescription, quiescentCount } from '../../src/verification/smt-property.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { encodePropertyViolation, resolveEnvInjection } from '../../src/verification/z3/smt-encoder.js';
import { satisfiesBad } from '../../src/verification/z3/abstract-replayer.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { andPlaces, outPlace } from '../../src/core/out.js';

/**
 * VER-002 QuiescentCount: a token count at every quiescent marking, its lower bound waived
 * while a marker holds a token.
 *
 * Two jobs share a budget of two: `start` takes a unit, `finish` refunds it. With `abort`
 * a running job may stop the run instead, keeping its unit; `start` is inhibited by `halt`.
 * Flat place order: budget, done, halt, jobs, running.
 */
const budget = place('budget'), done = place('done'), halt = place('halt');
const jobs = place('jobs'), running = place('running');

function jobsNet(opts: { refund?: boolean; abort?: boolean } = {}) {
  const t = (name: string) => Transition.builder(name).action(produces());
  const transitions = [
    t('start').inputs(one(jobs), one(budget)).inhibitor(halt).outputs(outPlace(running)).build(),
    t('finish').inputs(one(running))
      .outputs(opts.refund === false ? outPlace(done) : andPlaces(budget, done)).build(),
  ];
  if (opts.abort === true) transitions.push(t('abort').inputs(one(running)).outputs(outPlace(halt)).build());
  return PetriNet.builder('jobs').transitions(...transitions).build();
}
const m0 = MarkingState.builder().tokens(jobs, 2).tokens(budget, 2).build();

describe('QuiescentCount (VER-002): the property', () => {
  it('validates its bounds and describes itself', () => {
    expect(() => quiescentCount([budget], 2, 1)).toThrow(/0 <= min <= max/);
    expect(() => quiescentCount([budget], -1, 1)).toThrow();
    expect(propertyDescription(quiescentCount([budget], 2, 2, [halt])))
      .toBe('Quiescent count: exactly 2 across {budget}; lower bound waived while {halt} is marked');
    expect(propertyDescription(quiescentCount([budget, done], 1, Infinity)))
      .toBe('Quiescent count: at least 1 across {budget, done}');
  });

  it('encodes the count clause on top of quiescence, places and waivers in index order', () => {
    const flat = flatten(jobsNet({ abort: true }));
    const mVars = flat.places.map((_, i) => `m${i}`);
    const encode = (min: number, max: number, waivedBy = [halt]) =>
      encodePropertyViolation(flat, quiescentCount([done, budget], min, max, waivedBy), mVars, new Set(), resolveEnvInjection(flat));
    expect(encode(1, 3)).toContain('(or (and (< (+ m0 m1) 1) (= m2 0)) (> (+ m0 m1) 3))');
    expect(encode(2, Infinity, [])).toContain('(< (+ m0 m1) 2)');
    expect(encode(0, 2)).toContain('(> (+ m0 m1) 2)');
    expect(encode(0, Infinity)).toBe('false');
  });

  it('is decided by the replayer exactly as the encoder states it', () => {
    const flat = flatten(jobsNet({ abort: true }));
    const bad = (state: number[], min: number, max: number, waivedBy = [halt]) =>
      satisfiesBad(state, flat, quiescentCount([budget], min, max, waivedBy), new Set());
    // [budget, done, halt, jobs, running]
    expect(bad([0, 2, 0, 0, 0], 2, 2)).toBe(true);          // quiescent, below, no waiver
    expect(bad([1, 1, 1, 0, 0], 2, 2)).toBe(false);         // below, but halt waives it
    expect(bad([1, 1, 1, 0, 0], 2, 2, [])).toBe(true);      // below, nothing waives it
    expect(bad([3, 0, 0, 0, 0], 2, 2)).toBe(true);          // above: an upper bound is never waived
    expect(bad([2, 0, 0, 1, 0], 0, 1)).toBe(false);         // not quiescent: start is enabled
    expect(bad([2, 2, 0, 0, 0], 2, 2)).toBe(false);         // meets it
  });
});

describe('QuiescentCount (VER-002): the enumeration route', () => {
  const verify = (net: PetriNet, min: number, max: number, waivedBy = [halt]) =>
    SmtVerifier.forNet(net).initialMarking(m0).property(quiescentCount([budget], min, max, waivedBy))
      .timeout(30_000).verify();

  it('proves a refunded budget, and finds the one a job keeps', async () => {
    const proven = await verify(jobsNet(), 2, 2);
    expect(proven.verdict.type, proven.report).toBe('proven');
    expect(proven.route).toBe('enumeration');

    const kept = await verify(jobsNet({ refund: false }), 2, 2);
    expect(kept.verdict.type, kept.report).toBe('violated');
    expect(kept.counterexampleTrace.at(-1)!.tokens(budget)).toBeLessThan(2);
  });

  it('waives the lower bound while the marker is marked, and only then', async () => {
    const waived = await verify(jobsNet({ abort: true }), 2, 2);
    expect(waived.verdict.type, waived.report).toBe('proven');
    const strict = await verify(jobsNet({ abort: true }), 2, 2, []);
    expect(strict.verdict.type, strict.report).toBe('violated');
    expect(strict.counterexampleTrace.at(-1)!.hasTokens(halt)).toBe(true);
  });
});

describeZ3('QuiescentCount (VER-002): the SMT routes agree', () => {
  const verify = (net: PetriNet, min: number, max: number, configure = (v: SmtVerifier) => v) =>
    configure(SmtVerifier.forNet(net).initialMarking(m0).property(quiescentCount([budget], min, max, [halt]))
      .enumerationMaxClasses(0).timeout(30_000)).verify();

  it('the state-equation phase decides it, proof and witness', async () => {
    const proven = await verify(jobsNet({ abort: true }), 2, 2);
    expect(proven.verdict.type, proven.report).toBe('proven');
    expect(proven.verdict.type === 'proven' && proven.verdict.method).toBe('state-equation');

    const kept = await verify(jobsNet({ refund: false }), 2, 2);
    expect(kept.verdict.type, kept.report).toBe('violated');
    expect(kept.counterexampleConfirmed).toBe(true);
  }, 120_000);

  it('IC3 decides it too, and its certificate passes the check', async () => {
    const pinned = (v: SmtVerifier) => v.stateEquationPhase(false).firingBound(false);
    const proven = await verify(jobsNet({ abort: true }), 2, 2, pinned);
    expect(proven.verdict.type, proven.report).toBe('proven');
    expect(proven.verdict.type === 'proven' && proven.verdict.method).toBe('IC3/PDR');

    const kept = await verify(jobsNet({ refund: false }), 2, 2, pinned);
    expect(kept.verdict.type, kept.report).toBe('violated');
  }, 120_000);

  it('refuses a count over a place the net does not declare', async () => {
    const r = await SmtVerifier.forNet(jobsNet()).initialMarking(m0)
      .property(quiescentCount([place('ghost')], 1, 1)).timeout(30_000).verify();
    expect(r.verdict.type).toBe('unknown');
    expect(r.verdict.type === 'unknown' && r.verdict.reason).toContain("'ghost'");
  }, 60_000);
});
