import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { deadlockFree, placeBound } from '../../src/verification/smt-property.js';
import type { SmtVerificationResult } from '../../src/verification/smt-verification-result.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { andPlaces, outPlace } from '../../src/core/out.js';
import { produces } from '../fixtures/producing-actions.js';

/**
 * VER-024: stubborn-set reduction of the enumeration route.
 *
 * `fork: start → s0_0 … s(k-1)_0`, then per subnet `i` a cycle (or, with `chain`, a chain ending
 * in `s(i)_n`) `s(i)_j → s(i)_(j+1)`.
 */
function forked(k: number, n: number, chain: boolean) {
  const start = place('start');
  const s = (i: number, j: number) => place(`s${i}_${j}`);
  const b = PetriNet.builder(`fork-${k}x${n}${chain ? '-chain' : ''}`);
  b.transition(Transition.builder('fork').inputs(one(start))
    .outputs(andPlaces(...Array.from({ length: k }, (_, i) => s(i, 0)))).action(produces()).build());
  for (let i = 0; i < k; i++) {
    for (let j = 0; j < n; j++) {
      const to = chain ? s(i, j + 1) : s(i, (j + 1) % n);
      b.transition(Transition.builder(`t${i}_${j}`).inputs(one(s(i, j))).outputs(outPlace(to)).action(produces()).build());
    }
  }
  const ends: Place<any>[] = Array.from({ length: k }, (_, i) => s(i, n));
  return { net: b.build(), m0: MarkingState.builder().tokens(start, 1).build(), ends };
}

function classes(result: SmtVerificationResult): number {
  const m = /State classes: (\d+)/.exec(result.report);
  if (m === null) throw new Error(`no class count\n${result.report}`);
  return Number(m[1]);
}

describe('stubborn-set reduction of the enumeration route (VER-024)', () => {
  it('closes k independent cycles in 1 + n classes instead of 1 + n^k (AC2)', async () => {
    const { net, m0 } = forked(3, 4, false);
    const reduced = await SmtVerifier.forNet(net).initialMarking(m0).property(deadlockFree()).verify();
    const full = await SmtVerifier.forNet(net).initialMarking(m0).property(deadlockFree())
      .partialOrderReduction(false).verify();
    expect(reduced.verdict.type, reduced.report).toBe('proven');
    expect(full.verdict.type, full.report).toBe('proven');
    expect(reduced.route).toBe('enumeration');
    expect(classes(reduced)).toBe(1 + 4);
    expect(classes(full)).toBe(1 + 4 ** 3);
    expect(reduced.report).toContain('  Stubborn-set reduction (VER-024): on');
    expect(full.report).not.toContain('Stubborn-set reduction');
  });

  it('keeps every dead marking: a chain end is a violation, proven once the ends are sinks (AC1)', async () => {
    const { net, m0, ends } = forked(3, 3, true);
    const violated = await SmtVerifier.forNet(net).initialMarking(m0).property(deadlockFree()).verify();
    expect(violated.verdict.type, violated.report).toBe('violated');
    expect(violated.counterexampleTransitions).toHaveLength(1 + 3 * 3);
    expect(violated.counterexampleConfirmed).toBe(true);
    expect(classes(violated)).toBe(2 + 3 * 3);
    const proven = await SmtVerifier.forNet(net).initialMarking(m0).property(deadlockFree())
      .sinkPlaces(...ends).verify();
    expect(proven.verdict.type, proven.report).toBe('proven');
  });

  it('treats a reset and a deposit on one place as dependent', async () => {
    // `a_produce` deposits into r, `b_reset` empties it. Firing `b_reset` last leaves r empty,
    // firing it first strands the token `a_produce` deposits later: only that order violates.
    const x = place('x'), y = place('y'), r = place('r'), done = place('done');
    const net = PetriNet.builder('reset-vs-deposit').transitions(
      Transition.builder('a_produce').inputs(one(x)).outputs(outPlace(r)).action(produces()).build(),
      Transition.builder('b_reset').inputs(one(y)).reset(r).outputs(outPlace(done)).action(produces()).build(),
    ).build();
    const m0 = MarkingState.builder().tokens(x, 1).tokens(y, 1).build();
    // Atomic firing: the reset would otherwise split `a_produce` in flight (VER-004).
    const q = (reduce: boolean) => SmtVerifier.forNet(net).initialMarking(m0).property(deadlockFree())
      .sinkPlaces(done).assumeAtomicFiring(true).partialOrderReduction(reduce).verify();
    const [reduced, full] = await Promise.all([q(true), q(false)]);
    expect(full.verdict.type, full.report).toBe('violated');
    expect(reduced.verdict.type, reduced.report).toBe('violated');
    expect(reduced.counterexampleTransitions).toEqual(['b_reset', 'a_produce']);
  });

  it('leaves a safety property on the full graph (AC3)', async () => {
    const { net, m0 } = forked(3, 4, false);
    const result = await SmtVerifier.forNet(net).initialMarking(m0).property(placeBound(place('s0_0'), 1))
      .linearBound(false).verify();
    expect(result.verdict.type, result.report).toBe('proven');
    expect(result.route).toBe('enumeration');
    expect(classes(result)).toBe(1 + 4 ** 3);
    expect(result.report).not.toContain('Stubborn-set reduction');
  });
});
