import { describe, it, expect } from 'vitest';
import { describeZ3 } from '../fixtures/z3.js';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { deadlockFree, mutualExclusion, placeBound, unreachable } from '../../src/verification/smt-property.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { alwaysAvailable } from '../../src/verification/analysis/environment-analysis-mode.js';
import {
  checkLinearBoundExact, decodeLinearBound, encodeLinearBound, formatLinearBound, formatLinearDemand, violationDemand,
} from '../../src/verification/z3/linear-bound.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { place } from '../../src/core/place.js';
import { one, all } from '../../src/core/in.js';
import { andPlaces, outPlace, xor } from '../../src/core/out.js';
import { produces } from '../fixtures/producing-actions.js';

/**
 * VER-015 linear state-equation bound.
 *
 * A fork that may halt instead: p0(1) → f → AND(a, b) | halt; a → ga → ra; b → gb → rb;
 * join: ra + rb → done. `{ra, rb, halt}` is unreachable — a halt consumes the token
 * that would have fed both arms — and no EQUALITY law says so (the halt branch turns
 * 2 units into 1), so the null-space basis cannot exclude it. The decreasing law
 * 2·p0 + a + b + ra + rb + halt + 2·done ≤ 2 does: the target needs 3.
 */
function forkOrHalt() {
  const p0 = place('p0'), a = place('a'), b = place('b'), ra = place('ra'), rb = place('rb');
  const halt = place('halt'), done = place('done');
  const f = Transition.builder('f').inputs(one(p0)).outputs(xor(andPlaces(a, b), outPlace(halt))).action(produces()).build();
  const ga = Transition.builder('ga').inputs(one(a)).outputs(outPlace(ra)).action(produces()).build();
  const gb = Transition.builder('gb').inputs(one(b)).outputs(outPlace(rb)).action(produces()).build();
  const join = Transition.builder('join').inputs(one(ra), one(rb)).outputs(outPlace(done)).action(produces()).build();
  const net = PetriNet.builder('forkOrHalt').transitions(f, ga, gb, join).build();
  const m0 = MarkingState.builder().tokens(p0, 1).build();
  return { net, m0, p0, a, b, ra, rb, halt, done };
}

describe('linear state-equation bound (VER-015) — encoding', () => {
  it('has no demand for the quiescence properties', () => {
    const { net, m0 } = forkOrHalt();
    const flat = flatten(net, new Set(), alwaysAvailable());
    expect(violationDemand(flat, deadlockFree())).toBeNull();
    expect(encodeLinearBound(flat, m0, deadlockFree())).toBeNull();
  });

  it('encodes y >= 0, one row per flat transition, and the demand against y.M0 + 1', () => {
    const { net, m0, ra, rb, halt } = forkOrHalt();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const idx = (p: { name: string }) => flat.placeIndex.get(p.name)!;
    const script = encodeLinearBound(flat, m0, unreachable(new Set([ra, rb, halt])))!;
    expect(script).toContain('(set-logic QF_LIA)');
    for (let p = 0; p < flat.places.length; p++) {
      expect(script).toContain(`(declare-const y${p} Int)`);
      expect(script).toContain(`(assert (>= y${p} 0))`);
    }
    // f's halt branch: -p0 + halt, places in flat-index order
    const haltRow = [idx(halt), idx(place('p0'))].sort((x, y) => x - y)
      .map(i => (i === idx(place('p0')) ? `(- y${i})` : `y${i}`)).join(' ');
    expect(script).toContain(`(assert (<= (+ ${haltRow}) 0))`);
    // Demand: ra + rb + halt >= 1 + p0
    const d = [idx(ra), idx(rb), idx(halt)].sort((x, y) => x - y).map(i => `y${i}`).join(' ');
    expect(script).toContain(`(assert (>= (+ ${d}) (+ 1 y${idx(place('p0'))})))`);
    expect(script.endsWith('(check-sat)\n(get-model)')).toBe(true);
  });

  it('pins consume-all places to zero weight (H1)', () => {
    const q = place('q'), r = place('r');
    const t = Transition.builder('t').inputs(all(q)).outputs(outPlace(r)).action(produces()).build();
    const net = PetriNet.builder('drain').transitions(t).build();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const script = encodeLinearBound(flat, MarkingState.builder().tokens(q, 2).build(), placeBound(r, 1))!;
    expect(script).toContain(`(assert (= y${flat.placeIndex.get('q')} 0))`);
    // A weighting that leans on the drained place is rejected by the exact check.
    const y = new Array<bigint>(flat.places.length).fill(0n);
    y[flat.placeIndex.get('q')!] = 1n;
    y[flat.placeIndex.get('r')!] = 1n;
    expect(checkLinearBoundExact(flat, MarkingState.builder().tokens(q, 2).build(), placeBound(r, 1), y)).toBeNull();
  });

  it('decodes a model and re-checks it exactly', () => {
    const { net, m0, p0, a, b, ra, rb, halt, done } = forkOrHalt();
    const flat = flatten(net, new Set(), alwaysAvailable());
    const idx = (p: { name: string }) => flat.placeIndex.get(p.name)!;
    const model = [
      'sat', '(', `  (define-fun y${idx(p0)} () Int\n    2)`, `  (define-fun y${idx(a)} () Int 1)`,
      `  (define-fun y${idx(b)} () Int 1)`, `  (define-fun y${idx(ra)} () Int 1)`, `  (define-fun y${idx(rb)} () Int 1)`,
      `  (define-fun y${idx(halt)} () Int 1)`, `  (define-fun y${idx(done)} () Int 2)`, ')',
    ].join('\n');
    const y = decodeLinearBound(model, flat.places.length)!;
    expect(y[idx(p0)]).toBe(2n);
    const bound = checkLinearBoundExact(flat, m0, unreachable(new Set([ra, rb, halt])), y)!;
    expect(bound).not.toBeNull();
    expect(bound.constant).toBe(2n);
    expect(bound.demandValue).toBe(3n);
    expect(formatLinearBound(flat, bound)).toBe('a + b + 2*done + halt + 2*p0 + ra + rb <= 2');
    expect(formatLinearDemand(flat, unreachable(new Set([ra, rb, halt])), bound)).toBe('halt + ra + rb >= 3');
    // A weighting that is not decreasing under the fork is rejected.
    const bad = [...y];
    bad[idx(p0)] = 1n;
    expect(checkLinearBoundExact(flat, m0, unreachable(new Set([ra, rb, halt])), bad)).toBeNull();
    // A weighting whose demand does not exceed the constant is rejected.
    expect(checkLinearBoundExact(flat, m0, unreachable(new Set([ra, halt])), y)).toBeNull();
    // Negative literals decode.
    expect(decodeLinearBound('sat\n(\n  (define-fun y0 () Int\n    (- 3))\n)', 1)![0]).toBe(-3n);
    expect(decodeLinearBound('sat\n(\n)', 1)).toBeNull();
  });
});

describeZ3('linear state-equation bound (VER-015) — end to end', () => {
  it('proves an unreachable marking structurally when no equality law excludes it', async () => {
    const { net, m0, ra, rb, halt } = forkOrHalt();
    const result = await SmtVerifier.forNet(net)
      .enumerationMaxClasses(0).initialMarking(m0)
      .property(unreachable(new Set([ra, rb, halt]))).timeout(30_000).verify();
    expect(result.verdict.type, result.report).toBe('proven');
    expect(result.verdict.type === 'proven' && result.verdict.method).toBe('structural');
    // The solver is free to pick any separating weighting; the report names it and
    // the exact re-check vouched for it.
    expect(result.report).toMatch(/Linear state-equation bound: .* <= \d+; violation needs .* >= \d+/);
    expect(result.report).toContain('Status: bound excludes every violating marking (re-checked in exact integer arithmetic)');
    expect(result.report).toContain('PROVEN (structural)');
    expect(result.report).not.toContain('Phase 5');
  });

  it('hands over to the fixpoint query when no bound separates a reachable target', async () => {
    const { net, m0, ra, rb } = forkOrHalt();
    const result = await SmtVerifier.forNet(net)
      .enumerationMaxClasses(0).initialMarking(m0)
      .property(mutualExclusion(ra, rb)).timeout(30_000).verify();
    expect(result.verdict.type, result.report).toBe('violated');
    expect(result.report).toContain('Linear state-equation bound: none separates the violation');
    expect(result.counterexampleConfirmed).toBe(true);
  });

  it('encodeScripts() reports the bound query for reachability-safety and null otherwise', () => {
    const { net, m0, ra, rb, halt } = forkOrHalt();
    const scripts = SmtVerifier.forNet(net)
      .enumerationMaxClasses(0).initialMarking(m0).property(unreachable(new Set([ra, rb, halt]))).encodeScripts();
    expect(scripts.bound).toContain('(set-logic QF_LIA)');
    const none = SmtVerifier.forNet(net)
      .enumerationMaxClasses(0).initialMarking(m0).property(deadlockFree()).encodeScripts();
    expect(none.bound).toBeNull();
  });
});
