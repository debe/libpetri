import { expect, it } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { placeBound, type SmtProperty } from '../../src/verification/smt-property.js';
import type { Place } from '../../src/core/place.js';
import { describeZ3 } from '../fixtures/z3.js';
import { FIG_12C_ROWS, N1_CORR_ROWS, pnidNet } from '../fixtures/pnid-nets.js';

/**
 * [VER-015] on a ν-net: the linear state-equation bound runs before the name-coloured
 * encoding of [NU-053]. The flat state equation is name-blind, an over-approximation of the
 * ν semantics, so its `proven` is sound; a bound it cannot separate falls through to the
 * coloured query with that query's verdict.
 */

function verifier(
  rows: Parameters<typeof pnidNet>[1],
  marking: ReadonlyArray<readonly [string, number]>,
  property: (p: (n: string) => Place<any>) => SmtProperty,
  budgets: readonly string[],
  carriers: readonly string[] = [],
) {
  const { net, places } = pnidNet('lb', rows);
  const p = (n: string) => places.get(n)!;
  const m = MarkingState.builder();
  for (const [n, k] of marking) m.tokens(p(n), k);
  return SmtVerifier.forNet(net)
    .enumerationMaxClasses(0)
    .initialMarking(m.build())
    .property(property(p))
    .budgetPlaces(...budgets.map(p))
    .carrierPlaces(...carriers.map(p))
    .fragmentMode('extended');
}

// PNID Fig. 6(a) N1 at budget 2: Route A's colour-slot bound is k=6, and the coloured IC3
// query ran into its full 8 s timeout on this trivially true bound.
const n1Bound = () => verifier(N1_CORR_ROWS, [['SUPPLY', 2]], p => placeBound(p('Y1'), 1000), ['SUPPLY']);

it('encodeScripts emits the bound script alongside the coloured encoding', () => {
  const scripts = n1Bound().encodeScripts();
  expect(scripts.coloured).toBe(true);
  expect(scripts.bound).not.toBeNull();
});

describeZ3('VER-015 before the name-coloured encoding (NU-053)', () => {
  it('PNID N1: placeBound(Y1, 1000) at budget 2 is proven structurally, in milliseconds', async () => {
    const t0 = performance.now();
    const result = await n1Bound().timeout(8_000).verify();
    const elapsed = performance.now() - t0;
    expect(result.verdict.type, result.report).toBe('proven');
    expect(result.route).toBe('structural');
    expect(result.report).toContain('PROVEN (structural)');
    expect(result.report).toContain('(VER-015)');
    expect(elapsed).toBeLessThan(1_000);
  }, 30_000);

  it('a bound the linear bound cannot separate reaches the coloured encoding with the same verdict', async () => {
    const run = (linear: boolean) => verifier(
      FIG_12C_ROWS, [['R', 2]], p => placeBound(p('OR'), 1), ['R'], ['P1', 'B1', 'B2', 'C1', 'D1'],
    ).linearBound(linear).timeout(30_000).verify();
    const withBound = await run(true);
    const without = await run(false);
    expect(withBound.verdict.type, withBound.report).toBe('violated');
    expect(withBound.verdict).toEqual(without.verdict);
    expect(withBound.route).toBe('smt');
    expect(withBound.route).toBe(without.route);
    expect(withBound.counterexampleTransitions).toEqual(without.counterexampleTransitions);
    expect(withBound.report).toContain('Linear state-equation bound: none separates the violation');
    expect(withBound.report).toContain('name-coloured');
  }, 60_000);
});
