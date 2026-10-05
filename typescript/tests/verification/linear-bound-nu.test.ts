import { expect, it } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { placeBound, type SmtProperty } from '../../src/verification/smt-property.js';
import type { Place } from '../../src/core/place.js';
import { describeZ3 } from '../fixtures/z3.js';
import { FIG_12C_ROWS, N1_CORR_ROWS, pnidNet } from '../fixtures/pnid-nets.js';
import { produces } from '../fixtures/producing-actions.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { and, outPlace } from '../../src/core/out.js';
import { matchKey, matchSpec } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';

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

/**
 * The report line the coloured plan's slot bound writes, and only it (the ν-encoding line
 * spells it `colour-slot bound`, lower case and without the colon).
 */
const SLOT_BOUND = 'Colour-slot bound: ';

const occurrences = (text: string, needle: string): number => text.split(needle).length - 1;

describeZ3('VER-015 before the name-coloured encoding (NU-053)', () => {
  it('PNID N1: placeBound(Y1, 1000) at budget 2 is proven structurally, in milliseconds', async () => {
    const t0 = performance.now();
    const result = await n1Bound().timeout(8_000).verify();
    const elapsed = performance.now() - t0;
    expect(result.verdict.type, result.report).toBe('proven');
    expect(result.route).toBe('structural');
    expect(result.report).toContain('PROVEN (structural)');
    expect(result.report).toContain('(VER-015)');
    // The coloured plan is built after the bound, so a structural Proven never runs its
    // slot-bound simplex, and nothing enumerates semiflows.
    expect(result.report).not.toContain(SLOT_BOUND);
    expect(result.report).not.toContain('semiflow');
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
    expect(withBound.report).toContain('ν-encoding: name-coloured (colour-slot bound k=6;');
    expect(withBound.report).toContain('  Colour-slot bound: LP optimum 6 over ');
    expect(withBound.report).toContain(', so k=6 (re-checked in exact arithmetic)\n');
    expect(occurrences(withBound.report, SLOT_BOUND), withBound.report).toBe(1);
    expect(withBound.report).not.toContain('semiflow');
  }, 60_000);

  it('a ν-net outside the fragment through an undeclared mint never solves the slot bound', async () => {
    // mA: budget, S1 -> A mints (it consumes the declared budget); mB: S2 -> B writes the
    // other coloured place without consuming a budget or being named (NU-010), so the
    // coloured plan refuses in its classification and the slot bound must never be solved, so
    // its report line never appears.
    const [budget, s1, s2, a, b, done] = ['budget', 'S1', 'S2', 'A', 'B', 'DONE'].map(n => place<string>(n));
    const net = PetriNet.builder('undeclared_mint').transitions(
      Transition.builder('mA').inputs(one(budget!), one(s1!)).outputs(outPlace(a!)).action(produces()).build(),
      Transition.builder('mB').inputs(one(s2!)).outputs(outPlace(b!)).action(produces()).build(),
      Transition.builder('J').inputs(one(a!), one(b!))
        .match(matchSpec(matchKey(a!, (x: string) => nameId(x)), matchKey(b!, (x: string) => nameId(x))))
        .outputs(and(outPlace(done!), outPlace(budget!))).action(produces()).build(),
    ).build();
    const run = (mints: readonly string[]) => SmtVerifier.forNet(net)
      .enumerationMaxClasses(0)
      .initialMarking(m => m.tokens(budget!, 1).tokens(s1!, 1).tokens(s2!, 1))
      .property(placeBound(done!, 0))
      .budgetPlaces(budget!)
      .mintTransitions(...mints)
      .linearBound(false)
      .timeout(30_000)
      .verify();
    const result = await run([]);
    expect(result.route, result.report).toBe('smt');
    expect(result.report).toContain('IC3/PDR');
    expect(result.report).not.toContain('ν-encoding: name-coloured');
    expect(result.report).not.toContain(SLOT_BOUND);
    expect(result.report).not.toContain('semiflow');
    // Declaring mB a mint admits the plan, and the line is there once, which is what makes
    // its absence above mean something. S2 weighs at least B, and S1 plus the budget at least
    // A: optimum 2 over A, B, S1, S2 and the budget, and the three rows producing into them.
    const declared = await run(['mB']);
    expect(declared.report).toContain('ν-encoding: name-coloured (colour-slot bound k=2;');
    expect(declared.report).toContain(
      '\n  Colour-slot bound: LP optimum 2 over 5 places and 3 transitions, so k=2 (re-checked in exact arithmetic)\n',
    );
    expect(occurrences(declared.report, SLOT_BOUND), declared.report).toBe(1);
    expect(declared.report).not.toContain('semiflow');
  }, 60_000);
});
