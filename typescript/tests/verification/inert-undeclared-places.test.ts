import { expect, it } from 'vitest';
import { SmtVerifier, withInertMarkedPlaces } from '../../src/verification/smt-verifier.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { deadlockFree, placeBound, type SmtProperty } from '../../src/verification/smt-property.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import { IncidenceMatrix } from '../../src/verification/encoding/incidence-matrix.js';
import { computePInvariants } from '../../src/verification/invariant/p-invariant-computer.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { transform } from '../../src/core/transition-action.js';
import { describeZ3 } from '../fixtures/z3.js';
import { JOIN_CHAIN_ROWS, pnidNet } from '../fixtures/pnid-nets.js';
import { allMints } from '../fixtures/all-mints.js';

/**
 * A place the initial marking marks and the net does not declare is an **inert** place of the
 * verified net ([CORE-072], [VER-001]): the executors retain its tokens, so every route sees
 * them. `deadlockFree` finds the token stranded whatever the class budget, `placeBound` counts
 * it, and a property may name it ([VER-003] AC5).
 */

const a = place<string>('a');
const c = place<string>('c');
const d = place<string>('d');
const net = PetriNet.builder('u')
  .transition(Transition.builder('t').inputs(one(c)).outputs(outPlace(d)).action(transform(() => null)).build())
  .build();
const stray = MarkingState.builder().tokens(a, 1).build();

function verifier(marking: MarkingState, property: SmtProperty, budget: number) {
  return SmtVerifier.forNet(net).mintTransitions(...allMints(net))
    .initialMarking(marking)
    .property(property)
    .sinkPlaces(d)
    .enumerationMaxClasses(budget);
}

it('a marking naming only declared places leaves the net untouched', () => {
  expect(withInertMarkedPlaces(net, MarkingState.builder().tokens(c, 1).build())).toBe(net);
});

it('an undeclared marked place is an inert place of the flat net and its own P-invariant', () => {
  const inert = withInertMarkedPlaces(net, stray);
  expect([...inert.places].map(p => p.name)).toEqual(['c', 'd', 'a']);
  const flat = flatten(inert);
  const ia = flat.places.findIndex(p => p.name === 'a');
  expect(ia).toBeGreaterThanOrEqual(0);
  expect(flat.transitions.every(t => t.preVector[ia] === 0 && t.postVector[ia] === 0)).toBe(true);
  const invariants = computePInvariants(IncidenceMatrix.from(flat), flat, stray);
  expect(invariants.some(inv => inv.support.size === 1 && inv.support.has(ia) && inv.constant === 1)).toBe(true);
});

describeZ3('undeclared marked places are inert in verification (CORE-072, VER-001)', () => {
  it.each([50_000, 1, 0])('deadlockFree is violated at class budget %i', async budget => {
    const result = await verifier(stray, deadlockFree(), budget).verify();
    expect(result.verdict.type, result.report).toBe('violated');
  }, 30_000);

  it.each([50_000, 0])('placeBound(a, 0) is violated at class budget %i', async budget => {
    const result = await verifier(stray, placeBound(a, 0), budget).verify();
    expect(result.verdict.type, result.report).toBe('violated');
  }, 30_000);

  it('a net with no stray token is unchanged: the same net proves deadlock-free', async () => {
    for (const budget of [50_000, 0]) {
      const result = await verifier(MarkingState.builder().tokens(c, 1).build(), deadlockFree(), budget).verify();
      expect(result.verdict.type, result.report).toBe('proven');
    }
  }, 30_000);

  it('Route B (ν) sees the stray token too', async () => {
    const { net: chain, places } = pnidNet('chain', JOIN_CHAIN_ROWS);
    const run = (marking: MarkingState) => SmtVerifier.forNet(chain).mintTransitions(...allMints(chain))
      .initialMarking(marking)
      .property(deadlockFree())
      .sinkPlaces(places.get('done')!)
      .fragmentMode('extended')
      .verify();
    const clean = await run(MarkingState.builder().tokens(places.get('S')!, 1).build());
    expect(clean.verdict.type, clean.report).toBe('proven');
    expect(clean.route).toBe('nu-scg');
    const dirty = await run(MarkingState.builder().tokens(places.get('S')!, 1).tokens(a, 1).build());
    expect(dirty.verdict.type, dirty.report).toBe('violated');
    expect(dirty.route).toBe('nu-scg');
  }, 30_000);

  it('a terminal excuses the inert place as it excuses every place (EXEC-042)', async () => {
    const halt = place<string>('halt');
    const terminal = PetriNet.builder('term')
      .transition(Transition.builder('t').inputs(one(c)).outputs(outPlace(halt)).action(transform(() => null)).build())
      .terminal(halt)
      .build();
    const result = await SmtVerifier.forNet(terminal).mintTransitions(...allMints(terminal))
      .initialMarking(MarkingState.builder().tokens(c, 1).tokens(a, 1).build())
      .property(deadlockFree())
      .verify();
    expect(result.verdict.type, result.report).toBe('proven');
  }, 30_000);
});
