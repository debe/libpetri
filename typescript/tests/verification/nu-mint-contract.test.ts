import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import type { SmtVerificationResult } from '../../src/verification/smt-verification-result.js';
import { describeZ3 } from '../fixtures/z3.js';
import { produces } from '../fixtures/producing-actions.js';
import { Transition } from '../../src/core/transition.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { place, type Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { and, forwardInput, outPlace, timeout, xor } from '../../src/core/out.js';
import { matchKey, matchSpec } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { placeBound } from '../../src/verification/smt-property.js';

/**
 * The ν mint and relay contracts (NU-010, NU-051) on both ν routes of NU-050. Each net has a run
 * the executor takes and the routes used to rule out, because they read a coloured write as a
 * fresh name when it was not one. The Rust twin, `rust/libpetri/tests/nu_mint_contract.rs`, runs
 * the executor to that run.
 */

const places = new Map<string, Place<string>>();
const p = (name: string): Place<string> => {
  let x = places.get(name);
  if (x === undefined) {
    x = place<string>(name);
    places.set(name, x);
  }
  return x;
};

const join = (name: string, a: Place<string>, b: Place<string>, out: Place<string>) =>
  Transition.builder(name).inputs(one(a), one(b))
    .match(matchSpec(matchKey(a, (s: string) => nameId(s)), matchKey(b, (s: string) => nameId(s))))
    .outputs(outPlace(out)).action(produces()).build();

const notProven = (r: SmtVerificationResult, what: string): void => {
  expect(r.verdict.type, `${what}: the executor reaches the bad marking\n${r.report}`).not.toBe('proven');
};

describe('copying producers (NU-010)', () => {
  // mA: S1 -> A and mB: S2 -> B write whatever their action writes; J: A, B -> DONE.
  const copyingMints = () => PetriNet.builder('copying_mints').transitions(
    Transition.builder('mA').inputs(one(p('S1'))).outputs(outPlace(p('A'))).action(produces()).build(),
    Transition.builder('mB').inputs(one(p('S2'))).outputs(outPlace(p('B'))).action(produces()).build(),
    join('J', p('A'), p('B'), p('DONE')),
  ).build();

  it('reads a producer as a mint only when declared', async () => {
    const net = copyingMints();
    const r = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(p('S1'), 1).tokens(p('S2'), 1))
      .property(placeBound(p('DONE'), 0))
      .verify();
    notProven(r, 'undeclared copying producers');
    expect(r.route, r.report).not.toBe('nu-scg');

    const declared = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(p('S1'), 1).tokens(p('S2'), 1))
      .property(placeBound(p('DONE'), 0))
      .mintTransitions('mA', 'mB')
      .verify();
    expect(declared.verdict.type, declared.report).toBe('proven');
    expect(declared.route).toBe('nu-scg');
    expect(declared.report).toContain(
      'Mint contract (NU-010) assumed for mA, mB: each writes a freshly minted name into every coloured place it writes.',
    );
  });

  it('rejects a declared mint that is not in the net', () => {
    expect(() => SmtVerifier.forNet(copyingMints()).mintTransitions('mA', 'mC'))
      .toThrow("declared mint transition 'mC' not in the net");
  });
});

// t1: budget, reqA -> xor(okA, timeout(20, forward(reqA, a))), its twin t2 into b,
// join: a, b -> done. Both timeouts forward the request token itself.
const forwardMints = () => PetriNet.builder('forward_mints').transitions(
  Transition.builder('t1').inputs(one(p('budget')), one(p('reqA')))
    .outputs(xor(outPlace(p('okA')), timeout(20, forwardInput(p('reqA'), p('a'))))).action(produces()).build(),
  Transition.builder('t2').inputs(one(p('budget')), one(p('reqB')))
    .outputs(xor(outPlace(p('okB')), timeout(20, forwardInput(p('reqB'), p('b'))))).action(produces()).build(),
  join('join', p('a'), p('b'), p('done')),
).build();

// m1: budget -> A1, m2: budget -> A2 mint (carriers A1, A2); r1: A1, reqA -> xor(okA,
// timeout(20, forward(reqA, KA))) and its twin r2 into KB forward the request, not the name they
// consumed; join: KA, KB -> done.
const forwardingConsumers = () => PetriNet.builder('forwarding_consumers').transitions(
  Transition.builder('m1').inputs(one(p('budget'))).outputs(outPlace(p('A1'))).action(produces()).build(),
  Transition.builder('m2').inputs(one(p('budget'))).outputs(outPlace(p('A2'))).action(produces()).build(),
  Transition.builder('r1').inputs(one(p('A1')), one(p('reqA')))
    .outputs(xor(outPlace(p('okA')), timeout(20, forwardInput(p('reqA'), p('KA'))))).action(produces()).build(),
  Transition.builder('r2').inputs(one(p('A2')), one(p('reqB')))
    .outputs(xor(outPlace(p('okB')), timeout(20, forwardInput(p('reqB'), p('KB'))))).action(produces()).build(),
  join('join', p('KA'), p('KB'), p('done')),
).build();

const requests = (net: PetriNet) => SmtVerifier.forNet(net)
  .initialMarking(m => m.tokens(p('budget'), 2).tokens(p('reqA'), 1).tokens(p('reqB'), 1))
  .property(placeBound(p('done'), 0));

describe('what the executor writes on timeout (IO-013, IO-014)', () => {
  it('a timeout forward into a match key is never a mint (Route B)', async () => {
    const r = await requests(forwardMints()).mintTransitions('t1', 't2').verify();
    notProven(r, 'Route B');
    expect(r.route, r.report).not.toBe('nu-scg');
  });

  it('a consumer timeout forwarding another input is not a relay (Route B)', async () => {
    const r = await requests(forwardingConsumers())
      .fragmentMode('extended').carrierPlaces(p('A1'), p('A2'))
      .mintTransitions('m1', 'm2')
      .verify();
    notProven(r, 'Route B');
    expect(r.route, r.report).not.toBe('nu-scg');
  });
});

describeZ3('Route A (NU-053)', () => {
  it('a timeout forward into a match key is never a mint', async () => {
    const r = await requests(forwardMints()).budgetPlaces(p('budget')).verify();
    notProven(r, 'Route A');
    expect(r.report).not.toContain('ν-encoding: name-coloured');
  }, 120_000);

  it('a consumer timeout forwarding another input is not a relay', async () => {
    const r = await requests(forwardingConsumers())
      .fragmentMode('extended').carrierPlaces(p('A1'), p('A2'))
      .budgetPlaces(p('budget'))
      .verify();
    notProven(r, 'Route A');
    expect(r.report).not.toContain('ν-encoding: name-coloured');
  }, 120_000);

  it('a consumer relaying into its own input keeps the colour there', async () => {
    // mint: budget -> a, b (one fresh name in both); spin: a, tick -> a, tock relays it back into
    // a; join: a, b -> done. spin can fire, so tock is reachable.
    const net = PetriNet.builder('self_loop').transitions(
      Transition.builder('mint').inputs(one(p('budget'))).outputs(and(outPlace(p('a')), outPlace(p('b')))).action(produces()).build(),
      Transition.builder('spin').inputs(one(p('a')), one(p('tick')))
        .outputs(and(outPlace(p('a')), outPlace(p('tock')))).action(produces()).build(),
      join('join', p('a'), p('b'), p('done')),
    ).build();
    const r = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(p('budget'), 1).tokens(p('tick'), 1))
      .property(placeBound(p('tock'), 0))
      .budgetPlaces(p('budget'))
      .fragmentMode('extended')
      .verify();
    expect(r.report).toContain('ν-encoding: name-coloured');
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.report).toContain(
      'Relay contract (NU-051) assumed for spin: each writes the name it consumed into every coloured place it writes.',
    );
  }, 120_000);
});
