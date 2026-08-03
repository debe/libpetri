import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { deadlockFree } from '../../src/verification/smt-property.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { bindProducers } from '../fixtures/producing-actions.js';

// Its own file rather than a block in smt-verifier.test.ts: vitest isolates test
// files into separate workers, so this gets a fresh z3 WASM heap. Appended to that
// file instead, the extra solver run tipped the shared heap past the 2 GB wasm32
// ceiling and OOM'd an unrelated test alongside it.
const Z3_TIMEOUT = 60_000;

// CORE-043: verification rejects the same nets compilation rejects.
describe('SmtVerifier — CORE-043', () => {
  it('rejects an output-declaring transition still on passthrough', async () => {
    const pA = place('A');
    const pB = place('B');
    const net = PetriNet.builder('inert')
      .transition(Transition.builder('t').inputs(one(pA)).outputs(outPlace(pB)).build())
      .build();

    // Throws before Z3 is reached, so this case costs no solver memory.
    await expect(SmtVerifier.forNet(net).property(deadlockFree()).verify())
      .rejects.toThrow(/Transition 't' declares an output spec/);
  });

  it('accepts the same net once an action is bound', async () => {
    const pA = place('A');
    const pB = place('B');
    const net = PetriNet.builder('live')
      .transition(Transition.builder('t').inputs(one(pA)).outputs(outPlace(pB)).build())
      .build();

    await expect(SmtVerifier.forNet(bindProducers(net)).property(deadlockFree())
      .initialMarking(m => { m.tokens(pA, 1); })
      .sinkPlaces(pB)
      .timeout(30_000)
      .verify()).resolves.toBeDefined();
  }, Z3_TIMEOUT);
});
