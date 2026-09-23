import { describe, it, expect } from 'vitest';
import { PetriNet } from '../../../src/core/petri-net.js';
import { Transition } from '../../../src/core/transition.js';
import { place } from '../../../src/core/place.js';
import { one } from '../../../src/core/in.js';
import { andPlaces, outPlace } from '../../../src/core/out.js';
import { matchKey, matchSpec } from '../../../src/core/match-spec.js';
import { nameId } from '../../../src/core/name.js';
import { classify } from '../../../src/verification/analysis/name-fragment.js';
import { SmtVerifier } from '../../../src/verification/smt-verifier.js';
import { joinedOrDeadLettered } from '../../../src/verification/smt-property.js';
import { bindProducers } from '../../fixtures/producing-actions.js';
import { describeZ3 } from '../../fixtures/z3.js';

// `join1` matches on `a`/`b` and also consumes `c`, a key of `join2`, as a non-correlated
// input: at runtime it takes `c`'s oldest token, whatever its name. With `mintB` first
// that token is `join2`'s, so `join2` never fires and `pending` strands. The name layer
// would drop nothing from `c` and prove the net stranding-free (NU-051 AC7).
function offKeyColouredNet() {
  const srcA = place('srcA');
  const srcB = place('srcB');
  const a = place<string>('a');
  const b = place<string>('b');
  const c = place<string>('c');
  const d = place<string>('d');
  const pending = place('pending');
  const out = place('out');
  const key = (s: string) => nameId(s);
  const mintA = Transition.builder('mintA').inputs(one(srcA)).outputs(andPlaces(a, b, c)).build();
  const mintB = Transition.builder('mintB').inputs(one(srcB)).outputs(andPlaces(c, d, pending)).build();
  const join1 = Transition.builder('join1')
    .inputs(one(a), one(b), one(c))
    .match(matchSpec(matchKey(a, key), matchKey(b, key)))
    .outputs(outPlace(out))
    .build();
  const join2 = Transition.builder('join2')
    .inputs(one(c), one(d), one(pending))
    .match(matchSpec(matchKey(c, key), matchKey(d, key)))
    .outputs(outPlace(out))
    .build();
  return {
    net: PetriNet.builder('off-key-coloured').transitions(mintA, mintB, join1, join2).build(),
    srcA, srcB, pending,
  };
}

describe('name fragment (NU-050)', () => {
  it('orders a join\'s coloured inputs by code point, not UTF-16 code unit', () => {
    // The first coloured input seeds the symbols a join enumerates, so this order decides
    // the order successors are explored in. As code units the surrogate pair of U+1F600
    // sorts before U+E000; as code points, as in the Rust port, it sorts after.
    const seed = place('seed');
    const emoji = place<string>('\u{1F600}');
    const privateUse = place<string>('\uE000');
    const out = place<string>('out');
    const mint = Transition.builder('mint').inputs(one(seed)).outputs(andPlaces(emoji, privateUse)).build();
    const join = Transition.builder('join')
      .inputs(one(emoji), one(privateUse))
      .match(matchSpec(matchKey(emoji, (s: string) => nameId(s)), matchKey(privateUse, (s: string) => nameId(s))))
      .outputs(outPlace(out))
      .build();
    const fragment = classify(PetriNet.builder('join-order').transitions(mint, join).build(), 'base', new Set())!;

    const role = fragment.role('join');
    expect(role.type).toBe('join');
    expect(role.type === 'join' && role.colouredIn.map(([p]) => p)).toEqual(['\uE000', '\u{1F600}']);
  });
});

describe('name fragment: off-key coloured input on a join (NU-051 AC7)', () => {
  it('is out of fragment in both modes', () => {
    const { net } = offKeyColouredNet();
    expect(classify(net, 'base', new Set())).toBeNull();
    expect(classify(net, 'extended', new Set())).toBeNull();
  });
});

describeZ3('name fragment: off-key coloured input, verdict (NU-051 AC7)', () => {
  it('is not proven stranding-free', async () => {
    const { net, srcA, srcB, pending } = offKeyColouredNet();
    const result = await SmtVerifier.forNet(bindProducers(net))
      .initialMarking(m => m.tokens(srcA, 1).tokens(srcB, 1))
      .property(joinedOrDeadLettered(pending))
      .verify();
    expect(result.verdict.type, result.report).not.toBe('proven');
  }, 60_000);
});
