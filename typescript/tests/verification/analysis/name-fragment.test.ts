import { describe, it, expect } from 'vitest';
import { PetriNet } from '../../../src/core/petri-net.js';
import { Transition } from '../../../src/core/transition.js';
import { place } from '../../../src/core/place.js';
import { one } from '../../../src/core/in.js';
import { andPlaces, outPlace } from '../../../src/core/out.js';
import { matchKey, matchSpec } from '../../../src/core/match-spec.js';
import { nameId } from '../../../src/core/name.js';
import { classify } from '../../../src/verification/analysis/name-fragment.js';

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
