import { describe, expect, it } from 'vitest';
import { expandNames } from '../src/net-utils.js';
import { perUnitProperties } from '../src/gates.js';

const names = ['s1/SOURCE', 's2/SOURCE', 's1/TURN_PERMIT', 's2/TURN_PERMIT', 's1/SPEAKING', 's2/SPEAKING', 's1/ABORTING', 's2/ABORTING', 'POOL'];

describe('contract name patterns', () => {
  it('expands patterns, keeps exact names even when missing', () => {
    expect(expandNames(['*/SOURCE', 'POOL', 'MISSING'], names)).toEqual(['s1/SOURCE', 's2/SOURCE', 'POOL', 'MISSING']);
    expect(expandNames(['*/NOPE'], names)).toEqual(['*/NOPE']);
  });

  it('expands a pattern bound into one check per unit', () => {
    const out = perUnitProperties([{ name: 'one turn', spec: { kind: 'placeBound', place: '*/TURN_PERMIT', bound: 1 } }], names);
    expect(out.map(p => p.spec.kind === 'placeBound' ? p.spec.place : '')).toEqual(['s1/TURN_PERMIT', 's2/TURN_PERMIT']);
  });

  it('pairs mutual exclusion per unit, never across units', () => {
    const out = perUnitProperties([{ name: 'mx', spec: { kind: 'mutualExclusion', a: '*/SPEAKING', b: '*/ABORTING' } }], names);
    const pairs = out.map(p => p.spec.kind === 'mutualExclusion' ? `${p.spec.a}~${p.spec.b}` : '');
    expect(pairs).toEqual(['s1/SPEAKING~s1/ABORTING', 's2/SPEAKING~s2/ABORTING']);
  });
});

import { PetriNet, Transition, one, outPlace, place } from 'libpetri';
import { membership } from '../src/net-utils.js';

describe('membership from name prefixes', () => {
  it('treats a prefix as a subnet only when transitions carry it', () => {
    const a = place<unknown>('a/IN'), b = place<unknown>('a/OUT'), obs = place<unknown>('obs/TURN'), host = place<unknown>('HOST');
    const net = PetriNet.builder('m').transitions(
      Transition.builder('a/work').inputs(one(a)).outputs(outPlace(b)).build(),
      Transition.builder('mark').inputs(one(host)).outputs(outPlace(obs)).build(),
    ).build();
    const m = membership(net);
    expect(m.get('a/IN')).toBe('a');
    expect(m.get('a/work')).toBe('a');
    expect(m.has('obs/TURN')).toBe(false);
  });
});
