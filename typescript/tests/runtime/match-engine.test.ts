import { describe, it, expect } from 'vitest';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { matchSpec, matchKey } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { findBinding } from '../../src/runtime/match-engine.js';
import type { Token } from '../../src/core/token.js';

// NU-020/NU-021 (name correlation): a binding exists only when a single name is
// supplied by *every* correlated input at its required count. Input arcs are
// purely structural (IO-006) — name equality is the only per-token filter the
// selection applies.
describe('match-engine name correlation (NU-020/NU-021)', () => {
  const a = place<string>('branchA');
  const b = place<string>('branchB');
  const merged = place<string>('merged');

  // Join correlates a and b by their string value.
  const join = Transition.builder('join')
    .inputs(one(a), one(b))
    .match(matchSpec(
      matchKey(a, (s: string) => nameId(s)),
      matchKey(b, (s: string) => nameId(s)),
    ))
    .outputs(outPlace(merged))
    .build();

  const tok = (value: string): Token<string> => ({ value, createdAt: 0 });

  function bindingFor(tokens: Record<string, Token<string>[]>) {
    return findBinding(join, (p) => tokens[p.name] ?? []);
  }

  it('does not select a name supplied by only one input', () => {
    // Both inputs hold a token, but no name is present on both sides.
    expect(bindingFor({ branchA: [tok('x')], branchB: [tok('y')] })).toBeNull();
  });

  it('selects a name shared by every correlated input', () => {
    expect(bindingFor({ branchA: [tok('good')], branchB: [tok('good')] })).toBe(nameId('good'));
  });

  it('skips a non-shared name but still selects a shared one', () => {
    // a holds both "bad" (only on a's side) and "good"; b holds "good". The join
    // must correlate on "good", never "bad".
    expect(bindingFor({ branchA: [tok('bad'), tok('good')], branchB: [tok('good')] }))
      .toBe(nameId('good'));
  });

  it('returns null when a correlated input is empty', () => {
    expect(bindingFor({ branchA: [tok('good')], branchB: [] })).toBeNull();
  });
});
