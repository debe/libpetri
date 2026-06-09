import { describe, it, expect } from 'vitest';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { matchSpec, matchKey } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { findBinding } from '../../src/runtime/match-engine.js';
import type { Token } from '../../src/core/token.js';

// NU-021 (guard + match composition): the input filter applies first and name
// correlation runs over the survivors — a token failing the filter is never
// selected even if its name matches. Pins nu-2: TS selection now guard-filters
// before indexing names, matching the Rust reference.
describe('match-engine guard+match composition (NU-021)', () => {
  const a = place<string>('branchA');
  const b = place<string>('branchB');
  const merged = place<string>('merged');

  // Join correlates a and b by their string value; input a carries a unary guard
  // rejecting the value "bad".
  const join = Transition.builder('join')
    .inputs(one(a, (v: string) => v !== 'bad'), one(b))
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

  it('does not select a name whose guarded-input tokens all fail the guard', () => {
    // "bad" is present in both inputs by count, but a's only "bad" token fails
    // a's guard — after guard-first filtering there is no shared name.
    expect(bindingFor({ branchA: [tok('bad')], branchB: [tok('bad')] })).toBeNull();
  });

  it('selects a name whose tokens pass the guard', () => {
    expect(bindingFor({ branchA: [tok('good')], branchB: [tok('good')] })).toBe(nameId('good'));
  });

  it('skips a guard-failing name but still selects a passing one', () => {
    // a holds both "bad" (fails guard) and "good"; b holds "good". The join must
    // correlate on "good", never "bad".
    expect(bindingFor({ branchA: [tok('bad'), tok('good')], branchB: [tok('good')] }))
      .toBe(nameId('good'));
  });
});
