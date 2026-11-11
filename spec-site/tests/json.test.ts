import { describe, expect, it } from 'vitest';
import { escapeJsonForScript, stableStringify } from '../src/gen/json.js';

describe('stableStringify', () => {
  it('sorts keys at every depth and keeps array order', () => {
    expect(stableStringify({ b: 1, a: { d: [3, 1], c: null } })).toBe('{"a":{"c":null,"d":[3,1]},"b":1}');
  });

  it('refuses undefined, non-finite numbers and class instances', () => {
    expect(() => stableStringify({ a: undefined })).toThrow(/\$\.a/);
    expect(() => stableStringify([Number.NaN])).toThrow(/non-finite/);
    expect(() => stableStringify({ m: new Map() })).toThrow(/plain object/);
  });
});

describe('escapeJsonForScript', () => {
  it('leaves no "<" and round-trips through JSON.parse', () => {
    const value = { s: '</script><!-- <b> \u2028 \u2029' };
    const out = escapeJsonForScript(stableStringify(value));
    expect(out).not.toContain('<');
    expect(out).not.toMatch(/[\u2028\u2029]/);
    expect(JSON.parse(out)).toEqual(value);
  });
});
