import { describe, it, expect } from 'vitest';
import { TokenInput } from '../../src/core/token-input.js';
import { TokenOutput } from '../../src/core/token-output.js';
import { place } from '../../src/core/place.js';
import { tokenOf } from '../../src/core/token.js';

describe('TokenInput', () => {
  const p = place<string>('P');
  const q = place<number>('Q');

  it('adds and retrieves token', () => {
    const input = new TokenInput();
    const token = tokenOf('hello');
    input.add(p, token);

    expect(input.get(p)).toBe(token);
    expect(input.value(p)).toBe('hello');
  });

  it('retrieves all tokens for a place', () => {
    const input = new TokenInput();
    input.add(p, tokenOf('a'));
    input.add(p, tokenOf('b'));

    expect(input.getAll(p)).toHaveLength(2);
    expect(input.values(p)).toEqual(['a', 'b']);
  });

  it('returns empty for unknown place', () => {
    const input = new TokenInput();
    expect(input.getAll(p)).toHaveLength(0);
    expect(input.has(p)).toBe(false);
    expect(input.count(p)).toBe(0);
  });

  it('throws on get for missing place', () => {
    const input = new TokenInput();
    expect(() => input.get(p)).toThrow('No token for place');
  });

  it('has/count work correctly', () => {
    const input = new TokenInput();
    input.add(p, tokenOf('x'));

    expect(input.has(p)).toBe(true);
    expect(input.count(p)).toBe(1);
    expect(input.has(q)).toBe(false);
    expect(input.count(q)).toBe(0);
  });

  it('supports different place types', () => {
    const input = new TokenInput();
    input.add(p, tokenOf('hello'));
    input.add(q, tokenOf(42));

    expect(input.value(p)).toBe('hello');
    expect(input.value(q)).toBe(42);
  });
});

describe('TokenOutput', () => {
  const p = place<string>('P');
  const q = place<number>('Q');

  it('starts empty', () => {
    const output = new TokenOutput();
    expect(output.isEmpty()).toBe(true);
    expect(output.entries()).toHaveLength(0);
  });

  it('adds value', () => {
    const output = new TokenOutput();
    output.add(p, 'hello');

    expect(output.isEmpty()).toBe(false);
    expect(output.entries()).toHaveLength(1);
    expect(output.entries()[0]!.place).toBe(p);
    expect(output.entries()[0]!.token.value).toBe('hello');
  });

  it('adds pre-existing token', () => {
    const output = new TokenOutput();
    const token = tokenOf('world');
    output.addToken(p, token);

    expect(output.entries()[0]!.token).toBe(token);
  });

  it('tracks places with tokens', () => {
    const output = new TokenOutput();
    output.add(p, 'hello');
    output.add(q, 42);

    const places = output.placesWithTokens();
    expect(places.size).toBe(2);
    expect(places.has('P')).toBe(true);
    expect(places.has('Q')).toBe(true);
  });

  it('supports chaining', () => {
    const output = new TokenOutput();
    output.add(p, 'a').add(q, 1);
    expect(output.entries()).toHaveLength(2);
  });
});
