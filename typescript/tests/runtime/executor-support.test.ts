import { describe, it, expect } from 'vitest';
import { validateOutSpec, produceTimeoutOutput } from '../../src/runtime/executor-support.js';
import { outPlace, andPlaces, xorPlaces, timeout, forwardInput, and, xor } from '../../src/core/out.js';
import { place } from '../../src/core/place.js';
import { TokenInput } from '../../src/core/token-input.js';
import { TokenOutput } from '../../src/core/token-output.js';
import { TransitionContext } from '../../src/core/transition-context.js';
import { tokenOf } from '../../src/core/token.js';

describe('validateOutSpec', () => {
  const pA = place('A');
  const pB = place('B');
  const pC = place('C');
  const pD = place('D');

  it('place spec satisfied', () => {
    const spec = outPlace(pA);
    const produced = new Set(['A']);
    const result = validateOutSpec('T', spec, produced);
    expect(result).not.toBeNull();
    expect(result!.has('A')).toBe(true);
  });

  it('place spec not satisfied', () => {
    const spec = outPlace(pA);
    const produced = new Set<string>();
    const result = validateOutSpec('T', spec, produced);
    expect(result).toBeNull();
  });

  it('AND spec all satisfied', () => {
    const spec = andPlaces(pA, pB);
    const produced = new Set(['A', 'B']);
    const result = validateOutSpec('T', spec, produced);
    expect(result).not.toBeNull();
    expect(result!.has('A')).toBe(true);
    expect(result!.has('B')).toBe(true);
  });

  it('AND spec partially satisfied returns null', () => {
    const spec = andPlaces(pA, pB);
    const produced = new Set(['A']);
    const result = validateOutSpec('T', spec, produced);
    expect(result).toBeNull();
  });

  it('XOR spec exactly one satisfied', () => {
    const spec = xorPlaces(pA, pB);
    const produced = new Set(['B']);
    const result = validateOutSpec('T', spec, produced);
    expect(result).not.toBeNull();
    expect(result!.has('B')).toBe(true);
  });

  it('XOR spec no branch throws', () => {
    const spec = xorPlaces(pA, pB);
    const produced = new Set<string>();
    expect(() => validateOutSpec('T', spec, produced)).toThrow('XOR violation');
    expect(() => validateOutSpec('T', spec, produced)).toThrow('no branch');
  });

  it('XOR spec multiple branches throws', () => {
    const spec = xorPlaces(pA, pB);
    const produced = new Set(['A', 'B']);
    expect(() => validateOutSpec('T', spec, produced)).toThrow('XOR violation');
    expect(() => validateOutSpec('T', spec, produced)).toThrow('multiple branches');
  });

  it('XOR with nested AND: correct branch produced', () => {
    const spec = xor(andPlaces(pA, pB), andPlaces(pC, pD));
    const produced = new Set(['C', 'D']);
    const result = validateOutSpec('T', spec, produced);
    expect(result).not.toBeNull();
    expect(result!.has('C')).toBe(true);
    expect(result!.has('D')).toBe(true);
  });

  it('timeout child validated', () => {
    const tOut = place('TIMEOUT');
    const spec = timeout(100, outPlace(tOut));
    const produced = new Set(['TIMEOUT']);
    const result = validateOutSpec('T', spec, produced);
    expect(result).not.toBeNull();
  });

  it('forwardInput satisfied', () => {
    const from = place('FROM');
    const to = place('TO');
    const spec = forwardInput(from, to);
    const produced = new Set(['TO']);
    const result = validateOutSpec('T', spec, produced);
    expect(result).not.toBeNull();
    expect(result!.has('TO')).toBe(true);
  });
});

describe('produceTimeoutOutput', () => {
  it('produces to place', () => {
    const input = place<string>('IN');
    const output = place<string>('OUT');
    const tokenInput = new TokenInput();
    const tokenOutput = new TokenOutput();
    const ctx = new TransitionContext(
      'T', tokenInput, tokenOutput,
      new Set([input]), new Set(), new Set([output]),
    );

    produceTimeoutOutput(ctx, outPlace(output));
    expect(tokenOutput.entries()).toHaveLength(1);
    expect(tokenOutput.entries()[0]!.place.name).toBe('OUT');
  });

  it('forwards input value', () => {
    const from = place<string>('FROM');
    const to = place<string>('TO');
    const tokenInput = new TokenInput();
    tokenInput.add(from, tokenOf('original'));
    const tokenOutput = new TokenOutput();
    const ctx = new TransitionContext(
      'T', tokenInput, tokenOutput,
      new Set([from]), new Set(), new Set([to]),
    );

    produceTimeoutOutput(ctx, forwardInput(from, to));
    expect(tokenOutput.entries()).toHaveLength(1);
    expect(tokenOutput.entries()[0]!.token.value).toBe('original');
  });

  it('produces to AND children', () => {
    const outA = place<string>('A');
    const outB = place<string>('B');
    const tokenInput = new TokenInput();
    const tokenOutput = new TokenOutput();
    const ctx = new TransitionContext(
      'T', tokenInput, tokenOutput,
      new Set(), new Set(), new Set([outA, outB]),
    );

    produceTimeoutOutput(ctx, andPlaces(outA, outB));
    expect(tokenOutput.entries()).toHaveLength(2);
  });

  it('throws on XOR child', () => {
    const pA = place('A');
    const pB = place('B');
    const tokenInput = new TokenInput();
    const tokenOutput = new TokenOutput();
    const ctx = new TransitionContext(
      'T', tokenInput, tokenOutput,
      new Set(), new Set(), new Set([pA, pB]),
    );

    expect(() => produceTimeoutOutput(ctx, xorPlaces(pA, pB))).toThrow('XOR not allowed');
  });
});
