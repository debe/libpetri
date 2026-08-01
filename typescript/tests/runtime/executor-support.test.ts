import { describe, it, expect } from 'vitest';
import { validateOutSpec, produceTimeoutOutput, executeAction } from '../../src/runtime/executor-support.js';
import { outPlace, andPlaces, xorPlaces, timeout, forwardInput, and, xor } from '../../src/core/out.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { Transition } from '../../src/core/transition.js';
import type { TransitionAction } from '../../src/core/transition-action.js';
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

  it('XOR with one branch subsuming the other picks the most specific', () => {
    // and(A,B,C) strictly contains and(A,B): producing A, B and C satisfies
    // both branches, but only the wider one is the intended match. Java and
    // Rust both resolve this; TypeScript used to reject it outright.
    const spec = xor(andPlaces(pA, pB, pC), andPlaces(pA, pB));
    const produced = new Set(['A', 'B', 'C']);
    const result = validateOutSpec('T', spec, produced);
    expect(result).not.toBeNull();
    expect([...result!].sort()).toEqual(['A', 'B', 'C']);
  });

  it('XOR with genuinely overlapping branches still throws', () => {
    // and(A,B) and and(B,C) both match, neither contains the other.
    const spec = xor(andPlaces(pA, pB), andPlaces(pB, pC));
    const produced = new Set(['A', 'B', 'C']);
    expect(() => validateOutSpec('T', spec, produced)).toThrow('multiple branches');
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

  it('forwards every consumed input value, in consumption order', () => {
    const from = place<string>('FROM');
    const to = place<string>('TO');
    const tokenInput = new TokenInput();
    tokenInput.add(from, tokenOf('a'));
    tokenInput.add(from, tokenOf('b'));
    tokenInput.add(from, tokenOf('c'));
    const tokenOutput = new TokenOutput();
    const ctx = new TransitionContext(
      'T', tokenInput, tokenOutput,
      new Set([from]), new Set(), new Set([to]),
    );

    produceTimeoutOutput(ctx, forwardInput(from, to));
    expect(tokenOutput.entries()).toHaveLength(3);
    expect(tokenOutput.entries().map(e => e.place.name)).toEqual(['TO', 'TO', 'TO']);
    expect(tokenOutput.entries().map(e => e.token.value)).toEqual(['a', 'b', 'c']);
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

describe('executeAction (E1)', () => {
  function ctxFor(t: Transition): TransitionContext {
    return new TransitionContext(
      t.name, new TokenInput(), new TokenOutput(),
      t.inputPlaces(), t.readPlaces(), t.outputPlaces(),
    );
  }

  it('rejects when the action throws synchronously', async () => {
    const inP = place<string>('IN');
    const t = Transition.builder('T').inputs(one(inP))
      .action(() => { throw new Error('sync boom'); }).build();
    await expect(executeAction(t, ctxFor(t))).rejects.toThrow('sync boom');
  });

  it('rejects when the action returns a non-thenable', async () => {
    const inP = place<string>('IN');
    const t = Transition.builder('T').inputs(one(inP))
      .action((() => null) as unknown as TransitionAction).build();
    await expect(executeAction(t, ctxFor(t))).rejects.toThrow('null/non-thenable');
  });

  it('resolves when the action returns a promise', async () => {
    const inP = place<string>('IN');
    const t = Transition.builder('T').inputs(one(inP))
      .action(async () => {}).build();
    await expect(executeAction(t, ctxFor(t))).resolves.toBeUndefined();
  });
});

describe('TransitionContext detach/harvest (E2)', () => {
  it('detachForTimeout drops action writes and swaps in a fresh harvest collector', () => {
    const out = place<string>('OUT');
    const ctx = new TransitionContext(
      'T', new TokenInput(), new TokenOutput(),
      new Set(), new Set(), new Set([out]),
    );

    ctx.output(out, 'pre'); // lands in the original write target
    const original = ctx.rawOutput();
    expect(original.entries()).toHaveLength(1);

    ctx.detachForTimeout();
    expect(ctx.rawOutput()).not.toBe(original);   // fresh harvest collector
    expect(ctx.rawOutput().entries()).toHaveLength(0);
    expect(original.entries()).toHaveLength(1);    // pre-timeout write stranded in old collector

    ctx.output(out, 'post'); // dropped — the write target is detached
    expect(ctx.rawOutput().entries()).toHaveLength(0);

    ctx.outputToHarvest(out, 'timeout-branch'); // reaches the harvest collector
    expect(ctx.rawOutput().entries()).toHaveLength(1);
    expect(ctx.rawOutput().entries()[0]!.token.value).toBe('timeout-branch');
  });
});
