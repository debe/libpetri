import { describe, it, expect } from 'vitest';
import { TransitionContext } from '../../src/core/transition-context.js';
import { TokenInput } from '../../src/core/token-input.js';
import { TokenOutput } from '../../src/core/token-output.js';
import { place } from '../../src/core/place.js';
import { tokenOf } from '../../src/core/token.js';

describe('TransitionContext', () => {
  const inputPlace = place<string>('INPUT');
  const readPlace = place<number>('READ');
  const outputPlace = place<string>('OUTPUT');
  const forbiddenPlace = place<string>('FORBIDDEN');

  function makeContext() {
    const rawInput = new TokenInput();
    rawInput.add(inputPlace, tokenOf('hello'));
    rawInput.add(readPlace, tokenOf(42));

    const rawOutput = new TokenOutput();

    return new TransitionContext(
      'TestTransition',
      rawInput,
      rawOutput,
      new Set([inputPlace]),
      new Set([readPlace]),
      new Set([outputPlace]),
    );
  }

  describe('input access', () => {
    it('reads input value', () => {
      const ctx = makeContext();
      expect(ctx.input(inputPlace)).toBe('hello');
    });

    it('reads input token', () => {
      const ctx = makeContext();
      const token = ctx.inputToken(inputPlace);
      expect(token.value).toBe('hello');
    });

    it('rejects undeclared input', () => {
      const ctx = makeContext();
      expect(() => ctx.input(forbiddenPlace)).toThrow('not in declared inputs');
    });

    it('returns input places', () => {
      const ctx = makeContext();
      expect(ctx.inputPlaces().size).toBe(1);
    });
  });

  describe('read access', () => {
    it('reads value', () => {
      const ctx = makeContext();
      expect(ctx.read(readPlace)).toBe(42);
    });

    it('rejects undeclared read', () => {
      const ctx = makeContext();
      expect(() => ctx.read(forbiddenPlace)).toThrow('not in declared reads');
    });
  });

  describe('output access', () => {
    it('produces output', () => {
      const ctx = makeContext();
      ctx.output(outputPlace, 'result');
      expect(ctx.rawOutput().entries()).toHaveLength(1);
    });

    it('rejects undeclared output', () => {
      const ctx = makeContext();
      expect(() => ctx.output(forbiddenPlace, 'x')).toThrow('not in declared outputs');
    });

    it('returns output places', () => {
      const ctx = makeContext();
      expect(ctx.outputPlaces().size).toBe(1);
    });

    it('produces multiple outputs via rest params', () => {
      const ctx = makeContext();
      ctx.output(outputPlace, 'a', 'b', 'c');
      const entries = ctx.rawOutput().entries();
      expect(entries).toHaveLength(3);
      expect(entries.map(e => e.token.value)).toEqual(['a', 'b', 'c']);
      expect(entries.every(e => e.place === outputPlace)).toBe(true);
    });

    it('produces multiple outputs via spread array', () => {
      const ctx = makeContext();
      const values = ['x', 'y', 'z'];
      ctx.output(outputPlace, ...values);
      expect(ctx.rawOutput().entries().map(e => e.token.value)).toEqual(['x', 'y', 'z']);
    });

    it('zero-value bulk output is a no-op', () => {
      const ctx = makeContext();
      ctx.output(outputPlace);
      expect(ctx.rawOutput().entries()).toHaveLength(0);
    });

    it('bulk rejects undeclared output before appending anything', () => {
      const ctx = makeContext();
      expect(() => ctx.output(forbiddenPlace, 'a', 'b')).toThrow('not in declared outputs');
      expect(ctx.rawOutput().entries()).toHaveLength(0);
    });

    it('outputToken accepts multiple tokens', () => {
      const ctx = makeContext();
      ctx.outputToken(outputPlace, tokenOf('t1'), tokenOf('t2'));
      expect(ctx.rawOutput().entries().map(e => e.token.value)).toEqual(['t1', 't2']);
    });
  });

  describe('structure info', () => {
    it('returns transition name', () => {
      const ctx = makeContext();
      expect(ctx.transitionName()).toBe('TestTransition');
    });
  });

  describe('execution context', () => {
    it('retrieves context by key', () => {
      const rawInput = new TokenInput();
      const rawOutput = new TokenOutput();
      const execCtx = new Map<string, unknown>([['tracing', { spanId: '123' }]]);

      const ctx = new TransitionContext(
        'T', rawInput, rawOutput,
        new Set(), new Set(), new Set(),
        execCtx,
      );

      expect(ctx.executionContext<{ spanId: string }>('tracing')).toEqual({ spanId: '123' });
      expect(ctx.hasExecutionContext('tracing')).toBe(true);
      expect(ctx.hasExecutionContext('missing')).toBe(false);
    });
  });
});
