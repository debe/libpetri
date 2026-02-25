import { describe, it, expect, vi } from 'vitest';
import { passthrough, transform, transformFrom, fork, produce, transformAsync, withTimeout } from '../../src/core/transition-action.js';
import { TransitionContext } from '../../src/core/transition-context.js';
import { TokenInput } from '../../src/core/token-input.js';
import { TokenOutput } from '../../src/core/token-output.js';
import { place } from '../../src/core/place.js';
import { tokenOf } from '../../src/core/token.js';

function makeCtx(
  inputPlaces: Map<string, unknown[]>,
  outputPlaceNames: string[],
) {
  const rawInput = new TokenInput();
  const inputSet = new Set<ReturnType<typeof place>>();
  for (const [name, values] of inputPlaces) {
    const p = place(name);
    inputSet.add(p);
    for (const v of values) {
      rawInput.add(p, tokenOf(v));
    }
  }

  const outputSet = new Set<ReturnType<typeof place>>();
  for (const name of outputPlaceNames) {
    outputSet.add(place(name));
  }

  const rawOutput = new TokenOutput();
  return new TransitionContext('Test', rawInput, rawOutput, inputSet, new Set(), outputSet);
}

describe('TransitionAction built-ins', () => {
  it('passthrough produces no output', async () => {
    const action = passthrough();
    const ctx = makeCtx(new Map(), []);
    await action(ctx);
    expect(ctx.rawOutput().isEmpty()).toBe(true);
  });

  it('transform applies fn to all outputs', async () => {
    const out1 = place<number>('O1');
    const out2 = place<number>('O2');
    const rawInput = new TokenInput();
    const rawOutput = new TokenOutput();
    const ctx = new TransitionContext('T', rawInput, rawOutput, new Set(), new Set(), new Set([out1, out2]));

    const action = transform(() => 42);
    await action(ctx);

    expect(rawOutput.entries()).toHaveLength(2);
    expect(rawOutput.entries()[0]!.token.value).toBe(42);
    expect(rawOutput.entries()[1]!.token.value).toBe(42);
  });

  it('transformFrom reads explicit input place and copies to all outputs', async () => {
    const inp = place<string>('I');
    const out1 = place<string>('O1');
    const out2 = place<string>('O2');

    const rawInput = new TokenInput();
    rawInput.add(inp, tokenOf('hello'));
    const rawOutput = new TokenOutput();
    const ctx = new TransitionContext('T', rawInput, rawOutput, new Set([inp]), new Set(), new Set([out1, out2]));

    const action = transformFrom(inp, (v: string) => v.toUpperCase());
    await action(ctx);

    expect(rawOutput.entries()).toHaveLength(2);
    expect(rawOutput.entries()[0]!.token.value).toBe('HELLO');
    expect(rawOutput.entries()[1]!.token.value).toBe('HELLO');
  });

  it('fork copies input to all outputs', async () => {
    const inp = place<string>('I');
    const out1 = place<string>('O1');
    const out2 = place<string>('O2');

    const rawInput = new TokenInput();
    rawInput.add(inp, tokenOf('data'));
    const rawOutput = new TokenOutput();
    const ctx = new TransitionContext('T', rawInput, rawOutput, new Set([inp]), new Set(), new Set([out1, out2]));

    const action = fork();
    await action(ctx);

    expect(rawOutput.entries()).toHaveLength(2);
    expect(rawOutput.entries()[0]!.token.value).toBe('data');
    expect(rawOutput.entries()[1]!.token.value).toBe('data');
  });

  it('fork throws with multiple inputs', async () => {
    const inp1 = place('I1');
    const inp2 = place('I2');

    const rawInput = new TokenInput();
    rawInput.add(inp1, tokenOf('a'));
    rawInput.add(inp2, tokenOf('b'));
    const rawOutput = new TokenOutput();
    const ctx = new TransitionContext('T', rawInput, rawOutput, new Set([inp1, inp2]), new Set(), new Set());

    const action = fork();
    await expect(action(ctx)).rejects.toThrow('exactly 1 input');
  });

  it('produce puts value to specific place', async () => {
    const p = place<string>('P');
    const rawInput = new TokenInput();
    const rawOutput = new TokenOutput();
    const ctx = new TransitionContext('T', rawInput, rawOutput, new Set(), new Set(), new Set([p]));

    const action = produce(p, 'hello');
    await action(ctx);

    expect(rawOutput.entries()).toHaveLength(1);
    expect(rawOutput.entries()[0]!.token.value).toBe('hello');
  });

  it('transformAsync applies async fn to all outputs', async () => {
    const out = place<number>('O');
    const rawInput = new TokenInput();
    const rawOutput = new TokenOutput();
    const ctx = new TransitionContext('T', rawInput, rawOutput, new Set(), new Set(), new Set([out]));

    const action = transformAsync(async () => {
      return 99;
    });
    await action(ctx);

    expect(rawOutput.entries()).toHaveLength(1);
    expect(rawOutput.entries()[0]!.token.value).toBe(99);
  });

  it('withTimeout completes normally when fast', async () => {
    const p = place<string>('P');
    const tp = place<string>('TIMEOUT');
    const rawInput = new TokenInput();
    const rawOutput = new TokenOutput();
    const ctx = new TransitionContext('T', rawInput, rawOutput, new Set(), new Set(), new Set([p, tp]));

    const inner = async (ctx: TransitionContext) => {
      ctx.output(p, 'done');
    };

    const action = withTimeout(inner, 1000, tp, 'timed-out');
    await action(ctx);

    const values = rawOutput.entries().map(e => e.token.value);
    expect(values).toContain('done');
    expect(values).not.toContain('timed-out');
  });

  it('withTimeout produces timeout value when slow', async () => {
    const p = place<string>('P');
    const tp = place<string>('TIMEOUT');
    const rawInput = new TokenInput();
    const rawOutput = new TokenOutput();
    const ctx = new TransitionContext('T', rawInput, rawOutput, new Set(), new Set(), new Set([p, tp]));

    const inner = async () => {
      // Simulate slow action
      await new Promise(resolve => setTimeout(resolve, 200));
      ctx.output(p, 'done');
    };

    const action = withTimeout(inner, 50, tp, 'timed-out');
    await action(ctx);

    const values = rawOutput.entries().map(e => e.token.value);
    expect(values).toContain('timed-out');
  });
});
