/**
 * [ENV-013] `run(timeoutMs, onTimeout)`: what happens to the orchestrator loop
 * when the timeout fires.
 *
 * `Promise.race` abandons the losing promise, it does not cancel it — so a bare
 * `run(timeoutMs)` rejects while the loop keeps firing transitions and mutating
 * the marking behind the caller's back. Java has always let the caller choose
 * (`PetriNetExecutor.RunTimeoutPolicy`); these tests pin the same two policies
 * for TypeScript, with `'abandon'` kept as the default for compatibility.
 */
import { describe, it, expect } from 'vitest';
import { BitmapNetExecutor } from '../../src/runtime/bitmap-net-executor.js';
import { PrecompiledNetExecutor } from '../../src/runtime/precompiled-net-executor.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { delayed } from '../../src/core/timing.js';
import { tokenOf } from '../../src/core/token.js';
import type { Token } from '../../src/core/token.js';
import type { PetriNetExecutor } from '../../src/runtime/petri-net-executor.js';

const sleep = (ms: number) => new Promise<void>(r => setTimeout(r, ms));

/**
 * A -> B -> A ping-pong on a 5 ms delay: never quiescent, so `run` can only end
 * by timing out. `fired` counts every firing, including any that happen after
 * the caller has walked away.
 */
function pingPong(): { net: PetriNet; tokens: Map<Place<any>, Token<any>[]>; fired: () => number } {
  const a = place<number>('A');
  const b = place<number>('B');
  let count = 0;
  const bump = (to: Place<number>) => async (ctx: any) => {
    count++;
    ctx.output(to, tokenOf(count));
  };
  const net = PetriNet.builder('ping-pong')
    .transition(Transition.builder('AB').inputs(one(a)).outputs(outPlace(b)).timing(delayed(5)).action(bump(b)).build())
    .transition(Transition.builder('BA').inputs(one(b)).outputs(outPlace(a)).timing(delayed(5)).action(bump(a)).build())
    .build();
  return { net, tokens: new Map([[a, [tokenOf(0)]]]), fired: () => count };
}

const backends: { name: string; make: (n: PetriNet, t: Map<Place<any>, Token<any>[]>) => PetriNetExecutor }[] = [
  { name: 'BitmapNetExecutor', make: (n, t) => new BitmapNetExecutor(n, t) },
  { name: 'PrecompiledNetExecutor', make: (n, t) => new PrecompiledNetExecutor(n, t) },
];

for (const backend of backends) {
  describe(`run() timeout policy (${backend.name})`, () => {
    it("defaults to 'abandon': the loop keeps firing after the caller gives up", async () => {
      const { net, tokens, fired } = pingPong();
      const exec = backend.make(net, tokens);

      await expect(exec.run(60)).rejects.toThrow('Execution timed out');

      const atRejection = fired();
      await sleep(60);
      expect(fired()).toBeGreaterThan(atRejection);

      exec.close();
    });

    it("'close' stops the loop: no firing outlives the rejection", async () => {
      const { net, tokens, fired } = pingPong();
      const exec = backend.make(net, tokens);

      await expect(exec.run(60, 'close')).rejects.toThrow('Execution timed out');

      // Let any in-flight action land (ENV-013 lets those complete), then pin.
      await sleep(30);
      const settled = fired();
      await sleep(60);
      expect(fired()).toBe(settled);
    });

    it("'abandon' passed explicitly matches the default", async () => {
      const { net, tokens, fired } = pingPong();
      const exec = backend.make(net, tokens);

      await expect(exec.run(60, 'abandon')).rejects.toThrow('Execution timed out');

      const atRejection = fired();
      await sleep(60);
      expect(fired()).toBeGreaterThan(atRejection);

      exec.close();
    });
  });
}
