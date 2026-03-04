/**
 * requestAnimationFrame loop that injects rafTick tokens,
 * throttling DOM-write transitions to 60fps.
 */

import type { BitmapNetExecutor } from 'libpetri';
import * as p from '../net/places.js';

/** Start the rAF loop that feeds rafTick tokens to the executor. */
export function startRafLoop(executor: BitmapNetExecutor): void {
  function tick() {
    executor.injectValue(p.rafTick, undefined);
    requestAnimationFrame(tick);
  }
  requestAnimationFrame(tick);
}
