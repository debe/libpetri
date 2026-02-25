import type { Place } from './place.js';
import type { TransitionContext } from './transition-context.js';

/**
 * The action executed when a transition fires.
 * Receives a TransitionContext providing filtered I/O and structure access.
 */
export type TransitionAction = (ctx: TransitionContext) => Promise<void>;

// ==================== Built-in Actions ====================

/** Identity action: produces no outputs. */
export function passthrough(): TransitionAction {
  return async () => {};
}

/**
 * Transform action: applies function to context, copies result to ALL output places.
 *
 * @example
 * ```ts
 * const action = transform(ctx => ctx.input(inputPlace).toUpperCase());
 * // Result is copied to every declared output place
 * ```
 */
export function transform(fn: (ctx: TransitionContext) => unknown): TransitionAction {
  return async (ctx) => {
    const result = fn(ctx);
    for (const outputPlace of ctx.outputPlaces()) {
      ctx.output(outputPlace, result);
    }
  };
}

/**
 * Fork action: copies single input token to all outputs.
 * Requires exactly one input place (derived from structure).
 */
export function fork(): TransitionAction {
  return transform((ctx) => {
    const inputPlaces = ctx.inputPlaces();
    if (inputPlaces.size !== 1) {
      throw new Error(`Fork requires exactly 1 input place, found ${inputPlaces.size}`);
    }
    const inputPlace = inputPlaces.values().next().value as Place<any>;
    return ctx.input(inputPlace);
  });
}

/**
 * Transform with explicit input place.
 */
export function transformFrom<I>(inputPlace: Place<I>, fn: (value: I) => unknown): TransitionAction {
  return transform((ctx) => fn(ctx.input(inputPlace)));
}

/**
 * Async transform: applies async function, copies result to all outputs.
 */
export function transformAsync(fn: (ctx: TransitionContext) => Promise<unknown>): TransitionAction {
  return async (ctx) => {
    const result = await fn(ctx);
    for (const outputPlace of ctx.outputPlaces()) {
      ctx.output(outputPlace, result);
    }
  };
}

/** Produce action: produces a single token with the given value to the specified place. */
export function produce<T>(place: Place<T>, value: T): TransitionAction {
  return async (ctx) => {
    ctx.output(place, value);
  };
}

/**
 * Wraps an action with timeout handling.
 * If the action completes within the timeout, normal completion.
 * If the timeout expires, the timeoutValue is produced to the timeoutPlace.
 *
 * @example
 * ```ts
 * const action = withTimeout(
 *   async (ctx) => { ctx.output(resultPlace, await fetchData()); },
 *   5000,
 *   timeoutPlace,
 *   'timed-out',
 * );
 * ```
 */
export function withTimeout<T>(
  action: TransitionAction,
  timeoutMs: number,
  timeoutPlace: Place<T>,
  timeoutValue: T,
): TransitionAction {
  return (ctx) => {
    return new Promise<void>((resolve, reject) => {
      let completed = false;
      const timer = setTimeout(() => {
        if (!completed) {
          completed = true;
          ctx.output(timeoutPlace, timeoutValue);
          resolve();
        }
      }, timeoutMs);
      action(ctx).then(
        () => {
          if (!completed) {
            completed = true;
            clearTimeout(timer);
            resolve();
          }
        },
        (err) => {
          if (!completed) {
            completed = true;
            clearTimeout(timer);
            reject(err);
          }
        },
      );
    });
  };
}
