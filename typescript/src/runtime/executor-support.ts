/**
 * @module executor-support
 *
 * Output validation and timeout production for the Petri net executor.
 *
 * **Output validation algorithm**: Recursively walks the declared Out spec tree,
 * checking that the action's produced tokens match the structure:
 * - Place/ForwardInput: place must be in the produced set
 * - AND: all children must be satisfied (conjunction)
 * - XOR: exactly 1 child must be satisfied (throws OutViolationError for 0 or 2+)
 * - Timeout: delegates to child spec
 *
 * Returns the set of "claimed" place names on success, or null if unsatisfied.
 *
 * **Timeout production**: When an action exceeds its timeout, produces default
 * tokens to the timeout branch's output places, enabling the net to continue.
 */
import type { Out } from '../core/out.js';
import type { Transition } from '../core/transition.js';
import type { TransitionContext } from '../core/transition-context.js';
import { OutViolationError } from './out-violation-error.js';

/**
 * Invokes a transition action, converting a synchronous throw or a non-Promise
 * return into a rejected promise.
 *
 * Actions are invoked inline on the orchestrator loop, so an action that throws
 * before returning its promise (an undeclared-place access, a bad closure) would
 * otherwise unwind out of the firing loop and take the whole executor with it.
 * Routing it through a rejected promise makes it flow the same contained path as an
 * asynchronously-reported failure. A `null`/non-thenable return (a mis-typed action
 * that forgot `async`) is likewise rejected rather than silently treated as complete.
 */
export function executeAction(t: Transition, context: TransitionContext): Promise<void> {
  try {
    const stage = t.action(context) as unknown;
    if (stage == null || typeof (stage as { then?: unknown }).then !== 'function') {
      return Promise.reject(new Error(
        `'${t.name}': action returned null/non-thenable instead of a Promise`));
    }
    return Promise.resolve(stage as Promise<void>);
  } catch (err) {
    return Promise.reject(err);
  }
}

/**
 * Swallows a failure thrown by a user {@link import('../event/event-store.js').EventStore}
 * from `append`, logging it once.
 *
 * An event emission is observation, not control flow: a store that throws must not
 * unwind the orchestrator loop or escape a failure handler. Each executor wraps its
 * single `emitEvent` choke point in a try/catch that routes here.
 *
 * @param when short description of what was being emitted, for the log message
 * @param err the throwable the store raised
 */
export function swallowEventStoreFailure(when: string, err: unknown): void {
  console.warn(
    `libpetri: EventStore.append threw while emitting ${when}; the event is dropped`, err);
}

/**
 * Default deadline-enforcement tolerance, in milliseconds.
 *
 * A transition with a hard deadline (`deadline()` / `window()`) is force-disabled only once its
 * elapsed time exceeds `latest + DEADLINE_TOLERANCE_MS`, absorbing timer-resolution and scheduling
 * jitter (TIME-013). Shared by both executors and matched by the Java and Rust runtimes so
 * deadline enforcement behaves identically across languages. Configurable per executor via the
 * `deadlineToleranceMs` option.
 *
 * `exact()` timing is enforced *softly* — an exact transition fires at the first opportunity at/after
 * its target time and is never force-disabled, so this tolerance does not gate its firing (TIME-006).
 */
export const DEADLINE_TOLERANCE_MS = 5;

/**
 * Recursively validates that a transition's output satisfies its declared Out spec.
 *
 * @returns the set of claimed place names, or null if not satisfied
 * @throws OutViolationError if a structural violation is detected (e.g. XOR with 0 or 2+ branches)
 */
export function validateOutSpec(
  tName: string,
  spec: Out,
  producedPlaceNames: Set<string>,
): Set<string> | null {
  switch (spec.type) {
    case 'place':
      return producedPlaceNames.has(spec.place.name)
        ? new Set([spec.place.name])
        : null;

    case 'forward-input':
      return producedPlaceNames.has(spec.to.name)
        ? new Set([spec.to.name])
        : null;

    case 'and': {
      const claimed = new Set<string>();
      for (const child of spec.children) {
        const result = validateOutSpec(tName, child, producedPlaceNames);
        if (result === null) return null;
        for (const p of result) claimed.add(p);
      }
      return claimed;
    }

    case 'xor': {
      const satisfied: Set<string>[] = [];
      for (const child of spec.children) {
        const result = validateOutSpec(tName, child, producedPlaceNames);
        if (result !== null) satisfied.push(result);
      }
      if (satisfied.length === 0) {
        throw new OutViolationError(
          `'${tName}': XOR violation - no branch produced (exactly 1 required)`
        );
      }
      if (satisfied.length > 1) {
        return resolveXorAmbiguity(tName, satisfied);
      }
      return satisfied[0]!;
    }

    case 'timeout':
      return validateOutSpec(tName, spec.child, producedPlaceNames);
  }
}

/**
 * Two or more XOR branches matched. When exactly one of them subsumes all the
 * others — as `and(a, b, c)` subsumes `and(a, b)` — it is the intended, most
 * specific branch and the firing is accepted with that branch's claim.
 * Anything else is genuinely ambiguous and violates [IO-015].
 *
 * Mirrors Java's `ExecutorSupport.validateOutSpec` and Rust's
 * `resolve_xor_ambiguity`; without it, overlapping XOR branches that the other
 * two runtimes accept were rejected here.
 */
function resolveXorAmbiguity(tName: string, satisfied: Set<string>[]): Set<string> {
  const subsuming = satisfied.filter((candidate) =>
    satisfied.every(
      (other) =>
        other === candidate || [...other].every((p) => candidate.has(p))
    )
  );
  if (subsuming.length === 1) return subsuming[0]!;
  throw new OutViolationError(
    `'${tName}': XOR violation - multiple branches produced`
  );
}

/**
 * Produces default tokens to the timeout branch's output places when an action
 * exceeds its timeout. Walks the Out spec tree recursively:
 *
 * - **Place**: produces `null` (the timeout sentinel value).
 * - **ForwardInput**: forwards *all* tokens consumed from the `from` place to the
 *   output place, in consumption order — one output token per consumed token, so a
 *   batched input spec (`all()` / `exactly(n)`) conserves its tokens on timeout.
 * - **AND**: recurses into all children (all branches get tokens).
 * - **XOR**: disallowed — timeout cannot choose a branch non-deterministically.
 * - **Timeout**: disallowed — nested timeouts would create ambiguous recovery paths.
 *
 * Writes through {@link TransitionContext.outputToHarvest} rather than `output(...)`:
 * by this point the context has been detached, so the ordinary write target is closed
 * and only the harvest collector still reaches the marking.
 */
export function produceTimeoutOutput(context: TransitionContext, timeoutChild: Out): void {
  switch (timeoutChild.type) {
    case 'place':
      context.outputToHarvest(timeoutChild.place, null);
      break;
    case 'forward-input': {
      // Forward *every* token consumed from `from`, not just the first: a batched
      // input spec (`all()`, `exactly(n)`, `atLeast(n)`) consumes N tokens, and
      // re-emitting only one would silently destroy N-1 of them on the retry path.
      // `inputs()` is the batched accessor and preserves consumption (FIFO) order;
      // the singular `input()` throws outright when the place yielded != 1 token.
      for (const value of context.inputs(timeoutChild.from)) {
        context.outputToHarvest(timeoutChild.to, value);
      }
      break;
    }
    case 'and':
      for (const child of timeoutChild.children) {
        produceTimeoutOutput(context, child);
      }
      break;
    case 'xor':
      throw new Error('XOR not allowed in timeout child');
    case 'timeout':
      throw new Error('Nested Timeout not allowed');
  }
}
