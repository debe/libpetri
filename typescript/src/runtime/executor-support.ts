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
import type { TransitionContext } from '../core/transition-context.js';
import { OutViolationError } from './out-violation-error.js';

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
        throw new OutViolationError(
          `'${tName}': XOR violation - multiple branches produced`
        );
      }
      return satisfied[0]!;
    }

    case 'timeout':
      return validateOutSpec(tName, spec.child, producedPlaceNames);
  }
}

/**
 * Produces default tokens to the timeout branch's output places when an action
 * exceeds its timeout. Walks the Out spec tree recursively:
 *
 * - **Place**: produces `null` (the timeout sentinel value).
 * - **ForwardInput**: forwards the consumed input token to the output place.
 * - **AND**: recurses into all children (all branches get tokens).
 * - **XOR**: disallowed — timeout cannot choose a branch non-deterministically.
 * - **Timeout**: disallowed — nested timeouts would create ambiguous recovery paths.
 */
export function produceTimeoutOutput(context: TransitionContext, timeoutChild: Out): void {
  switch (timeoutChild.type) {
    case 'place':
      context.output(timeoutChild.place, null);
      break;
    case 'forward-input': {
      const value = context.input(timeoutChild.from);
      context.output(timeoutChild.to, value);
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
