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
 * [IO-015] output validation as an **exact-explanation search**.
 *
 * An *assignment* picks exactly one child at each `xor` it reaches; subtrees under
 * an unselected child are never evaluated. Each assignment claims a set of places,
 * and validation succeeds iff **exactly one** assignment's claim *equals* the
 * produced set.
 *
 * Returns that claim on success and throws `OutViolationError` otherwise — whether
 * nothing explains the write or two or more branches do.
 *
 * Equality — rather than "every obligation was satisfied" — is what makes a token
 * written to a declared place outside the selected branch a violation instead of a
 * silent deposit. It also removes the need for a subsumption tie-break:
 * `xor(and(A,B,C), and(A,B))` with A, B, C produced has exactly one *exact* claim.
 *
 * Being a search rather than an eager walk is what makes `and` genuinely unordered
 * ([IO-015] AC8): the old version short-circuited on its first unsatisfied child and
 * let an inner `xor` throw before an enclosing one could try a sibling, so the same
 * write set could pass or fail depending on declaration order.
 */
export function validateOutSpec(
  tName: string,
  spec: Out,
  producedPlaceNames: Set<string>,
): Set<string> {
  // Equality is tested against the produced places the spec could name at all.
  // A token produced to a place the spec never mentions is [CORE-072]'s business
  // — retained and reported, not an [IO-015] violation — so it must not make the
  // claim sets unmatchable.
  const named = specNames(spec);
  let relevant = 0;
  for (const name of producedPlaceNames) {
    if (named.has(name)) relevant++;
  }

  const exact: Set<string>[] = [];
  for (const claim of claimsWithin(spec, producedPlaceNames)) {
    // Every claim is a subset of the produced set by construction (a leaf only
    // claims a place that was produced), so equal size means equal set.
    if (claim.size === relevant) {
      exact.push(claim);
      if (exact.length > 1) break;
    }
  }
  const wrote = [...producedPlaceNames].filter(n => named.has(n)).sort();
  if (exact.length === 0) {
    throw new OutViolationError(
      `'${tName}': output does not match the declared spec - produced {${wrote.join(', ')}}, ` +
      `which no single branch of the spec claims exactly`
    );
  }
  if (exact.length > 1) {
    throw new OutViolationError(
      `'${tName}': ambiguous output - {${wrote.join(', ')}} is claimed by more than one branch`
    );
  }
  return exact[0]!;
}

/**
 * Collapses identical claims, keeping at most two of each.
 *
 * Validation only needs to distinguish "no assignment", "exactly one" and "more
 * than one", so a third assignment claiming an already-seen set carries no
 * information. Without this the `and` join is O(2^k) in the number of `xor`
 * children — 21us at k=8, seconds at k=20, on a path that runs every firing.
 * With it the working set is bounded by the number of DISTINCT claim subsets,
 * which is at most 2^|produced|; the produced set is what the action actually
 * wrote, and is small.
 */
function capMultiplicity(claims: Set<string>[]): Set<string>[] {
  if (claims.length < 3) return claims;
  const seen = new Map<string, number>();
  const out: Set<string>[] = [];
  for (const claim of claims) {
    const key = [...claim].sort().join('\u0000');
    const n = seen.get(key) ?? 0;
    if (n >= 2) continue;
    seen.set(key, n + 1);
    out.push(claim);
  }
  return out;
}

/** Every place named anywhere in the spec tree, memoised per spec object. */
const specNamesCache = new WeakMap<object, Set<string>>();
function specNames(spec: Out): Set<string> {
  const hit = specNamesCache.get(spec as object);
  if (hit !== undefined) return hit;
  const names = new Set<string>();
  const walk = (node: Out): void => {
    switch (node.type) {
      case 'place': names.add(node.place.name); break;
      case 'forward-input': names.add(node.to.name); break;
      case 'timeout': walk(node.child); break;
      case 'xor':
      case 'and': for (const c of node.children) walk(c); break;
    }
  };
  walk(spec);
  specNamesCache.set(spec as object, names);
  return names;
}

/**
 * Claims of every assignment whose claim is a subset of `produced`.
 *
 * The subset restriction is the pruning that keeps this linear in practice: a leaf
 * naming a place that was not produced yields nothing, so a `xor` branch dies as soon
 * as it claims something unwritten, and an `and` dies with any unsatisfiable child.
 * Branching survives only where several `xor` children are simultaneously consistent
 * with what was produced — the ambiguous case, which is rejected anyway.
 */
function claimsWithin(spec: Out, produced: Set<string>): Set<string>[] {
  switch (spec.type) {
    case 'place':
      return produced.has(spec.place.name) ? [new Set([spec.place.name])] : [];

    case 'forward-input':
      return produced.has(spec.to.name) ? [new Set([spec.to.name])] : [];

    case 'timeout':
      return claimsWithin(spec.child, produced);

    case 'xor': {
      const out: Set<string>[] = [];
      for (const child of spec.children) {
        for (const claim of claimsWithin(child, produced)) out.push(claim);
      }
      return capMultiplicity(out);
    }

    case 'and': {
      // Unordered: the children are a set of obligations, so this is a join over
      // their claim sets and the result cannot depend on their declaration order.
      let acc: Set<string>[] = [new Set()];
      for (const child of spec.children) {
        const childClaims = claimsWithin(child, produced);
        if (childClaims.length === 0) return []; // no assignment can satisfy this AND
        const next: Set<string>[] = [];
        for (const partial of acc) {
          for (const claim of childClaims) {
            const merged = new Set(partial);
            for (const name of claim) merged.add(name);
            next.push(merged);
          }
        }
        acc = capMultiplicity(next);
      }
      return acc;
    }
  }
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
