import { place } from '../../src/core/place.js';
import { Transition } from '../../src/core/transition.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { one } from '../../src/core/in.js';
import { outPlace, andPlaces } from '../../src/core/out.js';

/**
 * Parameter record for {@link leakyBucket}. Carries a declared `rate`
 * (effective bucket capacity) and an optional `label` for disambiguation in
 * fusion-composition tests where multiple instances share a single rate
 * limiter.
 */
export interface LeakyBucketParams {
  readonly rate: number;
  readonly label: string;
}

/**
 * Fixture factory for canonical subnet definitions used across the modular
 * composition test suite (MOD-010 through MOD-023).
 *
 * These fixtures are deliberately minimal: each declares one or two
 * interface ports, a small body of internal places and transitions, and
 * action-less control-flow only. Tests pair them via
 * {@link PetriNetBuilder.compose} to verify port-place merging and
 * per-instance state isolation.
 *
 * ## Available fixtures
 *
 * - {@link producer} — single `output` port, internal `nextItem` place,
 *   one `produce` transition.
 * - {@link boundedBuffer} — `put`/`get` ports, internal `slots` capacity
 *   place pre-loaded by the caller (initial-marking concern is caller-side
 *   per the MOD-012 isolation contract), and `enqueue`/`dequeue`
 *   transitions.
 * - {@link consumer} — single `input` port, internal `consumed` sink, one
 *   `consume` transition.
 * - {@link retryPolicy} — single `attempt` synchronous channel (interface
 *   transition) and one internal `attemptCount` place written by the
 *   channel transition. Used by channel-composition tests (MOD-021,
 *   landing in task #13).
 *
 * Mirrors `java/src/test/java/org/libpetri/fixtures/SubnetFixtures.java`.
 */

/**
 * A producer subnet: one transition draws from an internal `nextItem`
 * place and emits to the `output` port. The `nextItem` place is internal
 * (per-instance state isolated per MOD-012); callers seed it via initial
 * marking.
 *
 * Interface:
 * - `output` (Output port) — token type `string`.
 */
export function producer(): SubnetDef<void> {
  const nextItem = place<string>('nextItem');
  const output = place<string>('output');

  const produce = Transition.builder('produce')
    .inputs(one(nextItem))
    .outputs(outPlace(output))
    .build();

  return SubnetDef.builder('Producer')
    .place(nextItem)
    .transition(produce)
    .outputPort('output', output)
    .build();
}

/**
 * A bounded-buffer subnet of the requested capacity. `enqueue` consumes a
 * slot token and forwards a token from `put` to the internal `items`
 * place; `dequeue` returns a slot and forwards from `items` to `get`.
 *
 * The `slots` capacity place is declared structurally; the caller is
 * responsible for seeding it with `capacity` initial tokens at execution
 * time (initial-marking concern is caller-side per the MOD-012 isolation
 * contract).
 *
 * Action-less: tokens just move through the buffer.
 *
 * Interface:
 * - `put` (Input port) — token type `string`.
 * - `get` (Output port) — token type `string`.
 */
export function boundedBuffer(capacity: number): SubnetDef<void> {
  if (capacity < 1) {
    throw new Error(`capacity must be >= 1, got: ${capacity}`);
  }

  const put = place<string>('put');
  const get = place<string>('get');
  const items = place<string>('items');
  const slots = place<string>('slots');

  const enqueue = Transition.builder('enqueue')
    .inputs(one(put), one(slots))
    .outputs(outPlace(items))
    .build();

  const dequeue = Transition.builder('dequeue')
    .inputs(one(items))
    .outputs(andPlaces(get, slots))
    .build();

  return SubnetDef.builder(`BoundedBuffer-${capacity}`)
    .place(items)
    .place(slots)
    .transition(enqueue)
    .transition(dequeue)
    .inputPort('put', put)
    .outputPort('get', get)
    .build();
}

/**
 * A consumer subnet: one transition draws from the `input` port and emits
 * to an internal `consumed` sink.
 *
 * Interface:
 * - `input` (Input port) — token type `string`.
 */
export function consumer(): SubnetDef<void> {
  const input = place<string>('input');
  const consumed = place<string>('consumed');

  const consume = Transition.builder('consume')
    .inputs(one(input))
    .outputs(outPlace(consumed))
    .build();

  return SubnetDef.builder('Consumer')
    .place(consumed)
    .transition(consume)
    .inputPort('input', input)
    .build();
}

/**
 * A retry-policy subnet: exposes a single synchronous channel `attempt`
 * (interface transition) per **MOD-005** with a caller-side transition
 * fused in at compose time per **MOD-021**. The channel transition
 * produces a token to the internal `attemptCount` place each time it
 * fires.
 *
 * Action-less by default; callers bind the `attempt` action via
 * {@link Instance.bindActions} when they need the channel's instance-side
 * action to do work.
 *
 * Interface:
 * - `attempt` (Channel) — synchronous; merges with a caller-side transition
 *   at compose time (channel composition lands in task #13).
 */
export function retryPolicy(): SubnetDef<void> {
  const attemptCount = place<string>('attemptCount');

  const attempt = Transition.builder('attempt')
    .outputs(outPlace(attemptCount))
    .build();

  return SubnetDef.builder('RetryPolicy')
    .place(attemptCount)
    .transition(attempt)
    .channel('attempt', attempt)
    .build();
}

/**
 * A leaky-bucket subnet: one transition consumes a `request` token plus a
 * `slots` token and emits to `accept`; a second transition consumes a
 * `request` token (with an inhibitor on `slots`) and emits to `reject`.
 *
 * The internal `slots` place models the per-bucket capacity:
 * fusion-composition tests (MOD-060/061) declare a fusion set across the
 * `slots` places of multiple bucket instances to model a shared rate
 * limiter.
 *
 * Action-less by default — tokens just move through the bucket. The caller
 * seeds `slots` with `rate` initial tokens at execution time
 * (initial-marking concern is caller-side, matching {@link boundedBuffer}).
 *
 * Interface:
 * - `request` (Input port) — token type `string`.
 * - `accept` (Output port) — token type `string`.
 * - `reject` (Output port) — token type `string`.
 *
 * Mirrors `java/src/test/java/org/libpetri/fixtures/SubnetFixtures.leakyBucket(int)`.
 */
export function leakyBucket(rate: number): SubnetDef<LeakyBucketParams> {
  if (rate < 1) {
    throw new Error(`rate must be >= 1, got: ${rate}`);
  }

  const request = place<string>('request');
  const accept = place<string>('accept');
  const reject = place<string>('reject');
  const slots = place<string>('slots');

  // accept-path: needs a slot, consumes the request, emits accept.
  const acceptT = Transition.builder('accept')
    .inputs(one(request), one(slots))
    .outputs(outPlace(accept))
    .build();

  // reject-path: no slot available (inhibitor), still consumes request,
  // emits reject. Action-less control-flow.
  const rejectT = Transition.builder('reject')
    .inputs(one(request))
    .inhibitor(slots)
    .outputs(outPlace(reject))
    .build();

  return SubnetDef.builder<LeakyBucketParams>(`LeakyBucket-${rate}`)
    .place(slots)
    .transitions(acceptT, rejectT)
    .inputPort('request', request)
    .outputPort('accept', accept)
    .outputPort('reject', reject)
    .build();
}
