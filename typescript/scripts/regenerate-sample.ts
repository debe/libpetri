/**
 * Regenerate /sample.dot from a synthetic Petri net that exercises every
 * visualization rule in spec/09-export.md (EXP-012, EXP-013, EXP-014) AND the
 * modular composition story from spec/11-modular-composition.md (EXP-016 /
 * MOD-020 / MOD-040):
 *
 * - reset+output combination on a leaf place
 * - reset+output combination underneath an XOR junction
 * - standalone reset (no matching output)
 * - XOR junction with ≥2 children
 * - AND junction with ≥2 children
 * - Single-child AND collapse (no junction)
 * - Nested AND-of-XOR (deterministic junction IDs)
 * - Out.Timeout wrapping a child
 * - Out.ForwardInput
 * - Inhibitor + read arcs
 * - Start / end / environment place styles
 * - Cardinality input labels (×n, ≥n, *)
 * - Composed subnet instances rendered as `subgraph cluster_*` blocks:
 *   a small producer subnet upstream of CustomerInput plus a bounded-buffer
 *   subnet bridging the producer output into the existing pipeline.
 *
 * Used by the dev-preview Vite app (`npm run dev:preview`) to iterate on
 * the renderer / styles. Run via `npm run regenerate-sample`.
 */

import { writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import { PetriNet } from '../src/core/petri-net.js';
import { Transition } from '../src/core/transition.js';
import { place } from '../src/core/place.js';
import { one, exactly, atLeast, all } from '../src/core/in.js';
import {
  outPlace,
  andPlaces,
  xorPlaces,
  and,
  xor,
  timeout,
  forwardInput,
} from '../src/core/out.js';
import { deadline } from '../src/core/timing.js';
import { SubnetDef } from '../src/core/subnet-def.js';
import { dotExport } from '../src/export/dot-exporter.js';

// ============================================================
// Place fixtures — covers start / mid / end / environment
// ============================================================

const intake = place<string>('Intake'); // new start (fed by producer subnet)
const customerInput = place<string>('CustomerInput'); // bridged by buffer subnet
const events = place<string>('Events'); // environment (config below)

const guardInput = place<string>('GuardInput');
const intentInput = place<string>('IntentInput');
const assistantInput = place<string>('AssistantInput');
const requestTimestamp = place<number>('RequestTimestamp');

// Reset+out leaf scenario
const cache = place<string>('Cache');

// Reset+out under XOR junction scenario
const ok = place<string>('Ok');
const fail = place<string>('Fail'); // also reset target

// Pure reset (no output)
const tmp = place<string>('Tmp');

// AND junction children
const sideA = place<string>('SideA');
const sideB = place<string>('SideB');

// XOR junction children
const success = place<string>('Success');
const error = place<string>('Error');

// Nested AND-of-XOR
const optX = place<string>('OptX');
const optY = place<string>('OptY');
const optZ = place<string>('OptZ');
const optW = place<string>('OptW');

// Single-child AND (collapses)
const onlyOut = place<string>('OnlyOut');

// Timeout / ForwardInput
const responseSent = place<string>('ResponseSent');
const retryQueue = place<string>('RetryQueue');

// Inhibitor / read companions
const conversation = place<string>('Conversation');
const searchInProgress = place<string>('SearchInProgress');

// End places (no outgoing)
const messageFinalized = place<string>('MessageFinalized');

// ============================================================
// Transitions
// ============================================================

// 1. Fork the customer input into multiple inputs (covers AND junction).
const tForkInput = Transition.builder('ForkInput')
  .inputs(one(customerInput))
  .outputs(andPlaces(guardInput, intentInput, assistantInput, requestTimestamp))
  .build();

// 2. Refresh cache: output(Cache) + reset(Cache) → combined edge.
const tRefreshCache = Transition.builder('RefreshCache')
  .inputs(one(guardInput))
  .outputs(outPlace(cache))
  .reset(cache)
  .build();

// 3. Try with XOR(ok, fail) where fail is also reset → combined under junction.
const tTry = Transition.builder('Try')
  .inputs(one(intentInput))
  .outputs(xorPlaces(ok, fail))
  .reset(fail)
  .reset(tmp) // standalone reset, distinct place
  .read(conversation)
  .build();

// 4. Validate with XOR(success, error) — pure XOR junction, no reset.
const tValidate = Transition.builder('Validate')
  .inputs(one(ok))
  .outputs(xorPlaces(success, error))
  .build();

// 5. Two-way AND fork.
const tParallel = Transition.builder('Parallel')
  .inputs(one(success))
  .outputs(andPlaces(sideA, sideB))
  .build();

// 6. Nested AND-of-XOR — deterministic junction IDs (and_0, xor_1, xor_2).
const tNested = Transition.builder('Nested')
  .inputs(one(assistantInput))
  .outputs(and(xorPlaces(optX, optY), xorPlaces(optZ, optW)))
  .build();

// 7. Single-child AND collapses (no junction in output).
const tCollapse = Transition.builder('Collapse')
  .inputs(one(error))
  .outputs(andPlaces(onlyOut))
  .build();

// 8. Timeout + ForwardInput (returns to retry on slow path).
const tSlow = Transition.builder('Slow')
  .inputs(one(sideA))
  .outputs(xor(outPlace(responseSent), timeout(5000, forwardInput(sideA, retryQueue))))
  .build();

// 9. Inhibitor + ≥cardinality + standalone reset.
const tFinalize = Transition.builder('Finalize')
  .inputs(atLeast(1, sideB))
  .outputs(outPlace(messageFinalized))
  .read(requestTimestamp)
  .inhibitor(searchInProgress)
  .build();

// 10. Drain the events environment place to feed conversation (×3 cardinality).
const tDrainEvents = Transition.builder('DrainEvents')
  .inputs(exactly(3, events))
  .outputs(outPlace(conversation))
  .build();

// 11. All-cardinality drain.
const tFlush = Transition.builder('Flush')
  .inputs(all(retryQueue))
  .outputs(outPlace(searchInProgress))
  .build();

// ============================================================
// Composition — multi-stage producer + bounded-buffer subnets that
// feed the existing pipeline through `intake` → `CustomerInput`.
//
// Both subnets carry non-trivial internal flow (multiple places,
// multiple transitions, branching/inhibitor structure) so the cluster
// boxes in the rendered DOT visibly demonstrate why composition is
// useful — there is real logic hidden behind each interface, not a
// single labeled node.
//
// The two subnets are also linked by a synchronous channel
// (`emit` on producer + `admit` on buffer fused with a single host-side
// `sync` transition) so the diagram demonstrates channel composition
// in addition to port composition.
// ============================================================

/**
 * Producer subnet: a 4-place, 3-transition pipeline that fans an
 * incoming `trigger` token through `prepare → validate → emit` with
 * an internal XOR branch on `validate` (`valid` vs `invalid`). The
 * emit transition is exposed as a synchronous channel so the producer
 * can be fused with a downstream subnet's intake step.
 *
 *   trigger  → t_prepare  → prepared
 *                          → t_validate  → XOR( valid, invalid )
 *                                                   |
 *                                          valid → t_emit → emit  (output port)
 *                                                       (channel "emit")
 *
 * - input port:   `trigger`  (where host tokens arrive)
 * - output port:  `emit`     (where validated tokens leave)
 * - channel:      `emit`     (the t_emit transition, fused with host
 *                              "sync" transition for cross-subnet
 *                              synchronization)
 *
 * Demonstrates: multi-stage flow inside a subnet, XOR branching on
 * the validation step, an internal `deadline(50)` timing constraint
 * on validation, and a channel exposed for cross-subnet fusion.
 */
function producerSubnet(): SubnetDef<void> {
  const trigger = place<string>('trigger');
  const prepared = place<string>('prepared');
  const valid = place<string>('valid');
  const invalid = place<string>('invalid');
  const emit = place<string>('emit');

  const prepare = Transition.builder('prepare')
    .inputs(one(trigger))
    .outputs(outPlace(prepared))
    .build();

  // XOR(valid, invalid) — the branching guard for the producer pipeline.
  // Carries a deadline(50ms) timing to demonstrate timing inside a subnet.
  const validate = Transition.builder('validate')
    .inputs(one(prepared))
    .outputs(xorPlaces(valid, invalid))
    .timing(deadline(50))
    .build();

  const emitT = Transition.builder('emit')
    .inputs(one(valid))
    .outputs(outPlace(emit))
    .build();

  return SubnetDef.builder('producer')
    .place(trigger)
    .place(prepared)
    .place(valid)
    .place(invalid)
    .place(emit)
    .transitions(prepare, validate, emitT)
    .inputPort('trigger', trigger)
    .outputPort('emit', emit)
    .channel('emit', emitT)
    .build();
}

/**
 * Bounded-buffer subnet: a 4-place, 3-transition admission-controlled
 * buffer. `put` arriving tokens are admitted into `pending` only when
 * a free `slot` token is available (consumed by t_admit, returned by
 * t_serve). An inhibitor on `pending` keeps the admit step from
 * over-firing when items are still waiting to be served. The admit
 * transition is exposed as a `admit` channel for fusion with the
 * producer's emit step.
 *
 *                      ┌──── slots (initial: N=3 tokens) ────┐
 *                      ▼                                       │
 *   put ──→ t_admit ──→ pending ──→ t_serve ──→ get  (output port)
 *              │                                       │
 *         (consumes one slot)                  (returns one slot)
 *         (channel "admit")
 *
 *   (overflow leg)
 *   put ──→ t_overflow ──→ overflow
 *              [inhibitor: slots]   — fires only when no slot is free
 *
 * - input port:   `put`     (where host pushes items)
 * - output port:  `get`     (where the buffer serves items downstream)
 * - channel:      `admit`   (the t_admit transition, fused at compose
 *                              time with the host's `sync` transition)
 *
 * Demonstrates: weighted state via the `slots` capacity-token pool,
 * the inhibitor arc on the overflow leg (an arc kind beyond plain
 * input/output), three internal places, three internal transitions,
 * and a channel exposed for cross-subnet fusion.
 */
function bufferSubnet(): SubnetDef<void> {
  const put = place<string>('put');
  const slots = place<string>('slots');
  const pending = place<string>('pending');
  const overflow = place<string>('overflow');
  const get = place<string>('get');

  const admit = Transition.builder('admit')
    .inputs(one(put), one(slots))
    .outputs(outPlace(pending))
    .build();

  // Overflow leg: only fires when `slots` is empty (inhibitor). Tokens
  // that arrive while the buffer is full are diverted to the
  // `overflow` sink — an internal back-pressure signal.
  const overflowT = Transition.builder('overflow')
    .inputs(one(put))
    .inhibitor(slots)
    .outputs(outPlace(overflow))
    .build();

  const serve = Transition.builder('serve')
    .inputs(one(pending))
    .outputs(andPlaces(get, slots)) // returns a slot when serving
    .build();

  return SubnetDef.builder('buffer')
    .place(put)
    .place(slots)
    .place(pending)
    .place(overflow)
    .place(get)
    .transitions(admit, overflowT, serve)
    .inputPort('put', put)
    .outputPort('get', get)
    .channel('admit', admit)
    .build();
}

// Instantiate each subnet. The producer emits into `Intake`; the
// buffer bridges `Intake` → `CustomerInput`, feeding the existing
// showcase pipeline.
const prodInst = producerSubnet().instantiate('producer');
const bufInst = bufferSubnet().instantiate('buffer');

// Host-side `sync` transition fused with BOTH subnets' channels.
// Channel binding is caller-wins-identity (MOD-021): the resulting
// flat net contains ONE merged `sync` transition that replaces both
// the renamed `producer/emit` and the renamed `buffer/admit`
// transitions. Their arc-sets are unioned, demonstrating channel
// composition between two subnets through a shared host transition.
const sync = Transition.builder('sync').build();

// Producer subnet trigger seed — a host place that feeds the producer's
// input port and unifies it with the existing showcase entry point.
const producerTrigger = place<string>('ProducerTrigger');

// ============================================================
// Build & export
// ============================================================

const net = PetriNet.builder('SampleVisualizationNet')
  .place(intake)
  .place(customerInput)
  .place(producerTrigger)
  .transitions(
    tForkInput,
    tRefreshCache,
    tTry,
    tValidate,
    tParallel,
    tNested,
    tCollapse,
    tSlow,
    tFinalize,
    tDrainEvents,
    tFlush,
  )
  // Producer subnet:
  //  - `trigger` input port wired to host `ProducerTrigger` place.
  //  - `emit`    output port wired to host `Intake` place.
  //  - `emit`    channel    fused with host `sync` transition.
  .compose(prodInst, (b) =>
    b
      .bindPort('trigger', producerTrigger)
      .bindPort('emit', intake)
      .bindChannel('emit', sync),
  )
  // Buffer subnet:
  //  - `put` input port  bridged from host `Intake` (producer output).
  //  - `get` output port bridged to host `CustomerInput`.
  //  - `admit` channel   fused with the same `sync` transition — so
  //    producer-emit and buffer-admit fire atomically together
  //    (channel-to-channel composition across two subnets).
  .compose(bufInst, (b) =>
    b
      .bindPort('put', intake)
      .bindPort('get', customerInput)
      .bindChannel('admit', sync),
  )
  .build();

const dot = dotExport(net, {
  direction: 'TB',
  showTypes: true,
  showIntervals: true,
  showPriority: true,
  environmentPlaces: new Set(['Events']),
});

const here = dirname(fileURLToPath(import.meta.url));
const outPath = resolve(here, '../../sample.dot');
writeFileSync(outPath, dot, 'utf8');

console.log(`Wrote ${outPath} (${dot.length} bytes)`);
