/**
 * Regenerate /sample.dot from a synthetic Petri net that exercises every
 * visualization rule in spec/09-export.md (EXP-012, EXP-013, EXP-014):
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
import { dotExport } from '../src/export/dot-exporter.js';

// ============================================================
// Place fixtures — covers start / mid / end / environment
// ============================================================

const customerInput = place<string>('CustomerInput'); // start (no incoming)
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
// Build & export
// ============================================================

const net = PetriNet.builder('SampleVisualizationNet')
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
