/**
 * Shared metadata computation for session archives.
 *
 * Mirrors the Java `SessionMetadata.computeFrom` helper: single-pass scan of
 * an event iterable producing the histogram / first-last timestamps /
 * hasErrors triple. Reused by the v2 archive writer (at archive time) and by
 * read-path fallbacks that need aggregate stats for a v1 archive.
 */

import type { NetEvent } from '../../event/net-event.js';
import { toEventInfo } from '../net-event-converter.js';
import type { SessionMetadata } from './session-archive.js';

/**
 * Walks the given event sequence once and produces a {@link SessionMetadata}
 * summary. Allocates one intermediate object for the histogram plus the
 * returned immutable-ish record.
 *
 * Histogram keys match the wire format emitted by {@link toEventInfo}
 * (PascalCase like `TransitionStarted`, `LogMessage`) so they are identical
 * to what the Java and Rust implementations produce.
 *
 * Keys are emitted in alphabetical order for deterministic JSON output
 * (prompt-cache friendly).
 */
export function computeMetadata(events: Iterable<NetEvent>): SessionMetadata {
  const raw: Record<string, number> = {};
  let first: number | undefined;
  let last: number | undefined;
  let hasErrors = false;

  for (const event of events) {
    // Reuse toEventInfo's PascalCase mapping so histogram keys match the
    // wire format the LLM already sees. Cheap — one small object per event,
    // garbage collected immediately.
    const typeName = toEventInfo(event).type;
    raw[typeName] = (raw[typeName] ?? 0) + 1;
    if (first === undefined) first = event.timestamp;
    last = event.timestamp;
    if (isErrorEvent(event)) hasErrors = true;
  }

  // Sort keys alphabetically for a deterministic JSON key order.
  const histogram: Record<string, number> = {};
  for (const key of Object.keys(raw).sort()) {
    histogram[key] = raw[key]!;
  }

  return {
    eventTypeHistogram: histogram,
    firstEventTime: first !== undefined ? new Date(first).toISOString() : undefined,
    lastEventTime: last !== undefined ? new Date(last).toISOString() : undefined,
    hasErrors,
  };
}

/**
 * Superset of `isFailureEvent` from `net-event.ts` that additionally treats
 * `LogMessage` at level `ERROR` (case-insensitive) as an error signal.
 *
 * Kept private to this module — `isFailureEvent` has a narrower meaning
 * (transition lifecycle failures only) and other callers rely on that.
 */
function isErrorEvent(event: NetEvent): boolean {
  switch (event.type) {
    case 'transition-failed':
    case 'transition-timed-out':
    case 'action-timed-out':
      return true;
    case 'log-message':
      return event.level.toUpperCase() === 'ERROR';
    default:
      return false;
  }
}
