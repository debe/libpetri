/**
 * Writes a debug session to a length-prefixed binary archive format.
 *
 * Format (inside gzip):
 * `[4 bytes: metadata JSON length][N bytes: metadata JSON]`
 * `[4 bytes: event JSON length][N bytes: event JSON]`
 * ...
 * (EOF terminates the stream)
 *
 * ## Format selection
 *
 * `write()` defaults to {@link CURRENT_VERSION} (v3 as of libpetri 1.8.0).
 * Callers that need to emit legacy archives — compatibility tests or readers
 * pinned to older libpetri versions — can call `writeV1()` or `writeV2()`.
 *
 * Note: all writers now emit the v3 token body format (structured alongside
 * value-string) regardless of header version. A 1.8.0+ writer cannot produce
 * byte-for-byte 1.7.x event bodies.
 *
 * Cross-language note: the `type` field in each serialized `TokenInfo` is
 * `value.constructor.name` — a simple name, not an FQN. Replaying a TypeScript
 * archive through the Java reader therefore cannot reconstruct the original
 * typed token (Java needs an FQN to `Class.forName`); Java falls through to
 * `Token<JsonNode>` preserving the `structured` JSON payload. See
 * {@link tokenInfo} for the full asymmetry and the [EVT-025](../../../../spec/08-events-observability.md)
 * spec entry for the full wire-format contract.
 */

import { gzipSync } from 'node:zlib';
import type { DebugSession } from '../debug-session-registry.js';
import { buildNetStructure } from '../debug-session-registry.js';
import type { NetEvent } from '../../event/net-event.js';
import { toEventInfo } from '../net-event-converter.js';
import type {
  SessionArchive,
  SessionArchiveV1,
  SessionArchiveV2,
  SessionArchiveV3,
} from './session-archive.js';
import { computeMetadata } from './session-metadata.js';

export class SessionArchiveWriter {
  /**
   * Writes a complete session archive in the current format (v3 as of 1.8.0)
   * and returns the compressed bytes.
   */
  write(session: DebugSession): Buffer {
    return this.writeV3(session);
  }

  /**
   * Writes a session in the legacy v1 format. Use only for compatibility
   * testing or when producing archives for consumers pinned to libpetri ≤ 1.6.1.
   */
  writeV1(session: DebugSession): Buffer {
    // Single snapshot — both header eventCount and body iterate the same frozen array.
    // DebugEventStore.events() returns the live readonly array, so we spread once and
    // freeze to make accidental mutation a runtime error.
    const events: readonly NetEvent[] = Object.freeze([...session.eventStore.events()]);
    const header: SessionArchiveV1 = {
      version: 1,
      sessionId: session.sessionId,
      netName: session.netName,
      dotDiagram: session.dotDiagram,
      startTime: new Date(session.startTime).toISOString(),
      eventCount: events.length,
      structure: buildNetStructure(session),
    };
    return this.writeFramed(header, events);
  }

  /**
   * Writes a session in the v2 format — richer header with `endTime`, `tags`,
   * and pre-computed {@link SessionMetadata}.
   *
   * Two passes over the event store: one to compute metadata, one to serialize
   * events. `DebugEventStore` stores events in a plain readonly array and its
   * `[Symbol.iterator]()` returns a fresh array iterator each call, so both
   * passes walk the same sequence from the start.
   */
  writeV2(session: DebugSession): Buffer {
    // Single snapshot drives metadata, header eventCount, and body. See writeV1.
    const events: readonly NetEvent[] = Object.freeze([...session.eventStore.events()]);
    const metadata = computeMetadata(events);

    const header: SessionArchiveV2 = {
      version: 2,
      sessionId: session.sessionId,
      netName: session.netName,
      dotDiagram: session.dotDiagram,
      startTime: new Date(session.startTime).toISOString(),
      endTime:
        session.endTime !== undefined
          ? new Date(session.endTime).toISOString()
          : undefined,
      eventCount: events.length,
      // Snapshot of tags at archive-write time — record the state that was
      // current when the session was archived, not whatever happens on the
      // live session afterwards.
      tags: { ...session.tags },
      metadata,
      structure: buildNetStructure(session),
    };
    return this.writeFramed(header, events);
  }

  /**
   * Writes a session in the v3 format — same header shape as v2, with version=3
   * signalling that token payloads carry a `structured` field alongside the
   * legacy `value` string (see {@link tokenInfo}).
   */
  writeV3(session: DebugSession): Buffer {
    // Single snapshot drives metadata, header eventCount, and body. See writeV1.
    const events: readonly NetEvent[] = Object.freeze([...session.eventStore.events()]);
    const metadata = computeMetadata(events);

    const header: SessionArchiveV3 = {
      version: 3,
      sessionId: session.sessionId,
      netName: session.netName,
      dotDiagram: session.dotDiagram,
      startTime: new Date(session.startTime).toISOString(),
      endTime:
        session.endTime !== undefined
          ? new Date(session.endTime).toISOString()
          : undefined,
      eventCount: events.length,
      tags: { ...session.tags },
      metadata,
      structure: buildNetStructure(session),
    };
    return this.writeFramed(header, events);
  }

  /**
   * Shared framing logic: length-prefixed header JSON, then length-prefixed
   * event JSON, then gzip. All header versions share the identical event wire
   * format, so the body loop is version-agnostic.
   *
   * Takes the events snapshot directly so the body iterates the same array the
   * caller used to populate {@link SessionArchive.eventCount} — preserving the
   * `header.eventCount === events.length` invariant.
   */
  private writeFramed(header: SessionArchive, events: readonly NetEvent[]): Buffer {
    const parts: Buffer[] = [];

    // Header
    const metaBytes = Buffer.from(JSON.stringify(header), 'utf-8');
    const metaLen = Buffer.alloc(4);
    metaLen.writeUInt32BE(metaBytes.length);
    parts.push(metaLen, metaBytes);

    // Events — same serialization across all header versions
    for (const event of events) {
      const eventInfo = toEventInfo(event);
      const eventBytes = Buffer.from(JSON.stringify(eventInfo), 'utf-8');
      const eventLen = Buffer.alloc(4);
      eventLen.writeUInt32BE(eventBytes.length);
      parts.push(eventLen, eventBytes);
    }

    return gzipSync(Buffer.concat(parts));
  }
}
