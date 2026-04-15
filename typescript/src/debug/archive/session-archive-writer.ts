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
 * `write()` defaults to {@link CURRENT_VERSION} (v2 as of libpetri 1.7.0).
 * Callers that need to emit legacy archives — compatibility tests or readers
 * pinned to libpetri ≤ 1.6.1 — can call `writeV1()`. v2 archives cost one extra
 * pass over the event store to pre-compute {@link SessionMetadata}; the savings
 * at read time (no event scan needed for hasErrors / histogram queries) pay it
 * back the first time a caller lists or samples a bucket of sessions.
 */

import { gzipSync } from 'node:zlib';
import type { DebugSession } from '../debug-session-registry.js';
import { buildNetStructure } from '../debug-session-registry.js';
import { toEventInfo } from '../net-event-converter.js';
import type { SessionArchive, SessionArchiveV1, SessionArchiveV2 } from './session-archive.js';
import { computeMetadata } from './session-metadata.js';

export class SessionArchiveWriter {
  /**
   * Writes a complete session archive in the current format (v2 as of 1.7.0)
   * and returns the compressed bytes.
   */
  write(session: DebugSession): Buffer {
    return this.writeV2(session);
  }

  /**
   * Writes a session in the legacy v1 format. Use only for compatibility
   * testing or when producing archives for consumers pinned to libpetri ≤ 1.6.1.
   */
  writeV1(session: DebugSession): Buffer {
    const header: SessionArchiveV1 = {
      version: 1,
      sessionId: session.sessionId,
      netName: session.netName,
      dotDiagram: session.dotDiagram,
      startTime: new Date(session.startTime).toISOString(),
      eventCount: session.eventStore.eventCount(),
      structure: buildNetStructure(session),
    };
    return this.writeFramed(header, session);
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
    const metadata = computeMetadata(session.eventStore);

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
      eventCount: session.eventStore.eventCount(),
      // Snapshot of tags at archive-write time — record the state that was
      // current when the session was archived, not whatever happens on the
      // live session afterwards.
      tags: { ...session.tags },
      metadata,
      structure: buildNetStructure(session),
    };
    return this.writeFramed(header, session);
  }

  /**
   * Shared framing logic: length-prefixed header JSON, then length-prefixed
   * event JSON, then gzip. Both v1 and v2 archives use the identical event
   * wire format, so the body loop is version-agnostic.
   */
  private writeFramed(header: SessionArchive, session: DebugSession): Buffer {
    const parts: Buffer[] = [];

    // Header
    const metaBytes = Buffer.from(JSON.stringify(header), 'utf-8');
    const metaLen = Buffer.alloc(4);
    metaLen.writeUInt32BE(metaBytes.length);
    parts.push(metaLen, metaBytes);

    // Events — same serialization for both versions
    for (const event of session.eventStore) {
      const eventInfo = toEventInfo(event);
      const eventBytes = Buffer.from(JSON.stringify(eventInfo), 'utf-8');
      const eventLen = Buffer.alloc(4);
      eventLen.writeUInt32BE(eventBytes.length);
      parts.push(eventLen, eventBytes);
    }

    return gzipSync(Buffer.concat(parts));
  }
}
