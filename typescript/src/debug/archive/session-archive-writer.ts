/**
 * Writes a debug session to a length-prefixed binary archive format.
 *
 * Format (inside gzip):
 * [4 bytes: metadata JSON length][N bytes: metadata JSON]
 * [4 bytes: event JSON length][N bytes: event JSON]
 * ...
 * (EOF terminates the stream)
 */

import { gzipSync } from 'node:zlib';
import type { DebugSession } from '../debug-session-registry.js';
import { buildNetStructure } from '../debug-session-registry.js';
import { toEventInfo } from '../net-event-converter.js';
import type { SessionArchive } from './session-archive.js';
import { CURRENT_VERSION } from './session-archive.js';

export class SessionArchiveWriter {

  /**
   * Writes a complete session archive and returns the compressed bytes.
   */
  write(session: DebugSession): Buffer {
    const structure = buildNetStructure(session);

    const metadata: SessionArchive = {
      version: CURRENT_VERSION,
      sessionId: session.sessionId,
      netName: session.netName,
      dotDiagram: session.dotDiagram,
      startTime: new Date(session.startTime).toISOString(),
      eventCount: session.eventStore.eventCount(),
      structure,
    };

    // Calculate total size for efficient allocation
    const parts: Buffer[] = [];

    // Metadata
    const metaBytes = Buffer.from(JSON.stringify(metadata), 'utf-8');
    const metaLen = Buffer.alloc(4);
    metaLen.writeUInt32BE(metaBytes.length);
    parts.push(metaLen, metaBytes);

    // Events
    for (const event of session.eventStore) {
      const eventInfo = toEventInfo(event);
      const eventBytes = Buffer.from(JSON.stringify(eventInfo), 'utf-8');
      const eventLen = Buffer.alloc(4);
      eventLen.writeUInt32BE(eventBytes.length);
      parts.push(eventLen, eventBytes);
    }

    const raw = Buffer.concat(parts);
    return gzipSync(raw);
  }
}
