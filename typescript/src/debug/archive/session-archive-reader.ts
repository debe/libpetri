/**
 * Reads session archives from length-prefixed binary format.
 */

import { gunzipSync } from 'node:zlib';
import { DebugEventStore } from '../debug-event-store.js';
import type { NetEventInfo } from '../debug-response.js';
import type { NetEvent } from '../../event/net-event.js';
import type { Token } from '../../core/token.js';
import type { SessionArchive } from './session-archive.js';
import { CURRENT_VERSION } from './session-archive.js';

export interface ImportedSession {
  readonly metadata: SessionArchive;
  readonly eventStore: DebugEventStore;
}

const MAX_EVENT_SIZE = 10 * 1024 * 1024; // 10 MB

export class SessionArchiveReader {

  /** Reads only the metadata header from an archive. */
  readMetadata(compressed: Buffer): SessionArchive {
    const data = gunzipSync(compressed);
    const metaLen = data.readUInt32BE(0);
    const metaJson = data.subarray(4, 4 + metaLen).toString('utf-8');
    const metadata: SessionArchive = JSON.parse(metaJson);
    if (metadata.version !== CURRENT_VERSION) {
      throw new Error(`Unsupported archive version: ${metadata.version} (expected ${CURRENT_VERSION})`);
    }
    return metadata;
  }

  /** Reads the full archive: metadata + all events into a DebugEventStore. */
  readFull(compressed: Buffer): ImportedSession {
    const data = gunzipSync(compressed);
    let offset = 0;

    // Read metadata
    const metaLen = data.readUInt32BE(offset);
    offset += 4;
    const metaJson = data.subarray(offset, offset + metaLen).toString('utf-8');
    offset += metaLen;
    const metadata: SessionArchive = JSON.parse(metaJson);
    if (metadata.version !== CURRENT_VERSION) {
      throw new Error(`Unsupported archive version: ${metadata.version} (expected ${CURRENT_VERSION})`);
    }

    // Read events
    const eventStore = new DebugEventStore(metadata.sessionId, Number.MAX_SAFE_INTEGER);
    while (offset < data.length) {
      if (offset + 4 > data.length) break;
      const eventLen = data.readUInt32BE(offset);
      offset += 4;
      if (eventLen <= 0 || eventLen > MAX_EVENT_SIZE) {
        throw new Error(`Invalid event size: ${eventLen}`);
      }
      if (offset + eventLen > data.length) break;
      const eventJson = data.subarray(offset, offset + eventLen).toString('utf-8');
      offset += eventLen;

      const eventInfo: NetEventInfo = JSON.parse(eventJson);
      const netEvent = eventInfoToNetEvent(eventInfo);
      eventStore.append(netEvent);
    }

    return { metadata, eventStore };
  }
}

/** Converts a serialized NetEventInfo back to a NetEvent. */
function eventInfoToNetEvent(info: NetEventInfo): NetEvent {
  const timestamp = new Date(info.timestamp).getTime();
  const d = info.details;

  switch (info.type) {
    case 'ExecutionStarted':
      return { type: 'execution-started', timestamp, netName: d['netName'] as string, executionId: d['executionId'] as string };
    case 'ExecutionCompleted':
      return { type: 'execution-completed', timestamp, netName: d['netName'] as string, executionId: d['executionId'] as string, totalDurationMs: d['totalDurationMs'] as number };
    case 'TransitionEnabled':
      return { type: 'transition-enabled', timestamp, transitionName: info.transitionName! };
    case 'TransitionClockRestarted':
      return { type: 'transition-clock-restarted', timestamp, transitionName: info.transitionName! };
    case 'TransitionStarted': {
      const tokens = (d['consumedTokens'] as Array<{ type: string; value: string | null; timestamp: string | null }>)
        .map(t => infoToToken(t));
      return { type: 'transition-started', timestamp, transitionName: info.transitionName!, consumedTokens: tokens };
    }
    case 'TransitionCompleted': {
      const tokens = (d['producedTokens'] as Array<{ type: string; value: string | null; timestamp: string | null }>)
        .map(t => infoToToken(t));
      return { type: 'transition-completed', timestamp, transitionName: info.transitionName!, producedTokens: tokens, durationMs: d['durationMs'] as number };
    }
    case 'TransitionFailed':
      return { type: 'transition-failed', timestamp, transitionName: info.transitionName!, errorMessage: d['errorMessage'] as string, exceptionType: d['exceptionType'] as string };
    case 'TransitionTimedOut':
      return { type: 'transition-timed-out', timestamp, transitionName: info.transitionName!, deadlineMs: d['deadlineMs'] as number, actualDurationMs: d['actualDurationMs'] as number };
    case 'ActionTimedOut':
      return { type: 'action-timed-out', timestamp, transitionName: info.transitionName!, timeoutMs: d['timeoutMs'] as number };
    case 'TokenAdded': {
      const t = d['token'] as { type: string; value: string | null; timestamp: string | null };
      return { type: 'token-added', timestamp, placeName: info.placeName!, token: infoToToken(t) };
    }
    case 'TokenRemoved': {
      const t = d['token'] as { type: string; value: string | null; timestamp: string | null };
      return { type: 'token-removed', timestamp, placeName: info.placeName!, token: infoToToken(t) };
    }
    case 'MarkingSnapshot': {
      const markingData = d['marking'] as Record<string, Array<{ type: string; value: string | null; timestamp: string | null }>>;
      const marking = new Map<string, Token<unknown>[]>();
      for (const [place, tokens] of Object.entries(markingData)) {
        marking.set(place, tokens.map(t => infoToToken(t)));
      }
      return { type: 'marking-snapshot', timestamp, marking };
    }
    case 'LogMessage':
      return {
        type: 'log-message',
        timestamp,
        transitionName: info.transitionName!,
        logger: d['loggerName'] as string,
        level: d['level'] as string,
        message: d['message'] as string,
        error: (d['throwable'] as string | undefined) ?? null,
        errorMessage: (d['throwableMessage'] as string | undefined) ?? null,
      };
    default:
      // Fallback: create a minimal event for unknown types
      return { type: 'transition-enabled', timestamp, transitionName: info.transitionName ?? 'unknown' };
  }
}

function infoToToken(t: { type: string; value: string | null; timestamp: string | null }): Token<unknown> {
  return {
    value: t.value,
    createdAt: t.timestamp ? new Date(t.timestamp).getTime() : Date.now(),
  };
}
