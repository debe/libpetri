/**
 * Reads session archives from length-prefixed binary format.
 *
 * Handles both v1 (libpetri 1.5.x–1.6.x) and v2 (libpetri 1.7.0+) archives via
 * a lenient "version probe": parse the header JSON once, switch on the
 * `version` field, narrow to the correct concrete type, and normalize missing
 * optional fields to their defaults. Events inside the body use the same wire
 * format across versions, so the event read path is shared.
 */

import { gunzipSync } from 'node:zlib';
import { DebugEventStore } from '../debug-event-store.js';
import type { NetEventInfo } from '../debug-response.js';
import type { NetEvent } from '../../event/net-event.js';
import type { Token } from '../../core/token.js';
import type {
  SessionArchive,
  SessionArchiveV1,
  SessionArchiveV2,
  SessionArchiveV3,
} from './session-archive.js';
import {
  CURRENT_VERSION,
  MIN_SUPPORTED_VERSION,
  emptyMetadata,
} from './session-archive.js';

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
    return parseHeader(metaJson);
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
    const metadata = parseHeader(metaJson);

    // Read events — same wire format across versions.
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

/**
 * Peeks the archive `version` field via a single JSON parse, then narrows the
 * result into the correct {@link SessionArchive} variant. v2-only optional
 * fields (`tags`, `metadata`) are normalized to their empty defaults so
 * callers never need to guard against `undefined` on a declared-v2 archive.
 */
function parseHeader(metaJson: string): SessionArchive {
  const raw = JSON.parse(metaJson) as { version: number } & Record<string, unknown>;
  switch (raw.version) {
    case 1:
      return raw as unknown as SessionArchiveV1;
    case 2: {
      const v2 = raw as unknown as SessionArchiveV2;
      // Normalize: v2 defines tags + metadata as REQUIRED in the type, but a
      // hand-written or partially-built header could omit them — fall back
      // to empty defaults rather than emit `undefined` into typed code.
      return {
        ...v2,
        tags: v2.tags ?? {},
        metadata: v2.metadata ?? emptyMetadata(),
      };
    }
    case 3: {
      const v3 = raw as unknown as SessionArchiveV3;
      return {
        ...v3,
        tags: v3.tags ?? {},
        metadata: v3.metadata ?? emptyMetadata(),
      };
    }
    default:
      throw new Error(
        `Unsupported archive version: ${raw.version} ` +
          `(reader supports ${MIN_SUPPORTED_VERSION}..${CURRENT_VERSION})`,
      );
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
      const tokens = (d['consumedTokens'] as readonly WireTokenInfo[])
        .map(t => infoToToken(t));
      return { type: 'transition-started', timestamp, transitionName: info.transitionName!, consumedTokens: tokens };
    }
    case 'TransitionCompleted': {
      const tokens = (d['producedTokens'] as readonly WireTokenInfo[])
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
      const t = d['token'] as WireTokenInfo;
      return { type: 'token-added', timestamp, placeName: info.placeName!, token: infoToToken(t) };
    }
    case 'TokenRemoved': {
      const t = d['token'] as WireTokenInfo;
      return { type: 'token-removed', timestamp, placeName: info.placeName!, token: infoToToken(t) };
    }
    case 'MarkingSnapshot': {
      const markingData = d['marking'] as Record<string, readonly WireTokenInfo[]>;
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

/**
 * Wire shape of a serialized token body. Matches {@link TokenInfo} minus the
 * `id` field (archives never emit token identity). `structured` is optional
 * and preserved verbatim on replay per EVT-025 AC5.
 */
interface WireTokenInfo {
  readonly type: string;
  readonly value: string | null;
  readonly structured?: unknown;
  readonly timestamp: string | null;
}

function infoToToken(t: WireTokenInfo): Token<unknown> {
  const createdAt = t.timestamp ? new Date(t.timestamp).getTime() : Date.now();
  // Preserve `structured` only when the writer emitted it — keep live-token
  // shape (no `structured` field) identical for tokens that lacked it.
  return t.structured === undefined
    ? { value: t.value, createdAt }
    : { value: t.value, createdAt, structured: t.structured };
}
