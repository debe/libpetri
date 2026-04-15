/**
 * Metadata header for a session archive file.
 *
 * Discriminated union across format versions so callers can pattern-match on
 * `archive.version` to access v2-only fields with type narrowing:
 *
 * ```ts
 * const archive = reader.readMetadata(bytes);
 * if (archive.version === 2) {
 *   console.log(archive.tags, archive.endTime, archive.metadata.hasErrors);
 * }
 * ```
 *
 * ## Version contract
 *
 * - **v1** (libpetri 1.5.x–1.6.x): original format. Header carries `sessionId`,
 *   `netName`, `dotDiagram`, `startTime`, `eventCount`, and net `structure`.
 * - **v2** (libpetri 1.7.0+): adds `endTime`, user-defined `tags`, and pre-computed
 *   {@link SessionMetadata} (event-type histogram, first/last event timestamps,
 *   hasErrors). Events inside v2 archives are serialized the same way as in v1 —
 *   only the header is enriched.
 *
 * The {@link SessionArchiveReader} peeks the `version` field via a lenient JSON
 * parse and dispatches to the correct concrete type. Both v1 and v2 archives
 * remain readable and may coexist in the same storage bucket.
 */
import type { NetStructure } from '../debug-response.js';

/** Common fields shared by v1 and v2 archive headers. */
interface SessionArchiveBase {
  readonly sessionId: string;
  readonly netName: string;
  readonly dotDiagram: string;
  /** ISO-8601 instant the session started. */
  readonly startTime: string;
  readonly eventCount: number;
  readonly structure: NetStructure;
}

/** Legacy v1 archive header (libpetri 1.5.x–1.6.x). */
export interface SessionArchiveV1 extends SessionArchiveBase {
  readonly version: 1;
}

/**
 * v2 archive header (libpetri 1.7.0+). Adds end time, tags, and pre-computed
 * metadata so listing tools and samplers can filter/aggregate without scanning
 * the event body.
 */
export interface SessionArchiveV2 extends SessionArchiveBase {
  readonly version: 2;
  /** ISO-8601 instant the session ended. Undefined for sessions archived while still active. */
  readonly endTime?: string;
  /** User-defined session tags (e.g., `{channel: "voice"}`). Always present; may be empty. */
  readonly tags: Readonly<Record<string, string>>;
  /** Pre-computed aggregate stats. Always present; `emptyMetadata()` for no-event sessions. */
  readonly metadata: SessionMetadata;
}

/**
 * Discriminated union of all supported archive header versions.
 *
 * Type-narrowing example:
 * ```ts
 * if (archive.version === 2) {
 *   // TS knows archive is SessionArchiveV2 here — tags / endTime / metadata typed.
 * }
 * ```
 */
export type SessionArchive = SessionArchiveV1 | SessionArchiveV2;

/** Version written by default by {@link SessionArchiveWriter.write} (latest supported). */
export const CURRENT_VERSION = 2;

/** Lowest version {@link SessionArchiveReader} can decode. */
export const MIN_SUPPORTED_VERSION = 1;

/**
 * Pre-computed aggregate statistics attached to a v2 session archive header.
 *
 * Computed once during archive write by a single-pass scan of the event store.
 * Readers can answer `hasErrors`, histogram, and first/last timestamp queries
 * without iterating the event stream — enabling cheap triage, sampling, and
 * listing of many archives.
 *
 * For v1 archives (no pre-computed metadata), callers can recompute on-demand
 * via {@link computeMetadata}.
 */
export interface SessionMetadata {
  /**
   * Count of events per `NetEvent` subtype name (PascalCase, matching the
   * wire format used by `NetEventInfo.type` — e.g. `TransitionStarted -> 412`).
   * Keys are stored in alphabetical order for deterministic JSON output.
   */
  readonly eventTypeHistogram: Readonly<Record<string, number>>;
  /** ISO-8601 timestamp of the oldest event, or undefined if the session had no events. */
  readonly firstEventTime?: string;
  /** ISO-8601 timestamp of the newest event, or undefined if the session had no events. */
  readonly lastEventTime?: string;
  /**
   * True if the session contains at least one error-signal event
   * (`TransitionFailed`, `TransitionTimedOut`, `ActionTimedOut`, or
   * a `LogMessage` at level `ERROR`).
   */
  readonly hasErrors: boolean;
}

/** Returns a {@link SessionMetadata} with no data. Used as a default for empty sessions. */
export function emptyMetadata(): SessionMetadata {
  return { eventTypeHistogram: {}, hasErrors: false };
}
