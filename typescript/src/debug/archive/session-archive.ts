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
 * - **v2** (libpetri 1.7.x): adds `endTime`, user-defined `tags`, and pre-computed
 *   {@link SessionMetadata}. Events inside v2 archives use the legacy `toString`-based
 *   token format — types are erased on disk.
 * - **v3** (libpetri 1.8.0+): same header shape as v2. Differs in the event body —
 *   token values are serialized with a `structured` JSON payload in addition to the
 *   legacy `value` string, so consumers that understand the original shape can
 *   surface typed fields without parsing the `toString` form.
 *
 * The {@link SessionArchiveReader} peeks the `version` field via a lenient JSON
 * parse and dispatches to the correct concrete type. All three versions coexist
 * in the same storage bucket.
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
 * v3 archive header (libpetri 1.8.0+). Structurally identical to `SessionArchiveV2`;
 * the version bump signals that the event body carries `structured` token payloads
 * alongside the legacy `value` string.
 */
export interface SessionArchiveV3 extends SessionArchiveBase {
  readonly version: 3;
  readonly endTime?: string;
  readonly tags: Readonly<Record<string, string>>;
  readonly metadata: SessionMetadata;
}

/**
 * Discriminated union of all supported archive header versions.
 *
 * Type-narrowing example:
 * ```ts
 * if (archive.version >= 2) {
 *   // TS knows archive has tags / endTime / metadata here.
 * }
 * ```
 */
export type SessionArchive = SessionArchiveV1 | SessionArchiveV2 | SessionArchiveV3;

/** Version written by default by {@link SessionArchiveWriter.write} (latest supported). */
export const CURRENT_VERSION = 3;

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
