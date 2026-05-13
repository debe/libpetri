/**
 * Responses sent from server to debug UI client via WebSocket.
 * TypeScript port of Java's DebugResponse sealed interface.
 */

import type { BreakpointConfig, EventFilter } from './debug-command.js';

export interface SessionSummary {
  readonly sessionId: string;
  readonly netName: string;
  readonly startTime: string;
  readonly active: boolean;
  readonly eventCount: number;
  /** User-defined session tags. Empty object if none. (libpetri 1.6.0+) */
  readonly tags?: Readonly<Record<string, string>>;
  /** ISO-8601 end time, present only for completed sessions. (libpetri 1.6.0+) */
  readonly endTime?: string;
  /** Session duration in milliseconds, present only for completed sessions. (libpetri 1.6.0+) */
  readonly durationMs?: number;
}

export interface TokenInfo {
  readonly id: string | null;
  readonly type: string;
  /**
   * `String(value)` form — stable display field that the bundled debug UI relies on.
   * Always populated unless compact mode strips values.
   */
  readonly value: string | null;
  /**
   * Structured JSON representation of the token value when the value is a plain
   * JSON-friendly object / enum-like string / primitive. Populated alongside `value`
   * (not instead of) so LLM-facing consumers can project typed fields without parsing
   * the stringified form. Omitted from the wire when absent.
   * (libpetri 1.8.0+)
   */
  readonly structured?: unknown;
  readonly timestamp: string | null;
}

export interface NetEventInfo {
  readonly type: string;
  readonly timestamp: string;
  readonly transitionName: string | null;
  readonly placeName: string | null;
  readonly details: Record<string, unknown>;
}

export interface PlaceInfo {
  readonly name: string;
  readonly graphId: string;
  readonly tokenType: string;
  readonly isStart: boolean;
  readonly isEnd: boolean;
  readonly isEnvironment: boolean;
  /**
   * Derived instance prefix per `spec/11-modular-composition.md` **MOD-041**:
   * the substring before the last `/` of {@link name}, omitted entirely from
   * the wire when the place is not part of any composed instance.
   */
  readonly instancePrefix?: string;
}

export interface TransitionInfo {
  readonly name: string;
  readonly graphId: string;
  /**
   * Derived instance prefix per `spec/11-modular-composition.md` **MOD-041**:
   * the substring before the last `/` of {@link name}, omitted entirely from
   * the wire when the transition is not part of any composed instance.
   */
  readonly instancePrefix?: string;
}

export interface NetStructure {
  readonly places: readonly PlaceInfo[];
  readonly transitions: readonly TransitionInfo[];
}

/**
 * Wire-facing descriptor of one composed subnet instance per
 * `spec/11-modular-composition.md` **MOD-041**.
 *
 * Mirrors {@code SubnetInstanceInfo} in Java: carries **names** instead of
 * object references so the JSON shape stays simple. {@link parentPrefix} is
 * absent (omitted from the wire) for top-level instances. {@link defName} is
 * absent in v1 — the runtime does not track {@code SubnetDef} provenance
 * once composition has flattened the topology.
 */
export interface SubnetInstanceInfo {
  /** Instantiation prefix (e.g. `"buf1"` or `"outer/inner"` for nested). */
  readonly prefix: string;
  /** Originating subnet definition name; absent in v1. */
  readonly defName?: string;
  /** Full prefixed transition names belonging to this instance. */
  readonly transitionNames: readonly string[];
  /** Full prefixed place names belonging to this instance. */
  readonly exposedPlaceNames: readonly string[];
  /** Parent-instance prefix; absent for top-level instances. */
  readonly parentPrefix?: string;
}

export interface ArchiveSummary {
  readonly sessionId: string;
  readonly key: string;
  readonly sizeBytes: number;
  readonly lastModified: string;
}

export type DebugResponse =
  | { readonly type: 'sessionList'; readonly sessions: readonly SessionSummary[] }
  | {
      readonly type: 'subscribed';
      readonly sessionId: string;
      readonly netName: string;
      readonly dotDiagram: string;
      readonly structure: NetStructure;
      readonly currentMarking: Record<string, readonly TokenInfo[]>;
      readonly enabledTransitions: readonly string[];
      readonly inFlightTransitions: readonly string[];
      readonly eventCount: number;
      readonly mode: string;
      /**
       * Composed subnet instance descriptors per
       * `spec/11-modular-composition.md` **MOD-041**. Empty array for nets
       * that were not produced via composition (no `/` in any node name) —
       * keeps the wire payload compact for the flat case.
       */
      readonly subnetInstances: readonly SubnetInstanceInfo[];
    }
  | { readonly type: 'unsubscribed'; readonly sessionId: string }
  | { readonly type: 'event'; readonly sessionId: string; readonly index: number; readonly event: NetEventInfo }
  | { readonly type: 'eventBatch'; readonly sessionId: string; readonly startIndex: number; readonly events: readonly NetEventInfo[]; readonly hasMore: boolean }
  | { readonly type: 'markingSnapshot'; readonly sessionId: string; readonly marking: Record<string, readonly TokenInfo[]>; readonly enabledTransitions: readonly string[]; readonly inFlightTransitions: readonly string[] }
  | { readonly type: 'playbackStateChanged'; readonly sessionId: string; readonly paused: boolean; readonly speed: number; readonly currentIndex: number }
  | { readonly type: 'filterApplied'; readonly sessionId: string; readonly filter: EventFilter }
  | { readonly type: 'breakpointHit'; readonly sessionId: string; readonly breakpointId: string; readonly event: NetEventInfo; readonly eventIndex: number }
  | { readonly type: 'breakpointList'; readonly sessionId: string; readonly breakpoints: readonly BreakpointConfig[] }
  | { readonly type: 'breakpointSet'; readonly sessionId: string; readonly breakpoint: BreakpointConfig }
  | { readonly type: 'breakpointCleared'; readonly sessionId: string; readonly breakpointId: string }
  | { readonly type: 'error'; readonly code: string; readonly message: string; readonly sessionId: string | null }
  | { readonly type: 'archiveList'; readonly archives: readonly ArchiveSummary[]; readonly storageAvailable: boolean }
  | { readonly type: 'archiveImported'; readonly sessionId: string; readonly netName: string; readonly eventCount: number };
