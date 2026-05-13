/**
 * Debug protocol responses sent from server to UI client via WebSocket.
 */

import type { BreakpointConfig, EventFilter } from './commands.js';

export interface SessionSummary {
  readonly sessionId: string;
  readonly netName: string;
  readonly startTime: string;
  readonly active: boolean;
  readonly eventCount: number;
}

export interface TokenInfo {
  readonly id: string | null;
  readonly type: string;
  readonly value: string | null;
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
   * Derived instance prefix per `spec/11-modular-composition.md` MOD-041:
   * substring before the last `/` of {@link name}; omitted from the wire
   * when the place is not part of any composed subnet instance.
   */
  readonly instancePrefix?: string;
}

export interface TransitionInfo {
  readonly name: string;
  readonly graphId: string;
  /**
   * Derived instance prefix per `spec/11-modular-composition.md` MOD-041:
   * substring before the last `/` of {@link name}; omitted from the wire
   * when the transition is not part of any composed subnet instance.
   */
  readonly instancePrefix?: string;
}

export interface NetStructure {
  readonly places: readonly PlaceInfo[];
  readonly transitions: readonly TransitionInfo[];
}

/**
 * Wire-facing descriptor of one composed subnet instance per
 * `spec/11-modular-composition.md` MOD-041. Mirrors {@code SubnetInstanceInfo}
 * in Java and TypeScript: carries fully-prefixed names rather than object
 * references so the JSON shape stays simple. {@link defName} and
 * {@link parentPrefix} are omitted entirely from the wire when absent
 * (the v1 runtime does not track subnet-def provenance after composition,
 * and top-level instances have no parent).
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
       * Composed subnet instance descriptors per `spec/11-modular-composition.md`
       * MOD-041. Always present; empty array for flat (non-composed) nets.
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
