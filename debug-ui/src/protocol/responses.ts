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
}

export interface TransitionInfo {
  readonly name: string;
  readonly graphId: string;
}

export interface NetStructure {
  readonly places: readonly PlaceInfo[];
  readonly transitions: readonly TransitionInfo[];
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
  | { readonly type: 'error'; readonly code: string; readonly message: string; readonly sessionId: string | null };
