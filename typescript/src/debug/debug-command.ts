/**
 * Commands sent from debug UI client to server via WebSocket.
 * TypeScript port of Java's DebugCommand sealed interface.
 */

export type SubscriptionMode = 'live' | 'replay';

export type BreakpointType =
  | 'TRANSITION_ENABLED'
  | 'TRANSITION_START'
  | 'TRANSITION_COMPLETE'
  | 'TRANSITION_FAIL'
  | 'TOKEN_ADDED'
  | 'TOKEN_REMOVED';

export interface BreakpointConfig {
  readonly id: string;
  readonly type: BreakpointType;
  readonly target: string | null;
  readonly enabled: boolean;
}

export interface EventFilter {
  readonly eventTypes: readonly string[] | null;
  readonly transitionNames: readonly string[] | null;
  readonly placeNames: readonly string[] | null;
}

export type DebugCommand =
  | { readonly type: 'subscribe'; readonly sessionId: string; readonly mode: SubscriptionMode; readonly fromIndex?: number }
  | { readonly type: 'unsubscribe'; readonly sessionId: string }
  | { readonly type: 'listSessions'; readonly limit?: number; readonly activeOnly?: boolean }
  | { readonly type: 'seek'; readonly sessionId: string; readonly timestamp: string }
  | { readonly type: 'playbackSpeed'; readonly sessionId: string; readonly speed: number }
  | { readonly type: 'filter'; readonly sessionId: string; readonly filter: EventFilter }
  | { readonly type: 'pause'; readonly sessionId: string }
  | { readonly type: 'resume'; readonly sessionId: string }
  | { readonly type: 'stepForward'; readonly sessionId: string }
  | { readonly type: 'stepBackward'; readonly sessionId: string }
  | { readonly type: 'setBreakpoint'; readonly sessionId: string; readonly breakpoint: BreakpointConfig }
  | { readonly type: 'clearBreakpoint'; readonly sessionId: string; readonly breakpointId: string }
  | { readonly type: 'listBreakpoints'; readonly sessionId: string };

export function eventFilterAll(): EventFilter {
  return { eventTypes: null, transitionNames: null, placeNames: null };
}
