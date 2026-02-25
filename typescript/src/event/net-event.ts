import type { Token } from '../core/token.js';

/**
 * Events emitted during Petri Net execution.
 * Discriminated union capturing all observable state changes.
 */
export type NetEvent =
  | ExecutionStarted
  | ExecutionCompleted
  | TransitionEnabled
  | TransitionClockRestarted
  | TransitionStarted
  | TransitionCompleted
  | TransitionFailed
  | TransitionTimedOut
  | ActionTimedOut
  | TokenAdded
  | TokenRemoved
  | LogMessage
  | MarkingSnapshot;

// ======================== Execution Lifecycle ========================

export interface ExecutionStarted {
  readonly type: 'execution-started';
  readonly timestamp: number;
  readonly netName: string;
  readonly executionId: string;
}

export interface ExecutionCompleted {
  readonly type: 'execution-completed';
  readonly timestamp: number;
  readonly netName: string;
  readonly executionId: string;
  readonly totalDurationMs: number;
}

// ======================== Transition Lifecycle ========================

export interface TransitionEnabled {
  readonly type: 'transition-enabled';
  readonly timestamp: number;
  readonly transitionName: string;
}

export interface TransitionClockRestarted {
  readonly type: 'transition-clock-restarted';
  readonly timestamp: number;
  readonly transitionName: string;
}

export interface TransitionStarted {
  readonly type: 'transition-started';
  readonly timestamp: number;
  readonly transitionName: string;
  readonly consumedTokens: readonly Token<unknown>[];
}

export interface TransitionCompleted {
  readonly type: 'transition-completed';
  readonly timestamp: number;
  readonly transitionName: string;
  readonly producedTokens: readonly Token<unknown>[];
  readonly durationMs: number;
}

export interface TransitionFailed {
  readonly type: 'transition-failed';
  readonly timestamp: number;
  readonly transitionName: string;
  readonly errorMessage: string;
  readonly exceptionType: string;
  /** Original stack trace, if available. */
  readonly stack?: string;
}

/**
 * Emitted when a transition exceeds its deadline (upper time bound) without firing.
 * Classical TPN semantics: transition is forcibly disabled by the executor in
 * `updateDirtyTransitions()` when elapsed time exceeds `latest(timing)`.
 */
export interface TransitionTimedOut {
  readonly type: 'transition-timed-out';
  readonly timestamp: number;
  readonly transitionName: string;
  /** The deadline that was exceeded, in milliseconds from enablement. */
  readonly deadlineMs: number;
  /** Actual time elapsed since enablement, in milliseconds. */
  readonly actualDurationMs: number;
}

export interface ActionTimedOut {
  readonly type: 'action-timed-out';
  readonly timestamp: number;
  readonly transitionName: string;
  readonly timeoutMs: number;
}

// ======================== Token Movement ========================

export interface TokenAdded {
  readonly type: 'token-added';
  readonly timestamp: number;
  readonly placeName: string;
  readonly token: Token<unknown>;
}

export interface TokenRemoved {
  readonly type: 'token-removed';
  readonly timestamp: number;
  readonly placeName: string;
  readonly token: Token<unknown>;
}

// ======================== Log Capture ========================

export interface LogMessage {
  readonly type: 'log-message';
  readonly timestamp: number;
  readonly transitionName: string;
  readonly logger: string;
  readonly level: string;
  readonly message: string;
  readonly error: string | null;
  readonly errorMessage: string | null;
}

// ======================== Checkpointing ========================

/**
 * Snapshot of the full marking (token state) at a point in time.
 * Emitted at two points during execution:
 * 1. After initialization (before the main loop) — captures the initial marking
 * 2. Before the execution-completed event — captures the final marking
 */
export interface MarkingSnapshot {
  readonly type: 'marking-snapshot';
  readonly timestamp: number;
  /** Place name -> tokens in that place at snapshot time. Only non-empty places are included. */
  readonly marking: ReadonlyMap<string, readonly Token<unknown>[]>;
}

// ======================== Helper Functions ========================

/** Extracts transition name from events that have one. Returns null otherwise. */
export function eventTransitionName(event: NetEvent): string | null {
  switch (event.type) {
    case 'transition-enabled':
    case 'transition-clock-restarted':
    case 'transition-started':
    case 'transition-completed':
    case 'transition-failed':
    case 'transition-timed-out':
    case 'action-timed-out':
    case 'log-message':
      return event.transitionName;
    default:
      return null;
  }
}

/** Checks if the event is a failure type. */
export function isFailureEvent(event: NetEvent): boolean {
  return event.type === 'transition-failed'
    || event.type === 'transition-timed-out'
    || event.type === 'action-timed-out';
}
