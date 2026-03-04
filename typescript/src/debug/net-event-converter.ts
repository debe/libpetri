/**
 * Converts CTPN NetEvent instances to serializable DebugResponse types.
 * TypeScript port of Java's NetEventConverter.
 */

import type { Token } from '../core/token.js';
import type { NetEvent } from '../event/net-event.js';
import type { NetEventInfo, TokenInfo } from './debug-response.js';

/** Converts a NetEvent to a serializable NetEventInfo. */
export function toEventInfo(event: NetEvent, compact = false): NetEventInfo {
  switch (event.type) {
    case 'execution-started':
      return {
        type: 'ExecutionStarted',
        timestamp: new Date(event.timestamp).toISOString(),
        transitionName: null,
        placeName: null,
        details: { netName: event.netName, executionId: event.executionId },
      };

    case 'execution-completed':
      return {
        type: 'ExecutionCompleted',
        timestamp: new Date(event.timestamp).toISOString(),
        transitionName: null,
        placeName: null,
        details: {
          netName: event.netName,
          executionId: event.executionId,
          totalDurationMs: event.totalDurationMs,
        },
      };

    case 'transition-enabled':
      return {
        type: 'TransitionEnabled',
        timestamp: new Date(event.timestamp).toISOString(),
        transitionName: event.transitionName,
        placeName: null,
        details: {},
      };

    case 'transition-clock-restarted':
      return {
        type: 'TransitionClockRestarted',
        timestamp: new Date(event.timestamp).toISOString(),
        transitionName: event.transitionName,
        placeName: null,
        details: {},
      };

    case 'transition-started':
      return {
        type: 'TransitionStarted',
        timestamp: new Date(event.timestamp).toISOString(),
        transitionName: event.transitionName,
        placeName: null,
        details: {
          consumedTokens: event.consumedTokens.map(t => compact ? compactTokenInfo(t) : tokenInfo(t)),
        },
      };

    case 'transition-completed':
      return {
        type: 'TransitionCompleted',
        timestamp: new Date(event.timestamp).toISOString(),
        transitionName: event.transitionName,
        placeName: null,
        details: {
          producedTokens: event.producedTokens.map(t => compact ? compactTokenInfo(t) : tokenInfo(t)),
          durationMs: event.durationMs,
        },
      };

    case 'transition-failed':
      return {
        type: 'TransitionFailed',
        timestamp: new Date(event.timestamp).toISOString(),
        transitionName: event.transitionName,
        placeName: null,
        details: {
          errorMessage: event.errorMessage,
          exceptionType: event.exceptionType,
        },
      };

    case 'transition-timed-out':
      return {
        type: 'TransitionTimedOut',
        timestamp: new Date(event.timestamp).toISOString(),
        transitionName: event.transitionName,
        placeName: null,
        details: {
          deadlineMs: event.deadlineMs,
          actualDurationMs: event.actualDurationMs,
        },
      };

    case 'action-timed-out':
      return {
        type: 'ActionTimedOut',
        timestamp: new Date(event.timestamp).toISOString(),
        transitionName: event.transitionName,
        placeName: null,
        details: { timeoutMs: event.timeoutMs },
      };

    case 'token-added':
      return {
        type: 'TokenAdded',
        timestamp: new Date(event.timestamp).toISOString(),
        transitionName: null,
        placeName: event.placeName,
        details: {
          token: compact ? compactTokenInfo(event.token) : tokenInfo(event.token),
        },
      };

    case 'token-removed':
      return {
        type: 'TokenRemoved',
        timestamp: new Date(event.timestamp).toISOString(),
        transitionName: null,
        placeName: event.placeName,
        details: {
          token: compact ? compactTokenInfo(event.token) : tokenInfo(event.token),
        },
      };

    case 'marking-snapshot':
      return {
        type: 'MarkingSnapshot',
        timestamp: new Date(event.timestamp).toISOString(),
        transitionName: null,
        placeName: null,
        details: {
          marking: convertMarking(event.marking, compact),
        },
      };

    case 'log-message': {
      const details: Record<string, unknown> = {
        loggerName: event.logger,
        level: event.level,
        message: event.message,
      };
      if (event.error != null) details['throwable'] = event.error;
      if (event.errorMessage != null) details['throwableMessage'] = event.errorMessage;
      return {
        type: 'LogMessage',
        timestamp: new Date(event.timestamp).toISOString(),
        transitionName: event.transitionName,
        placeName: null,
        details,
      };
    }
  }
}

/** Converts a Token to serializable TokenInfo with full value. */
export function tokenInfo(token: Token<unknown>): TokenInfo {
  const value = token.value;
  const type = value != null ? typeof value === 'object' ? value.constructor.name : typeof value : 'null';
  const fullValue = value != null ? String(value) : 'null';
  return {
    id: null,
    type,
    value: fullValue,
    timestamp: new Date(token.createdAt).toISOString(),
  };
}

/** Converts a Token to compact TokenInfo (type only, no value). */
export function compactTokenInfo(token: Token<unknown>): TokenInfo {
  const value = token.value;
  const type = value != null ? typeof value === 'object' ? value.constructor.name : typeof value : 'null';
  return {
    id: null,
    type,
    value: null,
    timestamp: new Date(token.createdAt).toISOString(),
  };
}

/** Converts a marking map to serializable form. */
export function convertMarking(
  marking: ReadonlyMap<string, readonly Token<unknown>[]>,
  compact = false,
): Record<string, readonly TokenInfo[]> {
  const result: Record<string, readonly TokenInfo[]> = {};
  const mapper = compact ? compactTokenInfo : tokenInfo;
  for (const [name, tokens] of marking) {
    result[name] = tokens.map(mapper);
  }
  return result;
}
