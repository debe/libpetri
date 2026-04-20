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

/**
 * Converts a Token to a serializable {@link TokenInfo}.
 *
 * @remarks
 * The emitted `type` is `value.constructor.name` for objects and `typeof value`
 * for primitives — a *simple name*, not a fully-qualified type identifier.
 * TypeScript has no portable FQN, so cross-language replay from TypeScript
 * archives into a Java reader loses the original type identity (Java's
 * `Class.forName` will fail on simple names) and falls through to the
 * `Token<JsonNode>` graceful-degradation path. The `structured` payload
 * survives intact across languages.
 *
 * The v3 archive body format described in [EVT-025](../../../spec/08-events-observability.md)
 * always emits `structured` alongside `value` so the bundled debug UI keeps
 * rendering while LLM-facing consumers get typed fields. See {@link structuredValue}
 * for the projection rules.
 */
export function tokenInfo(token: Token<unknown>): TokenInfo {
  const value = token.value;
  const type = value != null ? typeof value === 'object' ? value.constructor.name : typeof value : 'null';
  const fullValue = value != null ? String(value) : 'null';
  const info: TokenInfo = {
    id: null,
    type,
    value: fullValue,
    timestamp: new Date(token.createdAt).toISOString(),
  };
  const structured = structuredValue(value);
  return structured === undefined ? info : { ...info, structured };
}

/**
 * Projects a token value into a JSON-friendly representation for the `structured`
 * TokenInfo field. Returns `undefined` when no useful projection exists (null values,
 * opaque objects Jackson-on-the-Java-side would drop); callers omit the field in that
 * case so wire size stays neutral for unstructurable tokens.
 *
 * @remarks
 * Implementation notes:
 * - Primitives and plain objects / arrays pass through untouched (already JSON-safe).
 * - Maps / Sets are projected to a plain shape — debug tooling doesn't need the
 *   prototype identity and JSON consumers can't use it anyway.
 * - Classes with a `toJSON()` method are respected via structured clone (uses the
 *   same path as `JSON.stringify`).
 *
 * Security: uses `JSON.parse(JSON.stringify(...))` which is safe against code
 * execution and prototype pollution. A hostile token value with a custom
 * `toJSON()` override could still return misleading data — archives are a
 * trust boundary (see [EVT-025](../../../spec/08-events-observability.md)).
 */
function structuredValue(value: unknown): unknown | undefined {
  if (value == null) return undefined;
  const t = typeof value;
  if (t === 'string' || t === 'number' || t === 'boolean') return value;
  if (t === 'bigint') return String(value); // bigint → string for JSON-safety
  if (t === 'symbol' || t === 'function') return undefined;
  // Plain arrays / plain objects / objects with toJSON — JSON.parse(JSON.stringify(...))
  // is the cheapest way to drop non-serializable fields and flatten to wire-ready shape.
  try {
    const cloned = JSON.parse(JSON.stringify(value));
    // Skip empty objects — they're opaque beans with no useful structure, just inflating responses.
    if (cloned && typeof cloned === 'object' && !Array.isArray(cloned) && Object.keys(cloned).length === 0) {
      return undefined;
    }
    return cloned;
  } catch {
    return undefined;
  }
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
