/**
 * Framework-agnostic handler for the Petri net debug protocol.
 * TypeScript port of Java's DebugProtocolHandler.
 *
 * Manages debug subscriptions, event filtering, breakpoints, and replay
 * for connected clients. Decoupled from any specific WebSocket framework
 * via the ResponseSink type.
 */

import type { NetEvent } from '../event/net-event.js';
import { sanitize } from '../export/petri-net-mapper.js';
import type { DebugCommand, EventFilter, BreakpointConfig } from './debug-command.js';
import type { DebugResponse, TokenInfo, NetEventInfo, NetStructure } from './debug-response.js';
import type { DebugSession } from './debug-session-registry.js';
import type { DebugSessionRegistry } from './debug-session-registry.js';
import type { Subscription } from './debug-event-store.js';
import { MarkingCache } from './marking-cache.js';
import { toEventInfo, tokenInfo, convertMarking } from './net-event-converter.js';

/** Callback for sending responses to a connected client. */
export type ResponseSink = (response: DebugResponse) => void;

/** Computed state from replaying events. */
export interface ComputedState {
  readonly marking: ReadonlyMap<string, readonly TokenInfo[]>;
  readonly enabledTransitions: readonly string[];
  readonly inFlightTransitions: readonly string[];
}

/** Maximum events per batch when sending historical events. */
const BATCH_SIZE = 500;

export class DebugProtocolHandler {
  private readonly _sessionRegistry: DebugSessionRegistry;
  private readonly _clients = new Map<string, ClientState>();

  constructor(sessionRegistry: DebugSessionRegistry) {
    this._sessionRegistry = sessionRegistry;
  }

  /** Registers a new client connection. */
  clientConnected(clientId: string, sink: ResponseSink): void {
    this._clients.set(clientId, new ClientState(sink));
  }

  /** Cleans up when a client disconnects. */
  clientDisconnected(clientId: string): void {
    const state = this._clients.get(clientId);
    this._clients.delete(clientId);
    if (state) state.subscriptions.cancelAll();
  }

  /** Handles a command from a connected client. */
  handleCommand(clientId: string, command: DebugCommand): void {
    const clientState = this._clients.get(clientId);
    if (!clientState) return;

    try {
      switch (command.type) {
        case 'listSessions': this.handleListSessions(clientState, command); break;
        case 'subscribe': this.handleSubscribe(clientState, command); break;
        case 'unsubscribe': this.handleUnsubscribe(clientState, command); break;
        case 'seek': this.handleSeek(clientState, command); break;
        case 'playbackSpeed': this.handlePlaybackSpeed(clientState, command); break;
        case 'filter': this.handleSetFilter(clientState, command); break;
        case 'pause': this.handlePause(clientState, command); break;
        case 'resume': this.handleResume(clientState, command); break;
        case 'stepForward': this.handleStepForward(clientState, command); break;
        case 'stepBackward': this.handleStepBackward(clientState, command); break;
        case 'setBreakpoint': this.handleSetBreakpoint(clientState, command); break;
        case 'clearBreakpoint': this.handleClearBreakpoint(clientState, command); break;
        case 'listBreakpoints': this.handleListBreakpoints(clientState, command); break;
      }
    } catch (e) {
      this.sendError(clientState, 'COMMAND_ERROR', e instanceof Error ? e.message : String(e), null);
    }
  }

  // ======================== Command Handlers ========================

  private handleListSessions(client: ClientState, cmd: Extract<DebugCommand, { type: 'listSessions' }>): void {
    const limit = cmd.limit ?? 50;
    const sessions = cmd.activeOnly
      ? this._sessionRegistry.listActiveSessions(limit)
      : this._sessionRegistry.listSessions(limit);

    const summaries = sessions.map(s => ({
      sessionId: s.sessionId,
      netName: s.netName,
      startTime: new Date(s.startTime).toISOString(),
      active: s.active,
      eventCount: s.eventStore.eventCount(),
    }));

    this.send(client, { type: 'sessionList', sessions: summaries });
  }

  private handleSubscribe(client: ClientState, cmd: Extract<DebugCommand, { type: 'subscribe' }>): void {
    const debugSession = this._sessionRegistry.getSession(cmd.sessionId);
    if (!debugSession) {
      this.sendError(client, 'SESSION_NOT_FOUND', `Session not found: ${cmd.sessionId}`, cmd.sessionId);
      return;
    }

    const eventStore = debugSession.eventStore;
    client.subscriptions.cancel(cmd.sessionId);

    const events = eventStore.events();
    const computed = computeState(events);
    const structure = buildNetStructure(debugSession);

    this.send(client, {
      type: 'subscribed',
      sessionId: cmd.sessionId,
      netName: debugSession.netName,
      dotDiagram: debugSession.dotDiagram,
      structure,
      currentMarking: mapToRecord(computed.marking),
      enabledTransitions: computed.enabledTransitions,
      inFlightTransitions: computed.inFlightTransitions,
      eventCount: eventStore.eventCount(),
      mode: cmd.mode,
    });

    const fromIndex = cmd.fromIndex ?? 0;
    if (cmd.mode === 'live') {
      this.subscribeLive(client, cmd.sessionId, debugSession, fromIndex);
    } else {
      this.subscribeReplay(client, cmd.sessionId, debugSession, fromIndex);
    }
  }

  private subscribeLive(client: ClientState, sessionId: string, debugSession: DebugSession, fromIndex: number): void {
    const eventStore = debugSession.eventStore;
    let eventIndex = fromIndex;

    const historicalEvents = eventStore.eventsFrom(fromIndex);
    if (historicalEvents.length > 0) {
      const filtered = historicalEvents
        .filter(e => client.subscriptions.matchesFilter(sessionId, e))
        .map(e => toEventInfo(e));
      this.sendInBatches(client, sessionId, fromIndex, filtered);
      eventIndex = fromIndex + historicalEvents.length;
    }

    const subscription = eventStore.subscribe(event => {
      if (!client.subscriptions.isPaused(sessionId) && client.subscriptions.matchesFilter(sessionId, event)) {
        const eventInfo = toEventInfo(event);
        const idx = eventIndex++;

        const hitBreakpoint = client.subscriptions.checkBreakpoints(sessionId, event);
        if (hitBreakpoint) {
          client.subscriptions.setPaused(sessionId, true);
          this.send(client, {
            type: 'breakpointHit',
            sessionId,
            breakpointId: hitBreakpoint.id,
            event: eventInfo,
            eventIndex: idx,
          });
        }

        this.send(client, { type: 'event', sessionId, index: idx, event: eventInfo });
      }
    });

    client.subscriptions.addSubscription(sessionId, subscription, eventIndex);
  }

  private subscribeReplay(client: ClientState, sessionId: string, debugSession: DebugSession, fromIndex: number): void {
    const eventStore = debugSession.eventStore;

    const events = eventStore.eventsFrom(fromIndex);
    const converted = events.map(e => toEventInfo(e));
    this.sendInBatches(client, sessionId, fromIndex, converted);

    const eventIndex = fromIndex + events.length;
    client.subscriptions.addSubscription(sessionId, null, eventIndex);
    client.subscriptions.setPaused(sessionId, true);
  }

  private handleUnsubscribe(client: ClientState, cmd: Extract<DebugCommand, { type: 'unsubscribe' }>): void {
    client.subscriptions.cancel(cmd.sessionId);
    this.send(client, { type: 'unsubscribed', sessionId: cmd.sessionId });
  }

  private handleSeek(client: ClientState, cmd: Extract<DebugCommand, { type: 'seek' }>): void {
    const debugSession = this._sessionRegistry.getSession(cmd.sessionId);
    if (!debugSession) {
      this.sendError(client, 'SESSION_NOT_FOUND', 'Session not found', cmd.sessionId);
      return;
    }

    const events = debugSession.eventStore.events();
    const targetTs = new Date(cmd.timestamp).getTime();

    let targetIndex = 0;
    for (let i = 0; i < events.length; i++) {
      if (events[i]!.timestamp >= targetTs) {
        targetIndex = i;
        break;
      }
      targetIndex = i + 1;
    }

    client.subscriptions.setEventIndex(cmd.sessionId, targetIndex);
    const computed = client.subscriptions.computeStateAt(cmd.sessionId, events, targetIndex);

    this.send(client, {
      type: 'markingSnapshot',
      sessionId: cmd.sessionId,
      marking: mapToRecord(computed.marking),
      enabledTransitions: computed.enabledTransitions,
      inFlightTransitions: computed.inFlightTransitions,
    });
  }

  private handlePlaybackSpeed(client: ClientState, cmd: Extract<DebugCommand, { type: 'playbackSpeed' }>): void {
    client.subscriptions.setSpeed(cmd.sessionId, cmd.speed);
    this.send(client, {
      type: 'playbackStateChanged',
      sessionId: cmd.sessionId,
      paused: client.subscriptions.isPaused(cmd.sessionId),
      speed: cmd.speed,
      currentIndex: client.subscriptions.getEventIndex(cmd.sessionId),
    });
  }

  private handleSetFilter(client: ClientState, cmd: Extract<DebugCommand, { type: 'filter' }>): void {
    client.subscriptions.setFilter(cmd.sessionId, cmd.filter);
    this.send(client, { type: 'filterApplied', sessionId: cmd.sessionId, filter: cmd.filter });
  }

  private handlePause(client: ClientState, cmd: Extract<DebugCommand, { type: 'pause' }>): void {
    client.subscriptions.setPaused(cmd.sessionId, true);
    this.send(client, {
      type: 'playbackStateChanged',
      sessionId: cmd.sessionId,
      paused: true,
      speed: client.subscriptions.getSpeed(cmd.sessionId),
      currentIndex: client.subscriptions.getEventIndex(cmd.sessionId),
    });
  }

  private handleResume(client: ClientState, cmd: Extract<DebugCommand, { type: 'resume' }>): void {
    client.subscriptions.setPaused(cmd.sessionId, false);
    this.send(client, {
      type: 'playbackStateChanged',
      sessionId: cmd.sessionId,
      paused: false,
      speed: client.subscriptions.getSpeed(cmd.sessionId),
      currentIndex: client.subscriptions.getEventIndex(cmd.sessionId),
    });
  }

  private handleStepForward(client: ClientState, cmd: Extract<DebugCommand, { type: 'stepForward' }>): void {
    const debugSession = this._sessionRegistry.getSession(cmd.sessionId);
    if (!debugSession) {
      this.sendError(client, 'SESSION_NOT_FOUND', `Session not found: ${cmd.sessionId}`, cmd.sessionId);
      return;
    }

    const events = debugSession.eventStore.events();
    const currentIndex = client.subscriptions.getEventIndex(cmd.sessionId);

    if (currentIndex < events.length) {
      const event = events[currentIndex]!;
      this.send(client, {
        type: 'event',
        sessionId: cmd.sessionId,
        index: currentIndex,
        event: toEventInfo(event),
      });
      client.subscriptions.setEventIndex(cmd.sessionId, currentIndex + 1);
    }
  }

  private handleStepBackward(client: ClientState, cmd: Extract<DebugCommand, { type: 'stepBackward' }>): void {
    const debugSession = this._sessionRegistry.getSession(cmd.sessionId);
    if (!debugSession) {
      this.sendError(client, 'SESSION_NOT_FOUND', `Session not found: ${cmd.sessionId}`, cmd.sessionId);
      return;
    }

    let currentIndex = client.subscriptions.getEventIndex(cmd.sessionId);
    if (currentIndex > 0) {
      currentIndex--;
      client.subscriptions.setEventIndex(cmd.sessionId, currentIndex);

      const events = debugSession.eventStore.events();
      const computed = client.subscriptions.computeStateAt(cmd.sessionId, events, currentIndex);

      this.send(client, {
        type: 'markingSnapshot',
        sessionId: cmd.sessionId,
        marking: mapToRecord(computed.marking),
        enabledTransitions: computed.enabledTransitions,
        inFlightTransitions: computed.inFlightTransitions,
      });
    }
  }

  private handleSetBreakpoint(client: ClientState, cmd: Extract<DebugCommand, { type: 'setBreakpoint' }>): void {
    client.subscriptions.addBreakpoint(cmd.sessionId, cmd.breakpoint);
    this.send(client, { type: 'breakpointSet', sessionId: cmd.sessionId, breakpoint: cmd.breakpoint });
  }

  private handleClearBreakpoint(client: ClientState, cmd: Extract<DebugCommand, { type: 'clearBreakpoint' }>): void {
    client.subscriptions.removeBreakpoint(cmd.sessionId, cmd.breakpointId);
    this.send(client, { type: 'breakpointCleared', sessionId: cmd.sessionId, breakpointId: cmd.breakpointId });
  }

  private handleListBreakpoints(client: ClientState, cmd: Extract<DebugCommand, { type: 'listBreakpoints' }>): void {
    const breakpoints = client.subscriptions.getBreakpoints(cmd.sessionId);
    this.send(client, { type: 'breakpointList', sessionId: cmd.sessionId, breakpoints });
  }

  // ======================== Helper Methods ========================

  private send(client: ClientState, response: DebugResponse): void {
    client.sink(response);
  }

  private sendError(client: ClientState, code: string, message: string, sessionId: string | null): void {
    this.send(client, { type: 'error', code, message, sessionId });
  }

  private sendInBatches(client: ClientState, sessionId: string, startIndex: number, events: readonly NetEventInfo[]): void {
    if (events.length === 0) {
      this.send(client, { type: 'eventBatch', sessionId, startIndex, events: [], hasMore: false });
      return;
    }
    for (let i = 0; i < events.length; i += BATCH_SIZE) {
      const end = Math.min(i + BATCH_SIZE, events.length);
      const chunk = events.slice(i, end);
      const hasMore = end < events.length;
      this.send(client, { type: 'eventBatch', sessionId, startIndex: startIndex + i, events: chunk, hasMore });
    }
  }
}

// ======================== State Computation (exported for MarkingCache) ========================

/** Computes marking, enabled transitions, and in-flight transitions from events. */
export function computeState(events: readonly NetEvent[]): ComputedState {
  const marking = new Map<string, TokenInfo[]>();
  const enabled = new Set<string>();
  const inFlight = new Set<string>();
  applyEvents(marking, enabled, inFlight, events);
  return toImmutableState(marking, enabled, inFlight);
}

/** Applies events to mutable accumulator collections. */
export function applyEvents(
  marking: Map<string, TokenInfo[]>,
  enabled: Set<string>,
  inFlight: Set<string>,
  events: readonly NetEvent[],
): void {
  for (const event of events) {
    switch (event.type) {
      case 'token-added': {
        let tokens = marking.get(event.placeName);
        if (!tokens) {
          tokens = [];
          marking.set(event.placeName, tokens);
        }
        tokens.push(tokenInfo(event.token));
        break;
      }
      case 'token-removed': {
        const tokens = marking.get(event.placeName);
        if (tokens && tokens.length > 0) tokens.shift();
        break;
      }
      case 'marking-snapshot': {
        marking.clear();
        const converted = convertMarking(event.marking);
        for (const [key, value] of Object.entries(converted)) {
          marking.set(key, [...value]);
        }
        break;
      }
      case 'transition-enabled':
        enabled.add(event.transitionName);
        break;
      case 'transition-started':
        enabled.delete(event.transitionName);
        inFlight.add(event.transitionName);
        break;
      case 'transition-completed':
        inFlight.delete(event.transitionName);
        break;
      case 'transition-failed':
        inFlight.delete(event.transitionName);
        break;
      case 'transition-timed-out':
        inFlight.delete(event.transitionName);
        break;
      case 'action-timed-out':
        inFlight.delete(event.transitionName);
        break;
      default:
        break;
    }
  }
}

/** Converts mutable accumulator collections into an immutable ComputedState. */
export function toImmutableState(
  marking: Map<string, TokenInfo[]>,
  enabled: Set<string>,
  inFlight: Set<string>,
): ComputedState {
  const resultMarking = new Map<string, readonly TokenInfo[]>();
  for (const [key, value] of marking) {
    resultMarking.set(key, [...value]);
  }
  return {
    marking: resultMarking,
    enabledTransitions: [...enabled],
    inFlightTransitions: [...inFlight],
  };
}

/** Builds net structure from a debug session. */
function buildNetStructure(debugSession: DebugSession): NetStructure {
  const places = debugSession.places;
  const transitions = debugSession.transitions;

  const placeInfos = [...places.data.entries()].map(([name, info]) => ({
    name,
    graphId: `p_${sanitize(name)}`,
    tokenType: info.tokenType,
    isStart: !info.hasIncoming,
    isEnd: !info.hasOutgoing,
    isEnvironment: false,
  }));

  const transitionInfos = [...transitions].map(t => ({
    name: t.name,
    graphId: `t_${sanitize(t.name)}`,
  }));

  return { places: placeInfos, transitions: transitionInfos };
}

/** Convert Map to Record for JSON serialization. */
function mapToRecord(map: ReadonlyMap<string, readonly TokenInfo[]>): Record<string, readonly TokenInfo[]> {
  const result: Record<string, readonly TokenInfo[]> = {};
  for (const [key, value] of map) {
    result[key] = value;
  }
  return result;
}

// ======================== Client State ========================

class ClientState {
  readonly sink: ResponseSink;
  readonly subscriptions = new SubscriptionState();

  constructor(sink: ResponseSink) {
    this.sink = sink;
  }
}

// ======================== Subscription State ========================

interface SessionSubscription {
  subscription: Subscription | null;
  eventIndex: number;
  markingCache: MarkingCache;
  breakpoints: Map<string, BreakpointConfig>;
  paused: boolean;
  speed: number;
  filter: EventFilter | null;
}

class SubscriptionState {
  private readonly _sessionSubs = new Map<string, SessionSubscription>();

  addSubscription(sessionId: string, subscription: Subscription | null, eventIndex: number): void {
    this._sessionSubs.set(sessionId, {
      subscription,
      eventIndex,
      markingCache: new MarkingCache(),
      breakpoints: new Map(),
      paused: false,
      speed: 1.0,
      filter: null,
    });
  }

  cancel(sessionId: string): void {
    const sub = this._sessionSubs.get(sessionId);
    if (sub?.subscription) sub.subscription.cancel();
    this._sessionSubs.delete(sessionId);
  }

  cancelAll(): void {
    for (const sub of this._sessionSubs.values()) {
      if (sub.subscription) sub.subscription.cancel();
    }
    this._sessionSubs.clear();
  }

  isPaused(sessionId: string): boolean {
    return this._sessionSubs.get(sessionId)?.paused ?? false;
  }

  setPaused(sessionId: string, paused: boolean): void {
    const sub = this._sessionSubs.get(sessionId);
    if (sub) sub.paused = paused;
  }

  getSpeed(sessionId: string): number {
    return this._sessionSubs.get(sessionId)?.speed ?? 1.0;
  }

  setSpeed(sessionId: string, speed: number): void {
    const sub = this._sessionSubs.get(sessionId);
    if (sub) sub.speed = speed;
  }

  getEventIndex(sessionId: string): number {
    return this._sessionSubs.get(sessionId)?.eventIndex ?? 0;
  }

  setEventIndex(sessionId: string, index: number): void {
    const sub = this._sessionSubs.get(sessionId);
    if (sub) sub.eventIndex = index;
  }

  computeStateAt(sessionId: string, events: readonly NetEvent[], targetIndex: number): ComputedState {
    const sub = this._sessionSubs.get(sessionId);
    if (sub) return sub.markingCache.computeAt(events, targetIndex);
    return computeState(events.slice(0, targetIndex));
  }

  setFilter(sessionId: string, filter: EventFilter): void {
    const sub = this._sessionSubs.get(sessionId);
    if (sub) sub.filter = filter;
  }

  matchesFilter(sessionId: string, event: NetEvent): boolean {
    const sub = this._sessionSubs.get(sessionId);
    if (!sub?.filter) return true;

    const filter = sub.filter;

    if (filter.eventTypes && filter.eventTypes.length > 0) {
      const eventType = eventTypeToName(event);
      if (!filter.eventTypes.includes(eventType)) return false;
    }

    if (filter.transitionNames && filter.transitionNames.length > 0) {
      const name = extractTransitionName(event);
      if (!name || !filter.transitionNames.includes(name)) return false;
    }

    if (filter.placeNames && filter.placeNames.length > 0) {
      const name = extractPlaceName(event);
      if (!name || !filter.placeNames.includes(name)) return false;
    }

    return true;
  }

  addBreakpoint(sessionId: string, breakpoint: BreakpointConfig): void {
    const sub = this._sessionSubs.get(sessionId);
    if (sub) sub.breakpoints.set(breakpoint.id, breakpoint);
  }

  removeBreakpoint(sessionId: string, breakpointId: string): void {
    const sub = this._sessionSubs.get(sessionId);
    if (sub) sub.breakpoints.delete(breakpointId);
  }

  getBreakpoints(sessionId: string): readonly BreakpointConfig[] {
    const sub = this._sessionSubs.get(sessionId);
    return sub ? [...sub.breakpoints.values()] : [];
  }

  checkBreakpoints(sessionId: string, event: NetEvent): BreakpointConfig | null {
    const sub = this._sessionSubs.get(sessionId);
    if (!sub || sub.breakpoints.size === 0) return null;

    for (const bp of sub.breakpoints.values()) {
      if (!bp.enabled) continue;
      if (matchesBreakpoint(bp, event)) return bp;
    }
    return null;
  }
}

function eventTypeToName(event: NetEvent): string {
  const map: Record<string, string> = {
    'execution-started': 'ExecutionStarted',
    'execution-completed': 'ExecutionCompleted',
    'transition-enabled': 'TransitionEnabled',
    'transition-clock-restarted': 'TransitionClockRestarted',
    'transition-started': 'TransitionStarted',
    'transition-completed': 'TransitionCompleted',
    'transition-failed': 'TransitionFailed',
    'transition-timed-out': 'TransitionTimedOut',
    'action-timed-out': 'ActionTimedOut',
    'token-added': 'TokenAdded',
    'token-removed': 'TokenRemoved',
    'marking-snapshot': 'MarkingSnapshot',
    'log-message': 'LogMessage',
  };
  return map[event.type] ?? event.type;
}

function extractTransitionName(event: NetEvent): string | null {
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

function extractPlaceName(event: NetEvent): string | null {
  switch (event.type) {
    case 'token-added':
    case 'token-removed':
      return event.placeName;
    default:
      return null;
  }
}

function matchesBreakpoint(bp: BreakpointConfig, event: NetEvent): boolean {
  switch (bp.type) {
    case 'TRANSITION_ENABLED':
      return event.type === 'transition-enabled' && (bp.target === null || bp.target === event.transitionName);
    case 'TRANSITION_START':
      return event.type === 'transition-started' && (bp.target === null || bp.target === event.transitionName);
    case 'TRANSITION_COMPLETE':
      return event.type === 'transition-completed' && (bp.target === null || bp.target === event.transitionName);
    case 'TRANSITION_FAIL':
      return event.type === 'transition-failed' && (bp.target === null || bp.target === event.transitionName);
    case 'TOKEN_ADDED':
      return event.type === 'token-added' && (bp.target === null || bp.target === event.placeName);
    case 'TOKEN_REMOVED':
      return event.type === 'token-removed' && (bp.target === null || bp.target === event.placeName);
    default:
      return false;
  }
}
