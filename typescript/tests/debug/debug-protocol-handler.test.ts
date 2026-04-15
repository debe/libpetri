import { describe, it, expect } from 'vitest';
import { DebugProtocolHandler, computeState } from '../../src/debug/debug-protocol-handler.js';
import { DebugSessionRegistry } from '../../src/debug/debug-session-registry.js';
import { DebugEventStore } from '../../src/debug/debug-event-store.js';
import type { DebugCommand } from '../../src/debug/debug-command.js';
import type { DebugResponse, NetStructure } from '../../src/debug/debug-response.js';
import type { NetEvent } from '../../src/event/net-event.js';
import { tokenOf } from '../../src/core/token.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';

const INPUT = place<string>('Input');
const OUTPUT = place<string>('Output');

const TEST_NET = PetriNet.builder('TestNet')
  .transition(
    Transition.builder('Process')
      .inputs(one(INPUT))
      .outputs(outPlace(OUTPUT))
      .build()
  )
  .build();

function enabledEvent(name: string, ts = Date.now()): NetEvent {
  return { type: 'transition-enabled', timestamp: ts, transitionName: name };
}

describe('DebugProtocolHandler', () => {
  let registry: DebugSessionRegistry;
  let handler: DebugProtocolHandler;
  let responses: DebugResponse[];

  function setup() {
    registry = new DebugSessionRegistry();
    handler = new DebugProtocolHandler(registry);
    responses = [];
  }

  function connectClient(clientId: string) {
    handler.clientConnected(clientId, r => responses.push(r));
  }

  function registerSessionWithEvents(sessionId: string, ...events: NetEvent[]): string {
    const session = registry.register(sessionId, TEST_NET);
    for (const event of events) {
      session.eventStore.append(event);
    }
    return sessionId;
  }

  function lastResponseOfType<T extends DebugResponse['type']>(type: T): Extract<DebugResponse, { type: T }> | undefined {
    for (let i = responses.length - 1; i >= 0; i--) {
      if (responses[i]!.type === type) return responses[i] as Extract<DebugResponse, { type: T }>;
    }
    return undefined;
  }

  function responsesOfType<T extends DebugResponse['type']>(type: T): Extract<DebugResponse, { type: T }>[] {
    return responses.filter(r => r.type === type) as Extract<DebugResponse, { type: T }>[];
  }

  describe('ConnectionLifecycle', () => {
    it('should ignore command from unknown client', () => {
      setup();
      handler.handleCommand('unknown', { type: 'listSessions', limit: 10, activeOnly: false });
      expect(responses).toHaveLength(0);
    });

    it('should clean subscriptions on disconnect', async () => {
      setup();
      connectClient('c1');
      const sessionId = registerSessionWithEvents('s1');

      handler.handleCommand('c1', { type: 'subscribe', sessionId, mode: 'live', fromIndex: 0 });
      responses.length = 0;

      handler.clientDisconnected('c1');

      registry.getSession(sessionId)!.eventStore.append(enabledEvent('T1'));
      await new Promise(r => setTimeout(r, 50));
      expect(responses).toHaveLength(0);
    });

    it('should support multiple independent clients', () => {
      setup();
      const responses1: DebugResponse[] = [];
      const responses2: DebugResponse[] = [];

      handler.clientConnected('c1', r => responses1.push(r));
      handler.clientConnected('c2', r => responses2.push(r));

      registerSessionWithEvents('s1');
      handler.handleCommand('c1', { type: 'listSessions', limit: 10, activeOnly: false });
      handler.handleCommand('c2', { type: 'listSessions', limit: 10, activeOnly: false });

      expect(responses1.length).toBeGreaterThan(0);
      expect(responses2.length).toBeGreaterThan(0);
      expect(responses1[0]!.type).toBe('sessionList');
      expect(responses2[0]!.type).toBe('sessionList');
    });
  });

  describe('ListSessionsFlow', () => {
    it('should list all sessions', () => {
      setup();
      connectClient('c1');
      registerSessionWithEvents('s1');
      registerSessionWithEvents('s2');

      handler.handleCommand('c1', { type: 'listSessions', limit: 50, activeOnly: false });

      const sessionList = lastResponseOfType('sessionList')!;
      expect(sessionList.sessions).toHaveLength(2);
    });

    it('should list active sessions only', () => {
      setup();
      connectClient('c1');
      registerSessionWithEvents('s1');
      registerSessionWithEvents('s2');
      registry.complete('s1');

      handler.handleCommand('c1', { type: 'listSessions', limit: 50, activeOnly: true });

      const sessionList = lastResponseOfType('sessionList')!;
      expect(sessionList.sessions).toHaveLength(1);
      expect(sessionList.sessions[0]!.sessionId).toBe('s2');
    });

    it('should respect limit', () => {
      setup();
      connectClient('c1');
      for (let i = 0; i < 5; i++) {
        registerSessionWithEvents(`s${i}`);
      }

      handler.handleCommand('c1', { type: 'listSessions', limit: 2, activeOnly: false });

      const sessionList = lastResponseOfType('sessionList')!;
      expect(sessionList.sessions).toHaveLength(2);
    });

    it('should filter sessions by tag', () => {
      setup();
      connectClient('c1');
      registry.register('voice-1', TEST_NET, { channel: 'voice' });
      registry.register('text-1', TEST_NET, { channel: 'text' });
      registry.register('voice-2', TEST_NET, { channel: 'voice' });

      handler.handleCommand('c1', {
        type: 'listSessions',
        limit: 50,
        activeOnly: false,
        tagFilter: { channel: 'voice' },
      });

      const sessionList = lastResponseOfType('sessionList')!;
      expect(sessionList.sessions).toHaveLength(2);
      expect(sessionList.sessions.every(s => s.sessionId.startsWith('voice'))).toBe(true);
      expect(sessionList.sessions[0]!.tags).toEqual({ channel: 'voice' });
    });

    it('should populate endTime and durationMs on completed sessions over protocol', () => {
      setup();
      connectClient('c1');
      registry.register('s1', TEST_NET, { channel: 'voice' });
      registry.complete('s1');

      handler.handleCommand('c1', { type: 'listSessions', limit: 50, activeOnly: false });

      const sessionList = lastResponseOfType('sessionList')!;
      expect(sessionList.sessions).toHaveLength(1);
      const summary = sessionList.sessions[0]!;
      expect(summary.tags).toEqual({ channel: 'voice' });
      expect(summary.endTime).toBeDefined();
      expect(summary.durationMs).toBeDefined();
    });

    it('should preserve endTime and tags on imported sessions over the wire', () => {
      setup();
      connectClient('c1');
      const structure: NetStructure = {
        places: [{ name: 'P1', graphId: 'p_P1', tokenType: 'String', isStart: true, isEnd: false, isEnvironment: false }],
        transitions: [{ name: 'T1', graphId: 't_T1' }],
      };
      registry.registerImported(
        'imp1', 'NetX', 'digraph {}', structure, new DebugEventStore('imp1'),
        /* startTime */ 1_000,
        /* endTime   */ 2_500,
        /* tags      */ { channel: 'voice', archived: 'true' },
      );

      handler.handleCommand('c1', { type: 'listSessions', limit: 50, activeOnly: false });

      const sessionList = lastResponseOfType('sessionList')!;
      expect(sessionList.sessions).toHaveLength(1);
      const summary = sessionList.sessions[0]!;
      expect(summary.endTime).toBeDefined();
      expect(summary.durationMs).toBe(1500);
      expect(summary.tags).toEqual({ channel: 'voice', archived: 'true' });
    });
  });

  describe('SubscribeLiveFlow', () => {
    it('should respond with subscribed and initial state', () => {
      setup();
      connectClient('c1');
      registerSessionWithEvents('s1');

      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'live', fromIndex: 0 });

      const subscribed = lastResponseOfType('subscribed')!;
      expect(subscribed.sessionId).toBe('s1');
      expect(subscribed.netName).toBe('TestNet');
      expect(subscribed.dotDiagram).toBeDefined();
      expect(subscribed.structure).toBeDefined();
      expect(subscribed.mode).toBe('live');
    });

    it('should send historical events as batch', () => {
      setup();
      connectClient('c1');
      const now = Date.now();
      registerSessionWithEvents('s1', enabledEvent('T1', now), enabledEvent('T2', now));

      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'live', fromIndex: 0 });

      const batches = responsesOfType('eventBatch');
      expect(batches.length).toBeGreaterThan(0);
      const allEvents = batches.flatMap(b => b.events);
      expect(allEvents).toHaveLength(2);
    });

    it('should receive live events after subscribe', async () => {
      setup();
      const liveResponses: DebugResponse[] = [];

      const sessionId = registerSessionWithEvents('s1');
      handler.clientConnected('c1', r => liveResponses.push(r));
      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'live', fromIndex: 0 });

      registry.getSession(sessionId)!.eventStore.append(enabledEvent('LiveT'));
      await new Promise(r => setTimeout(r, 50));

      const liveEvents = liveResponses.filter(r => r.type === 'event');
      expect(liveEvents.length).toBeGreaterThan(0);
      const lastEvent = liveEvents[liveEvents.length - 1] as Extract<DebugResponse, { type: 'event' }>;
      expect(lastEvent.event.type).toBe('TransitionEnabled');
    });

    it('should filter by event type', () => {
      setup();
      connectClient('c1');
      const now = Date.now();
      registerSessionWithEvents('s1',
        enabledEvent('T1', now),
        { type: 'token-added', timestamp: now, placeName: 'P1', token: tokenOf('val') });

      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'live', fromIndex: 0 });
      handler.handleCommand('c1', { type: 'filter', sessionId: 's1', filter: { eventTypes: ['TransitionEnabled'], transitionNames: null, placeNames: null } });

      const filterApplied = lastResponseOfType('filterApplied')!;
      expect(filterApplied).toBeDefined();
      expect(filterApplied.sessionId).toBe('s1');
    });

    it('should pause and resume live events', () => {
      setup();
      connectClient('c1');
      registerSessionWithEvents('s1');

      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'live', fromIndex: 0 });

      handler.handleCommand('c1', { type: 'pause', sessionId: 's1' });
      const paused = lastResponseOfType('playbackStateChanged')!;
      expect(paused.paused).toBe(true);

      handler.handleCommand('c1', { type: 'resume', sessionId: 's1' });
      const resumed = lastResponseOfType('playbackStateChanged')!;
      expect(resumed.paused).toBe(false);
    });
  });

  describe('SubscribeReplayFlow', () => {
    it('should send all events on replay', () => {
      setup();
      connectClient('c1');
      const now = Date.now();
      registerSessionWithEvents('s1',
        enabledEvent('T1', now),
        enabledEvent('T2', now),
        enabledEvent('T3', now));

      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'replay', fromIndex: 0 });

      const subscribed = lastResponseOfType('subscribed')!;
      expect(subscribed.mode).toBe('replay');

      const batches = responsesOfType('eventBatch');
      const totalEvents = batches.reduce((sum, b) => sum + b.events.length, 0);
      expect(totalEvents).toBe(3);
    });

    it('should start paused in replay mode', () => {
      setup();
      connectClient('c1');
      registerSessionWithEvents('s1', enabledEvent('T1'));

      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'replay', fromIndex: 0 });

      handler.handleCommand('c1', { type: 'pause', sessionId: 's1' });
      const state = lastResponseOfType('playbackStateChanged')!;
      expect(state.paused).toBe(true);
    });

    it('should unsubscribe cleanly', () => {
      setup();
      connectClient('c1');
      registerSessionWithEvents('s1');

      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'replay', fromIndex: 0 });
      handler.handleCommand('c1', { type: 'unsubscribe', sessionId: 's1' });

      const unsubscribed = lastResponseOfType('unsubscribed')!;
      expect(unsubscribed.sessionId).toBe('s1');
    });
  });

  describe('SeekAndStepFlow', () => {
    it('should seek to timestamp', () => {
      setup();
      connectClient('c1');
      const t1 = new Date('2024-01-01T00:00:00Z').getTime();
      const t2 = new Date('2024-01-01T00:00:01Z').getTime();
      const t3 = new Date('2024-01-01T00:00:02Z').getTime();

      registerSessionWithEvents('s1',
        enabledEvent('T1', t1),
        enabledEvent('T2', t2),
        enabledEvent('T3', t3));

      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'replay', fromIndex: 0 });

      handler.handleCommand('c1', { type: 'seek', sessionId: 's1', timestamp: new Date(t2).toISOString() });
      const snapshot = lastResponseOfType('markingSnapshot')!;
      expect(snapshot).toBeDefined();
      expect(snapshot.sessionId).toBe('s1');
    });

    it('should step forward', () => {
      setup();
      connectClient('c1');
      const now = Date.now();
      registerSessionWithEvents('s1', enabledEvent('T1', now), enabledEvent('T2', now));

      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'replay', fromIndex: 0 });

      // Seek to beginning
      handler.handleCommand('c1', { type: 'seek', sessionId: 's1', timestamp: new Date(0).toISOString() });
      responses.length = 0;

      handler.handleCommand('c1', { type: 'stepForward', sessionId: 's1' });

      const events = responsesOfType('event');
      expect(events.length).toBeGreaterThan(0);
    });

    it('should step backward', () => {
      setup();
      connectClient('c1');
      const now = Date.now();
      registerSessionWithEvents('s1',
        { type: 'token-added', timestamp: now, placeName: 'P1', token: tokenOf('val') },
        enabledEvent('T1', now));

      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'replay', fromIndex: 0 });

      handler.handleCommand('c1', { type: 'stepForward', sessionId: 's1' });
      handler.handleCommand('c1', { type: 'stepForward', sessionId: 's1' });
      responses.length = 0;

      handler.handleCommand('c1', { type: 'stepBackward', sessionId: 's1' });

      const snapshots = responsesOfType('markingSnapshot');
      expect(snapshots.length).toBeGreaterThan(0);
    });

    it('should not step forward past end', () => {
      setup();
      connectClient('c1');
      registerSessionWithEvents('s1', enabledEvent('T1'));

      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'replay', fromIndex: 0 });

      // Replay sends all events then pauses at end. Step shouldn't produce more.
      handler.handleCommand('c1', { type: 'stepForward', sessionId: 's1' });
      responses.length = 0;

      handler.handleCommand('c1', { type: 'stepForward', sessionId: 's1' });
      const events = responsesOfType('event');
      expect(events).toHaveLength(0);
    });

    it('should not step backward before start', () => {
      setup();
      connectClient('c1');
      registerSessionWithEvents('s1', enabledEvent('T1'));

      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'replay', fromIndex: 0 });

      // Seek to beginning
      handler.handleCommand('c1', { type: 'seek', sessionId: 's1', timestamp: new Date(0).toISOString() });
      responses.length = 0;

      handler.handleCommand('c1', { type: 'stepBackward', sessionId: 's1' });
      const snapshots = responsesOfType('markingSnapshot');
      expect(snapshots).toHaveLength(0);
    });
  });

  describe('BreakpointFlow', () => {
    it('should set and list breakpoints', () => {
      setup();
      connectClient('c1');
      registerSessionWithEvents('s1');
      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'live', fromIndex: 0 });

      handler.handleCommand('c1', {
        type: 'setBreakpoint', sessionId: 's1',
        breakpoint: { id: 'bp1', type: 'TRANSITION_ENABLED', target: 'T1', enabled: true },
      });

      const setResponse = lastResponseOfType('breakpointSet')!;
      expect(setResponse.breakpoint.id).toBe('bp1');

      handler.handleCommand('c1', { type: 'listBreakpoints', sessionId: 's1' });
      const listResponse = lastResponseOfType('breakpointList')!;
      expect(listResponse.breakpoints).toHaveLength(1);
      expect(listResponse.breakpoints[0]!.id).toBe('bp1');
    });

    it('should clear breakpoint', () => {
      setup();
      connectClient('c1');
      registerSessionWithEvents('s1');
      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'live', fromIndex: 0 });

      handler.handleCommand('c1', {
        type: 'setBreakpoint', sessionId: 's1',
        breakpoint: { id: 'bp1', type: 'TRANSITION_ENABLED', target: 'T1', enabled: true },
      });
      handler.handleCommand('c1', { type: 'clearBreakpoint', sessionId: 's1', breakpointId: 'bp1' });

      const cleared = lastResponseOfType('breakpointCleared')!;
      expect(cleared.breakpointId).toBe('bp1');

      handler.handleCommand('c1', { type: 'listBreakpoints', sessionId: 's1' });
      const list = lastResponseOfType('breakpointList')!;
      expect(list.breakpoints).toHaveLength(0);
    });

    it('should hit breakpoint on matching event', async () => {
      setup();
      const liveResponses: DebugResponse[] = [];

      handler.clientConnected('c1', r => liveResponses.push(r));

      const sessionId = registerSessionWithEvents('s1');
      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'live', fromIndex: 0 });

      handler.handleCommand('c1', {
        type: 'setBreakpoint', sessionId: 's1',
        breakpoint: { id: 'bp1', type: 'TRANSITION_ENABLED', target: 'T1', enabled: true },
      });

      registry.getSession(sessionId)!.eventStore.append(enabledEvent('T1'));
      await new Promise(r => setTimeout(r, 50));

      const hits = liveResponses.filter(r => r.type === 'breakpointHit') as Extract<DebugResponse, { type: 'breakpointHit' }>[];
      expect(hits).toHaveLength(1);
      expect(hits[0]!.breakpointId).toBe('bp1');
    });

    it('should ignore disabled breakpoint', async () => {
      setup();
      const liveResponses: DebugResponse[] = [];

      handler.clientConnected('c1', r => liveResponses.push(r));

      const sessionId = registerSessionWithEvents('s1');
      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'live', fromIndex: 0 });

      handler.handleCommand('c1', {
        type: 'setBreakpoint', sessionId: 's1',
        breakpoint: { id: 'bp1', type: 'TRANSITION_ENABLED', target: 'T1', enabled: false },
      });

      registry.getSession(sessionId)!.eventStore.append(enabledEvent('T1'));
      await new Promise(r => setTimeout(r, 50));

      const hits = liveResponses.filter(r => r.type === 'breakpointHit');
      expect(hits).toHaveLength(0);
    });
  });

  describe('PlaybackControlFlow', () => {
    it('should set playback speed', () => {
      setup();
      connectClient('c1');
      registerSessionWithEvents('s1');
      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'live', fromIndex: 0 });

      handler.handleCommand('c1', { type: 'playbackSpeed', sessionId: 's1', speed: 2.0 });

      const state = lastResponseOfType('playbackStateChanged')!;
      expect(state.speed).toBe(2.0);
      expect(state.sessionId).toBe('s1');
    });

    it('should toggle pause resume state', () => {
      setup();
      connectClient('c1');
      registerSessionWithEvents('s1');
      handler.handleCommand('c1', { type: 'subscribe', sessionId: 's1', mode: 'live', fromIndex: 0 });

      handler.handleCommand('c1', { type: 'pause', sessionId: 's1' });
      expect(lastResponseOfType('playbackStateChanged')!.paused).toBe(true);

      handler.handleCommand('c1', { type: 'resume', sessionId: 's1' });
      expect(lastResponseOfType('playbackStateChanged')!.paused).toBe(false);
    });
  });

  describe('ErrorHandling', () => {
    it('should return error for unknown session', () => {
      setup();
      connectClient('c1');
      handler.handleCommand('c1', { type: 'subscribe', sessionId: 'nonexistent', mode: 'live', fromIndex: 0 });

      const error = lastResponseOfType('error')!;
      expect(error.code).toBe('SESSION_NOT_FOUND');
      expect(error.sessionId).toBe('nonexistent');
    });

    it('should return error for seek on unknown session', () => {
      setup();
      connectClient('c1');
      handler.handleCommand('c1', { type: 'seek', sessionId: 'nonexistent', timestamp: new Date().toISOString() });

      const error = lastResponseOfType('error')!;
      expect(error.code).toBe('SESSION_NOT_FOUND');
    });
  });

  describe('ComputeStatePureFunctions', () => {
    it('should compute state from event sequence', () => {
      const now = Date.now();
      const events: NetEvent[] = [
        { type: 'token-added', timestamp: now, placeName: 'P1', token: tokenOf('a') },
        { type: 'transition-enabled', timestamp: now, transitionName: 'T1' },
        { type: 'transition-started', timestamp: now, transitionName: 'T1', consumedTokens: [tokenOf('a')] },
        { type: 'transition-completed', timestamp: now, transitionName: 'T1', producedTokens: [tokenOf('b')], durationMs: 10 },
        { type: 'token-added', timestamp: now, placeName: 'P2', token: tokenOf('b') },
      ];

      const state = computeState(events);

      // T1 was started then completed
      expect(state.enabledTransitions).not.toContain('T1');
      expect(state.inFlightTransitions).not.toContain('T1');

      // P1 and P2 should have tokens
      expect(state.marking.get('P1')).toBeDefined();
      expect(state.marking.get('P2')).toBeDefined();
    });
  });
});
