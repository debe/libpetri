/**
 * Pins the WebSocket message router of the debug-ui net (definition.ts, "Message router").
 *
 * The router replaced fifteen guarded inputs on `wsMessage` (guards left the core with IO-006).
 * What is pinned here, against the running net:
 *
 * - every protocol message type reaches exactly its own handler and no other;
 * - a frame with no route is dead-lettered: logged, not lost in a place, not misrouted;
 * - messages of different types are handled in arrival order (one permit, `routerReady`);
 * - a message its handler has no use for in the current session state is dead-lettered
 *   instead of waiting for a later session, and a throwing handler cannot take the permit down.
 *
 * The topology claims (nothing strands, the permit is conserved) are proven on the same
 * transitions in `message-router-verification.test.ts`.
 */
import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import {
  BitmapNetExecutor, InMemoryEventStore, PetriNet, Transition, environmentPlace, one, outPlace, immediate,
  type NetEvent,
} from 'libpetri';
import { initElements } from '../src/dom/elements.js';
import { buildDebugNet, setExecutor } from '../src/net/definition.js';
import { allEnvironmentPlaces, messageRoutes } from '../src/net/places.js';
import * as p from '../src/net/places.js';
import { shared } from '../src/net/shared-state.js';
import type { UIState } from '../src/net/types.js';
import type { DebugResponse, NetEventInfo } from '../src/protocol/index.js';

vi.mock('../src/net/actions/connection.js', async (importOriginal) => {
  const original = await importOriginal<typeof import('../src/net/actions/connection.js')>();
  return { ...original, createWebSocket: vi.fn() };
});

vi.mock('../src/net/actions/diagram.js', async (importOriginal) => {
  const original = await importOriginal<typeof import('../src/net/actions/diagram.js')>();
  return {
    ...original,
    renderDotDiagram: vi.fn().mockResolvedValue(undefined),
    updateDiagramHighlighting: vi.fn(),
  };
});

type MessageType = DebugResponse['type'];

/** The one transition that may consume each message type while a live session is subscribed. */
const HANDLER: Record<MessageType, string> = {
  sessionList: 't_on_session_list',
  subscribed: 't_on_subscribed',
  unsubscribed: 't_on_unsubscribed',
  event: 't_on_event',
  eventBatch: 't_on_event_batch',
  markingSnapshot: 't_on_marking_snapshot',
  playbackStateChanged: 't_on_playback_state',
  filterApplied: 't_on_filter_applied',
  breakpointHit: 't_on_breakpoint_hit',
  breakpointList: 't_on_bp_list',
  breakpointSet: 't_on_bp_set',
  breakpointCleared: 't_on_bp_cleared',
  error: 't_on_error',
  archiveList: 't_on_archive_list',
  archiveImported: 't_on_archive_imported',
};

const SESSION = 'test-session';

function tokenAdded(placeName: string, id: string): NetEventInfo {
  return {
    type: 'TokenAdded',
    timestamp: '2024-01-01T00:00:00Z',
    transitionName: null,
    placeName,
    details: { token: { id, type: 'Int', value: id, timestamp: null } },
  };
}

function subscribed(sessionId = SESSION, mode: 'live' | 'replay' = 'live'): Extract<DebugResponse, { type: 'subscribed' }> {
  return {
    type: 'subscribed',
    sessionId,
    netName: 'TestNet',
    dotDiagram: 'digraph G { p_start -> t_go -> p_end }',
    structure: {
      places: [{ name: 'start', graphId: 'p_start', tokenType: 'Void', isStart: true, isEnd: false, isEnvironment: false }],
      transitions: [{ name: 'go', graphId: 't_go' }],
    },
    currentMarking: {},
    enabledTransitions: [],
    inFlightTransitions: [],
    eventCount: 0,
    mode,
    subnetInstances: [],
  };
}

const breakpoint = { id: 'bp1', type: 'TRANSITION_START', target: 'go', enabled: true } as const;

/** One well-formed message of every protocol type. */
const SAMPLE: { [K in MessageType]: Extract<DebugResponse, { type: K }> } = {
  sessionList: { type: 'sessionList', sessions: [] },
  subscribed: subscribed('other-session'),
  unsubscribed: { type: 'unsubscribed', sessionId: SESSION },
  event: { type: 'event', sessionId: SESSION, index: 0, event: tokenAdded('pA', '1') },
  eventBatch: { type: 'eventBatch', sessionId: SESSION, startIndex: 0, events: [tokenAdded('pA', '1')], hasMore: false },
  markingSnapshot: { type: 'markingSnapshot', sessionId: SESSION, marking: {}, enabledTransitions: [], inFlightTransitions: [] },
  playbackStateChanged: { type: 'playbackStateChanged', sessionId: SESSION, paused: true, speed: 2, currentIndex: 0 },
  filterApplied: { type: 'filterApplied', sessionId: SESSION, filter: {} as never },
  breakpointHit: { type: 'breakpointHit', sessionId: SESSION, breakpointId: 'bp1', event: tokenAdded('pA', '1'), eventIndex: 0 },
  breakpointList: { type: 'breakpointList', sessionId: SESSION, breakpoints: [breakpoint as never] },
  breakpointSet: { type: 'breakpointSet', sessionId: SESSION, breakpoint: breakpoint as never },
  breakpointCleared: { type: 'breakpointCleared', sessionId: SESSION, breakpointId: 'bp1' },
  error: { type: 'error', code: 'E_TEST', message: 'boom', sessionId: null },
  archiveList: { type: 'archiveList', archives: [], storageAvailable: true },
  archiveImported: { type: 'archiveImported', sessionId: 'imported', netName: 'TestNet', eventCount: 0 },
};

async function settle(ms = 40): Promise<void> {
  await new Promise(resolve => setTimeout(resolve, ms));
}

describe('message router', () => {
  let executor: BitmapNetExecutor;
  let store: InMemoryEventStore;
  let warn: ReturnType<typeof vi.spyOn>;
  let debug: ReturnType<typeof vi.spyOn>;
  let error: ReturnType<typeof vi.spyOn>;

  beforeEach(() => {
    initElements();
    shared.ws = null;
    shared.currentSession = null;
    shared.currentMode = null;
    shared.replay = { allEvents: [], checkpoints: [], checkpointInterval: 20 };
    shared.playback = { timer: null, animationFrame: null, speed: 1 };
    shared.svgNodeCache = null;
    shared.viewerHandle = null;
    shared.prevHighlighted = { shapes: [], edges: [] };
    shared.allSessions = [];
    shared.netNameFilter = '';

    warn = vi.spyOn(console, 'warn').mockImplementation(() => {});
    debug = vi.spyOn(console, 'debug').mockImplementation(() => {});
    error = vi.spyOn(console, 'error').mockImplementation(() => {});

    const { net, initialTokens } = buildDebugNet();
    store = new InMemoryEventStore();
    executor = new BitmapNetExecutor(net, initialTokens, {
      environmentPlaces: allEnvironmentPlaces,
      eventStore: store,
    });
    setExecutor(executor);
    executor.run();
  });

  afterEach(() => {
    executor.close();
    warn.mockRestore();
    debug.mockRestore();
    error.mockRestore();
  });

  const inject = (message: unknown) => executor.injectValue(p.wsMessage, message as DebugResponse);

  async function connect(): Promise<void> {
    await settle();
    await executor.injectValue(p.wsOpenSignal, undefined);
    await settle();
  }

  async function subscribeLive(): Promise<void> {
    await connect();
    await executor.injectValue(p.userSelectSession, { sessionId: SESSION, mode: 'live' });
    await settle();
    await inject(subscribed());
    await settle();
  }

  async function subscribeReplay(events = 0): Promise<void> {
    await connect();
    await executor.injectValue(p.userSelectSession, { sessionId: SESSION, mode: 'replay' });
    await settle();
    await inject(subscribed(SESSION, 'replay'));
    await settle();
    if (events > 0) {
      await inject({ type: 'eventBatch', sessionId: SESSION, startIndex: 0, events: Array.from({ length: events }, (_, i) => tokenAdded(`r${i}`, String(i))), hasMore: false });
      await settle();
    }
  }

  /** Router and handler firings since `from`, in firing order. */
  function routed(from: number): string[] {
    return store.events().slice(from)
      .filter((e): e is Extract<NetEvent, { type: 'transition-started' }> => e.type === 'transition-started')
      .map(e => e.transitionName)
      .filter(name => /^t_(route_message|on_|drop_|log_dead_letter)/.test(name) && !/^t_on_(open|close)/.test(name));
  }

  function failures(from = 0): NetEvent[] {
    return store.events().slice(from).filter(e => e.type === 'transition-failed');
  }

  function tokens(place: Parameters<ReturnType<BitmapNetExecutor['getMarking']>['peekTokens']>[0]): number {
    return executor.getMarking().peekTokens(place).length;
  }

  /** The router is at rest: permit back, nothing queued, nothing between classifier and handler. */
  function expectRouterAtRest(): void {
    expect(tokens(p.routerReady), 'routerReady').toBe(1);
    expect(tokens(p.wsMessage.place), 'wsMessage').toBe(0);
    expect(tokens(p.deadLetter), 'deadLetter').toBe(0);
    for (const [type, route] of Object.entries(messageRoutes)) {
      expect(tokens(route), `route of ${type}`).toBe(0);
    }
  }

  function uiState(): UIState {
    return executor.getMarking().peekTokens(p.uiState)[0]!.value as UIState;
  }

  // ---------------------------------------------------------------------------------------
  // Each type reaches exactly its handler
  // ---------------------------------------------------------------------------------------

  describe('each message type reaches exactly its handler', () => {
    const types = (Object.keys(HANDLER) as MessageType[]).filter(t => t !== 'subscribed');

    it.each(types)('%s', async (type) => {
      await subscribeLive();
      const from = store.events().length;

      await inject(SAMPLE[type]);
      await settle();

      expect(routed(from)).toEqual(['t_route_message', HANDLER[type]]);
      expect(failures()).toEqual([]);
      expect(warn).not.toHaveBeenCalled();
      expect(debug).not.toHaveBeenCalled();
      expectRouterAtRest();
    });

    it('subscribed (while a subscribe is outstanding)', async () => {
      await subscribeLive();
      await executor.injectValue(p.userSelectSession, { sessionId: 'other-session', mode: 'live' });
      await settle();
      const from = store.events().length;

      await inject(SAMPLE.subscribed);
      await settle();

      expect(routed(from)).toEqual(['t_route_message', 't_on_subscribed']);
      expect(failures()).toEqual([]);
      expect(shared.currentSession!.sessionId).toBe('other-session');
      expectRouterAtRest();
    });

    it('eventBatch in a replay session goes to the replay handler: stored, not followed', async () => {
      await subscribeReplay();
      const from = store.events().length;

      await inject(SAMPLE.eventBatch);
      await settle();

      expect(routed(from)).toEqual(['t_route_message', 't_on_replay_event_batch']);
      expect(failures()).toEqual([]);
      expect(shared.replay.allEvents).toHaveLength(1);
      expect(uiState().totalEvents).toBe(1);
      expect(uiState().eventIndex).toBe(0);
      expect(uiState().marking).toEqual({});
      expectRouterAtRest();
    });

    it('the route table covers the whole protocol, one place per type', () => {
      expect(Object.keys(messageRoutes).sort()).toEqual(Object.keys(HANDLER).sort());
      const names = Object.values(messageRoutes).map(route => route.name);
      expect(new Set(names).size).toBe(names.length);
    });
  });

  // ---------------------------------------------------------------------------------------
  // Frames with no route
  // ---------------------------------------------------------------------------------------

  describe('a frame with no route is dead-lettered, not lost and not misrouted', () => {
    const frames: Array<[string, unknown]> = [
      ['an unknown type', { type: 'telemetry', sessions: 7 }],
      ['no type', { sessions: [] }],
      ['a non-string type', { type: 42 }],
      ['null', null],
      ['a string', 'sessionList'],
      ['an array', [{ type: 'sessionList' }]],
      // Own keys of no route table, inherited members of an ordinary object.
      ['type "__proto__"', { type: '__proto__' }],
      ['type "constructor"', { type: 'constructor' }],
      ['type "toString"', { type: 'toString' }],
    ];

    it.each(frames)('%s', async (_label, frame) => {
      await subscribeLive();
      const before = uiState();
      const from = store.events().length;

      await inject(frame);
      await settle();

      expect(routed(from)).toEqual(['t_route_message', 't_log_dead_letter']);
      expect(failures()).toEqual([]);
      expect(warn).toHaveBeenCalledTimes(1);
      expect(String(warn.mock.calls[0]![0])).toContain('unknown-type');
      expect(warn.mock.calls[0]).toContain(frame);
      expect(uiState()).toBe(before);
      expectRouterAtRest();
    });

    it('does not stall the messages behind it', async () => {
      await subscribeLive();
      const from = store.events().length;

      await inject({ type: 'telemetry' });
      await inject(SAMPLE.event);
      await settle();

      expect(routed(from)).toEqual(['t_route_message', 't_log_dead_letter', 't_route_message', 't_on_event']);
      expect(uiState().eventIndex).toBe(1);
      expectRouterAtRest();
    });
  });

  // ---------------------------------------------------------------------------------------
  // Order
  // ---------------------------------------------------------------------------------------

  describe('interleaved types keep arrival order', () => {
    // What this first test observes is the order, and it would catch a classifier that
    // reordered or misrouted. It does not pin the *permit*: with `routerReady` taken out of the
    // classifier the order still holds, because every handler here is enabled the moment its
    // message is routed, and a pipeline of always-enabled stages keeps its order by itself. The
    // permit is pinned by the test after it, by "while uiState is held by a slow transition"
    // below, and by the two-permit control in message-router-verification.test.ts.
    it('handlers fire in arrival order while none of them has to wait', async () => {
      await subscribeLive();
      const from = store.events().length;

      // The final marking depends on the order: the snapshot wipes pA and must not wipe pC.
      const sequence: Array<[unknown, string]> = [
        [{ type: 'event', sessionId: SESSION, index: 0, event: tokenAdded('pA', '1') }, 't_on_event'],
        [SAMPLE.sessionList, 't_on_session_list'],
        [{ type: 'markingSnapshot', sessionId: SESSION, marking: { pB: [{ id: '2', type: 'Int', value: '2', timestamp: null }] }, enabledTransitions: [], inFlightTransitions: [] }, 't_on_marking_snapshot'],
        [{ type: 'telemetry' }, 't_log_dead_letter'],
        [{ type: 'event', sessionId: SESSION, index: 1, event: tokenAdded('pC', '3') }, 't_on_event'],
        [SAMPLE.breakpointList, 't_on_bp_list'],
        [{ type: 'eventBatch', sessionId: SESSION, startIndex: 2, events: [tokenAdded('pD', '4')], hasMore: false }, 't_on_event_batch'],
        [SAMPLE.error, 't_on_error'],
      ];
      // No settling in between: all eight are queued on wsMessage before the router sees one.
      for (const [message] of sequence) void inject(message);
      await settle(120);

      expect(routed(from).filter(name => name !== 't_route_message')).toEqual(sequence.map(([, handler]) => handler));
      expect(routed(from).filter(name => name === 't_route_message')).toHaveLength(sequence.length);
      expect(Object.keys(uiState().marking).sort()).toEqual(['pB', 'pC', 'pD']);
      expect(uiState().eventIndex).toBe(3);
      expect(failures()).toEqual([]);
      expectRouterAtRest();
    });

    it('one message is between classifier and handler at a time', async () => {
      await subscribeLive();
      for (let i = 0; i < 20; i++) void inject({ type: 'event', sessionId: SESSION, index: i, event: tokenAdded(`p${i}`, String(i)) });
      await settle(200);

      // Read off the event log: between two firings of the classifier, exactly one consumer ran.
      let open = 0;
      for (const name of routed(0)) {
        if (name === 't_route_message') { open++; expect(open).toBe(1); } else { open--; expect(open).toBe(0); }
      }
      expect(uiState().events.map(e => e.placeName)).toEqual(Array.from({ length: 20 }, (_, i) => `p${i}`));
      expectRouterAtRest();
    });
  });

  // ---------------------------------------------------------------------------------------
  // Session state decides, structurally
  // ---------------------------------------------------------------------------------------

  describe('a message the session state has no use for', () => {
    it.each(['event', 'eventBatch', 'markingSnapshot'] as const)('%s with no subscribed session is dead-lettered, not kept for the next session', async (type) => {
      await connect();
      const from = store.events().length;

      await inject(SAMPLE[type]);
      await settle();

      expect(routed(from)).toEqual(['t_route_message', `t_drop_${type === 'event' ? 'event' : type === 'eventBatch' ? 'event_batch' : 'marking_snapshot'}`, 't_log_dead_letter']);
      // Routine, not a defect: the session these belonged to is gone.
      expect(warn).not.toHaveBeenCalled();
      expect(debug).toHaveBeenCalledTimes(1);
      expect(String(debug.mock.calls[0]![0])).toContain('no-session');
      expectRouterAtRest();

      // The session that follows starts clean.
      await executor.injectValue(p.userSelectSession, { sessionId: SESSION, mode: 'live' });
      await settle();
      await inject(subscribed());
      await settle();
      expect(uiState().eventIndex).toBe(0);
      expect(uiState().events).toEqual([]);
      expectRouterAtRest();
    });

    it('subscribed with no subscribe outstanding is dead-lettered and leaves the session alone', async () => {
      await subscribeLive();
      const before = uiState();
      const from = store.events().length;

      await inject(SAMPLE.subscribed);
      await settle();

      expect(routed(from)).toEqual(['t_route_message', 't_drop_subscribed', 't_log_dead_letter']);
      expect(warn).not.toHaveBeenCalled();
      expect(String(debug.mock.calls[0]![0])).toContain('not-subscribing');
      expect(shared.currentSession!.sessionId).toBe(SESSION);
      expect(uiState()).toBe(before);
      expect(tokens(p.subscribedSession)).toBe(1);
      expectRouterAtRest();
    });
  });

  // ---------------------------------------------------------------------------------------
  // A throwing handler
  // ---------------------------------------------------------------------------------------

  describe('a handler that throws', () => {
    it('hands the permit back through the dead-letter place', async () => {
      await subscribeLive();
      const from = store.events().length;

      await inject({ type: 'sessionList', sessions: null });
      await inject(SAMPLE.event);
      await settle();

      expect(routed(from)).toEqual(['t_route_message', 't_on_session_list', 't_log_dead_letter', 't_route_message', 't_on_event']);
      expect(failures()).toEqual([]);
      expect(String(warn.mock.calls[0]![0])).toContain('handler-failed');
      expect(uiState().eventIndex).toBe(1);
      expectRouterAtRest();
    });

    it('puts uiState back unchanged', async () => {
      await subscribeLive();
      const before = uiState();

      await inject({ type: 'event', sessionId: SESSION, index: 0, event: null });
      await settle();

      expect(failures()).toEqual([]);
      expect(String(warn.mock.calls[0]![0])).toContain('handler-failed');
      expect(uiState()).toBe(before);
      expectRouterAtRest();
    });

    it('a malformed breakpointList puts breakpoints back unchanged', async () => {
      await subscribeLive();
      await inject(SAMPLE.breakpointList);
      await settle();
      const before = executor.getMarking().peekTokens(p.breakpoints)[0]!.value;
      expect(before).toEqual([breakpoint]);
      const from = store.events().length;

      await inject({ type: 'breakpointList', sessionId: SESSION, breakpoints: null });
      await inject(SAMPLE.breakpointList);
      await settle();

      expect(routed(from)).toEqual(['t_route_message', 't_on_bp_list', 't_log_dead_letter', 't_route_message', 't_on_bp_list']);
      expect(failures()).toEqual([]);
      expect(warn).toHaveBeenCalledTimes(1);
      expect(String(warn.mock.calls[0]![0])).toContain('handler-failed');
      expect(tokens(p.breakpoints)).toBe(1);
      expect(executor.getMarking().peekTokens(p.breakpoints)[0]!.value).toEqual(before);
      expectRouterAtRest();
    });

    it('a failed subscribe returns to noSession, so the user can select again', async () => {
      await connect();
      await executor.injectValue(p.userSelectSession, { sessionId: SESSION, mode: 'live' });
      await settle();

      await inject({ type: 'subscribed', sessionId: SESSION, structure: null });
      await settle();

      expect(failures()).toEqual([]);
      expect(String(warn.mock.calls[0]![0])).toContain('handler-failed');
      expect(tokens(p.noSession)).toBe(1);
      expect(tokens(p.subscribing)).toBe(0);
      expect(tokens(p.uiState)).toBe(0);
      expectRouterAtRest();

      await executor.injectValue(p.userSelectSession, { sessionId: SESSION, mode: 'live' });
      await settle();
      await inject(subscribed());
      await settle();
      expect(tokens(p.subscribedSession)).toBe(1);
      expect(shared.currentSession!.sessionId).toBe(SESSION);
    });
  });

  // ---------------------------------------------------------------------------------------
  // A handler that has to wait
  // ---------------------------------------------------------------------------------------

  /**
   * Every transition that takes `uiState` today has a synchronous action, so the token is back
   * before the orchestrator looks again, and no message ever finds it missing. Two design
   * choices only show when a holder is slow, so this block runs the real transitions plus one
   * test transition that holds `uiState` until told to let go:
   *
   * - the permit: a message that waits for its handler is not overtaken by the ones behind it;
   * - the drops are inhibited by `subscribedSession`, not by `uiState`: a message that arrives
   *   while the state is held waits for it, and is not dead-lettered as if no session existed.
   */
  describe('while uiState is held by a slow transition', () => {
    const holdRequest = environmentPlace<void>('testHoldUiState');
    let slow: BitmapNetExecutor;
    let slowStore: InMemoryEventStore;
    let release: () => void;

    beforeEach(async () => {
      executor.close();
      const held = new Promise<void>(resolve => { release = resolve; });
      const t_test_hold = Transition.builder('t_test_hold')
        .inputs(one(p.uiState), one(holdRequest.place))
        .outputs(outPlace(p.uiState))
        .timing(immediate())
        .action(async (ctx) => {
          const state = ctx.input(p.uiState);
          await held;
          ctx.output(p.uiState, state);
        })
        .build();

      const { net, initialTokens } = buildDebugNet();
      slowStore = new InMemoryEventStore();
      slow = new BitmapNetExecutor(
        PetriNet.builder('DebugUIWithSlowHolder').transitions(...net.transitions, t_test_hold).build(),
        initialTokens,
        { environmentPlaces: new Set([...allEnvironmentPlaces, holdRequest]), eventStore: slowStore },
      );
      setExecutor(slow);
      void slow.run();

      await settle();
      await slow.injectValue(p.wsOpenSignal, undefined);
      await slow.injectValue(p.userSelectSession, { sessionId: SESSION, mode: 'live' });
      await settle();
      await slow.injectValue(p.wsMessage, subscribed());
      await settle();
      await slow.injectValue(holdRequest, undefined);
      await settle();
      expect(slow.getMarking().peekTokens(p.uiState)).toHaveLength(0);
      expect(slow.getMarking().peekTokens(p.subscribedSession)).toHaveLength(1);
    });

    afterEach(() => { release(); slow.close(); });

    const started = (from: number) => slowStore.events().slice(from)
      .filter((e): e is Extract<NetEvent, { type: 'transition-started' }> => e.type === 'transition-started')
      .map(e => e.transitionName)
      .filter(name => /^t_(on_|drop_|log_dead_letter)/.test(name));

    it('the message waits for its handler, and the ones behind it wait with it', async () => {
      const from = slowStore.events().length;
      void slow.injectValue(p.wsMessage, SAMPLE.event);
      void slow.injectValue(p.wsMessage, SAMPLE.sessionList);
      void slow.injectValue(p.wsMessage, SAMPLE.error);
      await settle(80);

      // Held: the event is between classifier and handler, and nothing has overtaken it.
      expect(started(from)).toEqual([]);
      expect(slow.getMarking().peekTokens(p.msgEvent)).toHaveLength(1);
      expect(slow.getMarking().peekTokens(p.wsMessage.place)).toHaveLength(2);

      release();
      await settle(80);

      expect(started(from)).toEqual(['t_on_event', 't_on_session_list', 't_on_error']);
      expect((slow.getMarking().peekTokens(p.uiState)[0]!.value as UIState).eventIndex).toBe(1);
      expect(debug).not.toHaveBeenCalled();
      expect(warn).not.toHaveBeenCalled();
    });

    it.each(['event', 'eventBatch', 'markingSnapshot'] as const)('%s is applied once the state is back, not dead-lettered', async (type) => {
      const from = slowStore.events().length;
      await slow.injectValue(p.wsMessage, SAMPLE[type]);
      await settle(80);
      expect(started(from)).toEqual([]);

      release();
      await settle(80);

      expect(started(from)).toEqual([HANDLER[type]]);
      expect(debug).not.toHaveBeenCalled();
      expect(slow.getMarking().peekTokens(p.routerReady)).toHaveLength(1);
    });
  });
});
