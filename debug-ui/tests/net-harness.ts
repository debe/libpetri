/**
 * Runs the real debug-ui net for the runtime tests: executor, event store, and the few moves
 * every test makes (connect, subscribe, read a place). The `vi.mock` calls for the WebSocket
 * and the diagram renderer stay in each test file, where vitest hoists them.
 */
import { BitmapNetExecutor, InMemoryEventStore, type NetEvent, type Place } from 'libpetri';
import { initElements } from '../src/dom/elements.js';
import { buildDebugNet, setExecutor } from '../src/net/definition.js';
import { allEnvironmentPlaces, messageRoutes } from '../src/net/places.js';
import * as p from '../src/net/places.js';
import { shared } from '../src/net/shared-state.js';
import type { UIState } from '../src/net/types.js';
import type { DebugResponse, NetEventInfo } from '../src/protocol/index.js';

export const SESSION = 'test-session';

export function tokenAdded(placeName: string, id: string): NetEventInfo {
  return {
    type: 'TokenAdded',
    timestamp: '2024-01-01T00:00:00Z',
    transitionName: null,
    placeName,
    details: { token: { id, type: 'Int', value: id, timestamp: null } },
  };
}

export function subscribed(sessionId = SESSION, mode: 'live' | 'replay' = 'live'): Extract<DebugResponse, { type: 'subscribed' }> {
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

/** `count` events, alternating TokenAdded (even index) and TransitionEnabled (odd index). */
export function eventBatch(count: number, startIndex = 0): Extract<DebugResponse, { type: 'eventBatch' }> {
  const events: NetEventInfo[] = Array.from({ length: count }, (_, i) => i % 2 === 0
    ? tokenAdded(`p${startIndex + i}`, String(startIndex + i))
    : { type: 'TransitionEnabled', timestamp: '2024-01-01T00:00:00Z', transitionName: `t${startIndex + i}`, placeName: null, details: {} });
  return { type: 'eventBatch', sessionId: SESSION, startIndex, events, hasMore: false };
}

export async function settle(ms = 40): Promise<void> {
  await new Promise(resolve => setTimeout(resolve, ms));
}

export interface RunningNet {
  readonly executor: BitmapNetExecutor;
  readonly store: InMemoryEventStore;
  inject(message: unknown): Promise<boolean>;
  connect(): Promise<void>;
  subscribe(mode: 'live' | 'replay', sessionId?: string): Promise<void>;
  tokens(place: Place<unknown>): number;
  uiState(): UIState;
  /** Names of the transitions started since event `from`, in firing order. */
  fired(from?: number): string[];
  failures(from?: number): NetEvent[];
  mark(): number;
  /** Permit back, nothing queued, nothing between the classifier and a handler. */
  routerAtRest(): Record<string, number>;
  close(): void;
}

export function resetShared(): void {
  shared.ws = null;
  shared.currentSession = null;
  shared.currentMode = null;
  shared.replay = { allEvents: [], checkpoints: [], checkpointInterval: 20 };
  if (shared.playback.timer) clearTimeout(shared.playback.timer);
  shared.playback.timer = null;
  shared.playback.animationFrame = null;
  shared.playback.speed = 1;
  shared.svgNodeCache = null;
  shared.viewerHandle = null;
  shared.prevHighlighted = { shapes: [], edges: [] };
  shared.allSessions = [];
  shared.netNameFilter = '';
}

export function startNet(): RunningNet {
  initElements();
  resetShared();
  const { net, initialTokens } = buildDebugNet();
  const store = new InMemoryEventStore();
  const executor = new BitmapNetExecutor(net, initialTokens, { environmentPlaces: allEnvironmentPlaces, eventStore: store });
  setExecutor(executor);
  void executor.run();

  const tokens = (place: Place<unknown>) => executor.getMarking().peekTokens(place).length;
  const inject = (message: unknown) => executor.injectValue(p.wsMessage, message as DebugResponse);
  async function connect(): Promise<void> {
    await settle();
    await executor.injectValue(p.wsOpenSignal, undefined);
    await settle();
  }
  return {
    executor, store, inject, connect, tokens,
    async subscribe(mode, sessionId = SESSION) {
      if (tokens(p.connected) === 0) await connect();
      await executor.injectValue(p.userSelectSession, { sessionId, mode });
      await settle();
      await inject(subscribed(sessionId, mode));
      await settle();
    },
    uiState: () => executor.getMarking().peekTokens(p.uiState)[0]!.value as UIState,
    fired: (from = 0) => store.events().slice(from)
      .filter((e): e is Extract<NetEvent, { type: 'transition-started' }> => e.type === 'transition-started')
      .map(e => e.transitionName),
    failures: (from = 0) => store.events().slice(from).filter(e => e.type === 'transition-failed'),
    mark: () => store.events().length,
    routerAtRest() {
      const resting: Record<string, number> = {};
      if (tokens(p.routerReady) !== 1) resting['routerReady'] = tokens(p.routerReady);
      if (tokens(p.wsMessage.place) !== 0) resting['wsMessage'] = tokens(p.wsMessage.place);
      if (tokens(p.deadLetter) !== 0) resting['deadLetter'] = tokens(p.deadLetter);
      for (const route of Object.values(messageRoutes) as Place<unknown>[]) {
        if (tokens(route) !== 0) resting[route.name] = tokens(route);
      }
      return resting;
    },
    close: () => { void executor.close(); },
  };
}

/** Makes every `updateTimelinePosition` throw until the returned function is called. */
export function breakTimeline(): () => void {
  const position = document.getElementById('timeline-position')!;
  Object.defineProperty(position, 'textContent', {
    configurable: true,
    get() { return ''; },
    set() { throw new Error('timeline is broken'); },
  });
  return () => { delete (position as unknown as { textContent?: unknown }).textContent; };
}
