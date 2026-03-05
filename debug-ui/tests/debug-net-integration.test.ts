/**
 * Integration tests: run the actual debug-ui Petri net with BitmapNetExecutor,
 * inject simulated WebSocket messages via environment places, and verify
 * resulting state. Uses happy-dom for DOM elements needed by transition actions.
 */
import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import { BitmapNetExecutor } from 'libpetri';
import { initElements } from '../src/dom/elements.js';
import { buildDebugNet, setExecutor } from '../src/net/definition.js';
import { allEnvironmentPlaces } from '../src/net/places.js';
import * as p from '../src/net/places.js';
import { shared } from '../src/net/shared-state.js';
import type { UIState } from '../src/net/types.js';
import type { DebugResponse } from '../src/protocol/index.js';

// Mock createWebSocket to prevent real WebSocket connections.
// The test manually injects wsOpenSignal/wsCloseSignal instead.
vi.mock('../src/net/actions/connection.js', async (importOriginal) => {
  const original = await importOriginal<typeof import('../src/net/actions/connection.js')>();
  return {
    ...original,
    createWebSocket: vi.fn(),
  };
});

// Mock renderDotDiagram to avoid viz.js rendering
vi.mock('../src/net/actions/diagram.js', async (importOriginal) => {
  const original = await importOriginal<typeof import('../src/net/actions/diagram.js')>();
  return {
    ...original,
    renderDotDiagram: vi.fn().mockResolvedValue(undefined),
    updateDiagramHighlighting: vi.fn(),
  };
});

/** Wait for the executor to process pending work. */
async function settle(ms = 50): Promise<void> {
  await new Promise(resolve => setTimeout(resolve, ms));
}

function makeSubscribedResponse(mode: 'live' | 'replay' = 'live'): Extract<DebugResponse, { type: 'subscribed' }> {
  return {
    type: 'subscribed',
    sessionId: 'test-session',
    netName: 'TestNet',
    dotDiagram: 'digraph G { p_start -> t_go -> p_end }',
    structure: {
      places: [
        { name: 'start', graphId: 'p_start', tokenType: 'Void', isStart: true, isEnd: false, isEnvironment: false },
        { name: 'end', graphId: 'p_end', tokenType: 'Void', isStart: false, isEnd: true, isEnvironment: false },
      ],
      transitions: [
        { name: 'go', graphId: 't_go' },
      ],
    },
    currentMarking: {
      start: [{ id: '1', type: 'Void', value: null, timestamp: null }],
    },
    enabledTransitions: ['go'],
    inFlightTransitions: [],
    eventCount: 0,
    mode,
  };
}

function makeEventBatch(count: number, startIndex = 0): Extract<DebugResponse, { type: 'eventBatch' }> {
  const events = Array.from({ length: count }, (_, i) => ({
    type: i % 2 === 0 ? 'TokenAdded' as const : 'TransitionEnabled' as const,
    timestamp: `2024-01-01T00:00:${String(i).padStart(2, '0')}Z`,
    transitionName: i % 2 === 1 ? `t${i}` : null,
    placeName: i % 2 === 0 ? `p${i}` : null,
    details: i % 2 === 0
      ? { token: { id: String(i), type: 'Int', value: String(i), timestamp: null } }
      : {},
  }));
  return {
    type: 'eventBatch',
    sessionId: 'test-session',
    startIndex,
    events,
    hasMore: false,
  };
}

function readUIState(executor: BitmapNetExecutor): UIState | null {
  const tokens = executor.getMarking().peekTokens(p.uiState);
  return tokens.length > 0 ? tokens[0]!.value as UIState : null;
}

describe('debug net integration', () => {
  let executor: BitmapNetExecutor;

  beforeEach(() => {
    // DOM setup is handled by setup.ts beforeEach
    initElements();

    // Reset shared state
    shared.ws = null;
    shared.currentSession = null;
    shared.currentMode = null;
    shared.replay = { allEvents: [], checkpoints: [], checkpointInterval: 20 };
    shared.playback = { timer: null, animationFrame: null, speed: 1 };
    shared.svgNodeCache = null;
    shared.prevHighlighted = { shapes: [], edges: [] };

    const { net, initialTokens } = buildDebugNet();
    executor = new BitmapNetExecutor(net, initialTokens, {
      environmentPlaces: allEnvironmentPlaces,
      longRunning: true,
    });
    setExecutor(executor);
    executor.run();
  });

  afterEach(() => {
    executor.close();
  });

  /** Drive the net through connection → subscribe flow. */
  async function subscribeWith(mode: 'live' | 'replay'): Promise<void> {
    // t_connect fires immediately from idle → connecting
    await settle();

    // Simulate WebSocket open (createWebSocket is mocked, so we drive this manually)
    await executor.injectValue(p.wsOpenSignal, undefined);
    await settle();

    // User selects session (needs noSession + userSelectSession, reads connected)
    await executor.injectValue(p.userSelectSession, { sessionId: 'test-session', mode });
    await settle();

    // Server responds with subscribed
    await executor.injectValue(p.wsMessage, makeSubscribedResponse(mode) as DebugResponse);
    await settle();
  }

  it('live mode event batch advances eventIndex', async () => {
    await subscribeWith('live');

    // Verify initial state
    let state = readUIState(executor);
    expect(state).not.toBeNull();
    expect(state!.eventIndex).toBe(0);

    // Inject event batch
    await executor.injectValue(p.wsMessage, makeEventBatch(10) as DebugResponse);
    await settle();

    state = readUIState(executor);
    expect(state).not.toBeNull();
    expect(state!.eventIndex).toBe(10);
    // Marking should have tokens from TokenAdded events
    expect(Object.keys(state!.marking).length).toBeGreaterThan(0);
  });

  it('live mode highlighting receives non-null session', async () => {
    await subscribeWith('live');

    // shared.currentSession should be set by t_on_subscribed
    expect(shared.currentSession).not.toBeNull();
    expect(shared.currentSession!.sessionId).toBe('test-session');
    expect(shared.currentSession!.mode).toBe('live');
    expect(shared.currentMode).toBe('live');
  });

  it('replay mode stores events without advancing eventIndex', async () => {
    await subscribeWith('replay');

    // Inject event batch in replay mode
    await executor.injectValue(p.wsMessage, makeEventBatch(100) as DebugResponse);
    await settle();

    const state = readUIState(executor);
    expect(state).not.toBeNull();
    // In replay mode, eventIndex should stay at 0 (user must manually step)
    expect(state!.eventIndex).toBe(0);
    // But all events should be stored in shared.replay
    expect(shared.replay.allEvents).toHaveLength(100);
  });

  it('replay step forward advances one event', async () => {
    await subscribeWith('replay');

    // Send events
    await executor.injectValue(p.wsMessage, makeEventBatch(10) as DebugResponse);
    await settle();

    // Step forward
    await executor.injectValue(p.userClickStepFwd, undefined);
    await settle();

    const state = readUIState(executor);
    expect(state).not.toBeNull();
    expect(state!.eventIndex).toBe(1);
  });

  it('replay seek to index uses checkpoints', async () => {
    await subscribeWith('replay');

    // Send 100 events (will create checkpoints at 20, 40, 60, 80, 100)
    await executor.injectValue(p.wsMessage, makeEventBatch(100) as DebugResponse);
    await settle();

    // Seek to index 50
    await executor.injectValue(p.userSeekSlider, 50);
    await settle();

    const state = readUIState(executor);
    expect(state).not.toBeNull();
    expect(state!.eventIndex).toBe(50);
  });

  it('subscribed response sets shared.currentSession and currentMode', async () => {
    await subscribeWith('replay');

    expect(shared.currentSession).not.toBeNull();
    expect(shared.currentSession!.netName).toBe('TestNet');
    expect(shared.currentMode).toBe('replay');
  });

  it('session list populates dropdown', async () => {
    // t_connect fires from idle
    await settle();

    // WebSocket open
    await executor.injectValue(p.wsOpenSignal, undefined);
    await settle();

    // Session list message
    await executor.injectValue(p.wsMessage, {
      type: 'sessionList',
      sessions: [
        { sessionId: 's1', netName: 'Net1', startTime: '2024-01-01T00:00:00Z', active: true, eventCount: 5 },
        { sessionId: 's2', netName: 'Net2', startTime: '2024-01-01T01:00:00Z', active: false, eventCount: 100 },
      ],
    } as DebugResponse);
    await settle();

    const select = document.getElementById('session-select') as HTMLSelectElement;
    // Default option + 2 sessions
    expect(select.options.length).toBe(3);
  });
});
