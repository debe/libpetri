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
    shared.playback = { timer: null, animationFrame: null, speed: 1, breakpointHitIndex: null };
    shared.svgNodeCache = null;
    shared.prevHighlighted = { shapes: [], edges: [] };
    shared.allSessions = [];
    shared.netNameFilter = '';
    shared.pendingDeepLink = null;

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

  it('replay play auto-advances eventIndex', async () => {
    await subscribeWith('replay');

    // Send 50 events
    await executor.injectValue(p.wsMessage, makeEventBatch(50) as DebugResponse);
    await settle();

    // Click play
    await executor.injectValue(p.userClickPlay, undefined);
    // Wait for several auto-steps to fire
    await settle(500);

    const state = readUIState(executor);
    expect(state).not.toBeNull();
    expect(state!.eventIndex).toBeGreaterThan(0);
  });

  it('replay play stops at end of events', async () => {
    await subscribeWith('replay');

    // Send only 5 events
    await executor.injectValue(p.wsMessage, makeEventBatch(5) as DebugResponse);
    await settle();

    // Click play
    await executor.injectValue(p.userClickPlay, undefined);
    await settle(500);

    const state = readUIState(executor);
    expect(state).not.toBeNull();
    expect(state!.eventIndex).toBe(5);

    // Should be back in paused state (replayPlaying consumed, replayPaused present)
    const playing = executor.getMarking().peekTokens(p.replayPlaying);
    expect(playing).toHaveLength(0);
  });

  it('replay pause stops auto-advance', async () => {
    await subscribeWith('replay');

    // Send 50 events
    await executor.injectValue(p.wsMessage, makeEventBatch(50) as DebugResponse);
    await settle();

    // Click play, let it run a bit
    await executor.injectValue(p.userClickPlay, undefined);
    await settle(200);

    // Click pause
    await executor.injectValue(p.userClickPause, undefined);
    await settle();

    const stateAfterPause = readUIState(executor);
    const indexAfterPause = stateAfterPause!.eventIndex;

    // Wait more — index should not advance
    await settle(200);

    const stateAfterWait = readUIState(executor);
    expect(stateAfterWait!.eventIndex).toBe(indexAfterPause);
  });

  it('replay speed affects playback rate', async () => {
    await subscribeWith('replay');

    // Send 100 events
    await executor.injectValue(p.wsMessage, makeEventBatch(100) as DebugResponse);
    await settle();

    // Set speed to 4x then play
    shared.playback.speed = 4;
    await executor.injectValue(p.userClickPlay, undefined);
    await settle(300);

    // Pause to stop
    await executor.injectValue(p.userClickPause, undefined);
    await settle();

    const state = readUIState(executor);
    expect(state).not.toBeNull();
    // At 4x speed (12.5ms/step), 300ms should advance significantly
    expect(state!.eventIndex).toBeGreaterThan(5);
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

  // ======================== Bug regression tests ========================

  it('switching session after initial subscription works (Bug 1)', async () => {
    await subscribeWith('live');
    expect(shared.currentSession!.sessionId).toBe('test-session');

    // Select a different session while already subscribed
    await executor.injectValue(p.userSelectSession, { sessionId: 'session-2', mode: 'replay' });
    await settle();

    // Server responds with new subscribed message
    const response2 = makeSubscribedResponse('replay');
    response2.sessionId = 'session-2';
    response2.netName = 'TestNet2';
    await executor.injectValue(p.wsMessage, response2 as DebugResponse);
    await settle();

    expect(shared.currentSession!.sessionId).toBe('session-2');
    expect(shared.currentMode).toBe('replay');
  });

  it('can switch sessions multiple times (Bug 1)', async () => {
    await subscribeWith('live');

    for (const id of ['s2', 's3', 's4']) {
      await executor.injectValue(p.userSelectSession, { sessionId: id, mode: 'live' });
      await settle();
      const resp = makeSubscribedResponse('live');
      resp.sessionId = id;
      await executor.injectValue(p.wsMessage, resp as DebugResponse);
      await settle();
      expect(shared.currentSession!.sessionId).toBe(id);
    }
  });

  it('archive import auto-subscribes to imported session (Bug 2)', async () => {
    // Connect (no session yet)
    await settle();
    await executor.injectValue(p.wsOpenSignal, undefined);
    await settle();

    // Simulate archive imported response
    await executor.injectValue(p.wsMessage, {
      type: 'archiveImported',
      sessionId: 'imported-1',
      netName: 'ArchivedNet',
      eventCount: 200,
    } as DebugResponse);
    await settle();

    // t_on_archive_imported should inject userSelectSession → t_subscribe fires
    // Server responds with subscribed
    const resp = makeSubscribedResponse('replay');
    resp.sessionId = 'imported-1';
    await executor.injectValue(p.wsMessage, resp as DebugResponse);
    await settle();

    expect(shared.currentSession!.sessionId).toBe('imported-1');
    expect(shared.currentMode).toBe('replay');

    // Archive modal should be hidden
    const modal = document.getElementById('archive-modal');
    expect(modal!.classList.contains('hidden')).toBe(true);
  });

  it('marking inspector renders on initial subscription (Bug 3)', async () => {
    await subscribeWith('live');

    // Three rafTick injections needed: t_update_highlighting, t_update_event_log,
    // and t_update_marking each consume one rafTick token.
    await executor.injectValue(p.rafTick, undefined);
    await executor.injectValue(p.rafTick, undefined);
    await executor.injectValue(p.rafTick, undefined);
    await settle();

    const inspector = document.getElementById('marking-inspector');
    // From makeSubscribedResponse: currentMarking has 'start' place with 1 token
    expect(inspector!.innerHTML).toContain('start');
  });

  it('subscription produces stateDirty which fans out to markingDirty (Bug 3)', async () => {
    await subscribeWith('live');
    // After t_on_subscribed + t_fan_out_dirty, markingDirty should exist
    // (waiting for rafTick to consume it)
    const marking = executor.getMarking();
    const dirty = marking.peekTokens(p.markingDirty);
    expect(dirty.length).toBe(1);
  });

  it('clicking a place by name shows tokens in token inspector', async () => {
    await subscribeWith('live');

    // Click place by name (as marking inspector does)
    await executor.injectValue(p.userClickPlace, 'start');
    await settle();

    const inspector = document.getElementById('token-inspector');
    expect(inspector!.innerHTML).toContain('start');
    expect(inspector!.innerHTML).toContain('Void');
  });

  it('clicking a place by graphId resolves to place name in token inspector', async () => {
    await subscribeWith('live');

    // Click place by graphId (as diagram click does)
    await executor.injectValue(p.userClickPlace, 'p_start');
    await settle();

    const inspector = document.getElementById('token-inspector');
    // Should resolve p_start → start via byGraphId lookup
    expect(inspector!.innerHTML).toContain('start');
    expect(inspector!.innerHTML).toContain('Void');
  });

  it('replay breakpoint halts playback at matching event', async () => {
    await subscribeWith('replay');

    // Send events: alternating TokenAdded and TransitionEnabled
    await executor.injectValue(p.wsMessage, makeEventBatch(20) as DebugResponse);
    await settle();

    // Set breakpoint on TransitionEnabled (odd indices in makeEventBatch)
    await executor.injectValue(p.userSetBreakpoint, {
      id: 'bp-test', type: 'TRANSITION_ENABLED', target: null, enabled: true,
    });
    await settle();

    // Click play
    await executor.injectValue(p.userClickPlay, undefined);
    await settle(500);

    const state = readUIState(executor);
    expect(state).not.toBeNull();
    // First TransitionEnabled is at index 1 — playback should stop BEFORE stepping past it
    expect(state!.eventIndex).toBe(1);

    // Should be in breakpointPaused state (not replayPlaying, not replayPaused)
    const playing = executor.getMarking().peekTokens(p.replayPlaying);
    expect(playing).toHaveLength(0);
    const bpPaused = executor.getMarking().peekTokens(p.breakpointPaused);
    expect(bpPaused).toHaveLength(1);

    // Button should be yellow (breakpoint hit)
    const btn = document.getElementById('btn-pause')!;
    expect(btn.classList.contains('bg-yellow-600')).toBe(true);
    expect(btn.classList.contains('bg-green-700')).toBe(false);

    // Resume: click play again — should advance past the breakpoint
    await executor.injectValue(p.userClickPlay, undefined);
    await settle(500);

    const stateAfter = readUIState(executor);
    expect(stateAfter).not.toBeNull();
    // Should have advanced past index 1 (the breakpoint hit index) and stopped at index 3 (next TransitionEnabled)
    expect(stateAfter!.eventIndex).toBe(3);

    // Button should be yellow again (hit next breakpoint)
    expect(btn.classList.contains('bg-yellow-600')).toBe(true);

    // Should be in breakpointPaused again
    const bpPaused2 = executor.getMarking().peekTokens(p.breakpointPaused);
    expect(bpPaused2).toHaveLength(1);
  });

  // ======================== DOM button breakpoint tests ========================

  it('breakpoint resume via DOM button click', async () => {
    const { bindDomEvents } = await import('../src/dom/bindings.js');
    bindDomEvents(executor);

    await subscribeWith('replay');
    await executor.injectValue(p.wsMessage, makeEventBatch(20) as DebugResponse);
    await settle();

    // Set breakpoint on TransitionEnabled
    await executor.injectValue(p.userSetBreakpoint, {
      id: 'bp-dom', type: 'TRANSITION_ENABLED', target: null, enabled: true,
    });
    await settle();

    // Start playback (direct injection OK for initial play)
    await executor.injectValue(p.userClickPlay, undefined);
    await settle(500);

    // Verify breakpoint hit state
    expect(readUIState(executor)!.eventIndex).toBe(1);
    const bpPaused = executor.getMarking().peekTokens(p.breakpointPaused);
    expect(bpPaused).toHaveLength(1);

    // Verify yellow button
    const btn = document.getElementById('btn-pause')!;
    expect(btn.classList.contains('bg-yellow-600')).toBe(true);

    // Resume via DOM button click (NOT direct injection)
    btn.click();
    await settle(500);

    // Should have advanced past breakpoint to next match
    const stateAfter = readUIState(executor);
    expect(stateAfter!.eventIndex).toBe(3);
    expect(btn.classList.contains('bg-yellow-600')).toBe(true);
  });

  it('breakpoint on first event (index 0) via DOM button', async () => {
    const { bindDomEvents } = await import('../src/dom/bindings.js');
    bindDomEvents(executor);

    await subscribeWith('replay');
    // TokenAdded at index 0
    await executor.injectValue(p.wsMessage, makeEventBatch(10) as DebugResponse);
    await settle();

    // Set breakpoint on TokenAdded (even indices)
    await executor.injectValue(p.userSetBreakpoint, {
      id: 'bp-first', type: 'TOKEN_ADDED', target: null, enabled: true,
    });
    await settle();

    // Start playback
    await executor.injectValue(p.userClickPlay, undefined);
    await settle(500);

    // Should stop at index 0 (first event is TokenAdded)
    expect(readUIState(executor)!.eventIndex).toBe(0);
    const bpPaused = executor.getMarking().peekTokens(p.breakpointPaused);
    expect(bpPaused).toHaveLength(1);

    // Resume via DOM button
    const btn = document.getElementById('btn-pause')!;
    expect(btn.classList.contains('bg-yellow-600')).toBe(true);
    btn.click();
    await settle(500);

    // Should advance to next TokenAdded at index 2
    expect(readUIState(executor)!.eventIndex).toBe(2);
  });

  it('multiple consecutive DOM-click resumes through breakpoints', async () => {
    const { bindDomEvents } = await import('../src/dom/bindings.js');
    bindDomEvents(executor);

    await subscribeWith('replay');
    await executor.injectValue(p.wsMessage, makeEventBatch(20) as DebugResponse);
    await settle();

    // Breakpoint on TransitionEnabled (indices 1, 3, 5, 7, ...)
    await executor.injectValue(p.userSetBreakpoint, {
      id: 'bp-multi', type: 'TRANSITION_ENABLED', target: null, enabled: true,
    });
    await settle();

    // Start playback
    await executor.injectValue(p.userClickPlay, undefined);
    await settle(500);

    const btn = document.getElementById('btn-pause')!;
    const expectedStops = [1, 3, 5];

    for (const expectedIndex of expectedStops) {
      expect(readUIState(executor)!.eventIndex).toBe(expectedIndex);
      expect(btn.classList.contains('bg-yellow-600')).toBe(true);
      expect(executor.getMarking().peekTokens(p.breakpointPaused)).toHaveLength(1);

      // Resume via DOM button click
      btn.click();
      await settle(500);
    }

    // After 3 resumes, should be at index 7
    expect(readUIState(executor)!.eventIndex).toBe(7);
  });

  it('clicking a token in token inspector opens value modal', async () => {
    await subscribeWith('live');

    // Populate token inspector by clicking on 'start' place
    await executor.injectValue(p.userClickPlace, 'start');
    await settle();

    // Simulate what the DOM click handler does: open modal with token value
    await executor.injectValue(p.userOpenModal, {
      title: 'start',
      subtitle: 'Token 1 of 1 · Void',
      json: 'null',
    });
    await settle();

    const modal = document.getElementById('value-modal');
    expect(modal!.classList.contains('hidden')).toBe(false);

    const title = document.getElementById('modal-title');
    expect(title!.textContent).toBe('start');

    const subtitle = document.getElementById('modal-subtitle');
    expect(subtitle!.textContent).toBe('Token 1 of 1 · Void');

    const json = document.getElementById('modal-json');
    expect(json!.textContent).toContain('null');

    // Close modal
    await executor.injectValue(p.userCloseModal, undefined);
    await settle();

    expect(modal!.classList.contains('hidden')).toBe(true);
  });
});
