/**
 * An action that throws must not cost the net a resource token.
 *
 * The executor consumes a transition's inputs before its action runs and does not restore them
 * when it fails. `uiState` and `breakpoints` are one-token resources the message router's
 * handlers wait on, and the router is serial: were one of them lost, the next message that
 * needs it would rest on its `msg*` place for good, hold the permit, and stop every message
 * behind it — `sessionList`, `error` and the archive replies included. Nor could the user
 * leave the session, since switching takes `uiState` too.
 *
 * So every transition that takes one of those tokens decides first and then emits it, changed
 * or not. Each case here makes one action throw, then checks the token is back and that a
 * message of every kind is still handled. The verifier cannot see any of this: to it a firing
 * is atomic and infallible.
 */
import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import * as p from '../src/net/places.js';
import { shared } from '../src/net/shared-state.js';
import { startNet, settle, eventBatch, subscribed, breakTimeline, SESSION, type RunningNet } from './net-harness.js';

vi.mock('../src/net/actions/connection.js', async (importOriginal) => {
  const original = await importOriginal<typeof import('../src/net/actions/connection.js')>();
  return { ...original, createWebSocket: vi.fn() };
});

vi.mock('../src/net/actions/diagram.js', async (importOriginal) => {
  const original = await importOriginal<typeof import('../src/net/actions/diagram.js')>();
  return { ...original, renderDotDiagram: vi.fn().mockResolvedValue(undefined), updateDiagramHighlighting: vi.fn() };
});

describe('an action that throws keeps its resource token', () => {
  let n: RunningNet;
  let restore: (() => void) | null;
  let error: ReturnType<typeof vi.spyOn>;
  let warn: ReturnType<typeof vi.spyOn>;

  beforeEach(() => {
    restore = null;
    error = vi.spyOn(console, 'error').mockImplementation(() => {});
    warn = vi.spyOn(console, 'warn').mockImplementation(() => {});
    vi.spyOn(console, 'debug').mockImplementation(() => {});
    n = startNet();
  });

  afterEach(() => {
    restore?.();
    n.close();
    vi.restoreAllMocks();
  });

  /** After the failure: the session still takes a batch, and an unrelated message gets through. */
  async function expectRouterStillServes(): Promise<void> {
    const from = n.mark();
    await n.inject(eventBatch(2, 100));
    await n.inject({ type: 'sessionList', sessions: [] });
    await n.inject({ type: 'error', code: 'E_TEST', message: 'after the failure', sessionId: null });
    await settle(80);

    const handlers = n.fired(from).filter(name => name.startsWith('t_on_'));
    expect(handlers).toEqual(['t_on_replay_event_batch', 't_on_session_list', 't_on_error']);
    expect(n.routerAtRest()).toEqual({});
  }

  const replayCommands: Array<[string, () => Promise<unknown>]> = [
    ['t_replay_step_fwd', () => n.executor.injectValue(p.userClickStepFwd, undefined)],
    ['t_replay_step_back', () => n.executor.injectValue(p.userClickStepBack, undefined)],
    ['t_replay_seek', () => n.executor.injectValue(p.userSeekSlider, 7)],
    ['t_replay_restart', () => n.executor.injectValue(p.userClickRestart, undefined)],
    ['t_replay_run_to_end', () => n.executor.injectValue(p.userClickRunToEnd, undefined)],
  ];

  it.each(replayCommands)('%s: uiState is back, unchanged, and the router still serves', async (name, command) => {
    await n.subscribe('replay');
    await n.inject(eventBatch(10));
    await n.executor.injectValue(p.userSeekSlider, 4);
    await settle();
    const before = n.uiState();
    expect(before.eventIndex).toBe(4);

    restore = breakTimeline();
    const from = n.mark();
    await command();
    await settle();
    restore(); restore = null;

    expect(n.fired(from)).toContain(name);
    expect(n.failures()).toEqual([]);
    expect(n.tokens(p.uiState)).toBe(1);
    expect(n.uiState()).toBe(before);
    expect(error).toHaveBeenCalled();
    await expectRouterStillServes();
  });

  it('t_replay_seek over a corrupt event: uiState is back and the user can still leave the session', async () => {
    await n.subscribe('replay');
    await n.inject(eventBatch(10));
    await settle();
    const before = n.uiState();
    shared.replay.allEvents[3] = null as never;

    await n.executor.injectValue(p.userSeekSlider, 8);
    await settle();

    expect(n.failures()).toEqual([]);
    expect(n.uiState()).toBe(before);

    await n.executor.injectValue(p.userSelectSession, { sessionId: 'other', mode: 'live' });
    await settle();
    expect(n.tokens(p.subscribing)).toBe(1);
    await n.inject(subscribed('other', 'live'));
    await settle();
    expect(n.tokens(p.subscribedSession)).toBe(1);
    expect(shared.currentSession!.sessionId).toBe('other');
    expect(n.routerAtRest()).toEqual({});
  });

  it('t_replay_auto_step: playback stops in replayPaused with uiState back', async () => {
    await n.subscribe('replay');
    await n.inject(eventBatch(10));
    await settle();
    const before = n.uiState();

    restore = breakTimeline();
    await n.executor.injectValue(p.userClickPlay, undefined);
    await settle(150);
    restore(); restore = null;

    expect(n.failures()).toEqual([]);
    expect(n.uiState()).toBe(before);
    expect(n.tokens(p.replayPlaying)).toBe(0);
    expect(n.tokens(p.replayPaused)).toBe(1);
    expect(n.tokens(p.autoStepTick.place)).toBe(0);
    await expectRouterStillServes();
  });

  it.each([
    ['t_set_breakpoint', () => n.executor.injectValue(p.userSetBreakpoint, null as never)],
    ['t_clear_breakpoint', async () => {
      // A list the renderer chokes on: the clear keeps the corrupt entry and renders it.
      await n.inject({ type: 'breakpointList', sessionId: SESSION, breakpoints: [] });
      restore = breakBreakpointList();
      await n.executor.injectValue(p.userClearBreakpoint, 'bp-absent');
    }],
  ] as Array<[string, () => Promise<unknown>]>)('%s: breakpoints is back, unchanged, and a breakpointList is still handled', async (name, command) => {
    await n.subscribe('replay');
    const before = n.executor.getMarking().peekTokens(p.breakpoints)[0]!.value;

    const from = n.mark();
    await command();
    await settle();
    restore?.(); restore = null;

    expect(n.fired(from)).toContain(name);
    expect(n.failures()).toEqual([]);
    expect(n.tokens(p.breakpoints)).toBe(1);
    expect(n.executor.getMarking().peekTokens(p.breakpoints)[0]!.value).toEqual(before);

    const bp = { id: 'bp1', type: 'TRANSITION_START', target: 'go', enabled: true };
    await n.inject({ type: 'breakpointList', sessionId: SESSION, breakpoints: [bp] });
    await settle();
    expect(n.executor.getMarking().peekTokens(p.breakpoints)[0]!.value).toEqual([bp]);
    expect(n.routerAtRest()).toEqual({});
  });

  it('a session switch whose commands cannot be sent returns to noSession, not to a lost session', async () => {
    await n.subscribe('live');
    shared.ws = { readyState: WebSocket.OPEN, send() { throw new Error('socket is gone'); } } as unknown as WebSocket;

    await n.executor.injectValue(p.userSelectSession, { sessionId: 'other', mode: 'live' });
    await settle();
    shared.ws = null;

    expect(n.failures()).toEqual([]);
    expect(n.tokens(p.noSession)).toBe(1);
    expect(n.tokens(p.subscribing)).toBe(0);
    expect(n.tokens(p.subscribedSession)).toBe(0);
    expect(n.tokens(p.liveSession)).toBe(0);
    expect(n.tokens(p.uiState)).toBe(0);

    await n.subscribe('live', 'other');
    expect(shared.currentSession!.sessionId).toBe('other');
  });

  // -------------------------------------------------------------------------------------
  // A failed handler leaves nothing half-done
  // -------------------------------------------------------------------------------------

  it('a subscribed that fails after the controls were enabled undoes them and unsubscribes', async () => {
    await n.connect();
    const sent: Array<{ type: string; sessionId?: string }> = [];
    shared.ws = { readyState: WebSocket.OPEN, send: (raw: string) => { sent.push(JSON.parse(raw)); } } as unknown as WebSocket;
    await n.executor.injectValue(p.userSelectSession, { sessionId: SESSION, mode: 'replay' });
    await settle();

    // Everything up to the timeline succeeds: session data, initial state, controls, autocomplete.
    restore = breakTimeline();
    await n.inject(subscribed(SESSION, 'replay'));
    await settle();
    restore(); restore = null;
    shared.ws = null;

    expect(n.failures()).toEqual([]);
    expect(String(warn.mock.calls[0]![0])).toContain('handler-failed');
    expect(n.tokens(p.noSession)).toBe(1);
    expect(n.tokens(p.replaySession)).toBe(0);
    expect(n.tokens(p.replayPaused)).toBe(0);
    expect(shared.currentSession).toBeNull();
    expect(document.getElementById('btn-pause')!.hasAttribute('disabled')).toBe(true);
    // The server was told, so it stops streaming a session nobody shows.
    expect(sent.map(c => `${c.type}:${c.sessionId}`)).toEqual([`subscribe:${SESSION}`, `unsubscribe:${SESSION}`]);
    expect(n.routerAtRest()).toEqual({});
  });

  it('a replay batch that fails leaves the replay buffer as it was', async () => {
    await n.subscribe('replay');
    await n.inject(eventBatch(30));
    await settle();
    const events = [...shared.replay.allEvents];
    const checkpoints = [...shared.replay.checkpoints];
    expect(checkpoints).toHaveLength(1);

    // Twenty good events, then a corrupt one: a checkpoint is due before the failure.
    const bad = eventBatch(25, 30);
    (bad.events as unknown[])[22] = null;
    await n.inject(bad);
    await settle();

    expect(n.failures()).toEqual([]);
    expect(String(warn.mock.calls[0]![0])).toContain('handler-failed');
    expect(shared.replay.allEvents).toEqual(events);
    expect(shared.replay.checkpoints).toEqual(checkpoints);
    expect(n.uiState().totalEvents).toBe(30);
    expect(n.routerAtRest()).toEqual({});
  });
});

/** Makes `renderBreakpointList` throw until the returned function is called. */
function breakBreakpointList(): () => void {
  const list = document.getElementById('breakpoint-list')!;
  Object.defineProperty(list, 'innerHTML', { configurable: true, get() { return ''; }, set() { throw new Error('list is broken'); } });
  return () => { delete (list as unknown as { innerHTML?: unknown }).innerHTML; };
}
