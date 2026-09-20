/**
 * The session and its mode are tokens the net emits and takes back — not injections its own
 * actions make behind the topology's back.
 *
 * `t_on_subscribed` used to inject `liveSession` / `replaySession` / `replayPaused` through the
 * executor, and nothing ever removed them: a second replay session added a second mode token,
 * and a session left in replay kept its `replaySession` and `replayPaused` beside the next
 * one's `liveSession`, so a play click meant for the live session enabled `t_replay_play` too. They are declared
 * outputs now, and the four `t_switch_from_*` transitions consume exactly what the session
 * being left holds. The same goes for the playback loop (`t_replay_auto_step` decides by XOR
 * leg instead of injecting clicks), the deep link and the archive import.
 *
 * The exclusions themselves are proven on the full net in `replay-subnet-verification.test.ts`
 * and `session-subnet-verification.test.ts`; this file runs them.
 */
import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import type { Place } from 'libpetri';
import * as p from '../src/net/places.js';
import { shared } from '../src/net/shared-state.js';
import { startNet, settle, eventBatch, subscribed, SESSION, type RunningNet } from './net-harness.js';

vi.mock('../src/net/actions/connection.js', async (importOriginal) => {
  const original = await importOriginal<typeof import('../src/net/actions/connection.js')>();
  return { ...original, createWebSocket: vi.fn() };
});

vi.mock('../src/net/actions/diagram.js', async (importOriginal) => {
  const original = await importOriginal<typeof import('../src/net/actions/diagram.js')>();
  return { ...original, renderDotDiagram: vi.fn().mockResolvedValue(undefined), updateDiagramHighlighting: vi.fn() };
});

const MODE_PLACES: Array<Place<unknown>> = [
  p.noSession, p.subscribing, p.subscribedSession, p.liveSession, p.replaySession,
  p.replayPaused, p.replayPlaying, p.breakpointPaused, p.uiState,
];

describe('session and replay modes', () => {
  let n: RunningNet;

  beforeEach(() => {
    vi.spyOn(console, 'error').mockImplementation(() => {});
    vi.spyOn(console, 'warn').mockImplementation(() => {});
    vi.spyOn(console, 'debug').mockImplementation(() => {});
    n = startNet();
  });

  afterEach(() => {
    n.close();
    vi.restoreAllMocks();
  });

  /** The marked mode places, by name. */
  function modes(): string[] {
    return MODE_PLACES.flatMap(place => Array.from({ length: n.tokens(place) }, () => place.name));
  }

  it('a live session holds exactly subscribedSession, liveSession and uiState', async () => {
    await n.subscribe('live');
    expect(modes()).toEqual(['subscribedSession', 'liveSession', 'uiState']);
  });

  it('a replay session starts paused', async () => {
    await n.subscribe('replay');
    expect(modes()).toEqual(['subscribedSession', 'replaySession', 'replayPaused', 'uiState']);
  });

  it.each([
    ['live', 't_switch_from_live', async () => {}],
    ['replay, paused', 't_switch_from_replay_paused', async () => {}],
    ['replay, playing', 't_switch_from_replay_playing', async () => {
      await n.executor.injectValue(p.userClickPlay, undefined);
      await settle(60);
    }],
    ['replay, stopped at a breakpoint', 't_switch_from_breakpoint', async () => {
      await n.executor.injectValue(p.userSetBreakpoint, { id: 'bp', type: 'TOKEN_ADDED', target: null, enabled: true });
      await n.executor.injectValue(p.userClickPlay, undefined);
      await settle(60);
      expect(n.tokens(p.breakpointPaused)).toBe(1);
    }],
  ] as Array<[string, string, () => Promise<void>]>)('leaving a session (%s) takes its mode with it', async (label, transition, arrange) => {
    await n.subscribe(label === 'live' ? 'live' : 'replay');
    await n.inject(eventBatch(200));
    await settle();
    await arrange();

    const from = n.mark();
    await n.executor.injectValue(p.userSelectSession, { sessionId: 'next', mode: 'replay' });
    await settle();
    expect(n.fired(from)).toContain(transition);
    expect(modes()).toEqual(['subscribing']);

    await n.inject(subscribed('next', 'replay'));
    await settle(120);
    expect(modes()).toEqual(['subscribedSession', 'replaySession', 'replayPaused', 'uiState']);
    expect(n.failures()).toEqual([]);

    // Nothing of the session left behind is still playing.
    expect(n.uiState().eventIndex).toBe(0);
    expect(n.tokens(p.autoStepTick.place)).toBe(0);
  });

  it('after replay → live, a play click reaches the live session, not the replay that was left', async () => {
    await n.subscribe('replay');
    await n.executor.injectValue(p.userSelectSession, { sessionId: 'live-one', mode: 'live' });
    await settle();
    await n.inject(subscribed('live-one', 'live'));
    await settle();
    expect(modes()).toEqual(['subscribedSession', 'liveSession', 'uiState']);

    // With the old session's replaySession and replayPaused still marked, t_replay_play was
    // enabled too, and took the click.
    const from = n.mark();
    await n.executor.injectValue(p.userClickPlay, undefined);
    await n.executor.injectValue(p.userClickPause, undefined);
    await settle();
    expect(n.fired(from)).toEqual(['t_live_resume', 't_live_pause']);
  });

  // -------------------------------------------------------------------------------------
  // The playback loop
  // -------------------------------------------------------------------------------------

  describe('playback', () => {
    it('plays to the end and comes to rest paused, by an output of the step itself', async () => {
      await n.subscribe('replay');
      await n.inject(eventBatch(5));
      await settle();

      const from = n.mark();
      await n.executor.injectValue(p.userClickPlay, undefined);
      await settle(500);

      expect(n.uiState().eventIndex).toBe(5);
      expect(modes()).toEqual(['subscribedSession', 'replaySession', 'replayPaused', 'uiState']);
      // Five steps and the one that found the end. No click was injected to get there.
      expect(n.fired(from).filter(name => /^t_(replay|live|drop_stale)/.test(name)))
        .toEqual(['t_replay_play', ...Array.from({ length: 6 }, () => 't_replay_auto_step')]);
      expect(n.tokens(p.userClickPause.place)).toBe(0);
      expect(n.tokens(p.userClickStepFwd.place)).toBe(0);
    });

    it('a tick that arrives while paused is dropped, so the next play runs at the single rate', async () => {
      await n.subscribe('replay');
      await n.inject(eventBatch(400));
      await settle();

      const from = n.mark();
      await n.executor.injectValue(p.autoStepTick, undefined);
      await n.executor.injectValue(p.autoStepTick, undefined);
      await settle();
      expect(n.fired(from)).toEqual(['t_drop_stale_tick', 't_drop_stale_tick']);
      expect(n.tokens(p.autoStepTick.place)).toBe(0);
      expect(n.uiState().eventIndex).toBe(0);
    });

    it('a second tick while playing does not start a second loop', async () => {
      await n.subscribe('replay');
      await n.inject(eventBatch(400));
      await settle();
      shared.playback.speed = 0.5; // 100 ms a step

      await n.executor.injectValue(p.userClickPlay, undefined);
      await settle(30);
      await n.executor.injectValue(p.autoStepTick, undefined); // the stray tick
      await settle(520);
      await n.executor.injectValue(p.userClickPause, undefined);
      await settle();

      // One loop makes about 6 steps in 550 ms, plus the stray one. Two loops would make about 12.
      expect(n.uiState().eventIndex).toBeGreaterThanOrEqual(4);
      expect(n.uiState().eventIndex).toBeLessThanOrEqual(9);
    });

    it('pause, then play again: still one loop', async () => {
      await n.subscribe('replay');
      await n.inject(eventBatch(400));
      await settle();
      shared.playback.speed = 0.5;

      await n.executor.injectValue(p.userClickPlay, undefined);
      await settle(130);
      await n.executor.injectValue(p.userClickPause, undefined);
      await n.executor.injectValue(p.userClickPlay, undefined);
      await settle(20);
      const resumedAt = n.uiState().eventIndex;
      await settle(520);
      await n.executor.injectValue(p.userClickPause, undefined);
      await settle();

      const steps = n.uiState().eventIndex - resumedAt;
      expect(steps).toBeGreaterThanOrEqual(3);
      expect(steps).toBeLessThanOrEqual(8);
    });
  });

  // -------------------------------------------------------------------------------------
  // Losing the connection
  // -------------------------------------------------------------------------------------

  describe('the connection closes', () => {
    it('while a subscribe is outstanding: back to noSession, and the selection after the reconnect fires', async () => {
      await n.connect();
      await n.executor.injectValue(p.userSelectSession, { sessionId: SESSION, mode: 'live' });
      await settle();
      expect(modes()).toEqual(['subscribing']);

      const from = n.mark();
      await n.executor.injectValue(p.wsCloseSignal, undefined);
      await settle();
      expect(n.fired(from)).toEqual(['t_on_close_connected', 't_abandon_subscribe']);
      expect(modes()).toEqual(['noSession']);

      // Selected while disconnected: waits for the connection, then subscribes.
      await n.executor.injectValue(p.userSelectSession, { sessionId: SESSION, mode: 'live' });
      await settle();
      expect(modes()).toEqual(['noSession']);

      await settle(2100); // t_reconnect
      await n.executor.injectValue(p.wsOpenSignal, undefined);
      await settle();
      expect(modes()).toEqual(['subscribing']);
      await n.inject(subscribed());
      await settle();
      expect(modes()).toEqual(['subscribedSession', 'liveSession', 'uiState']);
    }, 10_000);

    it('while subscribed: the session stays on screen', async () => {
      await n.subscribe('live');
      await n.inject(eventBatch(4));
      await settle();
      const before = n.uiState();

      await n.executor.injectValue(p.wsCloseSignal, undefined);
      await settle();

      // The net under debug has usually just exited; its last state is what the user came for.
      expect(modes()).toEqual(['subscribedSession', 'liveSession', 'uiState']);
      expect(n.uiState()).toBe(before);
    });
  });

  // -------------------------------------------------------------------------------------
  // Selections the net makes itself
  // -------------------------------------------------------------------------------------

  describe('a selection made by the net is an output, not an injection', () => {
    const sessions = [{ sessionId: 'linked', netName: 'TestNet', active: false, startTime: '2024-01-01T00:00:00Z', eventCount: 3 }];

    it('the deep link selects its session when the first list names it', async () => {
      await n.executor.injectValue(p.deepLink, 'linked');
      await n.connect();

      const from = n.mark();
      await n.inject({ type: 'sessionList', sessions });
      await settle();

      expect(n.fired(from)).toEqual(['t_route_message', 't_on_session_list_deep_link', 't_subscribe']);
      expect(n.executor.getMarking().peekTokens(p.subscribing)[0]!.value).toBe('linked');
      expect(n.tokens(p.deepLink.place)).toBe(0);
    });

    it('a deep link the list does not name is spent, and selects nothing', async () => {
      await n.executor.injectValue(p.deepLink, 'gone');
      await n.connect();

      const from = n.mark();
      await n.inject({ type: 'sessionList', sessions });
      await n.inject({ type: 'sessionList', sessions });
      await settle();

      expect(n.fired(from)).toEqual(['t_route_message', 't_on_session_list_deep_link', 't_route_message', 't_on_session_list']);
      expect(modes()).toEqual(['noSession']);
      expect(n.tokens(p.userSelectSession.place)).toBe(0);
    });

    it('an imported archive is selected for replay', async () => {
      await n.connect();
      const from = n.mark();
      await n.inject({ type: 'archiveImported', sessionId: 'imported', netName: 'TestNet', eventCount: 0 });
      await settle();

      expect(n.fired(from)).toEqual(['t_route_message', 't_on_archive_imported', 't_subscribe']);
      expect(n.executor.getMarking().peekTokens(p.subscribing)[0]!.value).toBe('imported');
    });
  });
});
