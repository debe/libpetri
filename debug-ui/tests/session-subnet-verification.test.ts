// @vitest-environment node
/**
 * Formal verification of the session subnet (subscribe, switch, abandon) and of the repaint
 * subnet.
 *
 * Both are proven on the transitions `buildDebugNet()` returns, not on a hand-copied model:
 * the safety properties on the **full net**, the contracts on the slice with an arc on the
 * places in question. `t_on_subscribed` takes its message from the router, so the session
 * slice includes the router; it includes the connection's open and close too, because a
 * subscribe that is outstanding when the connection closes has to be abandoned.
 *
 * Environment places are injectable at any time (`alwaysAvailable()`, VER-006) in the safety
 * queries. Each is asserted on the slice before the full net: a regression on the slice is
 * `violated` in milliseconds, where the full net tends to say `unknown` after the whole
 * timeout. The claims that used to be `deadlockFree()` are open-net contracts (VER-022): with
 * an always-available environment no marking is quiescent and deadlock-freedom is proven
 * whatever the net does, so the environment is made to run dry instead.
 */
import { describe, it, expect } from 'vitest';
import type { PetriNet, Place } from 'libpetri';
import {
  OpenNetContract, verifyOpenNet,
  mutualExclusion, placeBound, unreachable,
  type MarkingStateBuilder, type SmtProperty,
} from 'libpetri/verification';
import * as p from '../src/net/places.js';
import { Z3_TIMEOUT, debugNet, seedInitialMarking, sliceNamed, sliceTouching, routerPlaces, check } from './verification-support.js';

/**
 * t_subscribe, the four t_switch_from_*, t_abandon_subscribe, the connection's open and close,
 * and the router with t_on_subscribed / t_drop_subscribed, the session-state handlers and
 * their drops.
 */
function sessionSlice(except: string[] = []): PetriNet {
  return sliceTouching(debugNet(), 'SessionSubnet',
    [...routerPlaces, p.noSession, p.subscribing, p.subscribedSession, p.connected], except);
}

const sessionMarking = (m: MarkingStateBuilder) =>
  m.tokens(p.noSession, 1).tokens(p.connected, 1).tokens(p.routerReady, 1).tokens(p.breakpoints, 1);

/** Proven on the session slice, then on the full net. */
async function expectProven(property: SmtProperty, label: string): Promise<void> {
  expect(await check(sessionSlice(), sessionMarking, property), `slice: ${label}`).toBe('proven');
  expect(await check(debugNet(), seedInitialMarking, property), `full net: ${label}`).toBe('proven');
}

/**
 * The user selects a session up to twice while up to three frames arrive and the connection
 * may close, interleaved anyhow. At rest the session is in exactly one phase, a subscribed
 * session has its state and exactly one mode, no frame is left in the router — and no
 * subscribe is left outstanding on a connection that is gone. A selection may wait on
 * `userSelectSession` (it is taken once the outstanding subscribe is answered, or once the
 * connection is back); nothing else may.
 */
function sessionContract() {
  return OpenNetContract.builder()
    .initialMarking(sessionMarking)
    .arriveBetween(0, 2, p.userSelectSession.place)
    .arriveBetween(0, 3, p.wsMessage.place)
    .arriveBetween(0, 1, p.wsCloseSignal.place)
    .expect('session phase', 1, p.noSession, p.subscribing, p.subscribedSession)
    .expect('uiState exactly while subscribed', 1, p.noSession, p.subscribing, p.uiState)
    .expect('one mode exactly while subscribed', 1, p.noSession, p.subscribing, p.liveSession, p.replaySession)
    .expect('a replay session is paused', 1, p.noSession, p.subscribing, p.liveSession, p.replayPaused)
    .expect('connection', 1, p.connected, p.waitReconnect)
    .expectBetween('no subscribe outstanding without a connection', 0, 1, p.subscribing, p.waitReconnect)
    .expect('permit', 1, p.routerReady)
    .expect('breakpoints', 1, p.breakpoints)
    .rest(p.userSelectSession.place, p.stateDirty, p.dotSource)
    .build();
}

const SWITCHES = ['t_switch_from_live', 't_switch_from_replay_paused', 't_switch_from_replay_playing', 't_switch_from_breakpoint'];

describe('session subnet formal verification', () => {
  it('the slice is the subscribe, switch and abandon transitions, the connection and the router', () => {
    const names = [...sessionSlice().transitions].map(t => t.name);
    for (const name of ['t_subscribe', ...SWITCHES, 't_abandon_subscribe', 't_on_close_connected', 't_on_subscribed', 't_route_message']) {
      expect(names).toContain(name);
    }
    const others = names.filter(n => !/^t_(subscribe|switch_from_|abandon_subscribe|route_message|log_dead_letter|on_|drop_)/.test(n));
    // Reads of `connected` that have nothing to do with the session; harmless here.
    expect(others.sort()).toEqual(['t_import_archive', 't_open_archive_browser', 't_upload_archive']);
  });

  it('leaving a session takes exactly what that session holds', () => {
    const byName = new Map([...debugNet().transitions].map(t => [t.name, t]));
    const held = (name: string) => [...byName.get(name)!.inputPlaces()].map(place => place.name)
      .filter(n => !['subscribedSession', 'userSelectSession', 'uiState'].includes(n)).sort();
    expect(held('t_switch_from_live')).toEqual(['liveSession']);
    expect(held('t_switch_from_replay_paused')).toEqual(['replayPaused', 'replaySession']);
    expect(held('t_switch_from_replay_playing')).toEqual(['replayPlaying', 'replaySession']);
    expect(held('t_switch_from_breakpoint')).toEqual(['breakpointPaused', 'replaySession']);
    for (const name of SWITCHES) {
      const t = byName.get(name)!;
      expect([...t.inputPlaces()].map(place => place.name)).toEqual(expect.arrayContaining(['subscribedSession', 'userSelectSession', 'uiState']));
      expect(t.resets, name).toEqual([]);
    }
    // No other transition takes a session token away.
    const takers = [...debugNet().transitions]
      .filter(t => [...t.inputPlaces()].some(place => place.name === 'subscribedSession')).map(t => t.name).sort();
    expect(takers).toEqual([...SWITCHES].sort());
  });

  it('mutual exclusion: the three session phases', async () => {
    await expectProven(mutualExclusion(p.noSession, p.subscribedSession), 'noSession / subscribedSession');
    await expectProven(mutualExclusion(p.subscribing, p.noSession), 'subscribing / noSession');
    await expectProven(mutualExclusion(p.subscribing, p.subscribedSession), 'subscribing / subscribedSession');
  }, Z3_TIMEOUT);

  it('place bound: every session place <= 1', async () => {
    for (const place of [p.noSession, p.subscribing, p.subscribedSession, p.uiState, p.liveSession, p.replaySession] as Place<unknown>[]) {
      await expectProven(placeBound(place, 1), place.name);
    }
  }, Z3_TIMEOUT);

  it('mutual exclusion: no state and no mode without a subscribed session', async () => {
    for (const held of [p.uiState, p.liveSession, p.replaySession] as Place<unknown>[]) {
      await expectProven(mutualExclusion(held, p.noSession), `${held.name} / noSession`);
      await expectProven(mutualExclusion(held, p.subscribing), `${held.name} / subscribing`);
    }
  }, Z3_TIMEOUT);

  it('mutual exclusion: a session is live or replay, never both', async () => {
    // Violated before the modes became outputs: t_on_subscribed injected them and nothing took
    // them back, so the second session's mode joined the first's.
    await expectProven(mutualExclusion(p.liveSession, p.replaySession), 'liveSession / replaySession');
  }, Z3_TIMEOUT);

  it('control: on the full net a subscribe goes out and is answered', async () => {
    // Were injection not modelled, every bound above would hold on a net frozen at its seed.
    // The witness is seven firings deep (connect, open, select, route, subscribed), which is
    // what makes this the slowest query of the file: about half a minute.
    const full = debugNet();
    expect(await check(full, seedInitialMarking, unreachable(new Set([p.subscribing])))).toBe('violated');
    expect(await check(full, seedInitialMarking, unreachable(new Set([p.subscribedSession])))).toBe('violated');
  }, Z3_TIMEOUT);

  it('control: on the slice both modes are reachable, each with its state', async () => {
    expect(await check(sessionSlice(), sessionMarking, mutualExclusion(p.liveSession, p.uiState))).toBe('violated');
    expect(await check(sessionSlice(), sessionMarking, mutualExclusion(p.replaySession, p.uiState))).toBe('violated');
    expect(await check(sessionSlice(), sessionMarking, mutualExclusion(p.replaySession, p.replayPaused))).toBe('violated');
    expect(await check(sessionSlice(), sessionMarking, placeBound(p.subscribedSession, 0))).toBe('violated');
  }, Z3_TIMEOUT);

  it('control: a session left without its mode token breaks the exclusion', async () => {
    // t_switch_from_live, were it to leave liveSession behind — modelled by seeding the stray.
    const stray = (m: MarkingStateBuilder) => { sessionMarking(m); m.tokens(p.liveSession, 1); };
    expect(await check(sessionSlice(), stray, mutualExclusion(p.liveSession, p.replaySession))).toBe('violated');
  }, Z3_TIMEOUT);

  it('comes to rest in exactly one phase and mode with no frame stranded (was: deadlock-freedom)', async () => {
    const result = await verifyOpenNet(sessionSlice(), sessionContract());

    expect(result.violations.map(v => `${v.kind}:${v.subject}`)).toEqual([]);
    expect(result.verdict.type).toBe('proven');
    expect(result.route).toBe('enumeration');
    expect(result.graphComplete).toBe(true);
  }, Z3_TIMEOUT);

  it('control: without t_drop_subscribed a late subscribed blocks the router', async () => {
    const result = await verifyOpenNet(sessionSlice(['t_drop_subscribed']), sessionContract());

    expect(result.verdict.type).toBe('violated');
    expect(result.violations.map(v => `${v.kind}:${v.subject}`)).toContain('stranded:msgSubscribed');
  }, Z3_TIMEOUT);

  it('control: without t_abandon_subscribe a close leaves the subscribe outstanding for good', async () => {
    const result = await verifyOpenNet(sessionSlice(['t_abandon_subscribe']), sessionContract());

    expect(result.verdict.type).toBe('violated');
    expect(result.violations.map(v => `${v.kind}:${v.subject}`)).toContain('clause:no subscribe outstanding without a connection');
  }, Z3_TIMEOUT);

  /** A subscribed session in one of its four modes, and one selection: it is always taken. */
  function switchContract(...held: Place<unknown>[]) {
    return OpenNetContract.builder()
      .initialMarking((m) => {
        m.tokens(p.subscribedSession, 1).tokens(p.uiState, 1).tokens(p.connected, 1).tokens(p.routerReady, 1).tokens(p.breakpoints, 1);
        for (const place of held) m.tokens(place, 1);
      })
      .arrive(1, p.userSelectSession.place)
      .expect('the old session is left, whole', 1, p.subscribing, p.noSession)
      .expect('permit', 1, p.routerReady)
      .expect('connected', 1, p.connected)
      .expect('breakpoints', 1, p.breakpoints)
      .build();
  }

  it.each([
    ['t_switch_from_live', [p.liveSession]],
    ['t_switch_from_replay_paused', [p.replaySession, p.replayPaused]],
    ['t_switch_from_replay_playing', [p.replaySession, p.replayPlaying]],
    ['t_switch_from_breakpoint', [p.replaySession, p.breakpointPaused]],
  ] as Array<[string, Place<unknown>[]]>)('%s: a selection leaves that session and nothing of it stays', async (name, held) => {
    const result = await verifyOpenNet(sessionSlice(), switchContract(...held));
    expect(result.violations.map(v => `${v.kind}:${v.subject}`)).toEqual([]);
    expect(result.verdict.type).toBe('proven');
    expect(result.graphComplete).toBe(true);

    // Control: it is this transition that does it.
    const without = await verifyOpenNet(sessionSlice([name]), switchContract(...held));
    expect(without.verdict.type).toBe('violated');
    expect(without.violations.map(v => `${v.kind}:${v.subject}`)).toContain('stranded:userSelectSession');
  }, Z3_TIMEOUT);
});

/**
 * The repaint subnet, as the real transitions:
 *
 *   t_fan_out_dirty:        stateDirty → highlightDirty + logDirty + markingDirty
 *   t_frame / t_idle_frame: all rafTick → a frame token per panel, or nothing without uiState
 *   t_update_x:             all xDirty + frameX, reads uiState (and svgReady, filterState)
 *   t_skip_x:               frameX, inhibited by xDirty
 *   t_await_diagram:        frameHighlight, inhibited by svgReady
 */
const REPAINT = [
  't_fan_out_dirty', 't_frame', 't_idle_frame',
  't_update_highlighting', 't_skip_highlighting', 't_await_diagram',
  't_update_event_log', 't_skip_event_log', 't_update_marking', 't_skip_marking',
];

function repaintSlice(except: string[] = []): PetriNet {
  return sliceNamed(debugNet(), 'Repaint', ...REPAINT.filter(n => !except.includes(n)));
}

const FRAME_PLACES = [p.rafTick.place, p.frameHighlight, p.frameLog, p.frameMarking];
const DIRTY_PLACES = [p.stateDirty, p.highlightDirty, p.logDirty, p.markingDirty];

interface RepaintSeed { changes?: number; dirty?: number; session?: boolean; diagram?: boolean }

function repaintMarking({ changes = 0, dirty = 0, session = true, diagram = true }: RepaintSeed) {
  return (m: MarkingStateBuilder) => {
    m.tokens(p.filterState, 1);
    if (session) m.tokens(p.uiState, 1);
    if (diagram) m.tokens(p.svgReady, 1);
    if (changes) m.tokens(p.stateDirty, changes);
    if (dirty) for (const place of [p.highlightDirty, p.logDirty, p.markingDirty]) m.tokens(place, dirty);
  };
}

/**
 * `frames` animation frames arrive. At rest no frame token is left anywhere, whatever was
 * dirty; `mayStayDirty` lists the flags that may wait for a later frame.
 */
function repaintContract(seed: RepaintSeed, frames: [number, number], ...mayStayDirty: Place<unknown>[]) {
  const contract = OpenNetContract.builder()
    .initialMarking(repaintMarking(seed))
    .arriveBetween(frames[0], frames[1], p.rafTick.place)
    .expect('filterState', 1, p.filterState)
    .expect('uiState', seed.session === false ? 0 : 1, p.uiState)
    .expect('svgReady', seed.diagram === false ? 0 : 1, p.svgReady);
  return (mayStayDirty.length ? contract.rest(...mayStayDirty) : contract).build();
}

const violationsOf = (result: Awaited<ReturnType<typeof verifyOpenNet>>) => result.violations.map(v => `${v.kind}:${v.subject}`);

describe('repaint subnet formal verification', () => {
  it('the slice is every transition with an arc on a frame place, and the fan-out', () => {
    const frames = new Set(FRAME_PLACES.map(place => place.name));
    const touching = [...debugNet().transitions]
      .filter(t => [...t.inputPlaces(), ...t.outputPlaces()].some(place => frames.has(place.name)))
      .map(t => t.name);
    expect([...touching, 't_fan_out_dirty'].sort()).toEqual([...REPAINT].sort());
  });

  it('a frame after any number of state changes repaints everything and leaves nothing', async () => {
    // Three flags on every panel, one frame: `all()` takes the lot.
    const result = await verifyOpenNet(repaintSlice(), repaintContract({ dirty: 3 }, [1, 1]));
    expect(violationsOf(result)).toEqual([]);
    expect(result.verdict.type).toBe('proven');
    expect(result.route).toBe('enumeration');
    expect(result.graphComplete).toBe(true);
  }, Z3_TIMEOUT);

  it('frames and state changes in any order: no frame token is ever left', async () => {
    // A change that comes after the last frame stays dirty until the next one; that is the
    // throttle working, and the only thing allowed to rest.
    const result = await verifyOpenNet(repaintSlice(), repaintContract({ changes: 2 }, [0, 3], p.highlightDirty, p.logDirty, p.markingDirty));
    expect(violationsOf(result)).toEqual([]);
    expect(result.verdict.type).toBe('proven');
    expect(result.graphComplete).toBe(true);
  }, Z3_TIMEOUT);

  it.each([
    ['nothing dirty', { }],
    ['no session', { session: false, dirty: 1 }],
    ['the diagram still being drawn', { diagram: false, dirty: 1 }],
  ] as Array<[string, RepaintSeed]>)('frames with %s are consumed, not kept', async (_label, seed) => {
    const mayStay = seed.session === false ? [p.highlightDirty, p.logDirty, p.markingDirty] : seed.diagram === false ? [p.highlightDirty] : [];
    const result = await verifyOpenNet(repaintSlice(), repaintContract(seed, [1, 3], ...mayStay));
    expect(violationsOf(result)).toEqual([]);
    expect(result.verdict.type).toBe('proven');
    expect(result.graphComplete).toBe(true);
  }, Z3_TIMEOUT);

  it.each([
    ['t_skip_marking', { }, 'stranded:frameMarking'],
    ['t_skip_event_log', { }, 'stranded:frameLog'],
    ['t_skip_highlighting', { }, 'stranded:frameHighlight'],
    ['t_await_diagram', { diagram: false, dirty: 1 }, 'stranded:frameHighlight'],
    ['t_idle_frame', { session: false }, 'stranded:rafTick'],
    ['t_update_marking', { dirty: 1 }, 'stranded:markingDirty'],
  ] as Array<[string, RepaintSeed, string]>)('control: without %s something is left', async (removed, seed, left) => {
    const mayStay = seed.diagram === false ? [p.highlightDirty] : [];
    const result = await verifyOpenNet(repaintSlice([removed]), repaintContract(seed, [1, 1], ...mayStay));
    expect(result.verdict.type).toBe('violated');
    expect(violationsOf(result)).toContain(left);
  }, Z3_TIMEOUT);

  it('control: a state change dirties every panel', async () => {
    for (const place of DIRTY_PLACES.slice(1)) {
      expect(await check(repaintSlice(), repaintMarking({ changes: 1 }), unreachable(new Set([place]))), place.name).toBe('violated');
    }
  }, Z3_TIMEOUT);
});
