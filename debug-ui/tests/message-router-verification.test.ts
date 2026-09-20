// @vitest-environment node
/**
 * Formal verification of the WebSocket message router (definition.ts, "Message router").
 *
 * Every net here is made of the transitions `buildDebugNet()` returns — the full net, or the
 * slice of it with an arc on a router place — so the proofs follow the definition.
 *
 * Two kinds of claim, two routes:
 *
 * - **Safety** (the permit is never duplicated, so at most one message is between `wsMessage`
 *   and its handler): `SmtVerifier` on the full net, every environment place injectable at any
 *   time (`alwaysAvailable()`, VER-006). Each bound is asserted on the router slice first: a
 *   regression there is `violated` in well under a second and names its property, where the
 *   full net tends to answer `unknown` after the whole timeout.
 * - **Nothing strands and the permit always comes back**: `verifyOpenNet` (VER-022). Under
 *   `alwaysAvailable()` no marking is quiescent, so `deadlockFree()` would be proven whatever
 *   the net does (VER-006, "the mirror-image vacuity"). The contract lets the environment run
 *   dry instead: a finite number of frames arrive, and every quiescent marking is judged.
 *
 * All routes are value-blind: the classifier may send any frame down any leg, so "proven"
 * covers every message type in every session state, including the ones no server sends.
 * Each proof has a control that must come back `violated`.
 */
import { describe, it, expect } from 'vitest';
import {
  OpenNetContract, verifyOpenNet,
  mutualExclusion, placeBound, unreachable,
  type MarkingStateBuilder,
} from 'libpetri/verification';
import * as p from '../src/net/places.js';
import { Z3_TIMEOUT, debugNet, seedInitialMarking, sliceTouching, routerPlaces, check } from './verification-support.js';

const routerSlice = (except: string[] = []) => sliceTouching(debugNet(), 'MessageRouter', routerPlaces, except);

type SessionState = 'noSession' | 'subscribing' | 'live' | 'replay';

/** The router's own tokens, plus one of the session states it can meet. */
function routerMarking(state: SessionState): (m: MarkingStateBuilder) => void {
  return (m) => {
    m.tokens(p.routerReady, 1).tokens(p.breakpoints, 1);
    if (state === 'noSession') m.tokens(p.noSession, 1);
    if (state === 'subscribing') m.tokens(p.subscribing, 1);
    if (state === 'live') m.tokens(p.subscribedSession, 1).tokens(p.uiState, 1).tokens(p.liveSession, 1);
    if (state === 'replay') m.tokens(p.subscribedSession, 1).tokens(p.uiState, 1).tokens(p.replaySession, 1).tokens(p.replayPaused, 1);
  };
}

/**
 * Up to three frames arrive, in any order, of any type, with or without a deep link waiting.
 * At rest: the permit is back, the resource tokens are where they were, the session is in
 * exactly one phase and a subscribed one in exactly one mode — and nothing is left on
 * `wsMessage`, a `msg*` place or `deadLetter`, which the contract does not let rest. A
 * selection the router made itself (deep link, imported archive) may wait for its taker,
 * which is outside this slice.
 */
function routerContract(state: SessionState) {
  return OpenNetContract.builder()
    .initialMarking(routerMarking(state))
    .arriveBetween(0, 3, p.wsMessage.place)
    .arriveBetween(0, 1, p.deepLink.place)
    .expect('permit', 1, p.routerReady)
    .expect('breakpoints', 1, p.breakpoints)
    .expect('session phase', 1, p.noSession, p.subscribing, p.subscribedSession)
    .expect('uiState exactly while subscribed', 1, p.noSession, p.subscribing, p.uiState)
    .expect('one mode exactly while subscribed', 1, p.noSession, p.subscribing, p.liveSession, p.replaySession)
    .expect('a replay session is paused', 1, p.noSession, p.subscribing, p.liveSession, p.replayPaused)
    .rest(p.stateDirty, p.dotSource, p.userSelectSession.place, p.deepLink.place)
    .build();
}

const STATES: SessionState[] = ['noSession', 'subscribing', 'live', 'replay'];

describe('message router: the slice is the real one', () => {
  it('is every transition with an arc on a router place', () => {
    const names = [...routerSlice().transitions].map(t => t.name).sort();
    expect(names).toEqual([
      't_drop_event', 't_drop_event_batch', 't_drop_marking_snapshot', 't_drop_subscribed',
      't_log_dead_letter',
      't_on_archive_imported', 't_on_archive_list', 't_on_bp_cleared', 't_on_bp_list', 't_on_bp_set',
      't_on_breakpoint_hit', 't_on_error', 't_on_event', 't_on_event_batch', 't_on_filter_applied',
      't_on_marking_snapshot', 't_on_playback_state', 't_on_replay_event_batch', 't_on_session_list',
      't_on_session_list_deep_link', 't_on_subscribed', 't_on_unsubscribed',
      't_route_message',
    ]);
  });

  it('only the classifier consumes wsMessage', () => {
    const consumers = [...debugNet().transitions]
      .filter(t => [...t.inputPlaces()].some(place => place.name === p.wsMessage.place.name))
      .map(t => t.name);
    expect(consumers).toEqual(['t_route_message']);
  });

  it('every route has the classifier as its only producer', () => {
    for (const route of Object.values(p.messageRoutes)) {
      const producers = [...debugNet().transitions]
        .filter(t => [...t.outputPlaces()].some(place => place.name === route.name))
        .map(t => t.name);
      expect(producers, route.name).toEqual(['t_route_message']);
    }
  });
});

describe('message router: each drop is the exact complement of its handler', () => {
  // The verifier cannot tell these apart from an inhibitor on uiState: firing is atomic to it,
  // and uiState is absent exactly while no session is subscribed. At runtime it is not — a seek
  // or a replay step holds uiState while its action runs, and a message that arrives then must
  // wait for its handler, not be dropped. So the choice of place is pinned here, on the arcs,
  // and run against a slow holder of uiState in message-routing.test.ts.
  it.each([
    ['t_on_subscribed', 't_drop_subscribed', 'msgSubscribed', 'subscribing'],
    ['t_on_event', 't_drop_event', 'msgEvent', 'subscribedSession'],
    ['t_on_event_batch', 't_drop_event_batch', 'msgEventBatch', 'subscribedSession'],
    ['t_on_replay_event_batch', 't_drop_event_batch', 'msgEventBatch', 'subscribedSession'],
    ['t_on_marking_snapshot', 't_drop_marking_snapshot', 'msgMarkingSnapshot', 'subscribedSession'],
  ])('%s requires what %s is inhibited by', (handlerName, dropName, message, phase) => {
    const byName = new Map([...debugNet().transitions].map(t => [t.name, t]));
    const handler = byName.get(handlerName)!;
    const drop = byName.get(dropName)!;

    expect([...drop.inputPlaces()].map(place => place.name)).toEqual([message]);
    expect(drop.inhibitors.map(arc => arc.place.name)).toEqual([phase]);
    expect([...drop.outputPlaces()].map(place => place.name)).toEqual(['deadLetter']);
    expect([...handler.inputPlaces()].map(place => place.name)).toContain(message);
    expect([...handler.inputPlaces(), ...handler.readPlaces()].map(place => place.name)).toContain(phase);
    expect(handler.inhibitors).toEqual([]);
  });

  it('the two batch handlers split on the session mode, which the net proves is exactly one', async () => {
    const byName = new Map([...debugNet().transitions].map(t => [t.name, t]));
    expect([...byName.get('t_on_event_batch')!.readPlaces()].map(place => place.name).sort()).toEqual(['liveSession', 'subscribedSession']);
    expect([...byName.get('t_on_replay_event_batch')!.readPlaces()].map(place => place.name).sort()).toEqual(['replaySession', 'subscribedSession']);
    expect(await check(debugNet(), seedInitialMarking, mutualExclusion(p.liveSession, p.replaySession))).toBe('proven');
  }, Z3_TIMEOUT);

  it('the session list is taken with the deep link or inhibited by it', () => {
    const byName = new Map([...debugNet().transitions].map(t => [t.name, t]));
    expect(byName.get('t_on_session_list')!.inhibitors.map(arc => arc.place.name)).toEqual(['deepLink']);
    expect([...byName.get('t_on_session_list_deep_link')!.inputPlaces()].map(place => place.name).sort()).toEqual(['deepLink', 'msgSessionList']);
  });

  it('no router transition leans on priority', () => {
    for (const t of routerSlice().transitions) expect(t.priority, t.name).toBe(0);
  });
});

describe('message router: safety on the full net', () => {
  it('place bound: every router place <= 1', async () => {
    for (const place of routerPlaces) {
      for (const state of STATES) {
        expect(await check(routerSlice(), routerMarking(state), placeBound(place, 1)), `slice, ${state}: ${place.name}`).toBe('proven');
      }
      expect(await check(debugNet(), seedInitialMarking, placeBound(place, 1)), `full net: ${place.name}`).toBe('proven');
    }
  }, Z3_TIMEOUT);

  it('mutual exclusion: any two router places (one message in the router at a time)', async () => {
    // The slice goes first, and all of it before the full net: were the permit duplicated, the
    // offending pair is named here in milliseconds instead of timing the loop below out.
    const pairs = routerPlaces.flatMap((a, i) => routerPlaces.slice(i + 1).map(b => [a, b] as const));
    for (const [a, b] of pairs) {
      expect(await check(routerSlice(), routerMarking('replay'), mutualExclusion(a, b)), `slice: ${a.name} / ${b.name}`).toBe('proven');
    }
    for (const [a, b] of pairs) {
      expect(await check(debugNet(), seedInitialMarking, mutualExclusion(a, b)), `full net: ${a.name} / ${b.name}`).toBe('proven');
    }
  }, 2 * Z3_TIMEOUT);

  it('control: a routed message is reachable on the full net, so the bounds are not vacuous', async () => {
    expect(await check(debugNet(), seedInitialMarking, unreachable(new Set([p.msgEvent])))).toBe('violated');
  }, Z3_TIMEOUT);

  it('control: every leg of the classifier is reachable', async () => {
    const net = routerSlice();
    for (const place of routerPlaces.filter(place => place !== p.routerReady)) {
      expect(await check(net, routerMarking('live'), unreachable(new Set([place]))), place.name).toBe('violated');
    }
  }, Z3_TIMEOUT);

  it('control: without the permit two messages are in the router at once', async () => {
    // Seeding a second permit is the smallest way to take the serialisation away.
    const twoPermits = (m: MarkingStateBuilder) => { routerMarking('live')(m); m.tokens(p.routerReady, 2); };
    expect(await check(routerSlice(), twoPermits, mutualExclusion(p.msgEvent, p.msgMarkingSnapshot))).toBe('violated');
    expect(await check(routerSlice(), routerMarking('live'), mutualExclusion(p.msgEvent, p.msgMarkingSnapshot))).toBe('proven');
  }, Z3_TIMEOUT);
});

describe('message router: nothing strands, in any session state (open-net contract)', () => {
  it.each(STATES)('%s: every frame is handled or dead-lettered, and the permit comes back', async (state) => {
    const result = await verifyOpenNet(routerSlice(), routerContract(state));

    expect(result.violations.map(v => `${v.kind}:${v.subject}`)).toEqual([]);
    expect(result.verdict.type).toBe('proven');
    // Exact: the state-class graph closed, so every quiescent marking was judged.
    expect(result.route).toBe('enumeration');
    expect(result.graphComplete).toBe(true);
  }, Z3_TIMEOUT);

  it.each([
    ['t_drop_event', 'msgEvent'],
    ['t_drop_event_batch', 'msgEventBatch'],
    ['t_drop_marking_snapshot', 'msgMarkingSnapshot'],
  ])('control: without %s a message for no session blocks the queue behind it', async (dropped, stuck) => {
    const result = await verifyOpenNet(routerSlice([dropped]), routerContract('noSession'));

    expect(result.verdict.type).toBe('violated');
    expect(result.violations.map(v => `${v.kind}:${v.subject}`)).toEqual([
      'clause:permit', `stranded:${stuck}`, 'stranded:wsMessage',
    ]);
    // …and only there: with a session the handler is enabled and the drop is never needed.
    expect((await verifyOpenNet(routerSlice([dropped]), routerContract('live'))).verdict.type).toBe('proven');
  }, Z3_TIMEOUT);

  it('control: without t_drop_subscribed an unsolicited subscribed blocks the queue', async () => {
    const result = await verifyOpenNet(routerSlice(['t_drop_subscribed']), routerContract('live'));

    expect(result.verdict.type).toBe('violated');
    expect(result.violations.map(v => `${v.kind}:${v.subject}`)).toEqual([
      'clause:permit', 'stranded:msgSubscribed', 'stranded:wsMessage',
    ]);
  }, Z3_TIMEOUT);

  it('control: without t_log_dead_letter the permit is lost with the first dead letter', async () => {
    for (const state of STATES) {
      const result = await verifyOpenNet(routerSlice(['t_log_dead_letter']), routerContract(state));
      expect(result.verdict.type, state).toBe('violated');
      expect(result.violations.map(v => `${v.kind}:${v.subject}`), state).toContain('stranded:deadLetter');
    }
  }, Z3_TIMEOUT);
});
