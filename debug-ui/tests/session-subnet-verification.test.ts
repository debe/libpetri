// @vitest-environment node
/**
 * Formal verification of the session subscribe/switch subnet.
 *
 * Uses SmtVerifier (Z3 WASM) to prove structural properties of a minimal
 * model of the session transitions. This is intentionally a reduced model
 * (not the full debug-ui net) to keep Z3 tractable.
 *
 * Also verifies the inspector dirty fan-out chain.
 */
import { describe, it, expect } from 'vitest';
import {
  PetriNet, Transition,
  place, environmentPlace,
  one, outPlace, and,
} from 'libpetri';
import {
  SmtVerifier,
  mutualExclusion, placeBound, deadlockFree,
  unbounded,
} from 'libpetri/verification';

const Z3_TIMEOUT = 60_000;

/**
 * Build a minimal model of the session subnet:
 *
 *   Places: noSession, subscribing, subscribedSession, connected, uiState, stateDirty
 *   Env: userSelectSession, wsMessage
 *
 *   t_subscribe:           noSession + userSelectSession, reads connected → subscribing
 *   t_on_subscribed:       subscribing + wsMessage → uiState + stateDirty + subscribedSession
 *   t_unsubscribe_switch:  subscribedSession + userSelectSession + uiState, reads connected → subscribing
 */
function buildSessionSubnet() {
  const noSession = place<void>('noSession');
  const subscribing = place<void>('subscribing');
  const subscribedSession = place<void>('subscribedSession');
  const connected = place<void>('connected');
  const uiState = place<void>('uiState');
  const stateDirty = place<void>('stateDirty');

  const userSelectSession = environmentPlace<void>('userSelectSession');
  const wsMessage = environmentPlace<void>('wsMessage');

  const t_subscribe = Transition.builder('t_subscribe')
    .inputs(one(noSession), one(userSelectSession.place))
    .reads(connected)
    .outputs(outPlace(subscribing))
    .build();

  const t_on_subscribed = Transition.builder('t_on_subscribed')
    .inputs(one(subscribing), one(wsMessage.place))
    .outputs(and(outPlace(uiState), outPlace(stateDirty), outPlace(subscribedSession)))
    .build();

  const t_unsubscribe_switch = Transition.builder('t_unsubscribe_switch')
    .inputs(one(subscribedSession), one(userSelectSession.place), one(uiState))
    .reads(connected)
    .outputs(outPlace(subscribing))
    .build();

  const net = PetriNet.builder('SessionSubnet')
    .transitions(t_subscribe, t_on_subscribed, t_unsubscribe_switch)
    .build();

  return {
    net,
    noSession, subscribing, subscribedSession, connected, uiState, stateDirty,
    userSelectSession, wsMessage,
  };
}

/**
 * Build a minimal model of the inspector dirty fan-out chain:
 *
 *   Places: stateDirty, highlightDirty, logDirty, markingDirty
 *   Env: rafTick
 *
 *   t_fan_out:      stateDirty → highlightDirty + logDirty + markingDirty
 *   t_update_mark:  markingDirty + rafTick → (consumed)
 *   t_update_high:  highlightDirty + rafTick → (consumed)
 *   t_update_log:   logDirty + rafTick → (consumed)
 */
function buildInspectorDirtyChain() {
  const stateDirty = place<void>('stateDirty');
  const highlightDirty = place<void>('highlightDirty');
  const logDirty = place<void>('logDirty');
  const markingDirty = place<void>('markingDirty');

  const rafTick = environmentPlace<void>('rafTick');

  const t_fan_out = Transition.builder('t_fan_out')
    .inputs(one(stateDirty))
    .outputs(and(outPlace(highlightDirty), outPlace(logDirty), outPlace(markingDirty)))
    .build();

  const t_update_mark = Transition.builder('t_update_mark')
    .inputs(one(markingDirty), one(rafTick.place))
    .build();

  const t_update_high = Transition.builder('t_update_high')
    .inputs(one(highlightDirty), one(rafTick.place))
    .build();

  const t_update_log = Transition.builder('t_update_log')
    .inputs(one(logDirty), one(rafTick.place))
    .build();

  const net = PetriNet.builder('InspectorDirtyChain')
    .transitions(t_fan_out, t_update_mark, t_update_high, t_update_log)
    .build();

  return {
    net,
    stateDirty, highlightDirty, logDirty, markingDirty,
    rafTick,
  };
}

describe('session subnet formal verification', () => {
  it('mutual exclusion: noSession and subscribedSession', async () => {
    const { net, noSession, subscribedSession, connected, userSelectSession, wsMessage } = buildSessionSubnet();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(noSession, 1).tokens(connected, 1))
      .environmentPlaces(userSelectSession, wsMessage)
      .environmentMode(unbounded())
      .property(mutualExclusion(noSession, subscribedSession))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
  }, Z3_TIMEOUT);

  it('place bound: subscribedSession <= 1', async () => {
    const { net, noSession, subscribedSession, connected, userSelectSession, wsMessage } = buildSessionSubnet();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(noSession, 1).tokens(connected, 1))
      .environmentPlaces(userSelectSession, wsMessage)
      .environmentMode(unbounded())
      .property(placeBound(subscribedSession, 1))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
  }, Z3_TIMEOUT);

  it('place bound: uiState <= 1', async () => {
    const { net, noSession, uiState, connected, userSelectSession, wsMessage } = buildSessionSubnet();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(noSession, 1).tokens(connected, 1))
      .environmentPlaces(userSelectSession, wsMessage)
      .environmentMode(unbounded())
      .property(placeBound(uiState, 1))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
  }, Z3_TIMEOUT);

  it('deadlock-freedom with noSession as sink', async () => {
    const { net, noSession, connected, userSelectSession, wsMessage } = buildSessionSubnet();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(noSession, 1).tokens(connected, 1))
      .environmentPlaces(userSelectSession, wsMessage)
      .environmentMode(unbounded())
      .sinkPlaces(noSession)
      .property(deadlockFree())
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
  }, Z3_TIMEOUT);
});

describe('inspector dirty chain formal verification', () => {
  it('place bound: markingDirty <= 1', async () => {
    const { net, stateDirty, markingDirty, rafTick } = buildInspectorDirtyChain();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(stateDirty, 1))
      .environmentPlaces(rafTick)
      .environmentMode(unbounded())
      .property(placeBound(markingDirty, 1))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
  }, Z3_TIMEOUT);

  it('deadlock-freedom with all dirty consumed as sinks', async () => {
    const { net, stateDirty, highlightDirty, logDirty, markingDirty, rafTick } = buildInspectorDirtyChain();

    // When no stateDirty is present, the net is idle — these are valid sinks
    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(stateDirty, 1))
      .environmentPlaces(rafTick)
      .environmentMode(unbounded())
      .sinkPlaces(highlightDirty, logDirty, markingDirty)
      .property(deadlockFree())
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
  }, Z3_TIMEOUT);
});
