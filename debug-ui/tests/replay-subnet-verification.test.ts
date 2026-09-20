// @vitest-environment node
/**
 * Formal verification of the replay play/pause/auto-step subnet.
 *
 * The net under test is the `t_replay_*` transitions `buildDebugNet()` returns — not a
 * hand-copied model, which is what this file verified at first and which had drifted from the
 * definition.
 *
 * The mode places are ordinary places now. `t_on_subscribed` emits `replaySession` and
 * `replayPaused` as one XOR leg, `t_replay_auto_step` moves between the modes by its own
 * legs, and a `t_switch_from_*` takes the session's tokens back. They used to be environment
 * places that actions injected into, which made every exclusion here false on the full net
 * (a second replay session added a second `replayPaused`), and provable only on a slice under
 * the assumption of a single session. That assumption is gone: each exclusion is asserted on
 * the slice — where a regression is `violated` in milliseconds, with a trace — and then on the
 * full net, from its real seed, with every environment place injectable at any time
 * (`alwaysAvailable()`, VER-006).
 *
 * The claim that used to be `deadlockFree()` is an open-net contract (VER-022): with an
 * always-available environment no marking is quiescent, so deadlock-freedom would be proven
 * whatever the net does.
 */
import { describe, it, expect } from 'vitest';
import type { PetriNet, Place } from 'libpetri';
import {
  OpenNetContract, verifyOpenNet,
  mutualExclusion, placeBound,
  type MarkingStateBuilder, type SmtProperty,
} from 'libpetri/verification';
import * as p from '../src/net/places.js';
import { Z3_TIMEOUT, debugNet, seedInitialMarking, sliceNamed, check } from './verification-support.js';

const MODE_TRANSITIONS = ['t_replay_play', 't_replay_play_from_bp', 't_replay_auto_step', 't_replay_pause', 't_drop_stale_tick'];
const COMMAND_TRANSITIONS = ['t_replay_step_fwd', 't_replay_step_back', 't_replay_seek', 't_replay_restart', 't_replay_run_to_end'];
const REPLAY_TRANSITIONS = [...MODE_TRANSITIONS, ...COMMAND_TRANSITIONS];
const MODES: Place<unknown>[] = [p.replayPaused, p.replayPlaying, p.breakpointPaused];

function replaySlice(except: string[] = []): PetriNet {
  return sliceNamed(debugNet(), 'ReplaySubnet', ...REPLAY_TRANSITIONS.filter(n => !except.includes(n)));
}

/** One replay session, paused, with its state. */
const replayMarking = (m: MarkingStateBuilder) =>
  m.tokens(p.replayPaused, 1).tokens(p.uiState, 1).tokens(p.replaySession, 1).tokens(p.breakpoints, 1);

/** Proven on the replay slice, then on the full net from its real seed. */
async function expectProven(property: SmtProperty, label: string): Promise<void> {
  expect(await check(replaySlice(), replayMarking, property), `slice: ${label}`).toBe('proven');
  expect(await check(debugNet(), seedInitialMarking, property), `full net: ${label}`).toBe('proven');
}

describe('replay subnet formal verification', () => {
  it('the slice is every transition with an arc on a replay mode place, but for those that start and leave a session', () => {
    const modes = new Set(MODES.map(place => place.name));
    const touching = [...debugNet().transitions]
      .filter(t => [...t.inputPlaces(), ...t.outputPlaces(), ...t.readPlaces(), ...t.inhibitors.map(arc => arc.place)].some(place => modes.has(place.name)))
      .map(t => t.name);
    expect(touching.sort()).toEqual([
      ...MODE_TRANSITIONS,
      't_on_subscribed', 't_switch_from_replay_paused', 't_switch_from_replay_playing', 't_switch_from_breakpoint',
    ].sort());
  });

  it('no mode place is an environment place, and no action can inject one', () => {
    const injectable = new Set([...p.allEnvironmentPlaces].map(env => env.place.name));
    for (const place of [...MODES, p.liveSession, p.replaySession]) expect(injectable.has(place.name), place.name).toBe(false);
  });

  it('mutual exclusion: any two replay modes', async () => {
    await expectProven(mutualExclusion(p.replayPlaying, p.replayPaused), 'replayPlaying / replayPaused');
    await expectProven(mutualExclusion(p.replayPlaying, p.breakpointPaused), 'replayPlaying / breakpointPaused');
    await expectProven(mutualExclusion(p.replayPaused, p.breakpointPaused), 'replayPaused / breakpointPaused');
  }, Z3_TIMEOUT);

  it('place bound: every mode <= 1, and uiState <= 1', async () => {
    for (const place of [...MODES, p.uiState as Place<unknown>]) await expectProven(placeBound(place, 1), place.name);
  }, Z3_TIMEOUT);

  it('mutual exclusion on the full net: no replay mode without a replay session', async () => {
    const full = debugNet();
    for (const mode of MODES) {
      for (const other of [p.liveSession, p.noSession, p.subscribing] as Place<unknown>[]) {
        expect(await check(full, seedInitialMarking, mutualExclusion(mode, other)), `${mode.name} / ${other.name}`).toBe('proven');
      }
    }
  }, Z3_TIMEOUT);

  it('control: playing and breakpoint-paused are both reachable', async () => {
    // Were injection not modelled, no click would ever arrive and every bound above would hold
    // on a net frozen at its initial marking — which is how this file passed before VER-006.
    expect(await check(replaySlice(), replayMarking, placeBound(p.replayPlaying, 0))).toBe('violated');
    expect(await check(replaySlice(), replayMarking, placeBound(p.breakpointPaused, 0))).toBe('violated');
  }, Z3_TIMEOUT);

  it('control: a second mode token breaks the exclusion', async () => {
    // What the injected replayPaused of a second session used to do.
    const second = (m: MarkingStateBuilder) => { replayMarking(m); m.tokens(p.replayPaused, 2); };
    expect(await check(replaySlice(), second, mutualExclusion(p.replayPlaying, p.replayPaused))).toBe('violated');
  }, Z3_TIMEOUT);

  it('the step decides by its output legs, and each leg keeps uiState', () => {
    const step = [...debugNet().transitions].find(t => t.name === 't_replay_auto_step')!;
    expect([...step.inputPlaces()].map(place => place.name).sort()).toEqual(['autoStepTick', 'replayPlaying', 'uiState']);
    expect([...step.readPlaces()].map(place => place.name)).toEqual(['breakpoints']);
    expect([...step.outputPlaces()].map(place => place.name).sort())
      .toEqual(['breakpointPaused', 'replayPaused', 'replayPlaying', 'stateDirty', 'uiState']);
  });

  /**
   * Clicks and ticks arrive in any order and then stop. At rest the replay is in exactly one
   * mode and still has its state; a click the current mode has no use for may wait on its
   * environment place. A tick may not: while playing it is a step, otherwise it is dropped, so
   * none is left to run beside the first tick of the next play. Nor may a step request.
   */
  function replayContract() {
    return OpenNetContract.builder()
      .initialMarking(replayMarking)
      .arriveBetween(0, 2, p.userClickPlay.place)
      .arriveBetween(0, 2, p.userClickPause.place)
      .arriveBetween(0, 2, p.autoStepTick.place)
      .arriveBetween(0, 2, p.userClickStepFwd.place)
      .expect('mode', 1, ...MODES)
      .expect('uiState', 1, p.uiState)
      .expect('replaySession', 1, p.replaySession)
      .expect('breakpoints', 1, p.breakpoints)
      .rest(p.userClickPlay.place, p.userClickPause.place, p.stateDirty)
      .build();
  }

  it('comes to rest in exactly one mode with no tick and no step request stranded (was: deadlock-freedom)', async () => {
    const result = await verifyOpenNet(replaySlice(), replayContract());

    expect(result.violations.map(v => `${v.kind}:${v.subject}`)).toEqual([]);
    expect(result.verdict.type).toBe('proven');
    expect(result.route).toBe('enumeration');
    expect(result.graphComplete).toBe(true);
  }, Z3_TIMEOUT);

  it('control: without t_drop_stale_tick a tick that finds nothing playing rests (was: the stale tick that doubled the rate)', async () => {
    const result = await verifyOpenNet(replaySlice(['t_drop_stale_tick']), replayContract());

    expect(result.verdict.type).toBe('violated');
    expect(result.violations.map(v => `${v.kind}:${v.subject}`)).toEqual(['stranded:autoStepTick']);
  }, Z3_TIMEOUT);

  it('control: without t_replay_step_fwd a step request strands', async () => {
    const result = await verifyOpenNet(replaySlice(['t_replay_step_fwd']), replayContract());

    expect(result.verdict.type).toBe('violated');
    expect(result.violations.map(v => `${v.kind}:${v.subject}`)).toEqual(['stranded:userClickStepFwd']);
  }, Z3_TIMEOUT);
});
