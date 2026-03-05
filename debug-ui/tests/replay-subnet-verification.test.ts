// @vitest-environment node
/**
 * Formal verification of the replay play/pause/auto-step subnet.
 *
 * Uses SmtVerifier (Z3 WASM) to prove structural properties of a minimal
 * model of the replay transitions. This is intentionally a reduced model
 * (not the full debug-ui net) to keep Z3 tractable.
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
 * Build a minimal model of the replay subnet:
 *
 *   Places: replayPaused, replayPlaying, autoStepTick, uiState
 *   Env places: userClickPlay, userClickPause, userClickStepFwd
 *
 *   t_play:      replayPaused + userClickPlay → replayPlaying + autoStepTick
 *   t_pause:     replayPlaying + userClickPause → replayPaused
 *   t_auto_step: autoStepTick, reads replayPlaying → userClickStepFwd
 *   t_step_fwd:  uiState + userClickStepFwd → uiState
 */
function buildReplaySubnet() {
  const replayPaused = place<void>('replayPaused');
  const replayPlaying = place<void>('replayPlaying');
  const autoStepTick = environmentPlace<void>('autoStepTick');
  const uiState = place<void>('uiState');

  const userClickPlay = environmentPlace<void>('userClickPlay');
  const userClickPause = environmentPlace<void>('userClickPause');
  const userClickStepFwd = environmentPlace<void>('userClickStepFwd');

  const t_play = Transition.builder('t_play')
    .inputs(one(replayPaused), one(userClickPlay.place))
    .outputs(and(outPlace(replayPlaying), outPlace(autoStepTick.place)))
    .build();

  const t_pause = Transition.builder('t_pause')
    .inputs(one(replayPlaying), one(userClickPause.place))
    .outputs(outPlace(replayPaused))
    .build();

  const t_auto_step = Transition.builder('t_auto_step')
    .inputs(one(autoStepTick.place))
    .reads(replayPlaying)
    .outputs(outPlace(userClickStepFwd.place))
    .build();

  const t_step_fwd = Transition.builder('t_step_fwd')
    .inputs(one(uiState), one(userClickStepFwd.place))
    .outputs(outPlace(uiState))
    .build();

  const net = PetriNet.builder('ReplaySubnet')
    .transitions(t_play, t_pause, t_auto_step, t_step_fwd)
    .build();

  return {
    net,
    replayPaused, replayPlaying, autoStepTick, uiState,
    userClickPlay, userClickPause, userClickStepFwd,
  };
}

describe('replay subnet formal verification', () => {
  it('mutual exclusion: replayPlaying and replayPaused', async () => {
    const { net, replayPaused, replayPlaying, uiState, autoStepTick, userClickPlay, userClickPause, userClickStepFwd } = buildReplaySubnet();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(replayPaused, 1).tokens(uiState, 1))
      .environmentPlaces(userClickPlay, userClickPause, userClickStepFwd, autoStepTick)
      .environmentMode(unbounded())
      .property(mutualExclusion(replayPlaying, replayPaused))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
  }, Z3_TIMEOUT);

  it('place bound: uiState <= 1', async () => {
    const { net, replayPaused, uiState, autoStepTick, userClickPlay, userClickPause, userClickStepFwd } = buildReplaySubnet();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(replayPaused, 1).tokens(uiState, 1))
      .environmentPlaces(userClickPlay, userClickPause, userClickStepFwd, autoStepTick)
      .environmentMode(unbounded())
      .property(placeBound(uiState, 1))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
  }, Z3_TIMEOUT);

  it('place bound: replayPlaying <= 1', async () => {
    const { net, replayPaused, replayPlaying, uiState, autoStepTick, userClickPlay, userClickPause, userClickStepFwd } = buildReplaySubnet();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(replayPaused, 1).tokens(uiState, 1))
      .environmentPlaces(userClickPlay, userClickPause, userClickStepFwd, autoStepTick)
      .environmentMode(unbounded())
      .property(placeBound(replayPlaying, 1))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
  }, Z3_TIMEOUT);

  it('deadlock-freedom with sink places', async () => {
    const { net, replayPaused, uiState, autoStepTick, userClickPlay, userClickPause, userClickStepFwd } = buildReplaySubnet();

    // replayPaused is a valid idle state (not a deadlock), so mark it as a sink
    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(replayPaused, 1).tokens(uiState, 1))
      .environmentPlaces(userClickPlay, userClickPause, userClickStepFwd, autoStepTick)
      .environmentMode(unbounded())
      .sinkPlaces(replayPaused)
      .property(deadlockFree())
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
  }, Z3_TIMEOUT);
});
