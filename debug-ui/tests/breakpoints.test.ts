import { describe, it, expect } from 'vitest';
import { checkClientBreakpoints } from '../src/net/actions/playback.js';
import type { BreakpointConfig } from '../src/protocol/index.js';
import type { NetEventInfo } from '../src/protocol/index.js';

function event(overrides: Partial<NetEventInfo>): NetEventInfo {
  return {
    type: 'TransitionStarted',
    timestamp: '2024-01-01T00:00:00Z',
    transitionName: null,
    placeName: null,
    details: {},
    ...overrides,
  };
}

function bp(overrides: Partial<BreakpointConfig>): BreakpointConfig {
  return {
    id: 'bp1',
    type: 'TRANSITION_START',
    target: null,
    enabled: true,
    ...overrides,
  };
}

describe('checkClientBreakpoints', () => {
  it('matches by type and target name', () => {
    const result = checkClientBreakpoints(
      event({ type: 'TransitionStarted', transitionName: 't_fire' }),
      [bp({ type: 'TRANSITION_START', target: 't_fire' })],
    );
    expect(result).not.toBeNull();
    expect(result!.target).toBe('t_fire');
  });

  it('null target matches all events of type', () => {
    const result = checkClientBreakpoints(
      event({ type: 'TransitionStarted', transitionName: 't_any' }),
      [bp({ type: 'TRANSITION_START', target: null })],
    );
    expect(result).not.toBeNull();
  });

  it('disabled breakpoints are skipped', () => {
    const result = checkClientBreakpoints(
      event({ type: 'TransitionStarted', transitionName: 't_fire' }),
      [bp({ type: 'TRANSITION_START', target: 't_fire', enabled: false })],
    );
    expect(result).toBeNull();
  });

  it('no match returns null', () => {
    const result = checkClientBreakpoints(
      event({ type: 'TokenAdded', placeName: 'p1' }),
      [bp({ type: 'TRANSITION_START', target: 't_fire' })],
    );
    expect(result).toBeNull();
  });

  it('matches TOKEN_ADDED by place name', () => {
    const result = checkClientBreakpoints(
      event({ type: 'TokenAdded', placeName: 'ready' }),
      [bp({ id: 'bp2', type: 'TOKEN_ADDED', target: 'ready' })],
    );
    expect(result).not.toBeNull();
    expect(result!.id).toBe('bp2');
  });

  it('returns first matching breakpoint', () => {
    const result = checkClientBreakpoints(
      event({ type: 'TransitionStarted', transitionName: 't1' }),
      [
        bp({ id: 'bp1', type: 'TRANSITION_COMPLETE', target: 't1' }),
        bp({ id: 'bp2', type: 'TRANSITION_START', target: 't1' }),
        bp({ id: 'bp3', type: 'TRANSITION_START', target: null }),
      ],
    );
    expect(result).not.toBeNull();
    expect(result!.id).toBe('bp2');
  });
});
