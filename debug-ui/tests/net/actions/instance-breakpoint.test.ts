import { describe, it, expect } from 'vitest';
import { checkClientBreakpoints } from '../../../src/net/actions/playback.js';
import type { BreakpointConfig, NetEventInfo } from '../../../src/protocol/index.js';

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

function instanceBp(prefix: string, overrides: Partial<BreakpointConfig> = {}): BreakpointConfig {
  return {
    id: 'bp-i1',
    type: 'INSTANCE_TRANSITION',
    target: prefix,
    enabled: true,
    ...overrides,
  };
}

describe('instance-prefix breakpoint matching', () => {
  it('instanceBreakpoint_firesOnPrefixedTransition', () => {
    const result = checkClientBreakpoints(
      event({ type: 'TransitionStarted', transitionName: 'buf1/produce' }),
      [instanceBp('buf1')],
    );
    expect(result).not.toBeNull();
    expect(result!.target).toBe('buf1');
  });

  it('instanceBreakpoint_firesOnNestedPrefix', () => {
    const result = checkClientBreakpoints(
      event({ type: 'TransitionStarted', transitionName: 'outer/inner/step' }),
      [instanceBp('outer/inner')],
    );
    expect(result).not.toBeNull();
  });

  it('instanceBreakpoint_doesNotFireOnUnrelated', () => {
    const result = checkClientBreakpoints(
      event({ type: 'TransitionStarted', transitionName: 'other/produce' }),
      [instanceBp('buf1')],
    );
    expect(result).toBeNull();
  });

  it('instanceBreakpoint_doesNotFireOnExactPrefixMatch_withoutSlash', () => {
    // 'buf1' alone without trailing slash should not match (it's the instance,
    // not a transition WITHIN the instance)
    const result = checkClientBreakpoints(
      event({ type: 'TransitionStarted', transitionName: 'buf1' }),
      [instanceBp('buf1')],
    );
    expect(result).toBeNull();
  });

  it('instanceBreakpoint_doesNotFireOnSimilarPrefix', () => {
    // 'buf10/x' should NOT match 'buf1' because 'buf10/' does not start with 'buf1/'
    const result = checkClientBreakpoints(
      event({ type: 'TransitionStarted', transitionName: 'buf10/produce' }),
      [instanceBp('buf1')],
    );
    expect(result).toBeNull();
  });

  it('instanceBreakpoint_onlyFiresOnTransitionStarted', () => {
    // Other event types are ignored — instance breakpoints are scoped to TS-Started.
    const result = checkClientBreakpoints(
      event({ type: 'TransitionCompleted', transitionName: 'buf1/produce' }),
      [instanceBp('buf1')],
    );
    expect(result).toBeNull();
  });

  it('instanceBreakpoint_disabled_isSkipped', () => {
    const result = checkClientBreakpoints(
      event({ type: 'TransitionStarted', transitionName: 'buf1/produce' }),
      [instanceBp('buf1', { enabled: false })],
    );
    expect(result).toBeNull();
  });

  it('instanceBreakpoint_coexistsWithTransitionBreakpoint', () => {
    // Mixed list: returns the first matching bp.
    const result = checkClientBreakpoints(
      event({ type: 'TransitionStarted', transitionName: 'buf1/produce' }),
      [
        { id: 'a', type: 'TRANSITION_START', target: 'other', enabled: true },
        instanceBp('buf1', { id: 'b' }),
      ],
    );
    expect(result).not.toBeNull();
    expect(result!.id).toBe('b');
  });
});
