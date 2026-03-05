import { describe, it, expect } from 'vitest';
import { buildSessionData, buildInitialUIState } from '../src/net/actions/session.js';
import type { DebugResponse } from '../src/protocol/index.js';

type SubscribedResponse = Extract<DebugResponse, { type: 'subscribed' }>;

function makeSubscribedResponse(overrides?: Partial<SubscribedResponse>): SubscribedResponse {
  return {
    type: 'subscribed',
    sessionId: 'sess-1',
    netName: 'TestNet',
    dotDiagram: 'digraph { a -> b }',
    structure: {
      places: [
        { name: 'p1', graphId: 'p_p1', tokenType: 'String', isStart: true, isEnd: false, isEnvironment: false },
        { name: 'p2', graphId: 'p_p2', tokenType: 'Int', isStart: false, isEnd: true, isEnvironment: false },
      ],
      transitions: [
        { name: 't1', graphId: 't_t1' },
      ],
    },
    currentMarking: {
      p1: [{ id: '1', type: 'String', value: '"hello"', timestamp: null }],
    },
    enabledTransitions: ['t1'],
    inFlightTransitions: [],
    eventCount: 42,
    mode: 'live',
    ...overrides,
  };
}

describe('buildSessionData', () => {
  it('constructs byGraphId lookup from structure', () => {
    const response = makeSubscribedResponse();
    const session = buildSessionData(response);

    expect(session.sessionId).toBe('sess-1');
    expect(session.netName).toBe('TestNet');
    expect(session.mode).toBe('live');

    expect(session.byGraphId['p_p1']).toEqual({
      name: 'p1',
      isTransition: false,
      tokenType: 'String',
      isStart: true,
      isEnd: false,
    });

    expect(session.byGraphId['t_t1']).toEqual({
      name: 't1',
      isTransition: true,
    });
  });

  it('handles empty structure', () => {
    const response = makeSubscribedResponse({
      structure: { places: [], transitions: [] },
    });
    const session = buildSessionData(response);
    expect(Object.keys(session.byGraphId)).toHaveLength(0);
  });
});

describe('buildInitialUIState', () => {
  it('replay mode: empty marking, eventIndex=0', () => {
    const response = makeSubscribedResponse({ mode: 'replay', eventCount: 100 });
    const state = buildInitialUIState(response, true);

    expect(state.marking).toEqual({});
    expect(state.enabledTransitions).toEqual([]);
    expect(state.inFlightTransitions).toEqual([]);
    expect(state.eventIndex).toBe(0);
    expect(state.totalEvents).toBe(100);
  });

  it('live mode: uses currentMarking from response', () => {
    const response = makeSubscribedResponse();
    const state = buildInitialUIState(response, false);

    expect(state.marking['p1']).toHaveLength(1);
    expect(state.enabledTransitions).toContain('t1');
    expect(state.eventIndex).toBe(0);
    expect(state.totalEvents).toBe(42);
  });
});
