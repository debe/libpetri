import { describe, it, expect } from 'vitest';
import { applyEventToState } from '../src/net/actions/playback.js';
import type { UIState } from '../src/net/types.js';
import type { NetEventInfo } from '../src/protocol/index.js';

function emptyState(): UIState {
  return {
    marking: {},
    enabledTransitions: [],
    inFlightTransitions: [],
    events: [],
    eventIndex: 0,
    totalEvents: 0,
  };
}

function event(overrides: Partial<NetEventInfo>): NetEventInfo {
  return {
    type: 'TokenAdded',
    timestamp: '2024-01-01T00:00:00Z',
    transitionName: null,
    placeName: null,
    details: {},
    ...overrides,
  };
}

describe('applyEventToState', () => {
  it('TokenAdded adds token to place marking', () => {
    const state = emptyState();
    const result = applyEventToState(state, event({
      type: 'TokenAdded',
      placeName: 'p1',
      details: { token: { id: '1', type: 'String', value: '"hello"', timestamp: null } },
    }));
    expect(result.marking['p1']).toHaveLength(1);
    expect(result.marking['p1']![0]).toEqual({ id: '1', type: 'String', value: '"hello"', timestamp: null });
  });

  it('TokenAdded creates new array for unknown place', () => {
    const state = emptyState();
    const result = applyEventToState(state, event({
      type: 'TokenAdded',
      placeName: 'newPlace',
      details: { token: { id: '2', type: 'Int', value: '42', timestamp: null } },
    }));
    expect(result.marking['newPlace']).toHaveLength(1);
  });

  it('TokenRemoved removes first token (FIFO)', () => {
    const state: UIState = {
      ...emptyState(),
      marking: {
        p1: [
          { id: '1', type: 'String', value: '"a"', timestamp: null },
          { id: '2', type: 'String', value: '"b"', timestamp: null },
        ],
      },
    };
    const result = applyEventToState(state, event({
      type: 'TokenRemoved',
      placeName: 'p1',
    }));
    expect(result.marking['p1']).toHaveLength(1);
    expect(result.marking['p1']![0]!.value).toBe('"b"');
  });

  it('TokenRemoved is no-op for empty place', () => {
    const state: UIState = { ...emptyState(), marking: { p1: [] } };
    const result = applyEventToState(state, event({ type: 'TokenRemoved', placeName: 'p1' }));
    expect(result.marking['p1']).toHaveLength(0);
  });

  it('TokenRemoved is no-op for missing place', () => {
    const state = emptyState();
    const result = applyEventToState(state, event({ type: 'TokenRemoved', placeName: 'missing' }));
    expect(result.marking['missing']).toBeUndefined();
  });

  it('TransitionEnabled adds to enabled list', () => {
    const state = emptyState();
    const result = applyEventToState(state, event({ type: 'TransitionEnabled', transitionName: 't1' }));
    expect(result.enabledTransitions).toContain('t1');
  });

  it('TransitionEnabled does not duplicate', () => {
    const state: UIState = { ...emptyState(), enabledTransitions: ['t1'] };
    const result = applyEventToState(state, event({ type: 'TransitionEnabled', transitionName: 't1' }));
    expect(result.enabledTransitions.filter(t => t === 't1')).toHaveLength(1);
  });

  it('TransitionStarted moves from enabled to inFlight', () => {
    const state: UIState = { ...emptyState(), enabledTransitions: ['t1', 't2'] };
    const result = applyEventToState(state, event({ type: 'TransitionStarted', transitionName: 't1' }));
    expect(result.enabledTransitions).not.toContain('t1');
    expect(result.inFlightTransitions).toContain('t1');
  });

  it('TransitionCompleted removes from inFlight', () => {
    const state: UIState = { ...emptyState(), inFlightTransitions: ['t1'] };
    const result = applyEventToState(state, event({ type: 'TransitionCompleted', transitionName: 't1' }));
    expect(result.inFlightTransitions).not.toContain('t1');
  });

  it('TransitionFailed removes from inFlight', () => {
    const state: UIState = { ...emptyState(), inFlightTransitions: ['t1'] };
    const result = applyEventToState(state, event({ type: 'TransitionFailed', transitionName: 't1' }));
    expect(result.inFlightTransitions).not.toContain('t1');
  });

  it('TransitionTimedOut removes from inFlight', () => {
    const state: UIState = { ...emptyState(), inFlightTransitions: ['t1'] };
    const result = applyEventToState(state, event({ type: 'TransitionTimedOut', transitionName: 't1' }));
    expect(result.inFlightTransitions).not.toContain('t1');
  });

  it('MarkingSnapshot replaces entire marking', () => {
    const state: UIState = {
      ...emptyState(),
      marking: { p1: [{ id: '1', type: 'String', value: '"old"', timestamp: null }] },
    };
    const newMarking = { p2: [{ id: '2', type: 'Int', value: '42', timestamp: null }] };
    const result = applyEventToState(state, event({
      type: 'MarkingSnapshot',
      details: { marking: newMarking },
    }));
    expect(result.marking['p1']).toBeUndefined();
    expect(result.marking['p2']).toHaveLength(1);
  });

  it('unrelated event type returns state unchanged', () => {
    const state = emptyState();
    const result = applyEventToState(state, event({ type: 'ExecutionStarted' }));
    expect(result.marking).toEqual({});
    expect(result.enabledTransitions).toEqual([]);
    expect(result.inFlightTransitions).toEqual([]);
  });

  it('preserves other state fields', () => {
    const events = [event({ type: 'TokenAdded', placeName: 'p1', details: { token: { id: '1', type: 'X', value: null, timestamp: null } } })];
    const state: UIState = { ...emptyState(), events, eventIndex: 5, totalEvents: 10 };
    const result = applyEventToState(state, event({ type: 'TransitionEnabled', transitionName: 't1' }));
    expect(result.events).toBe(events);
    expect(result.eventIndex).toBe(5);
    expect(result.totalEvents).toBe(10);
  });
});
