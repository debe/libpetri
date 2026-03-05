import { describe, it, expect } from 'vitest';
import { computeSearchMatches, nextSearchMatch, prevSearchMatch } from '../src/net/actions/filter-search.js';
import type { NetEventInfo } from '../src/protocol/index.js';
import type { SearchState } from '../src/net/types.js';

function makeEvent(overrides: Partial<NetEventInfo>): NetEventInfo {
  return {
    type: 'TokenAdded',
    timestamp: '2024-01-01T00:00:00Z',
    transitionName: null,
    placeName: null,
    details: {},
    ...overrides,
  };
}

describe('computeSearchMatches', () => {
  it('empty search term returns empty matches', () => {
    const events = [makeEvent({ type: 'TokenAdded' })];
    const result = computeSearchMatches('', events, events.length);
    expect(result.matches).toHaveLength(0);
    expect(result.currentMatchIndex).toBe(-1);
  });

  it('matches event type', () => {
    const events = [
      makeEvent({ type: 'TokenAdded' }),
      makeEvent({ type: 'TransitionStarted' }),
      makeEvent({ type: 'TokenRemoved' }),
    ];
    const result = computeSearchMatches('TokenAdded', events, events.length);
    expect(result.matches).toEqual([0]);
  });

  it('matches transition name', () => {
    const events = [
      makeEvent({ transitionName: 'fire_missile' }),
      makeEvent({ transitionName: 'reload' }),
    ];
    const result = computeSearchMatches('fire_missile', events, events.length);
    expect(result.matches).toEqual([0]);
  });

  it('matches place name', () => {
    const events = [
      makeEvent({ placeName: 'ready' }),
      makeEvent({ placeName: 'waiting' }),
    ];
    const result = computeSearchMatches('waiting', events, events.length);
    expect(result.matches).toEqual([1]);
  });

  it('is case insensitive', () => {
    const events = [makeEvent({ type: 'TokenAdded', placeName: 'MyPlace' })];
    const result = computeSearchMatches('myplace', events, events.length);
    expect(result.matches).toEqual([0]);
  });
});

describe('nextSearchMatch', () => {
  it('wraps around to start', () => {
    const state: SearchState = { searchTerm: 'test', matches: [0, 5, 10], currentMatchIndex: 2 };
    const result = nextSearchMatch(state);
    expect(result.currentMatchIndex).toBe(0);
  });

  it('advances to next', () => {
    const state: SearchState = { searchTerm: 'test', matches: [0, 5, 10], currentMatchIndex: 0 };
    const result = nextSearchMatch(state);
    expect(result.currentMatchIndex).toBe(1);
  });

  it('no-op with empty matches', () => {
    const state: SearchState = { searchTerm: 'test', matches: [], currentMatchIndex: -1 };
    const result = nextSearchMatch(state);
    expect(result.currentMatchIndex).toBe(-1);
  });
});

describe('prevSearchMatch', () => {
  it('wraps around to end', () => {
    const state: SearchState = { searchTerm: 'test', matches: [0, 5, 10], currentMatchIndex: 0 };
    const result = prevSearchMatch(state);
    expect(result.currentMatchIndex).toBe(2);
  });

  it('goes to previous', () => {
    const state: SearchState = { searchTerm: 'test', matches: [0, 5, 10], currentMatchIndex: 2 };
    const result = prevSearchMatch(state);
    expect(result.currentMatchIndex).toBe(1);
  });

  it('no-op with empty matches', () => {
    const state: SearchState = { searchTerm: 'test', matches: [], currentMatchIndex: -1 };
    const result = prevSearchMatch(state);
    expect(result.currentMatchIndex).toBe(-1);
  });
});
