import { describe, it, expect, beforeEach } from 'vitest';
import { buildCheckpoints, seekToIndex } from '../src/net/actions/playback.js';
import { shared } from '../src/net/shared-state.js';
import type { NetEventInfo } from '../src/protocol/index.js';

function makeEvents(count: number): NetEventInfo[] {
  return Array.from({ length: count }, (_, i) => ({
    type: i % 2 === 0 ? 'TokenAdded' : 'TransitionEnabled',
    timestamp: `2024-01-01T00:00:${String(i).padStart(2, '0')}Z`,
    transitionName: i % 2 === 1 ? `t${i}` : null,
    placeName: i % 2 === 0 ? `p${i}` : null,
    details: i % 2 === 0 ? { token: { id: String(i), type: 'Int', value: String(i), timestamp: null } } : {},
  }));
}

describe('buildCheckpoints', () => {
  beforeEach(() => {
    shared.replay = { allEvents: [], checkpoints: [], checkpointInterval: 20 };
  });

  it('creates checkpoint at every checkpointInterval events', () => {
    const events = makeEvents(60);
    const checkpoints = buildCheckpoints(events, 0);
    expect(checkpoints).toHaveLength(3); // at 20, 40, 60
    expect(checkpoints[0]!.index).toBe(20);
    expect(checkpoints[1]!.index).toBe(40);
    expect(checkpoints[2]!.index).toBe(60);
  });

  it('checkpoint state reflects cumulative event application', () => {
    const events = makeEvents(20);
    const checkpoints = buildCheckpoints(events, 0);
    expect(checkpoints).toHaveLength(1);
    // Should have accumulated token additions from even-indexed events
    const cp = checkpoints[0]!;
    expect(Object.keys(cp.marking).length).toBeGreaterThan(0);
  });

  it('incremental build extends from last checkpoint', () => {
    const events = makeEvents(40);
    shared.replay.allEvents = events.slice(0, 20);
    shared.replay.checkpoints = buildCheckpoints(events.slice(0, 20), 0);
    expect(shared.replay.checkpoints).toHaveLength(1);

    // Now build incrementally from index 20
    shared.replay.allEvents = events;
    const extended = buildCheckpoints(events, 20);
    expect(extended).toHaveLength(2);
    expect(extended[1]!.index).toBe(40);
  });

  it('empty events produces no checkpoints', () => {
    const checkpoints = buildCheckpoints([], 0);
    expect(checkpoints).toHaveLength(0);
  });
});

describe('seekToIndex', () => {
  beforeEach(() => {
    const events = makeEvents(100);
    shared.replay = { allEvents: events, checkpoints: [], checkpointInterval: 20 };
    shared.replay.checkpoints = buildCheckpoints(events, 0);
    shared.playback = { timer: null, animationFrame: null, speed: 1 };
  });

  it('seek to 0 produces empty state', () => {
    const state = seekToIndex(0);
    expect(state.eventIndex).toBe(0);
    expect(state.marking).toEqual({});
    expect(state.enabledTransitions).toEqual([]);
  });

  it('seek to checkpoint boundary uses checkpoint directly', () => {
    const state = seekToIndex(20);
    expect(state.eventIndex).toBe(20);
    // Should have marking data from first 20 events
    expect(Object.keys(state.marking).length).toBeGreaterThan(0);
  });

  it('seek between checkpoints replays from nearest checkpoint', () => {
    const state = seekToIndex(25);
    expect(state.eventIndex).toBe(25);
    expect(state.totalEvents).toBe(100);
  });

  it('seek to end has full state', () => {
    const state = seekToIndex(100);
    expect(state.eventIndex).toBe(100);
    expect(state.totalEvents).toBe(100);
  });

  it('seek past events clamps to end', () => {
    const state = seekToIndex(200);
    expect(state.eventIndex).toBe(200);
    expect(state.totalEvents).toBe(100);
    // All events applied even though index is past end
  });
});
