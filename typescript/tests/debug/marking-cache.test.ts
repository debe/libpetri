import { describe, it, expect } from 'vitest';
import { MarkingCache, SNAPSHOT_INTERVAL } from '../../src/debug/marking-cache.js';
import { computeState } from '../../src/debug/debug-protocol-handler.js';
import type { NetEvent } from '../../src/event/net-event.js';
import { tokenOf } from '../../src/core/token.js';

/** Seeded pseudo-random number generator (mulberry32). */
function mulberry32(seed: number): () => number {
  let a = seed | 0;
  return () => {
    a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function generateEvents(count: number): NetEvent[] {
  const events: NetEvent[] = [];
  const rng = mulberry32(12345);
  const transitions = ['T1', 'T2', 'T3', 'T4'];
  const places = ['P1', 'P2', 'P3', 'P4'];
  let ts = Date.now();

  for (let i = 0; i < count; i++) {
    ts++;
    const choice = Math.floor(rng() * 6);
    switch (choice) {
      case 0:
        events.push({ type: 'transition-enabled', timestamp: ts, transitionName: transitions[Math.floor(rng() * 4)]! });
        break;
      case 1:
        events.push({ type: 'transition-started', timestamp: ts, transitionName: transitions[Math.floor(rng() * 4)]!, consumedTokens: [tokenOf(`input-${i}`)] });
        break;
      case 2:
        events.push({ type: 'transition-completed', timestamp: ts, transitionName: transitions[Math.floor(rng() * 4)]!, producedTokens: [tokenOf(`output-${i}`)], durationMs: Math.floor(rng() * 100) });
        break;
      case 3:
        events.push({ type: 'token-added', timestamp: ts, placeName: places[Math.floor(rng() * 4)]!, token: tokenOf(`val-${i}`) });
        break;
      case 4:
        events.push({ type: 'token-removed', timestamp: ts, placeName: places[Math.floor(rng() * 4)]!, token: tokenOf(`val-${i}`) });
        break;
      case 5:
        events.push({ type: 'transition-failed', timestamp: ts, transitionName: transitions[Math.floor(rng() * 4)]!, errorMessage: 'error', exceptionType: 'RuntimeException' });
        break;
    }
  }
  return events;
}

describe('MarkingCache', () => {
  it('empty events should return empty state', () => {
    const cache = new MarkingCache();
    const state = cache.computeAt([], 0);

    expect(state.marking.size).toBe(0);
    expect(state.enabledTransitions).toHaveLength(0);
    expect(state.inFlightTransitions).toHaveLength(0);
  });

  it('should match brute force for small event list', () => {
    const events = generateEvents(50);
    const cache = new MarkingCache();

    for (let i = 0; i <= events.length; i++) {
      const expected = computeState(events.slice(0, i));
      const actual = cache.computeAt(events, i);
      expect(actual.marking).toEqual(expected.marking);
      expect(actual.enabledTransitions).toEqual(expected.enabledTransitions);
      expect(actual.inFlightTransitions).toEqual(expected.inFlightTransitions);
    }
  });

  it('should match brute force for large event list', () => {
    const events = generateEvents(1000);
    const cache = new MarkingCache();
    const rng = mulberry32(42);

    for (let trial = 0; trial < 50; trial++) {
      const idx = Math.floor(rng() * (events.length + 1));
      const expected = computeState(events.slice(0, idx));
      const actual = cache.computeAt(events, idx);
      expect(actual.marking).toEqual(expected.marking);
      expect(actual.enabledTransitions).toEqual(expected.enabledTransitions);
      expect(actual.inFlightTransitions).toEqual(expected.inFlightTransitions);
    }
  });

  it('should match at snapshot boundaries', () => {
    const events = generateEvents(SNAPSHOT_INTERVAL * 3 + 10);
    const cache = new MarkingCache();

    for (const boundary of [SNAPSHOT_INTERVAL, SNAPSHOT_INTERVAL * 2, SNAPSHOT_INTERVAL * 3]) {
      if (boundary <= events.length) {
        const expected = computeState(events.slice(0, boundary));
        const actual = cache.computeAt(events, boundary);
        expect(actual.marking).toEqual(expected.marking);
        expect(actual.enabledTransitions).toEqual(expected.enabledTransitions);
        expect(actual.inFlightTransitions).toEqual(expected.inFlightTransitions);
      }
    }
  });

  it('should match just before and after boundaries', () => {
    const events = generateEvents(SNAPSHOT_INTERVAL * 2 + 10);
    const cache = new MarkingCache();

    for (const offset of [SNAPSHOT_INTERVAL - 1, SNAPSHOT_INTERVAL + 1, SNAPSHOT_INTERVAL * 2 - 1, SNAPSHOT_INTERVAL * 2 + 1]) {
      if (offset <= events.length) {
        const expected = computeState(events.slice(0, offset));
        const actual = cache.computeAt(events, offset);
        expect(actual.marking).toEqual(expected.marking);
      }
    }
  });

  it('invalidate should reset cache', () => {
    const events = generateEvents(500);
    const cache = new MarkingCache();

    // Build cache
    cache.computeAt(events, 400);

    // Invalidate and verify still works
    cache.invalidate();

    const expected = computeState(events.slice(0, 300));
    const actual = cache.computeAt(events, 300);
    expect(actual.marking).toEqual(expected.marking);
  });

  it('should handle marking snapshot events', () => {
    const events: NetEvent[] = [];
    const ts = Date.now();

    events.push({ type: 'token-added', timestamp: ts, placeName: 'P1', token: tokenOf('a') });
    events.push({ type: 'token-added', timestamp: ts, placeName: 'P1', token: tokenOf('b') });

    events.push({
      type: 'marking-snapshot',
      timestamp: ts,
      marking: new Map([['P2', [tokenOf('x')]]]),
    });

    events.push({ type: 'token-added', timestamp: ts, placeName: 'P2', token: tokenOf('y') });

    const cache = new MarkingCache();
    for (let i = 0; i <= events.length; i++) {
      const expected = computeState(events.slice(0, i));
      const actual = cache.computeAt(events, i);
      expect(actual.marking).toEqual(expected.marking);
    }
  });
});
