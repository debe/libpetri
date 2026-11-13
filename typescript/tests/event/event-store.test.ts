import { describe, it, expect } from 'vitest';
import {
  InMemoryEventStore, noopEventStore,
  filterEvents, eventsOfType, transitionEvents, failures,
  placeEvents, queryEvents, countEvents, counters,
} from '../../src/event/event-store.js';
import type { NetEvent } from '../../src/event/net-event.js';
import { eventPlaceName, eventTransitionName, isFailureEvent } from '../../src/event/net-event.js';
import { tokenOf } from '../../src/core/token.js';

function makeEvent(type: NetEvent['type'], extra: Record<string, unknown> = {}): NetEvent {
  return { type, timestamp: Date.now(), ...extra } as NetEvent;
}

describe('InMemoryEventStore', () => {
  it('starts empty', () => {
    const store = new InMemoryEventStore();
    expect(store.isEmpty()).toBe(true);
    expect(store.size()).toBe(0);
    expect(store.events()).toHaveLength(0);
  });

  it('appends and retrieves events', () => {
    const store = new InMemoryEventStore();
    const event: NetEvent = {
      type: 'execution-started',
      timestamp: Date.now(),
      netName: 'test',
      executionId: '123',
    };
    store.append(event);

    expect(store.size()).toBe(1);
    expect(store.isEmpty()).toBe(false);
    expect(store.events()[0]).toBe(event);
  });

  it('preserves chronological order', () => {
    const store = new InMemoryEventStore();
    store.append(makeEvent('execution-started', { netName: 'a', executionId: '1' }));
    store.append(makeEvent('transition-enabled', { transitionName: 'T1' }));
    store.append(makeEvent('transition-started', { transitionName: 'T1', consumedTokens: [] }));

    const types = store.events().map(e => e.type);
    expect(types).toEqual(['execution-started', 'transition-enabled', 'transition-started']);
  });

  it('is enabled', () => {
    expect(new InMemoryEventStore().isEnabled()).toBe(true);
  });

  it('clears events', () => {
    const store = new InMemoryEventStore();
    store.append(makeEvent('execution-started', { netName: 'a', executionId: '1' }));
    expect(store.size()).toBe(1);

    store.clear();
    expect(store.isEmpty()).toBe(true);
  });
});

describe('noopEventStore', () => {
  it('discards events', () => {
    const store = noopEventStore();
    store.append(makeEvent('execution-started', { netName: 'a', executionId: '1' }));
    expect(store.isEmpty()).toBe(true);
    expect(store.size()).toBe(0);
  });

  it('is not enabled', () => {
    expect(noopEventStore().isEnabled()).toBe(false);
  });

  it('is a singleton', () => {
    expect(noopEventStore()).toBe(noopEventStore());
  });
});

describe('query helpers', () => {
  function populatedStore(): InMemoryEventStore {
    const store = new InMemoryEventStore();
    store.append({ type: 'execution-started', timestamp: 1, netName: 'N', executionId: 'E1' });
    store.append({ type: 'transition-enabled', timestamp: 2, transitionName: 'T1' });
    store.append({ type: 'transition-started', timestamp: 3, transitionName: 'T1', consumedTokens: [tokenOf('x')] });
    store.append({ type: 'transition-completed', timestamp: 4, transitionName: 'T1', producedTokens: [], durationMs: 10 });
    store.append({ type: 'transition-failed', timestamp: 5, transitionName: 'T2', errorMessage: 'oops', exceptionType: 'Error' });
    store.append({ type: 'action-timed-out', timestamp: 6, transitionName: 'T3', timeoutMs: 5000 });
    store.append({ type: 'token-added', timestamp: 7, placeName: 'P1', token: tokenOf('y') });
    return store;
  }

  it('filterEvents', () => {
    const store = populatedStore();
    const result = filterEvents(store, e => e.timestamp > 4);
    expect(result).toHaveLength(3);
  });

  it('eventsOfType', () => {
    const store = populatedStore();
    const started = eventsOfType(store, 'transition-started');
    expect(started).toHaveLength(1);
    expect(started[0]!.transitionName).toBe('T1');
  });

  it('transitionEvents', () => {
    const store = populatedStore();
    const t1Events = transitionEvents(store, 'T1');
    expect(t1Events).toHaveLength(3); // enabled, started, completed
  });

  it('failures', () => {
    const store = populatedStore();
    const failEvents = failures(store);
    expect(failEvents).toHaveLength(2); // failed + action-timed-out
  });
});

describe('[EVT-030] event store queries', () => {
  function mixedStore(): InMemoryEventStore {
    const store = new InMemoryEventStore();
    store.append({ type: 'execution-started', timestamp: 1, netName: 'N', executionId: 'E1' });
    store.append({ type: 'token-added', timestamp: 2, placeName: 'P1', token: tokenOf('a') });
    store.append({ type: 'transition-enabled', timestamp: 3, transitionName: 'T1' });
    store.append({ type: 'transition-started', timestamp: 4, transitionName: 'T1', consumedTokens: [tokenOf('a')] });
    store.append({ type: 'token-removed', timestamp: 5, placeName: 'P1', token: tokenOf('a') });
    store.append({ type: 'token-added', timestamp: 6, placeName: 'P2', token: tokenOf('b') });
    store.append({ type: 'transition-completed', timestamp: 7, transitionName: 'T1', producedTokens: [tokenOf('b')], durationMs: 1 });
    store.append({ type: 'transition-enabled', timestamp: 8, transitionName: 'T2' });
    store.append({ type: 'token-added', timestamp: 9, placeName: 'P1', token: tokenOf('c') });
    store.append({ type: 'transition-failed', timestamp: 10, transitionName: 'T2', errorMessage: 'e', exceptionType: 'Error' });
    store.append({ type: 'execution-completed', timestamp: 11, netName: 'N', executionId: 'E1', totalDurationMs: 10 });
    return store;
  }

  const stamps = (events: readonly NetEvent[]) => events.map(e => e.timestamp);

  it('without filters or paging returns exactly events()', () => {
    const store = mixedStore();
    expect(queryEvents(store)).toEqual([...store.events()]);
    expect(queryEvents(store, {})).toEqual([...store.events()]);
  });

  it('AC3: placeEvents returns only the token events of the named place', () => {
    const store = mixedStore();
    expect(stamps(placeEvents(store, 'P1'))).toEqual([2, 5, 9]);
    expect(stamps(placeEvents(store, 'P2'))).toEqual([6]);
    expect(placeEvents(store, 'Missing')).toEqual([]);
  });

  it('AC3: a place filter matches any of the given places, in store order', () => {
    const store = mixedStore();
    expect(stamps(queryEvents(store, { places: ['P2', 'P1'] }))).toEqual([2, 5, 6, 9]);
  });

  it('type, transition and place filters combine: every given filter must match', () => {
    const store = mixedStore();
    expect(stamps(queryEvents(store, { types: ['token-added'], places: ['P1'] }))).toEqual([2, 9]);
    expect(stamps(queryEvents(store, { types: ['transition-enabled', 'transition-failed'] }))).toEqual([3, 8, 10]);
    expect(stamps(queryEvents(store, { transitions: ['T1'] }))).toEqual([3, 4, 7]);
    expect(stamps(queryEvents(store, { transitions: ['T2'], types: ['transition-failed'] }))).toEqual([10]);
    // Token events carry no transition name and transition events no place name.
    expect(queryEvents(store, { transitions: ['T1'], places: ['P1'] })).toEqual([]);
  });

  it('an event with no transition name matches no transition filter', () => {
    const store = mixedStore();
    for (const e of queryEvents(store, { transitions: ['T1', 'T2'] })) {
      expect(eventTransitionName(e)).not.toBeNull();
    }
  });

  it('an empty filter matches nothing', () => {
    const store = mixedStore();
    expect(queryEvents(store, { types: [] })).toEqual([]);
    expect(queryEvents(store, { transitions: [] })).toEqual([]);
    expect(queryEvents(store, { places: [] })).toEqual([]);
  });

  it('AC3: offset and limit page the filtered result, not the store', () => {
    const store = mixedStore();
    expect(stamps(queryEvents(store, { places: ['P1', 'P2'], offset: 1, limit: 2 }))).toEqual([5, 6]);
    expect(stamps(queryEvents(store, { places: ['P1', 'P2'], offset: 3 }))).toEqual([9]);
    expect(stamps(queryEvents(store, { places: ['P1', 'P2'], limit: 1 }))).toEqual([2]);
    expect(queryEvents(store, { places: ['P1', 'P2'], offset: 4 })).toEqual([]);
    expect(queryEvents(store, { limit: 0 })).toEqual([]);
    expect(stamps(queryEvents(store, { offset: 9 }))).toEqual([10, 11]);
  });

  it('rejects a negative or fractional offset or limit', () => {
    const store = mixedStore();
    expect(() => queryEvents(store, { offset: -1 })).toThrow(RangeError);
    expect(() => queryEvents(store, { offset: 1.5 })).toThrow(RangeError);
    expect(() => queryEvents(store, { limit: -1 })).toThrow(RangeError);
    expect(() => queryEvents(store, { limit: Number.NaN })).toThrow(RangeError);
  });

  it('countEvents counts all events, or those of the given types', () => {
    const store = mixedStore();
    expect(countEvents(store)).toBe(store.size());
    expect(countEvents(store, ['token-added'])).toBe(3);
    expect(countEvents(store, ['token-added', 'token-removed'])).toBe(4);
    expect(countEvents(store, [])).toBe(0);
  });

  it('AC5: counters() names each occurring type once with its count, and sums to the total', () => {
    const store = mixedStore();
    const histogram = counters(store);
    expect(histogram).toEqual({
      'execution-completed': 1,
      'execution-started': 1,
      'token-added': 3,
      'token-removed': 1,
      'transition-completed': 1,
      'transition-enabled': 2,
      'transition-failed': 1,
      'transition-started': 1,
    });
    expect(Object.keys(histogram)).toEqual([...Object.keys(histogram)].sort());
    expect(Object.values(histogram).reduce((a, b) => a + (b ?? 0), 0)).toBe(store.size());
    expect(counters(new InMemoryEventStore())).toEqual({});
  });

  it('works over any EventStore (noop store is empty)', () => {
    const store = noopEventStore();
    expect(queryEvents(store, { places: ['P1'] })).toEqual([]);
    expect(countEvents(store, ['token-added'])).toBe(0);
    expect(counters(store)).toEqual({});
  });
});

describe('eventPlaceName', () => {
  it('returns the place name of token events and null otherwise', () => {
    expect(eventPlaceName(makeEvent('token-added', { placeName: 'P', token: tokenOf('x') }))).toBe('P');
    expect(eventPlaceName(makeEvent('token-removed', { placeName: 'Q', token: tokenOf('x') }))).toBe('Q');
    expect(eventPlaceName(makeEvent('transition-enabled', { transitionName: 'T' }))).toBeNull();
    expect(eventPlaceName(makeEvent('marking-snapshot', { marking: new Map() }))).toBeNull();
  });
});

describe('eventTransitionName', () => {
  it('returns name for transition events', () => {
    expect(eventTransitionName(makeEvent('transition-enabled', { transitionName: 'T1' }))).toBe('T1');
    expect(eventTransitionName(makeEvent('transition-started', { transitionName: 'T2', consumedTokens: [] }))).toBe('T2');
    expect(eventTransitionName(makeEvent('transition-completed', { transitionName: 'T3', producedTokens: [], durationMs: 1 }))).toBe('T3');
    expect(eventTransitionName(makeEvent('transition-failed', { transitionName: 'T4', errorMessage: 'e', exceptionType: 'E' }))).toBe('T4');
    expect(eventTransitionName(makeEvent('log-message', { transitionName: 'T5', logger: 'L', level: 'INFO', message: 'm', error: null, errorMessage: null }))).toBe('T5');
  });

  it('returns null for non-transition events', () => {
    expect(eventTransitionName(makeEvent('execution-started', { netName: 'N', executionId: 'E' }))).toBeNull();
    expect(eventTransitionName(makeEvent('token-added', { placeName: 'P', token: tokenOf('x') }))).toBeNull();
    expect(eventTransitionName(makeEvent('execution-completed', { netName: 'N', executionId: 'E', totalDurationMs: 1 }))).toBeNull();
  });
});

describe('isFailureEvent', () => {
  it('returns true for failure types', () => {
    expect(isFailureEvent(makeEvent('transition-failed', { transitionName: 'T', errorMessage: 'e', exceptionType: 'E' }))).toBe(true);
    expect(isFailureEvent(makeEvent('transition-timed-out', { transitionName: 'T', deadlineMs: 100, actualDurationMs: 200 }))).toBe(true);
    expect(isFailureEvent(makeEvent('action-timed-out', { transitionName: 'T', timeoutMs: 100 }))).toBe(true);
  });

  it('returns false for non-failure types', () => {
    expect(isFailureEvent(makeEvent('transition-started', { transitionName: 'T', consumedTokens: [] }))).toBe(false);
    expect(isFailureEvent(makeEvent('transition-completed', { transitionName: 'T', producedTokens: [], durationMs: 1 }))).toBe(false);
    expect(isFailureEvent(makeEvent('token-added', { placeName: 'P', token: tokenOf('x') }))).toBe(false);
  });
});
