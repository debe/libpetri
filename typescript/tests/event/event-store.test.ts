import { describe, it, expect } from 'vitest';
import {
  InMemoryEventStore, noopEventStore, inMemoryEventStore,
  filterEvents, eventsOfType, transitionEvents, failures,
} from '../../src/event/event-store.js';
import type { NetEvent } from '../../src/event/net-event.js';
import { eventTransitionName, isFailureEvent } from '../../src/event/net-event.js';
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
