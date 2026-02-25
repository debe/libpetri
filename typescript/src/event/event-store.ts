import type { NetEvent } from './net-event.js';
import { eventTransitionName, isFailureEvent } from './net-event.js';

/**
 * Storage for events emitted during Petri net execution.
 */
export interface EventStore {
  /** Appends an event to the store. */
  append(event: NetEvent): void;

  /** Returns all events in chronological order. */
  events(): readonly NetEvent[];

  /** Whether this store is enabled (false = skip event creation). */
  isEnabled(): boolean;

  /** Number of events captured. */
  size(): number;

  /** Whether no events have been captured. */
  isEmpty(): boolean;
}

// ==================== Query Helpers ====================

/** Returns events matching a predicate. */
export function filterEvents(store: EventStore, predicate: (e: NetEvent) => boolean): NetEvent[] {
  return store.events().filter(predicate);
}

/** Returns events of a specific type. */
export function eventsOfType<T extends NetEvent['type']>(
  store: EventStore,
  type: T,
): Extract<NetEvent, { type: T }>[] {
  return store.events().filter(e => e.type === type) as Extract<NetEvent, { type: T }>[];
}

/** Returns all events for a specific transition. */
export function transitionEvents(store: EventStore, transitionName: string): NetEvent[] {
  return store.events().filter(e => eventTransitionName(e) === transitionName);
}

/** Returns all failure events. */
export function failures(store: EventStore): NetEvent[] {
  return store.events().filter(isFailureEvent);
}

// ==================== InMemoryEventStore ====================

export class InMemoryEventStore implements EventStore {
  private readonly _events: NetEvent[] = [];

  append(event: NetEvent): void {
    this._events.push(event);
  }

  events(): readonly NetEvent[] {
    return this._events;
  }

  isEnabled(): boolean {
    return true;
  }

  size(): number {
    return this._events.length;
  }

  isEmpty(): boolean {
    return this._events.length === 0;
  }

  /** Clears all stored events. */
  clear(): void {
    this._events.length = 0;
  }
}

// ==================== NoopEventStore ====================

const EMPTY: readonly NetEvent[] = Object.freeze([]);

class NoopEventStoreImpl implements EventStore {
  append(_event: NetEvent): void {
    // No-op
  }

  events(): readonly NetEvent[] {
    return EMPTY;
  }

  isEnabled(): boolean {
    return false;
  }

  size(): number {
    return 0;
  }

  isEmpty(): boolean {
    return true;
  }
}

const NOOP_INSTANCE = new NoopEventStoreImpl();

/** Returns a no-op event store that discards all events. */
export function noopEventStore(): EventStore {
  return NOOP_INSTANCE;
}

/** Creates a new in-memory event store. */
export function inMemoryEventStore(): InMemoryEventStore {
  return new InMemoryEventStore();
}
