import type { NetEvent } from './net-event.js';
import { eventPlaceName, eventTransitionName, isFailureEvent } from './net-event.js';

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

/** Returns all token events (`token-added`, `token-removed`) for a specific place. */
export function placeEvents(store: EventStore, placeName: string): NetEvent[] {
  return store.events().filter(e => eventPlaceName(e) === placeName);
}

/** Returns all failure events. */
export function failures(store: EventStore): NetEvent[] {
  return store.events().filter(isFailureEvent);
}

/**
 * A query over the events of a store ([EVT-030]). Every given filter must match;
 * an omitted filter matches every event, an empty one matches none.
 */
export interface EventQuery {
  /** Keep only events of these types. */
  readonly types?: Iterable<NetEvent['type']>;
  /** Keep only events that carry one of these transition names. */
  readonly transitions?: Iterable<string>;
  /** Keep only token events that carry one of these place names. */
  readonly places?: Iterable<string>;
  /** Number of matching events to skip (default 0). */
  readonly offset?: number;
  /** Maximum number of matching events to return after the offset (default: all). */
  readonly limit?: number;
}

/**
 * Returns the events matching every filter of `query`, in store order, skipping the
 * first `offset` matches and returning at most `limit` of the rest. The page is taken
 * over the filtered result, not over the store.
 */
export function queryEvents(store: EventStore, query: EventQuery = {}): NetEvent[] {
  const offset = query.offset ?? 0;
  const limit = query.limit ?? Infinity;
  if (!Number.isInteger(offset) || offset < 0) {
    throw new RangeError(`offset must be a non-negative integer, got: ${offset}`);
  }
  if (limit !== Infinity && (!Number.isInteger(limit) || limit < 0)) {
    throw new RangeError(`limit must be a non-negative integer, got: ${limit}`);
  }
  const types = query.types !== undefined ? new Set<string>(query.types) : null;
  const transitions = query.transitions !== undefined ? new Set(query.transitions) : null;
  const places = query.places !== undefined ? new Set(query.places) : null;

  const result: NetEvent[] = [];
  let skipped = 0;
  for (const e of store.events()) {
    if (result.length >= limit) break;
    if (types !== null && !types.has(e.type)) continue;
    if (transitions !== null) {
      const name = eventTransitionName(e);
      if (name === null || !transitions.has(name)) continue;
    }
    if (places !== null) {
      const name = eventPlaceName(e);
      if (name === null || !places.has(name)) continue;
    }
    if (skipped < offset) {
      skipped++;
      continue;
    }
    result.push(e);
  }
  return result;
}

/**
 * Counts the events whose type is one of `types`, or all events when `types` is omitted.
 */
export function countEvents(store: EventStore, types?: Iterable<NetEvent['type']>): number {
  if (types === undefined) return store.size();
  const wanted = new Set<string>(types);
  let count = 0;
  for (const e of store.events()) {
    if (wanted.has(e.type)) count++;
  }
  return count;
}

/**
 * Histogram of the store's events by type: each event type that occurs names its
 * count, and no other type is named. Keys are inserted in ascending order, so two
 * stores holding the same events produce identical objects.
 */
export function counters(store: EventStore): Partial<Record<NetEvent['type'], number>> {
  const counts = new Map<NetEvent['type'], number>();
  for (const e of store.events()) {
    counts.set(e.type, (counts.get(e.type) ?? 0) + 1);
  }
  const result: Partial<Record<NetEvent['type'], number>> = {};
  for (const type of [...counts.keys()].sort()) {
    result[type] = counts.get(type)!;
  }
  return result;
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
