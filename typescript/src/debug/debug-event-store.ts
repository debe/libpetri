/**
 * EventStore with live tailing and historical replay.
 * TypeScript port of Java's DebugEventStore.
 *
 * Node.js simplifications: single-threaded, no locks needed,
 * synchronous Set<Function> for subscribers, microtask broadcast.
 */

import type { EventStore } from '../event/event-store.js';
import type { NetEvent } from '../event/net-event.js';

/** Handle for managing a live event subscription. */
export interface Subscription {
  cancel(): void;
  isActive(): boolean;
}

/** Default maximum events to retain before evicting oldest. */
export const DEFAULT_MAX_EVENTS = 10_000;

export class DebugEventStore implements EventStore {
  private readonly _events: NetEvent[] = [];
  private readonly _subscribers = new Set<(event: NetEvent) => void>();
  private readonly _sessionId: string;
  private readonly _maxEvents: number;
  private _eventCount = 0;
  private _evictedCount = 0;

  constructor(sessionId: string, maxEvents = DEFAULT_MAX_EVENTS) {
    if (maxEvents <= 0) throw new Error(`maxEvents must be positive, got: ${maxEvents}`);
    this._sessionId = sessionId;
    this._maxEvents = maxEvents;
  }

  get sessionId(): string { return this._sessionId; }
  get maxEvents(): number { return this._maxEvents; }

  /** Total events appended (including evicted). */
  eventCount(): number { return this._eventCount; }

  /** Number of events evicted from the store. */
  evictedCount(): number { return this._evictedCount; }

  // ======================== EventStore Implementation ========================

  append(event: NetEvent): void {
    this._events.push(event);
    this._eventCount++;

    // Evict oldest when capacity exceeded
    while (this._events.length > this._maxEvents) {
      this._events.shift();
      this._evictedCount++;
    }

    // Broadcast to subscribers (microtask for async-like behavior)
    if (this._subscribers.size > 0) {
      // Use queueMicrotask instead of synchronous call to avoid blocking
      const subscribers = [...this._subscribers];
      queueMicrotask(() => {
        for (const sub of subscribers) {
          try {
            sub(event);
          } catch (e) {
            console.warn('Subscriber threw exception during event broadcast', e);
          }
        }
      });
    }
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

  // ======================== Live Tailing ========================

  /** Subscribe to receive events as they occur. */
  subscribe(listener: (event: NetEvent) => void): Subscription {
    this._subscribers.add(listener);
    return {
      cancel: () => { this._subscribers.delete(listener); },
      isActive: () => this._subscribers.has(listener),
    };
  }

  /** Number of active subscribers. */
  subscriberCount(): number {
    return this._subscribers.size;
  }

  // ======================== Historical Replay ========================

  /** Returns events starting from a specific index. */
  eventsFrom(fromIndex: number): readonly NetEvent[] {
    const adjustedSkip = Math.max(0, fromIndex - this._evictedCount);
    if (adjustedSkip <= 0) return this._events;
    return this._events.slice(adjustedSkip);
  }

  /** Returns all events since the specified timestamp. */
  eventsSince(from: number): readonly NetEvent[] {
    return this._events.filter(e => e.timestamp >= from);
  }

  /** Returns events within a time range. */
  eventsBetween(from: number, to: number): readonly NetEvent[] {
    return this._events.filter(e => e.timestamp >= from && e.timestamp < to);
  }

  /**
   * Returns an iterator over all retained events.
   * Useful for archive writers that need zero-copy traversal.
   */
  [Symbol.iterator](): Iterator<NetEvent> {
    return this._events[Symbol.iterator]();
  }

  // ======================== Lifecycle ========================

  /** Close the store (no-op in JS, but matches Java interface). */
  close(): void {
    this._subscribers.clear();
  }
}
