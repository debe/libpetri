/**
 * EventStore that delegates to both a primary store and a debug store.
 * TypeScript port of Java's DebugAwareEventStore.
 */

import type { EventStore } from '../event/event-store.js';
import type { NetEvent } from '../event/net-event.js';
import type { DebugEventStore } from './debug-event-store.js';

export class DebugAwareEventStore implements EventStore {
  private readonly _primary: EventStore;
  private readonly _debugStore: DebugEventStore;

  constructor(primary: EventStore, debugStore: DebugEventStore) {
    this._primary = primary;
    this._debugStore = debugStore;
  }

  append(event: NetEvent): void {
    this._primary.append(event);
    try {
      this._debugStore.append(event);
    } catch {
      // Debug failures must not break production
    }
  }

  events(): readonly NetEvent[] {
    return this._primary.events();
  }

  isEnabled(): boolean {
    return true;
  }

  size(): number {
    return this._primary.size();
  }

  isEmpty(): boolean {
    return this._primary.isEmpty();
  }

  /** Returns the underlying debug store for subscription management. */
  get debugStore(): DebugEventStore {
    return this._debugStore;
  }
}
