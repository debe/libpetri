/**
 * Registry for managing Petri net debug sessions.
 * TypeScript port of Java's DebugSessionRegistry.
 */

import type { PetriNet } from '../core/petri-net.js';
import type { Transition } from '../core/transition.js';
import { dotExport } from '../export/dot-exporter.js';
import { PlaceAnalysis } from './place-analysis.js';
import { DebugEventStore } from './debug-event-store.js';

export interface DebugSession {
  readonly sessionId: string;
  readonly netName: string;
  readonly dotDiagram: string;
  readonly places: PlaceAnalysis;
  readonly transitions: ReadonlySet<Transition>;
  readonly eventStore: DebugEventStore;
  readonly startTime: number;
  readonly active: boolean;
}

export type EventStoreFactory = (sessionId: string) => DebugEventStore;

export class DebugSessionRegistry {
  private readonly _sessions = new Map<string, DebugSession>();
  private readonly _maxSessions: number;
  private readonly _eventStoreFactory: EventStoreFactory;

  constructor(maxSessions = 50, eventStoreFactory?: EventStoreFactory) {
    this._maxSessions = maxSessions;
    this._eventStoreFactory = eventStoreFactory ?? ((id: string) => new DebugEventStore(id));
  }

  /**
   * Registers a new debug session for the given Petri net.
   * Generates DOT diagram and extracts net structure.
   */
  register(sessionId: string, net: PetriNet): DebugSession {
    const dotDiagram = dotExport(net);
    const places = PlaceAnalysis.from(net);
    const eventStore = this._eventStoreFactory(sessionId);

    const session: DebugSession = {
      sessionId,
      netName: net.name,
      dotDiagram,
      places,
      transitions: net.transitions,
      eventStore,
      startTime: Date.now(),
      active: true,
    };

    this.evictIfNecessary();
    this._sessions.set(sessionId, session);
    return session;
  }

  /** Marks a session as completed (no longer active). */
  complete(sessionId: string): void {
    const session = this._sessions.get(sessionId);
    if (session) {
      this._sessions.set(sessionId, { ...session, active: false });
    }
  }

  /** Removes a session from the registry. */
  remove(sessionId: string): DebugSession | undefined {
    const removed = this._sessions.get(sessionId);
    if (removed) {
      this._sessions.delete(sessionId);
      removed.eventStore.close();
    }
    return removed;
  }

  /** Returns a session by ID. */
  getSession(sessionId: string): DebugSession | undefined {
    return this._sessions.get(sessionId);
  }

  /** Lists sessions, ordered by start time (most recent first). */
  listSessions(limit: number): readonly DebugSession[] {
    return [...this._sessions.values()]
      .sort((a, b) => b.startTime - a.startTime)
      .slice(0, limit);
  }

  /** Lists only active sessions. */
  listActiveSessions(limit: number): readonly DebugSession[] {
    return [...this._sessions.values()]
      .filter(s => s.active)
      .sort((a, b) => b.startTime - a.startTime)
      .slice(0, limit);
  }

  /** Total number of sessions. */
  get size(): number {
    return this._sessions.size;
  }

  /** Evicts oldest inactive sessions if at capacity. */
  private evictIfNecessary(): void {
    if (this._sessions.size < this._maxSessions) return;

    const candidates = [...this._sessions.values()]
      .sort((a, b) => {
        // Inactive first, then oldest
        if (a.active !== b.active) return a.active ? 1 : -1;
        return a.startTime - b.startTime;
      });

    for (const candidate of candidates) {
      if (this._sessions.size < this._maxSessions) break;
      const evicted = this._sessions.get(candidate.sessionId);
      if (evicted) {
        this._sessions.delete(candidate.sessionId);
        evicted.eventStore.close();
      }
    }
  }
}
