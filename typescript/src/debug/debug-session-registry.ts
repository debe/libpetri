/**
 * Registry for managing Petri net debug sessions.
 * TypeScript port of Java's DebugSessionRegistry.
 */

import type { PetriNet } from '../core/petri-net.js';
import type { Transition } from '../core/transition.js';
import { dotExport } from '../export/dot-exporter.js';
import { sanitize } from '../export/petri-net-mapper.js';
import type { NetStructure, PlaceInfo, TransitionInfo } from './debug-response.js';
import { PlaceAnalysis } from './place-analysis.js';
import { DebugEventStore } from './debug-event-store.js';
import type { SessionCompletionListener } from './session-completion-listener.js';

export interface DebugSession {
  readonly sessionId: string;
  readonly netName: string;
  readonly dotDiagram: string;
  readonly places: PlaceAnalysis | null;
  readonly transitions: ReadonlySet<Transition>;
  readonly eventStore: DebugEventStore;
  readonly startTime: number;
  readonly active: boolean;
  readonly importedStructure: NetStructure | null;
}

/** Builds the net structure from a session's stored place and transition info. */
export function buildNetStructure(session: DebugSession): NetStructure {
  if (session.importedStructure) {
    return session.importedStructure;
  }

  const places = session.places;
  if (!places) {
    return { places: [], transitions: [] };
  }

  const placeInfos: PlaceInfo[] = [];
  for (const [name, info] of places.data) {
    placeInfos.push({
      name,
      graphId: `p_${sanitize(name)}`,
      tokenType: info.tokenType,
      isStart: !info.hasIncoming,
      isEnd: !info.hasOutgoing,
      isEnvironment: false,
    });
  }

  const transitionInfos: TransitionInfo[] = [];
  for (const t of session.transitions) {
    transitionInfos.push({
      name: t.name,
      graphId: `t_${sanitize(t.name)}`,
    });
  }

  return { places: placeInfos, transitions: transitionInfos };
}

export type EventStoreFactory = (sessionId: string) => DebugEventStore;

export class DebugSessionRegistry {
  private readonly _sessions = new Map<string, DebugSession>();
  private readonly _maxSessions: number;
  private readonly _eventStoreFactory: EventStoreFactory;
  private readonly _completionListeners: readonly SessionCompletionListener[];

  constructor(
    maxSessions = 50,
    eventStoreFactory?: EventStoreFactory,
    completionListeners?: SessionCompletionListener[],
  ) {
    this._maxSessions = maxSessions;
    this._eventStoreFactory = eventStoreFactory ?? ((id: string) => new DebugEventStore(id));
    this._completionListeners = completionListeners ? [...completionListeners] : [];
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
      importedStructure: null,
    };

    this.evictIfNecessary();
    this._sessions.set(sessionId, session);
    return session;
  }

  /**
   * Marks a session as completed (no longer active) and notifies completion listeners.
   */
  complete(sessionId: string): void {
    const session = this._sessions.get(sessionId);
    if (session) {
      const completed: DebugSession = { ...session, active: false };
      this._sessions.set(sessionId, completed);
      this.notifyCompletionListeners(completed);
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

  /**
   * Registers an imported (archived) session as an inactive, read-only session.
   */
  registerImported(
    sessionId: string,
    netName: string,
    dotDiagram: string,
    structure: NetStructure,
    eventStore: DebugEventStore,
    startTime: number,
  ): DebugSession {
    this.evictIfNecessary();

    const session: DebugSession = {
      sessionId,
      netName,
      dotDiagram,
      places: null,
      transitions: new Set(),
      eventStore,
      startTime,
      active: false,
      importedStructure: structure,
    };

    this._sessions.set(sessionId, session);
    return session;
  }

  /** Notifies all completion listeners. Exceptions are caught and logged. */
  private notifyCompletionListeners(session: DebugSession): void {
    for (const listener of this._completionListeners) {
      try {
        listener(session);
      } catch (e) {
        console.warn(`Session completion listener failed for ${session.sessionId}`, e);
      }
    }
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
