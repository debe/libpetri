/**
 * Caches computed state snapshots at periodic intervals for efficient seek/step.
 * TypeScript port of Java's MarkingCache.
 */

import type { NetEvent } from '../event/net-event.js';
import type { TokenInfo } from './debug-response.js';
import { computeState, applyEvents, toImmutableState, type ComputedState } from './debug-protocol-handler.js';

/** Number of events between cached snapshots. */
export const SNAPSHOT_INTERVAL = 256;

export class MarkingCache {
  private readonly _snapshots: ComputedState[] = [];

  /**
   * Computes the state at the given event index, using cached snapshots
   * to minimize the number of events that need to be replayed.
   *
   * @param events the full event list for the session
   * @param targetIndex event index to compute state at (exclusive upper bound)
   */
  computeAt(events: readonly NetEvent[], targetIndex: number): ComputedState {
    if (targetIndex <= 0) {
      return computeState([]);
    }

    this.ensureCachedUpTo(events, targetIndex);

    if (this._snapshots.length === 0) {
      return computeState(events.slice(0, targetIndex));
    }

    // Find highest snapshot <= targetIndex
    const snapshotSlot = Math.min(Math.floor(targetIndex / SNAPSHOT_INTERVAL), this._snapshots.length) - 1;

    if (snapshotSlot < 0) {
      return computeState(events.slice(0, targetIndex));
    }

    const snapshotEventIndex = (snapshotSlot + 1) * SNAPSHOT_INTERVAL;

    if (snapshotEventIndex === targetIndex) {
      return this._snapshots[snapshotSlot]!;
    }

    return replayDelta(this._snapshots[snapshotSlot]!, events.slice(snapshotEventIndex, targetIndex));
  }

  /** Invalidates the cache. */
  invalidate(): void {
    this._snapshots.length = 0;
  }

  /** Extends the snapshot cache to cover at least up to the given event index. */
  private ensureCachedUpTo(events: readonly NetEvent[], targetIndex: number): void {
    const neededSnapshots = Math.floor(targetIndex / SNAPSHOT_INTERVAL);

    while (this._snapshots.length < neededSnapshots) {
      const nextSnapshotIndex = (this._snapshots.length + 1) * SNAPSHOT_INTERVAL;
      if (nextSnapshotIndex > events.length) break;

      if (this._snapshots.length === 0) {
        this._snapshots.push(computeState(events.slice(0, nextSnapshotIndex)));
      } else {
        const prevSnapshotIndex = this._snapshots.length * SNAPSHOT_INTERVAL;
        const delta = events.slice(prevSnapshotIndex, nextSnapshotIndex);
        this._snapshots.push(replayDelta(this._snapshots[this._snapshots.length - 1]!, delta));
      }
    }
  }
}

/** Replays delta events on top of a base snapshot to produce a new state. */
function replayDelta(base: ComputedState, delta: readonly NetEvent[]): ComputedState {
  const marking = new Map<string, TokenInfo[]>();
  for (const [key, value] of base.marking) {
    marking.set(key, [...value]);
  }
  const enabled = new Set(base.enabledTransitions);
  const inFlight = new Set(base.inFlightTransitions);
  applyEvents(marking, enabled, inFlight, delta);
  return toImmutableState(marking, enabled, inFlight);
}
