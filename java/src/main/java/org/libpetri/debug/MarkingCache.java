package org.libpetri.debug;

import org.libpetri.debug.DebugProtocolHandler.ComputedState;
import org.libpetri.event.NetEvent;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

/**
 * Caches {@link ComputedState} snapshots at periodic intervals to accelerate seek/step operations.
 *
 * <p>Without caching, computing state at index N requires replaying all N events from the start.
 * With a snapshot interval of 256, the worst case is replaying 255 events from the nearest snapshot.
 *
 * <p>Snapshots are immutable (events are append-only) so they never become stale.
 * The cache is built lazily and extended incrementally as new events arrive.
 *
 * <h2>Thread Safety</h2>
 * <p>Not thread-safe. Each instance is used by a single client's subscription state,
 * which is accessed only from the WebSocket handler thread for that client.
 */
public final class MarkingCache {

    /** Number of events between cached snapshots. */
    static final int SNAPSHOT_INTERVAL = 256;

    private final List<ComputedState> snapshots = new ArrayList<>();
    private int indexedUpTo = 0;

    /**
     * Computes the {@link ComputedState} at the given event index, using cached snapshots
     * to minimize the number of events that need to be replayed.
     *
     * @param events the full event list for the session
     * @param targetIndex the event index to compute state at (exclusive upper bound, like subList)
     * @return the computed state at the target index
     */
    public ComputedState computeAt(List<NetEvent> events, int targetIndex) {
        if (targetIndex <= 0) {
            return DebugProtocolHandler.computeState(List.of());
        }

        // Extend cache if needed
        // snapshots.get(i) = state at event index (i+1)*INTERVAL
        ensureCachedUpTo(events, targetIndex);

        if (snapshots.isEmpty()) {
            // No snapshots available, compute from scratch
            return DebugProtocolHandler.computeState(events.subList(0, targetIndex));
        }

        // Find the highest snapshot whose event index <= targetIndex
        // Snapshot i covers events [0, (i+1)*INTERVAL)
        int snapshotSlot = Math.min(targetIndex / SNAPSHOT_INTERVAL, snapshots.size()) - 1;

        if (snapshotSlot < 0) {
            // targetIndex is before the first snapshot, compute from scratch
            return DebugProtocolHandler.computeState(events.subList(0, targetIndex));
        }

        int snapshotEventIndex = (snapshotSlot + 1) * SNAPSHOT_INTERVAL;

        if (snapshotEventIndex == targetIndex) {
            return snapshots.get(snapshotSlot);
        }

        // Replay delta events from snapshot to targetIndex
        return replayDelta(snapshots.get(snapshotSlot), events.subList(snapshotEventIndex, targetIndex));
    }

    /**
     * Invalidates the cache. Should be called when the event list changes
     * (e.g., session switch or event store reset).
     */
    public void invalidate() {
        snapshots.clear();
        indexedUpTo = 0;
    }

    /**
     * Extends the snapshot cache to cover at least up to the given event index.
     */
    private void ensureCachedUpTo(List<NetEvent> events, int targetIndex) {
        // We need snapshots at INTERVAL, 2*INTERVAL, etc.
        // snapshots.get(i) = state at event index (i+1)*INTERVAL
        int neededSnapshots = targetIndex / SNAPSHOT_INTERVAL;

        while (snapshots.size() < neededSnapshots) {
            int nextSnapshotIndex = (snapshots.size() + 1) * SNAPSHOT_INTERVAL;
            if (nextSnapshotIndex > events.size()) break;

            if (snapshots.isEmpty()) {
                // Build first snapshot from scratch
                snapshots.add(DebugProtocolHandler.computeState(events.subList(0, nextSnapshotIndex)));
            } else {
                // Build incrementally from previous snapshot
                int prevSnapshotIndex = snapshots.size() * SNAPSHOT_INTERVAL;
                var delta = events.subList(prevSnapshotIndex, nextSnapshotIndex);
                snapshots.add(replayDelta(snapshots.getLast(), delta));
            }
            indexedUpTo = nextSnapshotIndex;
        }
    }

    /**
     * Replays delta events on top of a base snapshot to produce a new state.
     */
    private static ComputedState replayDelta(ComputedState base, List<NetEvent> delta) {
        var marking = new HashMap<String, ArrayList<DebugResponse.TokenInfo>>();
        for (var entry : base.marking().entrySet()) {
            marking.put(entry.getKey(), new ArrayList<>(entry.getValue()));
        }
        var enabled = new HashSet<>(base.enabledTransitions());
        var inFlight = new HashSet<>(base.inFlightTransitions());
        DebugProtocolHandler.applyEvents(marking, enabled, inFlight, delta);
        return DebugProtocolHandler.toImmutableState(marking, enabled, inFlight);
    }
}
