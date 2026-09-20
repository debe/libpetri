package org.libpetri.runtime;

import org.libpetri.core.Token;

import java.util.List;
import java.util.Map;

/**
 * A point-in-time capture of an executor's marking, per <b>ENV-014</b>, together with whether
 * any work was in flight at the instant it was taken.
 *
 * <p>The two travel as one value <b>deliberately</b>. A separately-queryable in-flight count
 * would be read at a different instant from the marking, so a caller could pair a marking with
 * an answer that was never true at the same moment — which is the race ENV-014 AC#5 exists to
 * close. The executors honour that on both sides: the orchestrator captures the pair in one
 * step and publishes it through one reference, so a caller never assembles it from two reads.
 *
 * @param marking        the snapshot form of <b>CORE-073</b>: place <b>name</b> to that place's
 *                       tokens in FIFO order, keys in ascending code-point order, empty places
 *                       omitted. An owned copy, independent of later executor state.
 * @param actionInFlight whether work was in flight <b>when this snapshot was taken</b>: an
 *                       action, or an accepted but un-injected external event. See below —
 *                       this is an observation about one past instant, not a quantity and not
 *                       a live reading.
 */
public record SnapshotResult(
    Map<String, List<Token<?>>> marking,
    boolean actionInFlight
) {

    /**
     * Whether work was in flight when this snapshot was taken: an action, or an accepted but
     * un-injected external event.
     *
     * <p><b>A boolean about one past instant, not a count and not a live reading.</b> The name
     * is singular for that reason: a plural would invite the reader to expect a quantity, and a
     * quantity is exactly what ENV-014 AC#5 rejects, because it would be read at a different
     * moment from the marking.
     *
     * <p><b>What it means for the caller.</b> {@code true} says the marking is a valid
     * <i>observation</i> but not a restore point, for either of two reasons:
     * <ul>
     *   <li><b>An action is in flight.</b> Its firing has already consumed its inputs
     *       ([EXEC-031] — no rollback) and its outputs have not landed, so those tokens appear
     *       nowhere in the marking. Restoring from it silently drops them. More fundamentally,
     *       the correspondence between an in-flight action and the external work it started is
     *       not something the engine can capture.</li>
     *   <li><b>An accepted external event is not yet injected.</b> {@code inject(...)} has
     *       taken the token — the caller holds a future, or nothing at all under
     *       {@code injectAsync} — but the orchestrator has not reached its external-events
     *       phase, so the token is in the queue and not in the marking. Restoring drops it
     *       exactly as above.</li>
     * </ul>
     *
     * <p>A snapshot taken <b>from inside an action</b> (Java invokes actions inline on the
     * orchestrator thread) always reports {@code true}: the calling firing has consumed its
     * inputs and has not produced its outputs.
     *
     * <p>The field reports the <b>fact</b>; {@link #isRestorePoint()} is the question most
     * callers are asking of it. The fact stays the record component because a mid-flight
     * snapshot is a perfectly valid observation for debugging, metrics or inspection, and a
     * component named {@code restorable} would describe one caller's intent rather than what
     * the engine saw.
     *
     * @return true when at least one action was in flight, or an accepted external event was
     *         still queued, at capture time
     */
    @Override
    public boolean actionInFlight() {
        return actionInFlight;
    }

    /**
     * Whether this snapshot may be persisted and later handed to {@code Builder.restore(...)}
     * without losing tokens (ENV-014 AC#5): exactly {@code !actionInFlight()}.
     *
     * <p>Named for the question a checkpointing caller is actually asking, and the same
     * accessor Rust and Python expose as {@code is_restore_point}. A caller that gets
     * {@code false} retries later; it is never an error.
     *
     * @return true when nothing was in flight at capture time
     */
    public boolean isRestorePoint() {
        return !actionInFlight;
    }
}
