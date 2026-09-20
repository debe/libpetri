package org.libpetri.runtime;

import org.junit.jupiter.api.Test;

import java.util.ArrayDeque;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * <b>ENV-014</b>: the one "work in flight" expression both executors publish with, mid-run and
 * at loop exit alike.
 *
 * <p>The executors cannot be driven into the state the last case describes on purpose — an
 * {@code inject} racing the end of a run sits in the queue only until its own re-drain refuses
 * it — so the expression is pinned here, and the executors are pinned to the expression by
 * having no other.
 */
class ExecutorSupportWorkInFlightTest {

    private static final ArrayDeque<String> EMPTY = new ArrayDeque<>();
    private static final ArrayDeque<String> QUEUED = new ArrayDeque<>(List.of("e"));

    @Test
    void anActionInFlightIsWorkInFlightWhateverElseHolds() {
        assertTrue(ExecutorSupport.workInFlight(true, false, EMPTY));
        assertTrue(ExecutorSupport.workInFlight(true, true, EMPTY));
        assertTrue(ExecutorSupport.workInFlight(true, true, QUEUED));
    }

    @Test
    void anAcceptedButUninjectedEventIsWorkInFlight() {
        assertTrue(ExecutorSupport.workInFlight(false, false, QUEUED));
        assertFalse(ExecutorSupport.workInFlight(false, false, EMPTY));
    }

    @Test
    void aQueuedEventThatWillBeRefusedWasNeverAccepted() {
        assertFalse(ExecutorSupport.workInFlight(false, true, QUEUED),
            "closed, or the loop has ended: the queue is completed `false`, the host keeps the "
                + "token, and the marking without it IS a restore point. The Precompiled "
                + "executor's final pair used to OR the queue in on a STOPPED/INTERRUPTED run "
                + "while the Bitmap one did not.");
    }
}
