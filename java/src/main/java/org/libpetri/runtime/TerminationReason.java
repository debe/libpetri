package org.libpetri.runtime;

/**
 * Why an executor's run loop stopped, per <b>EXEC-041</b>.
 *
 * <p>The returned marking says what the net <i>holds</i>, not whether the run <i>finished</i>.
 * A partial marking presented as final is indistinguishable from a net that had nothing left
 * to do, so every consumer that treats completion as proof the run finished — a durable
 * checkpoint, a workflow step, an assertion on the final marking — would silently accept a
 * truncation. This enum is the distinguishing signal EXEC-041 AC#3 requires.
 *
 * @see PetriNetExecutor#terminationReason()
 */
public enum TerminationReason {

    /** The run has not finished — no loop has completed on this executor yet. */
    RUNNING,

    /**
     * The net reached quiescence ([EXEC-040]): nothing enabled, nothing in flight. This is the
     * only value for which the returned marking is a <b>final</b> marking.
     */
    QUIESCENT,

    /** {@link PetriNetExecutor#close()} stopped the run before quiescence ([ENV-013]). */
    CLOSED,

    /**
     * The orchestrator observed a cancellation <i>itself</i> while waiting — in Java, an
     * {@link InterruptedException} from the wait.
     *
     * <p>Distinct from an interrupt flag merely being <i>set</i>: EXEC-041 forbids treating
     * ambient host state as a stop request, because on a runtime that invokes actions inline
     * on the orchestrator thread the conventional
     * {@code catch (InterruptedException e) { Thread.currentThread().interrupt(); }} idiom is
     * indistinguishable from one. Only a cancellation raised <i>at</i> the executor counts,
     * and the flag is restored for the caller before the run returns.
     */
    INTERRUPTED,

    /** The run stopped before quiescence for another reason, such as a caller's run budget. */
    STOPPED;

    /** True when the returned marking is a final marking rather than a truncated one. */
    public boolean isComplete() {
        return this == QUIESCENT;
    }
}
