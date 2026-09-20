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
     * {@link InterruptedException} from the wait, or the interrupt flag found set on return
     * from a hosted wait.
     *
     * <p>Distinct from an interrupt flag merely being <i>set</i>: EXEC-041 forbids treating
     * ambient host state as a stop request, because on a runtime that invokes actions inline
     * on the orchestrator thread the conventional
     * {@code catch (InterruptedException e) { Thread.currentThread().interrupt(); }} idiom is
     * indistinguishable from one. Only a cancellation raised <i>at</i> the executor counts:
     * an interrupt that arrives during a wait that was <b>entered with the flag clear</b>. A
     * built-in wait reports it by throwing {@link InterruptedException}. A hosted wait
     * ({@link ExecutionEnvironment#awaitWork}, [TIME-015]) cannot throw it, so there the
     * executor reads the flag when the wait returns: set on return from a wait entered clear
     * is the same event, and ends the run {@code INTERRUPTED} the same way.
     *
     * <p>To make that distinction the executor takes the flag down — and remembers it — at the
     * start of the run, after every inline action returns and before every wait, and puts it
     * back when {@code run()} returns (AC#4, AC#5). The consequences are deliberate:
     * <ul>
     *   <li>a flag set before {@code run()}, or by action code, never truncates the run, and
     *       the caller still finds it set afterwards;</li>
     *   <li>an <i>external</i> interrupt that lands while an inline action is executing cannot
     *       be told from one the action set itself, so it is <b>deferred</b> to
     *       {@code run()}'s return rather than stopping the run. A net that never waits is
     *       therefore not interruptible — stop it with {@link PetriNetExecutor#terminateNow()}
     *       or {@link PetriNetExecutor#close()};</li>
     *   <li>under an injected {@link ExecutionEnvironment} the hosted wait is always entered
     *       with the flag clear, and an interrupt that arrives during it <b>does</b> end the
     *       run — provided the host lets the flag survive its wait, which the conventional
     *       catch-and-re-interrupt does. Anything the host runs on the orchestrator thread
     *       inside {@code awaitWork} that sets the flag is indistinguishable from that
     *       interrupt, and ends the run as well;</li>
     *   <li>later actions of the same run do not observe a flag an earlier one set.</li>
     * </ul>
     */
    INTERRUPTED,

    /** The run stopped before quiescence for another reason, such as a caller's run budget. */
    STOPPED;

    /** True when the returned marking is a final marking rather than a truncated one. */
    public boolean isComplete() {
        return this == QUIESCENT;
    }
}
