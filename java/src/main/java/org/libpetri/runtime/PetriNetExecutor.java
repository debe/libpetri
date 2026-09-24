package org.libpetri.runtime;

import java.time.Duration;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionStage;

import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.Token;

/**
 * Common interface for Petri net executors.
 *
 * <p>Both {@link PrecompiledNetExecutor} and {@link BitmapNetExecutor} implement this
 * interface, allowing tests and client code to be written against a single
 * contract.
 */
public interface PetriNetExecutor extends AutoCloseable {

    /**
     * What to do with the orchestrator loop when {@link #run(Duration, RunTimeoutPolicy)}
     * hits its timeout.
     */
    enum RunTimeoutPolicy {
        /**
         * Fail the returned stage and leave the loop running.
         *
         * <p>The net keeps firing transitions and mutating its marking after the caller has
         * given up. This is what the single-argument {@link #run(Duration)} has always done,
         * and it is the default only for compatibility — it is rarely what you want.
         */
        ABANDON,

        /**
         * Fail the returned stage and {@link #close()} the executor.
         *
         * <p>Queued external events are discarded and in-flight actions are allowed to
         * complete, per ENV-013. Pair with {@link #awaitTermination(Duration)} to observe
         * the loop actually stopping.
         */
        CLOSE
    }

    Marking run();

    CompletionStage<Marking> run(Duration timeout);

    /**
     * Runs with a timeout and an explicit policy for what happens to the loop on expiry.
     *
     * <p>{@link #run(Duration)} is equivalent to {@code run(timeout, ABANDON)}.
     *
     * @param timeout how long the caller is willing to wait
     * @param policy what to do with the orchestrator loop when the timeout expires
     * @return the final marking, or a stage failing with {@code TimeoutException}
     */
    default CompletionStage<Marking> run(Duration timeout, RunTimeoutPolicy policy) {
        return run(timeout);
    }

    /**
     * Blocks until the orchestrator loop has finished.
     *
     * <p>Returns immediately if the loop never started. A {@code true} result means the loop
     * has run its termination bookkeeping: pending {@code inject()} futures are completed and
     * {@code ExecutionCompleted} has been emitted.
     *
     * @param timeout how long to wait
     * @return {@code true} if the loop terminated within the timeout
     * @throws InterruptedException if the calling thread is interrupted while waiting
     */
    default boolean awaitTermination(Duration timeout) throws InterruptedException {
        return true;
    }

    /**
     * Stops the orchestrator loop without waiting for in-flight actions.
     *
     * <p>An explicit escape hatch from ENV-013, which requires {@link #close()} to let
     * in-flight actions complete. Their results are discarded rather than admitted to the
     * marking. The actions themselves keep running — libpetri does not own their threads and
     * cannot stop them.
     *
     * <p>Never invoked implicitly by {@code close()}.
     */
    default void terminateNow() {
        close();
    }

    Marking marking();

    <T> CompletableFuture<Boolean> inject(EnvironmentPlace<T> place, T token);

    <T> CompletableFuture<Boolean> inject(EnvironmentPlace<T> place, Token<T> token);

    <T> void injectAsync(EnvironmentPlace<T> place, Token<T> token);

    /**
     * Why the last run stopped, per <b>EXEC-041</b>.
     *
     * <p>The marking returned by {@link #run()} says what the net <i>holds</i>, not whether the
     * run <i>finished</i>. Only a completed reason ({@link TerminationReason#isComplete()}:
     * {@link TerminationReason#QUIESCENT} or {@link TerminationReason#TERMINAL}) means it is a
     * final marking; any other value means the run was truncated and the marking is partial. A consumer that
     * treats completion as proof the run finished — a durable checkpoint, a workflow step, an
     * assertion on the final marking — must consult this.
     *
     * @return the reason, or {@link TerminationReason#RUNNING} before the first run completes
     */
    TerminationReason terminationReason();

    /**
     * Captures a point-in-time snapshot of the marking together with whether work was in
     * flight at that same instant, per <b>ENV-014</b>.
     *
     * <p>The marking is the snapshot form of [CORE-073] — what
     * {@code Builder.restore(...)} takes back. Consult
     * {@link SnapshotResult#isRestorePoint()} before persisting it as a checkpoint: a snapshot
     * taken while an action is in flight, or while an accepted external event has not yet been
     * injected, is a valid observation but drops tokens when restored.
     *
     * <p><b>Implementers.</b> Abstract, like {@link #terminationReason()}: a wrapper that
     * answered with a default could only lie about one of the two facts this returns. A
     * third-party implementation of this interface must add it.
     *
     * @return the marking and the in-flight observation, taken together
     * @throws IllegalStateException if the executor has been drained or closed (AC#4), or if
     *         the net declares two places with one name, which the name-keyed snapshot form
     *         cannot tell apart ([MOD-024])
     */
    SnapshotResult snapshot();

    boolean isQuiescent();

    boolean isWaitingForCompletion();

    int inFlightCount();

    int enabledCount();

    String executionId();

    /**
     * Initiates graceful shutdown per [ENV-011].
     *
     * <p>After this call, new {@code inject()} calls are rejected (return {@code false}).
     * Already-queued external events are processed normally. In-flight actions complete.
     * The executor terminates when quiescent.
     *
     * <p>For executors without environment places this is a no-op since the
     * executor already terminates at quiescence.
     */
    void drain();

    /**
     * Initiates immediate shutdown per [ENV-013].
     *
     * <p>After this call, new {@code inject()} calls are rejected. Queued external
     * events are discarded (completed with {@code false}). In-flight actions are
     * allowed to complete. The executor terminates after in-flight completion.
     *
     * <p>Calling {@code close()} after {@code drain()} escalates from graceful
     * to immediate shutdown.
     */
    @Override
    void close();
}
