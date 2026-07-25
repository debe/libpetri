package org.libpetri.runtime;

import java.time.Duration;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionStage;

import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.Token;

/**
 * Common interface for Petri net executors.
 *
 * <p>Both {@link NetExecutor} and {@link BitmapNetExecutor} implement this
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
