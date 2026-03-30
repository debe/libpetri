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

    Marking run();

    CompletionStage<Marking> run(Duration timeout);

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
