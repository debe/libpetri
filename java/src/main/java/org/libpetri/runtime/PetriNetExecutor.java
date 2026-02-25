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

    @Override
    void close();
}
