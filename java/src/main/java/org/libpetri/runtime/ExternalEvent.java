package org.libpetri.runtime;

import java.util.concurrent.CompletableFuture;

import org.libpetri.core.Place;
import org.libpetri.core.Token;

/**
 * An external event queued for injection into the net.
 *
 * <p>External events are created when {@link NetExecutor#inject} is called
 * from an external thread. They are queued and processed by the orchestrator
 * thread on the next loop iteration.
 *
 * @param <T> token value type
 * @param place target place (must be an environment place)
 * @param token token to inject
 * @param resultFuture completes with true when injection is processed, false if executor closed
 */
record ExternalEvent<T>(
    Place<T> place,
    Token<T> token,
    CompletableFuture<Boolean> resultFuture
) {}
