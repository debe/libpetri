package org.libpetri.runtime;

import org.libpetri.core.Transition;

/**
 * Out-of-band sink for a transition-action failure, configured via
 * {@code Builder.uncaughtActionHandler(...)} on any executor.
 *
 * <p>A failing action destroys the tokens it consumed (EXEC-031, no rollback). That loss is
 * normally reported as a {@code TransitionFailed} event, but the default {@code EventStore.noop()}
 * discards it, so without a handler the failure can be entirely silent. This interface is the
 * escape hatch: a configured handler is <em>always</em> invoked with the failing transition and the
 * unwrapped cause; with no handler configured, libpetri logs at WARNING when — and only when — no
 * event store actually recorded the failure.
 *
 * <p>The handler runs on the orchestrator thread, inside the executor's failure path. It MUST NOT
 * block or touch the marking. A handler that throws is swallowed (and logged) rather than allowed
 * to stop the orchestrator — reporting a failure must not become the failure that kills the net.
 *
 * <p>Named (rather than a raw {@code BiConsumer}) to match libpetri's pluggable-behaviour idiom
 * ({@link org.libpetri.core.TransitionAction}, {@link org.libpetri.event.EventStore}) and to leave
 * room to grow the callback's context without breaking callers.
 */
@FunctionalInterface
public interface ActionFailureHandler {

    /**
     * Invoked when {@code transition}'s action fails.
     *
     * @param transition the transition whose action failed
     * @param cause the unwrapped cause the action raised (never a {@code CompletionException} wrapper)
     */
    void onActionFailed(Transition transition, Throwable cause);
}
