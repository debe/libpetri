package org.libpetri.debug;

/**
 * Listener notified when a debug session completes.
 *
 * <p>Register listeners via the {@link DebugSessionRegistry} constructor to receive
 * callbacks when sessions transition from active to completed state.
 *
 * @see DebugSessionRegistry
 */
@FunctionalInterface
public interface SessionCompletionListener {

    /**
     * Called when a session is marked as completed.
     *
     * <p>Implementations should be fast and non-blocking. Exceptions are caught and
     * logged by the registry — a failing listener does not affect other listeners.
     *
     * @param session the completed session
     */
    void onSessionCompleted(DebugSessionRegistry.DebugSession session);
}
