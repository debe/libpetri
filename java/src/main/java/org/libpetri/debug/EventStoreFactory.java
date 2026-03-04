package org.libpetri.debug;

/**
 * Factory for creating {@link DebugEventStore} instances.
 *
 * <p>Allows pluggable event store implementations. For example, the default
 * creates in-memory stores, while an MMap-backed factory creates file-persistent stores.
 *
 * @see DebugSessionRegistry
 */
@FunctionalInterface
public interface EventStoreFactory {

    /**
     * Creates a new event store for the given session.
     *
     * @param sessionId the debug session identifier
     * @return a new DebugEventStore instance
     */
    DebugEventStore create(String sessionId);
}
