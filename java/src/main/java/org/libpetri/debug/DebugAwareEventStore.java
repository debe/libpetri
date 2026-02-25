package org.libpetri.debug;

import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;

import java.util.List;

/**
 * EventStore that delegates to both a primary store and a debug store.
 *
 * <p>This allows events to be captured for both production use (e.g., tracing)
 * and debug visualization simultaneously.
 */
public class DebugAwareEventStore implements EventStore {

    private final EventStore primary;
    private final DebugEventStore debugStore;

    /**
     * Creates a debug-aware event store.
     *
     * @param primary the primary event store (e.g., TracingEventStore)
     * @param debugStore the debug event store for visualization
     */
    public DebugAwareEventStore(EventStore primary, DebugEventStore debugStore) {
        this.primary = primary;
        this.debugStore = debugStore;
    }

    @Override
    public void append(NetEvent event) {
        primary.append(event);
        try { debugStore.append(event); }
        catch (Exception _) { /* debug failures must not break production */ }
    }

    @Override
    public List<NetEvent> events() {
        // Return from primary store (debug store has same events)
        return primary.events();
    }

    @Override
    public boolean isEnabled() {
        return true;
    }

    @Override
    public int size() {
        return primary.size();
    }

    @Override
    public boolean isEmpty() {
        return primary.isEmpty();
    }

    /**
     * Returns the underlying debug store for subscription management.
     *
     * @return the debug event store
     */
    public DebugEventStore debugStore() {
        return debugStore;
    }
}
