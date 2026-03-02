package org.libpetri.debug;

import java.io.IOException;
import java.lang.System.Logger;
import java.lang.System.Logger.Level;
import java.nio.file.Files;
import java.time.Instant;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;

import org.libpetri.core.PetriNet;
import org.libpetri.core.Transition;
import org.libpetri.export.DotExporter;
import org.libpetri.export.ExportConfig;
import org.libpetri.export.PlaceAnalysis;

/**
 * Registry for managing Petri net debug sessions.
 *
 * <p>This registry maintains active and historical debug sessions, enabling:
 * <ul>
 *   <li>Session discovery for debugging tools</li>
 *   <li>Session lifecycle management</li>
 *   <li>DOT diagram generation and caching</li>
 * </ul>
 *
 * <h2>Usage Example</h2>
 * <pre>{@code
 * var registry = new DebugSessionRegistry();
 *
 * // Register a new session when NetExecutor starts
 * var session = registry.register("session-123", net);
 *
 * // List active sessions
 * var sessions = registry.listSessions(10);
 *
 * // Get session details
 * registry.getSession("session-123").ifPresent(s -> {
 *     System.out.println("DOT: " + s.dotDiagram());
 * });
 *
 * // Mark session as completed
 * registry.complete("session-123");
 * }</pre>
 *
 * <h2>Thread Safety</h2>
 * <p>All methods are thread-safe, using {@link ConcurrentHashMap} for storage.
 *
 * @see DebugEventStore
 * @see DebugSession
 */
public class DebugSessionRegistry {

    private static final Logger LOG = System.getLogger(DebugSessionRegistry.class.getName());

    private final ConcurrentHashMap<String, DebugSession> sessions = new ConcurrentHashMap<>();
    private final int maxSessions;
    private final EventStoreFactory eventStoreFactory;

    /**
     * Creates a registry with default maximum of 50 sessions and in-memory event stores.
     */
    public DebugSessionRegistry() {
        this(50);
    }

    /**
     * Creates a registry with the specified maximum session count and in-memory event stores.
     *
     * @param maxSessions maximum number of sessions to retain
     */
    public DebugSessionRegistry(int maxSessions) {
        this(maxSessions, DebugEventStore::new);
    }

    /**
     * Creates a registry with the specified maximum session count and custom event store factory.
     *
     * @param maxSessions maximum number of sessions to retain
     * @param eventStoreFactory factory for creating event stores per session
     */
    public DebugSessionRegistry(int maxSessions, EventStoreFactory eventStoreFactory) {
        this.maxSessions = maxSessions;
        this.eventStoreFactory = eventStoreFactory;
    }

    /**
     * Registers a new debug session for the given Petri net.
     *
     * <p>Creates a {@link DebugEventStore} and generates a DOT diagram
     * for the net. Also extracts net structure (places and transitions) for
     * debug tooling. Old sessions may be evicted if the maximum is reached.
     *
     * @param sessionId unique identifier for the session
     * @param net the Petri net being executed
     * @return the created debug session
     */
    public DebugSession register(String sessionId, PetriNet net) {
        // Generate DOT diagram
        String dotDiagram = DotExporter.export(net, ExportConfig.minimal());

        // Extract place information
        var places = PlaceAnalysis.from(net);

        // Create debug event store via factory
        var eventStore = eventStoreFactory.create(sessionId);

        // Create session record
        var session = new DebugSession(
            sessionId,
            net.name(),
            dotDiagram,
            places,
            net.transitions(),
            eventStore,
            Instant.now(),
            true
        );

        // Evict old sessions if needed
        evictIfNecessary();

        sessions.put(sessionId, session);
        return session;
    }

    /**
     * Marks a session as completed (no longer active).
     *
     * @param sessionId the session to complete
     */
    public void complete(String sessionId) {
        sessions.computeIfPresent(sessionId, (id, session) ->
            new DebugSession(
                session.sessionId(),
                session.netName(),
                session.dotDiagram(),
                session.places(),
                session.transitions(),
                session.eventStore(),
                session.startTime(),
                false
            )
        );
    }

    /**
     * Removes a session from the registry.
     *
     * @param sessionId the session to remove
     * @return the removed session, or empty if not found
     */
    public Optional<DebugSession> remove(String sessionId) {
        var removed = sessions.remove(sessionId);
        if (removed != null) {
            cleanupEventStore(removed.eventStore());
        }
        return Optional.ofNullable(removed);
    }

    /**
     * Returns a session by ID.
     *
     * @param sessionId the session ID
     * @return the session, or empty if not found
     */
    public Optional<DebugSession> getSession(String sessionId) {
        return Optional.ofNullable(sessions.get(sessionId));
    }

    /**
     * Lists sessions, ordered by start time (most recent first).
     *
     * @param limit maximum number of sessions to return
     * @return list of sessions
     */
    public List<DebugSession> listSessions(int limit) {
        return sessions.values().stream()
            .sorted(Comparator.comparing(DebugSession::startTime).reversed())
            .limit(limit)
            .toList();
    }

    /**
     * Lists only active sessions.
     *
     * @param limit maximum number of sessions to return
     * @return list of active sessions
     */
    public List<DebugSession> listActiveSessions(int limit) {
        return sessions.values().stream()
            .filter(DebugSession::active)
            .sorted(Comparator.comparing(DebugSession::startTime).reversed())
            .limit(limit)
            .toList();
    }

    /**
     * Returns the total number of sessions in the registry.
     *
     * @return session count
     */
    public int size() {
        return sessions.size();
    }

    /**
     * Evicts oldest inactive sessions if at capacity.
     */
    private void evictIfNecessary() {
        if (sessions.size() < maxSessions) return;

        // Sort candidates once: inactive first (preferred for eviction), then by oldest start time
        var candidates = sessions.values().stream()
            .sorted(Comparator.<DebugSession, Boolean>comparing(DebugSession::active)
                .thenComparing(DebugSession::startTime))
            .iterator();

        while (sessions.size() >= maxSessions && candidates.hasNext()) {
            var evicted = sessions.remove(candidates.next().sessionId());
            if (evicted != null) {
                cleanupEventStore(evicted.eventStore());
            }
        }
    }

    /**
     * Cleans up resources associated with an event store.
     * Always closes the broadcast executor. For {@link MMapEventStore}, also deletes the backing file.
     */
    private void cleanupEventStore(DebugEventStore eventStore) {
        eventStore.close();
        if (eventStore instanceof MMapEventStore mmap) {
            try {
                Files.deleteIfExists(mmap.filePath());
            } catch (IOException e) {
                LOG.log(Level.WARNING, () -> "Failed to clean up MMap file: " + mmap.filePath(), e);
            }
        }
    }

    /**
     * Represents a debug session for a Petri net execution.
     *
     * @param sessionId unique identifier
     * @param netName name of the Petri net
     * @param dotDiagram DOT (Graphviz) diagram of the net
     * @param places analyzed place information for the net
     * @param transitions set of transitions in the net
     * @param eventStore the event store for this session
     * @param startTime when the session started
     * @param active whether the session is still running
     */
    public record DebugSession(
        String sessionId,
        String netName,
        String dotDiagram,
        PlaceAnalysis places,
        java.util.Set<Transition> transitions,
        DebugEventStore eventStore,
        Instant startTime,
        boolean active
    ) {
        /**
         * Returns a summary of this session for listing.
         *
         * @return session summary
         */
        public SessionSummary toSummary() {
            return new SessionSummary(
                sessionId,
                netName,
                startTime,
                active,
                eventStore.eventCount()
            );
        }
    }

    /**
     * Summary information for session listing (without full event store).
     *
     * @param sessionId unique identifier
     * @param netName name of the Petri net
     * @param startTime when the session started
     * @param active whether the session is still running
     * @param eventCount number of events captured
     */
    public record SessionSummary(
        String sessionId,
        String netName,
        Instant startTime,
        boolean active,
        long eventCount
    ) {}
}
