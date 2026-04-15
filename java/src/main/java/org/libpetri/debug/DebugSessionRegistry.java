package org.libpetri.debug;

import java.lang.System.Logger;
import java.lang.System.Logger.Level;
import java.time.Duration;
import java.time.Instant;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
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
 *   <li>Completion listener notification for archival</li>
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
 * @see SessionCompletionListener
 */
public class DebugSessionRegistry {

    private static final Logger LOG = System.getLogger(DebugSessionRegistry.class.getName());

    private final ConcurrentHashMap<String, DebugSession> sessions = new ConcurrentHashMap<>();
    private final int maxSessions;
    private final EventStoreFactory eventStoreFactory;
    private final List<SessionCompletionListener> completionListeners;

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
        this(maxSessions, eventStoreFactory, List.of());
    }

    /**
     * Creates a registry with the specified maximum session count, custom event store factory,
     * and completion listeners.
     *
     * @param maxSessions maximum number of sessions to retain
     * @param eventStoreFactory factory for creating event stores per session
     * @param completionListeners listeners to notify when sessions complete
     */
    public DebugSessionRegistry(int maxSessions, EventStoreFactory eventStoreFactory,
                                List<SessionCompletionListener> completionListeners) {
        this.maxSessions = maxSessions;
        this.eventStoreFactory = eventStoreFactory;
        this.completionListeners = List.copyOf(completionListeners);
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
        return register(sessionId, net, Map.of());
    }

    /**
     * Registers a new debug session with user-defined tags.
     *
     * <p>Tags are arbitrary {@code Map<String,String>} attributes attached to the session
     * (e.g., {@code channel=voice}, {@code env=staging}). They can be used to filter
     * sessions via {@link #listSessions(int, Map)} and are exposed in
     * {@link SessionSummary#tags()}.
     *
     * @param sessionId unique identifier for the session
     * @param net the Petri net being executed
     * @param tags initial tags for the session (may be empty, not null)
     * @return the created debug session
     */
    public DebugSession register(String sessionId, PetriNet net, Map<String, String> tags) {
        // Generate DOT diagram
        String dotDiagram = DotExporter.export(net, ExportConfig.minimal());

        // Extract place information
        var places = PlaceAnalysis.from(net);

        // Create debug event store via factory
        var eventStore = eventStoreFactory.create(sessionId);

        // Create session record. Tags live on the session itself so their lifetime
        // is bound to the session object — no parallel map, no cleanup coordination.
        var session = new DebugSession(
            sessionId,
            net.name(),
            dotDiagram,
            places,
            net.transitions(),
            eventStore,
            Instant.now(),
            true,
            null,
            null,
            tagStorage(tags)
        );

        // Evict old sessions if needed
        evictIfNecessary();

        sessions.put(sessionId, session);
        return session;
    }

    private static ConcurrentHashMap<String, String> tagStorage(Map<String, String> initial) {
        return initial == null || initial.isEmpty()
            ? new ConcurrentHashMap<>()
            : new ConcurrentHashMap<>(initial);
    }

    /**
     * Marks a session as completed (no longer active) and notifies completion listeners.
     *
     * <p>Stamps {@code endTime = Instant.now()} on the session when transitioning from
     * active to inactive. If the session is already inactive, the existing {@code endTime}
     * is preserved (idempotent).
     *
     * <p>Listeners are notified <em>after</em> the session is marked inactive, outside
     * the ConcurrentHashMap lock to avoid holding the lock during potentially slow operations.
     *
     * @param sessionId the session to complete
     */
    public void complete(String sessionId) {
        var completedSession = new DebugSession[1];
        sessions.computeIfPresent(sessionId, (id, session) -> {
            // Preserve existing endTime if already completed; stamp now on first completion.
            // Tags CHM is reused by reference so any in-flight tag() on the old record still
            // reaches the same storage.
            var endTime = session.endTime() != null ? session.endTime() : Instant.now();
            var completed = new DebugSession(
                session.sessionId(),
                session.netName(),
                session.dotDiagram(),
                session.places(),
                session.transitions(),
                session.eventStore(),
                session.startTime(),
                false,
                session.importedStructure(),
                endTime,
                session.tags()
            );
            completedSession[0] = completed;
            return completed;
        });
        if (completedSession[0] != null) {
            notifyCompletionListeners(completedSession[0]);
        }
    }

    /**
     * Removes a session from the registry. Tags die with the session.
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
     * Sets or overwrites a single tag on a session.
     *
     * <p>Tags accumulate until the session is removed. Setting a key that already exists
     * replaces its value. This method is idempotent and thread-safe.
     *
     * <p>If {@code sessionId} does not correspond to a registered session the call is a
     * no-op. Any tag write that races with {@link #remove(String)} is harmless: the write
     * lands on the now-orphaned session object and is garbage collected alongside it.
     *
     * @param sessionId the session to tag
     * @param key tag key (non-null)
     * @param value tag value (non-null)
     */
    public void tag(String sessionId, String key, String value) {
        Objects.requireNonNull(sessionId, "sessionId");
        Objects.requireNonNull(key, "key");
        Objects.requireNonNull(value, "value");
        var session = sessions.get(sessionId);
        if (session == null) {
            LOG.log(Level.DEBUG, () -> "tag(" + sessionId + ", " + key + ") ignored: session not registered");
            return;
        }
        session.tags().put(key, value);
    }

    /**
     * Returns a snapshot of the tags attached to a session.
     *
     * @param sessionId the session id
     * @return immutable tag map, or {@code Map.of()} if the session has no tags or does not exist
     */
    public Map<String, String> tagsFor(String sessionId) {
        var session = sessions.get(sessionId);
        return session == null ? Map.of() : Map.copyOf(session.tags());
    }

    /**
     * Builds a wire-facing {@link DebugResponse.SessionSummary} for the given session,
     * including tags and computed duration.
     *
     * <p>This is the single source of truth for session summaries. Protocol handlers and
     * MCP tools should call this rather than constructing summaries by hand.
     *
     * @param session the session to summarize
     * @return summary including tags, ISO-8601 endTime, and durationMs
     */
    public DebugResponse.SessionSummary summaryOf(DebugSession session) {
        return new DebugResponse.SessionSummary(
            session.sessionId(),
            session.netName(),
            session.startTime().toString(),
            session.active(),
            session.eventStore().eventCount(),
            tagsFor(session.sessionId()),
            session.endTime() != null ? session.endTime().toString() : null,
            session.duration().map(Duration::toMillis).orElse(null)
        );
    }

    /**
     * Returns true if the session's tags match every entry in {@code filter} (AND semantics).
     * An empty filter matches all sessions. Iterates the live CHM — no defensive copy.
     */
    private boolean matchesTagFilter(DebugSession session, Map<String, String> filter) {
        if (filter == null || filter.isEmpty()) {
            return true;
        }
        var tags = session.tags();
        for (var entry : filter.entrySet()) {
            if (!entry.getValue().equals(tags.get(entry.getKey()))) {
                return false;
            }
        }
        return true;
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
        return listSessions(limit, Map.of());
    }

    /**
     * Lists sessions matching the given tag filter, ordered by start time (most recent first).
     *
     * <p>The filter uses AND semantics: a session is included only if every entry in
     * {@code tagFilter} matches one of its tags exactly. Empty or null filter matches all.
     *
     * @param limit maximum number of sessions to return
     * @param tagFilter tag key/value pairs required to match (empty for no filter)
     * @return list of sessions
     */
    public List<DebugSession> listSessions(int limit, Map<String, String> tagFilter) {
        return sessions.values().stream()
            .filter(s -> matchesTagFilter(s, tagFilter))
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
        return listActiveSessions(limit, Map.of());
    }

    /**
     * Lists active sessions matching the given tag filter.
     *
     * @param limit maximum number of sessions to return
     * @param tagFilter tag key/value pairs required to match (empty for no filter)
     * @return list of active sessions
     */
    public List<DebugSession> listActiveSessions(int limit, Map<String, String> tagFilter) {
        return sessions.values().stream()
            .filter(DebugSession::active)
            .filter(s -> matchesTagFilter(s, tagFilter))
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
     * Registers an imported (archived) session as an inactive, read-only session.
     *
     * <p>Imported sessions have a pre-built {@link DebugResponse.NetStructure} instead of
     * live {@link PlaceAnalysis} and {@link Transition} sets, since the original
     * Petri net object is not available.
     *
     * @param sessionId unique identifier
     * @param netName name of the Petri net
     * @param dotDiagram DOT diagram source
     * @param structure pre-built net structure
     * @param eventStore populated event store
     * @param startTime when the original session started
     * @return the registered session
     */
    public DebugSession registerImported(String sessionId, String netName, String dotDiagram,
                                         DebugResponse.NetStructure structure, DebugEventStore eventStore,
                                         Instant startTime) {
        return registerImported(sessionId, netName, dotDiagram, structure, eventStore,
            startTime, null, Map.of());
    }

    /**
     * Registers an imported (archived) session with tags and endTime.
     *
     * @param sessionId unique identifier
     * @param netName name of the Petri net
     * @param dotDiagram DOT diagram source
     * @param structure pre-built net structure
     * @param eventStore populated event store
     * @param startTime when the original session started
     * @param endTime when the original session ended (nullable)
     * @param tags tags attached to the imported session (may be empty)
     * @return the registered session
     */
    public DebugSession registerImported(String sessionId, String netName, String dotDiagram,
                                         DebugResponse.NetStructure structure, DebugEventStore eventStore,
                                         Instant startTime, Instant endTime, Map<String, String> tags) {
        evictIfNecessary();

        var session = new DebugSession(
            sessionId,
            netName,
            dotDiagram,
            null,  // no live place analysis for imported sessions
            Set.of(),  // no live transitions for imported sessions
            eventStore,
            startTime,
            false,  // imported sessions are always inactive
            structure,
            endTime,
            tagStorage(tags)
        );

        sessions.put(sessionId, session);
        return session;
    }

    /**
     * Notifies all completion listeners. Exceptions are caught and logged.
     */
    private void notifyCompletionListeners(DebugSession session) {
        for (var listener : completionListeners) {
            try {
                listener.onSessionCompleted(session);
            } catch (Exception e) {
                LOG.log(Level.WARNING, "Session completion listener failed for " + session.sessionId(), e);
            }
        }
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
            var evictedId = candidates.next().sessionId();
            var evicted = sessions.remove(evictedId);
            if (evicted != null) {
                cleanupEventStore(evicted.eventStore());
            }
        }
    }

    /**
     * Cleans up resources associated with an event store.
     */
    private void cleanupEventStore(DebugEventStore eventStore) {
        eventStore.close();
    }

    /**
     * Represents a debug session for a Petri net execution.
     *
     * @param sessionId unique identifier
     * @param netName name of the Petri net
     * @param dotDiagram DOT (Graphviz) diagram of the net
     * @param places analyzed place information for the net (null for imported sessions)
     * @param transitions set of transitions in the net (empty for imported sessions)
     * @param eventStore the event store for this session
     * @param startTime when the session started
     * @param active whether the session is still running
     * @param importedStructure pre-built net structure for imported sessions (null for live sessions)
     * @param endTime when the session ended (null while active; stamped on first {@code complete()})
     * @param tags per-session tag storage — always non-null, thread-safe; prefer
     *        {@link DebugSessionRegistry#tag(String, String, String)} / {@link DebugSessionRegistry#tagsFor(String)}
     */
    public record DebugSession(
        String sessionId,
        String netName,
        String dotDiagram,
        PlaceAnalysis places,
        java.util.Set<Transition> transitions,
        DebugEventStore eventStore,
        Instant startTime,
        boolean active,
        DebugResponse.NetStructure importedStructure,
        Instant endTime,
        ConcurrentHashMap<String, String> tags
    ) {
        /**
         * Returns the session duration (startTime → endTime) if the session has completed.
         *
         * @return duration between start and end, or empty for active sessions
         */
        public Optional<Duration> duration() {
            return endTime != null ? Optional.of(Duration.between(startTime, endTime)) : Optional.empty();
        }

        /**
         * Builds the net structure from this session's stored place and transition info.
         * For imported sessions, returns the pre-built structure directly.
         *
         * @return the net structure for debug protocol responses
         */
        public DebugResponse.NetStructure buildNetStructure() {
            if (importedStructure != null) {
                return importedStructure;
            }

            var placeInfos = places.data().entrySet().stream()
                .map(entry -> {
                    var name = entry.getKey();
                    var info = entry.getValue();
                    var sanitized = DotExporter.sanitize(name);
                    return new DebugResponse.PlaceInfo(
                        name,
                        "p_" + sanitized,
                        info.tokenType(),
                        info.isStart(),
                        info.isEnd(),
                        false  // isEnvironment - not tracked at session level yet
                    );
                })
                .toList();

            var transitionInfos = transitions.stream()
                .map(t -> {
                    var graphId = "t_" + DotExporter.sanitize(t.name());
                    return new DebugResponse.TransitionInfo(
                        t.name(),
                        graphId
                    );
                })
                .toList();

            return new DebugResponse.NetStructure(placeInfos, transitionInfos);
        }
    }
}
