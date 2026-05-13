package org.libpetri.debug;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonSubTypes;
import com.fasterxml.jackson.annotation.JsonTypeInfo;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Responses sent from server to debug UI client via WebSocket.
 *
 * <p>This sealed hierarchy represents all debug protocol responses.
 * Jackson polymorphic serialization includes a "type" field to identify
 * the response type.
 *
 * <h2>Protocol Example</h2>
 * <pre>{@code
 * // Session list
 * {"type": "sessionList", "sessions": [...]}
 *
 * // Subscribed to session
 * {"type": "subscribed", "sessionId": "abc-123", "dotDiagram": "...", ...}
 *
 * // Event received
 * {"type": "event", "sessionId": "abc-123", "event": {...}}
 * }</pre>
 */
@JsonTypeInfo(use = JsonTypeInfo.Id.NAME, property = "type")
@JsonSubTypes({
    @JsonSubTypes.Type(value = DebugResponse.SessionList.class, name = "sessionList"),
    @JsonSubTypes.Type(value = DebugResponse.Subscribed.class, name = "subscribed"),
    @JsonSubTypes.Type(value = DebugResponse.Unsubscribed.class, name = "unsubscribed"),
    @JsonSubTypes.Type(value = DebugResponse.Event.class, name = "event"),
    @JsonSubTypes.Type(value = DebugResponse.EventBatch.class, name = "eventBatch"),
    @JsonSubTypes.Type(value = DebugResponse.MarkingSnapshot.class, name = "markingSnapshot"),
    @JsonSubTypes.Type(value = DebugResponse.PlaybackStateChanged.class, name = "playbackStateChanged"),
    @JsonSubTypes.Type(value = DebugResponse.FilterApplied.class, name = "filterApplied"),
    @JsonSubTypes.Type(value = DebugResponse.BreakpointHit.class, name = "breakpointHit"),
    @JsonSubTypes.Type(value = DebugResponse.BreakpointList.class, name = "breakpointList"),
    @JsonSubTypes.Type(value = DebugResponse.BreakpointSet.class, name = "breakpointSet"),
    @JsonSubTypes.Type(value = DebugResponse.BreakpointCleared.class, name = "breakpointCleared"),
    @JsonSubTypes.Type(value = DebugResponse.Error.class, name = "error"),
    @JsonSubTypes.Type(value = DebugResponse.ArchiveList.class, name = "archiveList"),
    @JsonSubTypes.Type(value = DebugResponse.ArchiveImported.class, name = "archiveImported")
})
public sealed interface DebugResponse {

    /**
     * List of available debug sessions.
     *
     * @param sessions list of session summaries
     */
    record SessionList(List<SessionSummary> sessions) implements DebugResponse {}

    /**
     * Confirmation of subscription with initial state.
     *
     * <p>The {@code subnetInstances} field carries the post-composition
     * subnet instance descriptors per {@code spec/11-modular-composition.md}
     * <b>MOD-041</b>. For nets that were not produced via composition (no
     * {@code "/"} in any node name) the list is empty.
     *
     * @param sessionId the subscribed session
     * @param netName the Petri net name
     * @param dotDiagram DOT (Graphviz) diagram of the net
     * @param structure explicit net topology with authoritative name-to-graphId mappings
     * @param currentMarking current token distribution
     * @param enabledTransitions currently enabled transitions
     * @param inFlightTransitions currently executing transitions (started but not yet completed/failed/timed out)
     * @param eventCount total events in session
     * @param mode subscription mode (live or replay)
     * @param subnetInstances composed subnet instance descriptors (empty for flat nets); per <b>MOD-041</b>
     */
    record Subscribed(
        String sessionId,
        String netName,
        String dotDiagram,
        NetStructure structure,
        Map<String, List<TokenInfo>> currentMarking,
        List<String> enabledTransitions,
        List<String> inFlightTransitions,
        long eventCount,
        String mode,
        List<SubnetInstanceInfo> subnetInstances
    ) implements DebugResponse {
        /**
         * Backwards-compatible constructor used by older call sites that
         * pre-date the {@code subnetInstances} field. Always passes an empty
         * list so wire shape stays stable for non-composed nets.
         */
        public Subscribed(
            String sessionId,
            String netName,
            String dotDiagram,
            NetStructure structure,
            Map<String, List<TokenInfo>> currentMarking,
            List<String> enabledTransitions,
            List<String> inFlightTransitions,
            long eventCount,
            String mode
        ) {
            this(sessionId, netName, dotDiagram, structure, currentMarking,
                enabledTransitions, inFlightTransitions, eventCount, mode, List.of());
        }
    }

    /**
     * Confirmation of unsubscription.
     *
     * @param sessionId the unsubscribed session
     */
    record Unsubscribed(String sessionId) implements DebugResponse {}

    /**
     * Single event notification.
     *
     * @param sessionId the session this event belongs to
     * @param index event index in the session
     * @param event the event data
     */
    record Event(
        String sessionId,
        long index,
        NetEventInfo event
    ) implements DebugResponse {}

    /**
     * Batch of events (for replay catch-up).
     *
     * @param sessionId the session these events belong to
     * @param startIndex index of first event in batch
     * @param events list of events
     * @param hasMore true if more events available
     */
    record EventBatch(
        String sessionId,
        long startIndex,
        List<NetEventInfo> events,
        boolean hasMore
    ) implements DebugResponse {}

    /**
     * Complete marking snapshot.
     *
     * @param sessionId the session this marking belongs to
     * @param marking map of place names to tokens
     * @param enabledTransitions currently enabled transitions
     * @param inFlightTransitions currently firing transitions
     */
    record MarkingSnapshot(
        String sessionId,
        Map<String, List<TokenInfo>> marking,
        List<String> enabledTransitions,
        List<String> inFlightTransitions
    ) implements DebugResponse {}

    /**
     * Playback state changed (pause/resume/speed).
     *
     * @param sessionId the session
     * @param paused whether playback is paused
     * @param speed current playback speed
     * @param currentIndex current event index
     */
    record PlaybackStateChanged(
        String sessionId,
        boolean paused,
        double speed,
        long currentIndex
    ) implements DebugResponse {}

    /**
     * Filter applied confirmation.
     *
     * @param sessionId the session the filter applies to
     * @param filter the applied filter configuration
     */
    record FilterApplied(
        String sessionId,
        DebugCommand.EventFilter filter
    ) implements DebugResponse {}

    /**
     * Breakpoint was hit - execution paused.
     *
     * @param sessionId the session where the breakpoint was hit
     * @param breakpointId the ID of the breakpoint that was hit
     * @param event the event that triggered the breakpoint
     * @param eventIndex the index of the event
     */
    record BreakpointHit(
        String sessionId,
        String breakpointId,
        NetEventInfo event,
        long eventIndex
    ) implements DebugResponse {}

    /**
     * List of breakpoints for a session.
     *
     * @param sessionId the session
     * @param breakpoints the list of breakpoints
     */
    record BreakpointList(
        String sessionId,
        List<DebugCommand.BreakpointConfig> breakpoints
    ) implements DebugResponse {}

    /**
     * Confirmation that a breakpoint was set.
     *
     * @param sessionId the session
     * @param breakpoint the breakpoint that was set
     */
    record BreakpointSet(
        String sessionId,
        DebugCommand.BreakpointConfig breakpoint
    ) implements DebugResponse {}

    /**
     * Confirmation that a breakpoint was cleared.
     *
     * @param sessionId the session
     * @param breakpointId the ID of the cleared breakpoint
     */
    record BreakpointCleared(
        String sessionId,
        String breakpointId
    ) implements DebugResponse {}

    /**
     * Error response.
     *
     * @param code error code
     * @param message human-readable error message
     * @param sessionId related session if applicable
     */
    record Error(
        String code,
        String message,
        String sessionId
    ) implements DebugResponse {}

    /**
     * List of available session archives.
     *
     * @param archives list of archive summaries
     * @param storageAvailable whether archive storage is configured
     */
    record ArchiveList(List<ArchiveSummary> archives, boolean storageAvailable) implements DebugResponse {}

    /**
     * Confirmation that an archive was imported.
     *
     * @param sessionId the imported session ID
     * @param netName the Petri net name
     * @param eventCount number of events imported
     */
    record ArchiveImported(String sessionId, String netName, long eventCount) implements DebugResponse {}

    /**
     * Summary of an archived session.
     *
     * @param sessionId the session identifier
     * @param key the storage key/path
     * @param sizeBytes file size in bytes
     * @param lastModified when the archive was last modified (ISO-8601)
     */
    record ArchiveSummary(String sessionId, String key, long sizeBytes, String lastModified) {}

    // ======================== Supporting Types ========================

    /**
     * Summary of a debug session for listing.
     *
     * <p>{@code tags}, {@code endTime}, and {@code durationMs} were added in libpetri 1.6.0.
     * Older clients that receive additional fields will ignore them (Jackson tolerance).
     *
     * @param sessionId unique identifier
     * @param netName name of the Petri net
     * @param startTime when the session started (ISO-8601 format)
     * @param active whether the session is still running
     * @param eventCount number of events captured
     * @param tags user-defined session tags (empty map if none)
     * @param endTime when the session ended (ISO-8601), null while active
     * @param durationMs session duration in milliseconds, null while active
     */
    @JsonInclude(JsonInclude.Include.NON_NULL)
    record SessionSummary(
        String sessionId,
        String netName,
        String startTime,
        boolean active,
        long eventCount,
        @JsonInclude(JsonInclude.Include.NON_EMPTY) Map<String, String> tags,
        String endTime,
        Long durationMs
    ) {}

    /**
     * Token information for display and downstream consumption.
     *
     * @param id unique token ID (if available)
     * @param type token value type simple name (display-friendly, LLM-budget-conscious)
     * @param value full {@code toString()} of the token value — stable display field that
     *     the bundled debug UI relies on; always populated unless {@code compact} mode
     *     strips values explicitly
     * @param structured structured JSON representation of the token value when Jackson
     *     can serialize it, else {@code null}. Populated in addition to {@code value} so
     *     LLM-facing MCP tools can surface typed fields (e.g. a {@code ClientMessage}'s
     *     {@code message} field) without parsing the toString string. Omitted from the
     *     wire when null via {@code @JsonInclude(NON_NULL)} at the consumer side
     * @param timestamp when token was created (ISO-8601 format)
     */
    record TokenInfo(
        String id,
        String type,
        String value,
        Object structured,
        String timestamp
    ) {
        /**
         * Backwards-compatible convenience constructor used by callers that only produce the
         * display-form token info (no structured payload). Keeps {@link org.libpetri.debug.DebugProtocolHandler}
         * and other legacy callers compiling unchanged.
         */
        public TokenInfo(String id, String type, String value, String timestamp) {
            this(id, type, value, null, timestamp);
        }
    }

    /**
     * Serializable representation of NetEvent.
     *
     * @param type event type name
     * @param timestamp when the event occurred (ISO-8601 format)
     * @param transitionName transition name (if applicable)
     * @param placeName place name (if applicable)
     * @param details additional event details
     */
    record NetEventInfo(
        String type,
        String timestamp,
        String transitionName,
        String placeName,
        Map<String, Object> details
    ) {}

    // ======================== Net Structure Types ========================

    /**
     * Explicit Petri net structure with authoritative name-to-graphId mappings.
     *
     * <p>This provides the frontend with a reliable mapping between the authoritative
     * place/transition names (used in events and marking) and the sanitized IDs used
     * in the DOT/SVG output. This eliminates fragile SVG ID parsing in the frontend.
     *
     * @param places list of places in the net
     * @param transitions list of transitions in the net
     */
    record NetStructure(
        List<PlaceInfo> places,
        List<TransitionInfo> transitions
    ) {}

    /**
     * Information about a place in the Petri net.
     *
     * <p>The {@code instancePrefix} field is derived from the place's name
     * per {@code spec/11-modular-composition.md} <b>MOD-041</b>: it is the
     * substring before the last {@code "/"}, or {@code null} for flat
     * names. Jackson serializes the {@code null} field as omitted via
     * {@code @JsonInclude(NON_NULL)} so flat-net payloads stay compact and
     * the wire shape pre-MOD-041 is preserved for non-composed nets. Use
     * {@link #instancePrefix()} to retrieve the field as an
     * {@link Optional} when reading from Java.
     *
     * @param name authoritative identifier (matches events/marking keys)
     * @param graphId sanitized ID with "p_" prefix (matches DOT/SVG node IDs)
     * @param tokenType simple name of the token type for this place
     * @param isStart true if this is a start place (no incoming arcs)
     * @param isEnd true if this is an end place (no outgoing arcs)
     * @param isEnvironment true if this is an environment place (external event injection)
     * @param instancePrefixOrNull nullable instance prefix; per <b>MOD-041</b>
     */
    record PlaceInfo(
        String name,
        String graphId,
        String tokenType,
        boolean isStart,
        boolean isEnd,
        boolean isEnvironment,
        @JsonInclude(JsonInclude.Include.NON_NULL)
        @com.fasterxml.jackson.annotation.JsonProperty("instancePrefix")
        String instancePrefixOrNull
    ) {
        /**
         * Backwards-compatible constructor used by call sites that pre-date
         * MOD-041. Sets {@code instancePrefix} to absent (null on the wire).
         */
        public PlaceInfo(String name, String graphId, String tokenType,
                         boolean isStart, boolean isEnd, boolean isEnvironment) {
            this(name, graphId, tokenType, isStart, isEnd, isEnvironment, (String) null);
        }

        /**
         * Convenience constructor that accepts an {@link Optional} for
         * call sites that already work with the optional API shape.
         */
        public PlaceInfo(String name, String graphId, String tokenType,
                         boolean isStart, boolean isEnd, boolean isEnvironment,
                         Optional<String> instancePrefix) {
            this(name, graphId, tokenType, isStart, isEnd, isEnvironment,
                instancePrefix == null ? null : instancePrefix.orElse(null));
        }

        /** Returns the derived instance prefix per [MOD-041] as an {@link Optional}. */
        @com.fasterxml.jackson.annotation.JsonIgnore
        public Optional<String> instancePrefix() {
            return Optional.ofNullable(instancePrefixOrNull);
        }
    }

    /**
     * Information about a transition in the Petri net.
     *
     * @param name authoritative identifier (matches events)
     * @param graphId sanitized ID with "t_" prefix (matches DOT/SVG node IDs)
     * @param instancePrefixOrNull nullable instance prefix; per <b>MOD-041</b>
     */
    record TransitionInfo(
        String name,
        String graphId,
        @JsonInclude(JsonInclude.Include.NON_NULL)
        @com.fasterxml.jackson.annotation.JsonProperty("instancePrefix")
        String instancePrefixOrNull
    ) {
        public TransitionInfo(String name, String graphId) {
            this(name, graphId, (String) null);
        }

        public TransitionInfo(String name, String graphId, Optional<String> instancePrefix) {
            this(name, graphId, instancePrefix == null ? null : instancePrefix.orElse(null));
        }

        /** Returns the derived instance prefix per [MOD-041] as an {@link Optional}. */
        @com.fasterxml.jackson.annotation.JsonIgnore
        public Optional<String> instancePrefix() {
            return Optional.ofNullable(instancePrefixOrNull);
        }
    }

    /**
     * Wire-facing descriptor of one composed subnet instance per
     * {@code spec/11-modular-composition.md} <b>MOD-041</b>.
     *
     * <p>This mirrors {@link org.libpetri.core.SubnetInstance} but carries
     * <b>names</b> instead of object references, so that JSON serialization
     * stays simple (sets of strings rather than recursively-serialized
     * Place/Transition records). {@code parentPrefix} is null on the wire
     * for top-level instances and serialized via {@code @JsonInclude(NON_NULL)}
     * to keep flat-shape payloads compact.
     *
     * @param prefix the instantiation prefix (e.g. {@code "buf1"} or
     *               {@code "outer/inner"} for nested instances)
     * @param defName originating subnet definition name, or {@code null}
     *                when not derivable from name shape alone
     * @param transitionNames full prefixed transition names belonging to this instance
     * @param exposedPlaceNames full prefixed place names belonging to this instance
     * @param parentPrefixOrNull nullable parent-instance prefix; null for top-level
     */
    record SubnetInstanceInfo(
        String prefix,
        @JsonInclude(JsonInclude.Include.NON_NULL) String defName,
        Set<String> transitionNames,
        Set<String> exposedPlaceNames,
        @JsonInclude(JsonInclude.Include.NON_NULL)
        @com.fasterxml.jackson.annotation.JsonProperty("parentPrefix")
        String parentPrefixOrNull
    ) {
        public SubnetInstanceInfo {
            transitionNames = Set.copyOf(transitionNames);
            exposedPlaceNames = Set.copyOf(exposedPlaceNames);
        }

        /**
         * Convenience constructor accepting an {@link Optional} for the
         * {@code parentPrefix} field — call sites that already work with the
         * optional shape can pass it directly.
         */
        public SubnetInstanceInfo(String prefix, String defName,
                                  Set<String> transitionNames, Set<String> exposedPlaceNames,
                                  Optional<String> parentPrefix) {
            this(prefix, defName, transitionNames, exposedPlaceNames,
                parentPrefix == null ? null : parentPrefix.orElse(null));
        }

        /** Returns the parent prefix per [MOD-041] as an {@link Optional}. */
        @com.fasterxml.jackson.annotation.JsonIgnore
        public Optional<String> parentPrefix() {
            return Optional.ofNullable(parentPrefixOrNull);
        }
    }
}
