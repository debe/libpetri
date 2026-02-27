package org.libpetri.debug;

import com.fasterxml.jackson.annotation.JsonSubTypes;
import com.fasterxml.jackson.annotation.JsonTypeInfo;

import java.util.List;
import java.util.Map;

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
 * {"type": "subscribed", "sessionId": "abc-123", "mermaidDiagram": "...", ...}
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
    @JsonSubTypes.Type(value = DebugResponse.Error.class, name = "error")
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
     * @param sessionId the subscribed session
     * @param netName the Petri net name
     * @param dotDiagram DOT (Graphviz) diagram of the net
     * @param mermaidDiagram Mermaid diagram of the net (deprecated, use dotDiagram)
     * @param structure explicit net topology with authoritative name-to-graphId mappings
     * @param currentMarking current token distribution
     * @param enabledTransitions currently enabled transitions
     * @param inFlightTransitions currently executing transitions (started but not yet completed/failed/timed out)
     * @param eventCount total events in session
     * @param mode subscription mode (live or replay)
     */
    record Subscribed(
        String sessionId,
        String netName,
        String dotDiagram,
        String mermaidDiagram,
        NetStructure structure,
        Map<String, List<TokenInfo>> currentMarking,
        List<String> enabledTransitions,
        List<String> inFlightTransitions,
        long eventCount,
        String mode
    ) implements DebugResponse {}

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

    // ======================== Supporting Types ========================

    /**
     * Summary of a debug session for listing.
     *
     * @param sessionId unique identifier
     * @param netName name of the Petri net
     * @param startTime when the session started (ISO-8601 format)
     * @param active whether the session is still running
     * @param eventCount number of events captured
     */
    record SessionSummary(
        String sessionId,
        String netName,
        String startTime,
        boolean active,
        long eventCount
    ) {}

    /**
     * Token information for display.
     *
     * @param id unique token ID (if available)
     * @param type token value type name
     * @param value full string representation of token value
     * @param timestamp when token was created (ISO-8601 format)
     */
    record TokenInfo(
        String id,
        String type,
        String value,
        String timestamp
    ) {}

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
     * @param name authoritative identifier (matches events/marking keys)
     * @param graphId sanitized ID with "p_" prefix (matches DOT/SVG node IDs)
     * @param mermaidId sanitized ID used in Mermaid SVG (deprecated, use graphId)
     * @param tokenType simple name of the token type for this place
     * @param isStart true if this is a start place (no incoming arcs)
     * @param isEnd true if this is an end place (no outgoing arcs)
     * @param isEnvironment true if this is an environment place (external event injection)
     */
    record PlaceInfo(
        String name,
        String graphId,
        String mermaidId,
        String tokenType,
        boolean isStart,
        boolean isEnd,
        boolean isEnvironment
    ) {}

    /**
     * Information about a transition in the Petri net.
     *
     * @param name authoritative identifier (matches events)
     * @param graphId sanitized ID with "t_" prefix (matches DOT/SVG node IDs)
     * @param mermaidId sanitized ID with "t_" prefix (deprecated, use graphId)
     */
    record TransitionInfo(
        String name,
        String graphId,
        String mermaidId
    ) {}
}
