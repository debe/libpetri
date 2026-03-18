package org.libpetri.debug;

import com.fasterxml.jackson.annotation.JsonSubTypes;
import com.fasterxml.jackson.annotation.JsonTypeInfo;

import java.time.Instant;
import java.util.Set;

/**
 * Commands sent from debug UI client to server via WebSocket.
 *
 * <p>This sealed hierarchy represents all valid debug protocol commands.
 * Jackson polymorphic deserialization routes to the correct subtype based
 * on the "type" field.
 *
 * <h2>Protocol Example</h2>
 * <pre>{@code
 * // Subscribe to a session
 * {"type": "subscribe", "sessionId": "abc-123", "mode": "live"}
 *
 * // List available sessions
 * {"type": "listSessions"}
 *
 * // Seek to specific time
 * {"type": "seek", "sessionId": "abc-123", "timestamp": "2024-01-15T10:30:00Z"}
 * }</pre>
 */
@JsonTypeInfo(use = JsonTypeInfo.Id.NAME, property = "type")
@JsonSubTypes({
    @JsonSubTypes.Type(value = DebugCommand.Subscribe.class, name = "subscribe"),
    @JsonSubTypes.Type(value = DebugCommand.Unsubscribe.class, name = "unsubscribe"),
    @JsonSubTypes.Type(value = DebugCommand.ListSessions.class, name = "listSessions"),
    @JsonSubTypes.Type(value = DebugCommand.Seek.class, name = "seek"),
    @JsonSubTypes.Type(value = DebugCommand.PlaybackSpeed.class, name = "playbackSpeed"),
    @JsonSubTypes.Type(value = DebugCommand.SetFilter.class, name = "filter"),
    @JsonSubTypes.Type(value = DebugCommand.Pause.class, name = "pause"),
    @JsonSubTypes.Type(value = DebugCommand.Resume.class, name = "resume"),
    @JsonSubTypes.Type(value = DebugCommand.StepForward.class, name = "stepForward"),
    @JsonSubTypes.Type(value = DebugCommand.StepBackward.class, name = "stepBackward"),
    @JsonSubTypes.Type(value = DebugCommand.SetBreakpoint.class, name = "setBreakpoint"),
    @JsonSubTypes.Type(value = DebugCommand.ClearBreakpoint.class, name = "clearBreakpoint"),
    @JsonSubTypes.Type(value = DebugCommand.ListBreakpoints.class, name = "listBreakpoints"),
    @JsonSubTypes.Type(value = DebugCommand.ListArchives.class, name = "listArchives"),
    @JsonSubTypes.Type(value = DebugCommand.ImportArchive.class, name = "importArchive"),
    @JsonSubTypes.Type(value = DebugCommand.UploadArchive.class, name = "uploadArchive")
})
public sealed interface DebugCommand {

    /**
     * Subscribe to a debug session for live tailing or replay.
     *
     * @param sessionId the session to subscribe to
     * @param mode subscription mode: "live" for live events, "replay" for historical
     * @param fromIndex optional starting index for replay (0 = start)
     */
    record Subscribe(
        String sessionId,
        SubscriptionMode mode,
        Integer fromIndex
    ) implements DebugCommand {
        public Subscribe {
            if (fromIndex == null) fromIndex = 0;
        }
    }

    /**
     * Unsubscribe from a debug session.
     *
     * @param sessionId the session to unsubscribe from
     */
    record Unsubscribe(String sessionId) implements DebugCommand {}

    /**
     * Request list of available debug sessions.
     *
     * @param limit maximum sessions to return (default 50)
     * @param activeOnly only return active sessions
     */
    record ListSessions(
        Integer limit,
        Boolean activeOnly
    ) implements DebugCommand {
        public ListSessions {
            if (limit == null) limit = 50;
            if (activeOnly == null) activeOnly = false;
        }
    }

    /**
     * Seek to a specific timestamp during replay.
     *
     * @param sessionId the session being replayed
     * @param timestamp the target timestamp
     */
    record Seek(String sessionId, Instant timestamp) implements DebugCommand {}

    /**
     * Set playback speed for replay.
     *
     * @param sessionId the session being replayed
     * @param speed playback multiplier (0.5 = half speed, 2.0 = double speed)
     */
    record PlaybackSpeed(String sessionId, double speed) implements DebugCommand {}

    /**
     * Set event filter for the subscription.
     *
     * @param sessionId the session to filter
     * @param filter the filter configuration
     */
    record SetFilter(String sessionId, EventFilter filter) implements DebugCommand {}

    /**
     * Pause live tailing or replay.
     *
     * @param sessionId the session to pause
     */
    record Pause(String sessionId) implements DebugCommand {}

    /**
     * Resume paused subscription.
     *
     * @param sessionId the session to resume
     */
    record Resume(String sessionId) implements DebugCommand {}

    /**
     * Step forward one event during paused replay.
     *
     * @param sessionId the session being replayed
     */
    record StepForward(String sessionId) implements DebugCommand {}

    /**
     * Step backward one event during paused replay.
     *
     * @param sessionId the session being replayed
     */
    record StepBackward(String sessionId) implements DebugCommand {}

    /**
     * Set a breakpoint on a session.
     *
     * @param sessionId the session to add the breakpoint to
     * @param breakpoint the breakpoint configuration
     */
    record SetBreakpoint(String sessionId, BreakpointConfig breakpoint) implements DebugCommand {}

    /**
     * Clear a breakpoint from a session.
     *
     * @param sessionId the session to remove the breakpoint from
     * @param breakpointId the ID of the breakpoint to remove
     */
    record ClearBreakpoint(String sessionId, String breakpointId) implements DebugCommand {}

    /**
     * List all breakpoints for a session.
     *
     * @param sessionId the session to list breakpoints for
     */
    record ListBreakpoints(String sessionId) implements DebugCommand {}

    /**
     * List available session archives from storage.
     *
     * @param limit maximum number of archives to return (default 50)
     * @param prefix optional session ID prefix filter
     */
    record ListArchives(Integer limit, String prefix) implements DebugCommand {
        public ListArchives { if (limit == null) limit = 50; }
    }

    /**
     * Import an archived session from storage by session ID.
     *
     * @param sessionId the archived session to import
     */
    record ImportArchive(String sessionId) implements DebugCommand {}

    /**
     * Upload and import an archive file (base64-encoded LZ4 content).
     *
     * @param fileName original file name
     * @param data base64-encoded LZ4 archive content
     */
    record UploadArchive(String fileName, String data) implements DebugCommand {}

    // ======================== Supporting Types ========================

    /**
     * Subscription mode for debug sessions.
     */
    enum SubscriptionMode {
        /** Live tailing - receive events as they occur */
        live,
        /** Replay - replay historical events */
        replay
    }

    /**
     * Event filter configuration.
     *
     * @param eventTypes event types to include (null = all)
     * @param transitionNames transitions to include (null = all)
     * @param placeNames places to include (null = all)
     * @param excludeEventTypes event types to exclude (null = exclude nothing)
     * @param excludeTransitionNames transitions to exclude (null = exclude nothing)
     * @param excludePlaceNames places to exclude (null = exclude nothing)
     */
    record EventFilter(
        Set<String> eventTypes,
        Set<String> transitionNames,
        Set<String> placeNames,
        Set<String> excludeEventTypes,
        Set<String> excludeTransitionNames,
        Set<String> excludePlaceNames
    ) {
        public static EventFilter all() {
            return new EventFilter(null, null, null, null, null, null);
        }
    }

    /**
     * Breakpoint configuration.
     *
     * @param id unique identifier for the breakpoint
     * @param type the type of breakpoint
     * @param target the transition or place name to break on
     * @param enabled whether the breakpoint is active
     */
    record BreakpointConfig(
        String id,
        BreakpointType type,
        String target,
        boolean enabled
    ) {}

    /**
     * Types of breakpoints that can be set.
     */
    enum BreakpointType {
        /** Break when a transition becomes enabled */
        TRANSITION_ENABLED,
        /** Break when a transition starts firing */
        TRANSITION_START,
        /** Break when a transition completes */
        TRANSITION_COMPLETE,
        /** Break when a transition fails */
        TRANSITION_FAIL,
        /** Break when a token is added to a place */
        TOKEN_ADDED,
        /** Break when a token is removed from a place */
        TOKEN_REMOVED
    }
}
