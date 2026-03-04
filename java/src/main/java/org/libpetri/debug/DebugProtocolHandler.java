package org.libpetri.debug;

import org.libpetri.debug.DebugSessionRegistry.DebugSession;
import org.libpetri.event.NetEvent;
import java.lang.System.Logger;
import java.lang.System.Logger.Level;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Framework-agnostic handler for the Petri net debug protocol.
 *
 * <p>Manages debug subscriptions, event filtering, breakpoints, and replay
 * for connected clients. Decoupled from any specific WebSocket framework
 * via the {@link ResponseSink} interface.
 *
 * @see DebugCommand
 * @see DebugResponse
 * @see DebugSessionRegistry
 */
public class DebugProtocolHandler {

    private static final Logger LOG = System.getLogger(DebugProtocolHandler.class.getName());

    /**
     * Functional interface for sending responses to a connected client.
     */
    @FunctionalInterface
    public interface ResponseSink {
        void send(DebugResponse response);
    }

    private final DebugSessionRegistry sessionRegistry;
    private final ConcurrentHashMap<String, ClientState> clients = new ConcurrentHashMap<>();

    public DebugProtocolHandler(DebugSessionRegistry sessionRegistry) {
        this.sessionRegistry = sessionRegistry;
    }

    /**
     * Registers a new client connection.
     *
     * @param clientId unique identifier for the client
     * @param sink callback for sending responses to the client
     */
    public void clientConnected(String clientId, ResponseSink sink) {
        LOG.log(Level.INFO, "Debug client connected: {0}", clientId);
        clients.put(clientId, new ClientState(sink));
    }

    /**
     * Cleans up when a client disconnects.
     *
     * @param clientId the disconnecting client
     */
    public void clientDisconnected(String clientId) {
        LOG.log(Level.INFO, "Debug client disconnected: {0}", clientId);
        var state = clients.remove(clientId);
        if (state != null) {
            state.subscriptions.cancelAll();
        }
    }

    /**
     * Handles a command from a connected client.
     *
     * @param clientId the client sending the command
     * @param command the debug command
     */
    public void handleCommand(String clientId, DebugCommand command) {
        LOG.log(Level.DEBUG, "Received debug command: {0} from {1}", command.getClass().getSimpleName(), clientId);

        var clientState = clients.get(clientId);
        if (clientState == null) {
            LOG.log(Level.WARNING, "Received command from unknown client: {0}", clientId);
            return;
        }

        try {
            switch (command) {
                case DebugCommand.ListSessions cmd -> handleListSessions(clientState, cmd);
                case DebugCommand.Subscribe cmd -> handleSubscribe(clientState, cmd);
                case DebugCommand.Unsubscribe cmd -> handleUnsubscribe(clientState, cmd);
                case DebugCommand.Seek cmd -> handleSeek(clientState, cmd);
                case DebugCommand.PlaybackSpeed cmd -> handlePlaybackSpeed(clientState, cmd);
                case DebugCommand.SetFilter cmd -> handleSetFilter(clientState, cmd);
                case DebugCommand.Pause cmd -> handlePause(clientState, cmd);
                case DebugCommand.Resume cmd -> handleResume(clientState, cmd);
                case DebugCommand.StepForward cmd -> handleStepForward(clientState, cmd);
                case DebugCommand.StepBackward cmd -> handleStepBackward(clientState, cmd);
                case DebugCommand.SetBreakpoint cmd -> handleSetBreakpoint(clientState, cmd);
                case DebugCommand.ClearBreakpoint cmd -> handleClearBreakpoint(clientState, cmd);
                case DebugCommand.ListBreakpoints cmd -> handleListBreakpoints(clientState, cmd);
            }
        } catch (Exception e) {
            LOG.log(Level.ERROR, "Error handling debug command", e);
            sendError(clientState, "COMMAND_ERROR", e.getMessage(), null);
        }
    }

    // ======================== Command Handlers ========================

    private void handleListSessions(ClientState client, DebugCommand.ListSessions cmd) {
        var sessions = cmd.activeOnly()
            ? sessionRegistry.listActiveSessions(cmd.limit())
            : sessionRegistry.listSessions(cmd.limit());

        var summaries = sessions.stream()
            .map(s -> new DebugResponse.SessionSummary(
                s.sessionId(),
                s.netName(),
                s.startTime().toString(),
                s.active(),
                s.eventStore().eventCount()
            ))
            .toList();

        send(client, new DebugResponse.SessionList(summaries));
    }

    private void handleSubscribe(ClientState client, DebugCommand.Subscribe cmd) {
        var debugSessionOpt = sessionRegistry.getSession(cmd.sessionId());
        if (debugSessionOpt.isEmpty()) {
            sendError(client, "SESSION_NOT_FOUND", "Session not found: " + cmd.sessionId(), cmd.sessionId());
            return;
        }

        var debugSession = debugSessionOpt.get();
        var eventStore = debugSession.eventStore();

        // Cancel existing subscription for this session
        client.subscriptions.cancel(cmd.sessionId());

        // Send subscribed confirmation FIRST, before creating subscription
        // This ensures frontend receives Subscribed before EventBatch and can
        // properly initialize replay mode state before events arrive
        var events = eventStore.events();
        var computed = computeState(events);

        // Generate net structure from stored place/transition info
        var structure = debugSession.buildNetStructure();

        send(client, new DebugResponse.Subscribed(
            cmd.sessionId(),
            debugSession.netName(),
            debugSession.dotDiagram(),
            structure,
            computed.marking(),
            computed.enabledTransitions(),
            computed.inFlightTransitions(),
            eventStore.eventCount(),
            cmd.mode().name()
        ));

        // THEN create subscription (which may send EventBatch)
        if (cmd.mode() == DebugCommand.SubscriptionMode.live) {
            subscribeLive(client, cmd.sessionId(), debugSession, cmd.fromIndex());
        } else {
            subscribeReplay(client, cmd.sessionId(), debugSession, cmd.fromIndex());
        }
    }

    /** Maximum events per batch when sending historical events. */
    private static final int BATCH_SIZE = 500;

    private void subscribeLive(ClientState client, String sessionId,
                               DebugSession debugSession, int fromIndex) {
        var eventStore = debugSession.eventStore();
        var eventIndex = new AtomicLong(fromIndex);

        // Send historical events first (filtered, paginated)
        var historicalEvents = eventStore.eventsFrom(fromIndex);
        if (!historicalEvents.isEmpty()) {
            var filtered = historicalEvents.stream()
                .filter(e -> client.subscriptions.matchesFilter(sessionId, e))
                .map(NetEventConverter::toEventInfo)
                .toList();
            sendInBatches(client, sessionId, fromIndex, filtered);
            eventIndex.set(fromIndex + historicalEvents.size());
        }

        // Subscribe for live events (filtered + breakpoints)
        var subscription = eventStore.subscribe(event -> {
            if (!client.subscriptions.isPaused(sessionId) && client.subscriptions.matchesFilter(sessionId, event)) {
                var eventInfo = NetEventConverter.toEventInfo(event);
                long idx = eventIndex.getAndIncrement();

                // Check for breakpoint hit
                var hitBreakpoint = client.subscriptions.checkBreakpoints(sessionId, event);
                if (hitBreakpoint != null) {
                    client.subscriptions.setPaused(sessionId, true);
                    send(client, new DebugResponse.BreakpointHit(sessionId, hitBreakpoint.id(), eventInfo, idx));
                }

                send(client, new DebugResponse.Event(sessionId, idx, eventInfo));
            }
        });

        client.subscriptions.addSubscription(sessionId, subscription, eventIndex);
    }

    private void subscribeReplay(ClientState client, String sessionId,
                                 DebugSession debugSession, int fromIndex) {
        var eventStore = debugSession.eventStore();
        var eventIndex = new AtomicLong(fromIndex);

        // For replay, we don't subscribe to live events
        // Instead we send events on demand via seek/step commands

        // Send all events so the frontend has the complete history for replay (paginated)
        var events = eventStore.eventsFrom(fromIndex);
        var converted = events.stream()
            .map(NetEventConverter::toEventInfo)
            .toList();
        sendInBatches(client, sessionId, fromIndex, converted);

        eventIndex.set(fromIndex + events.size());
        client.subscriptions.addSubscription(sessionId, null, eventIndex); // No live subscription for replay
        client.subscriptions.setPaused(sessionId, true); // Replay starts paused
    }

    private void handleUnsubscribe(ClientState client, DebugCommand.Unsubscribe cmd) {
        client.subscriptions.cancel(cmd.sessionId());
        send(client, new DebugResponse.Unsubscribed(cmd.sessionId()));
    }

    private void handleSeek(ClientState client, DebugCommand.Seek cmd) {
        var debugSessionOpt = sessionRegistry.getSession(cmd.sessionId());
        if (debugSessionOpt.isEmpty()) {
            sendError(client, "SESSION_NOT_FOUND", "Session not found", cmd.sessionId());
            return;
        }

        var debugSession = debugSessionOpt.get();
        var events = debugSession.eventStore().events();

        // Find event index at or after the timestamp
        int targetIndex = 0;
        for (int i = 0; i < events.size(); i++) {
            if (!events.get(i).timestamp().isBefore(cmd.timestamp())) {
                targetIndex = i;
                break;
            }
            targetIndex = i + 1;
        }

        client.subscriptions.setEventIndex(cmd.sessionId(), targetIndex);

        // Compute state up to this point (using cache for O(interval) instead of O(n))
        var computed = client.subscriptions.computeStateAt(cmd.sessionId(), events, targetIndex);

        send(client, new DebugResponse.MarkingSnapshot(
            cmd.sessionId(),
            computed.marking(),
            computed.enabledTransitions(),
            computed.inFlightTransitions()
        ));
    }

    private void handlePlaybackSpeed(ClientState client, DebugCommand.PlaybackSpeed cmd) {
        client.subscriptions.setSpeed(cmd.sessionId(), cmd.speed());
        send(client, new DebugResponse.PlaybackStateChanged(
            cmd.sessionId(),
            client.subscriptions.isPaused(cmd.sessionId()),
            cmd.speed(),
            client.subscriptions.getEventIndex(cmd.sessionId())
        ));
    }

    private void handleSetFilter(ClientState client, DebugCommand.SetFilter cmd) {
        client.subscriptions.setFilter(cmd.sessionId(), cmd.filter());
        send(client, new DebugResponse.FilterApplied(cmd.sessionId(), cmd.filter()));
    }

    private void handlePause(ClientState client, DebugCommand.Pause cmd) {
        client.subscriptions.setPaused(cmd.sessionId(), true);
        send(client, new DebugResponse.PlaybackStateChanged(
            cmd.sessionId(),
            true,
            client.subscriptions.getSpeed(cmd.sessionId()),
            client.subscriptions.getEventIndex(cmd.sessionId())
        ));
    }

    private void handleResume(ClientState client, DebugCommand.Resume cmd) {
        client.subscriptions.setPaused(cmd.sessionId(), false);
        send(client, new DebugResponse.PlaybackStateChanged(
            cmd.sessionId(),
            false,
            client.subscriptions.getSpeed(cmd.sessionId()),
            client.subscriptions.getEventIndex(cmd.sessionId())
        ));
    }

    private void handleStepForward(ClientState client, DebugCommand.StepForward cmd) {
        var debugSessionOpt = sessionRegistry.getSession(cmd.sessionId());
        if (debugSessionOpt.isEmpty()) return;

        var events = debugSessionOpt.get().eventStore().events();
        long currentIndex = client.subscriptions.getEventIndex(cmd.sessionId());

        if (currentIndex < events.size()) {
            var event = events.get((int) currentIndex);
            send(client, new DebugResponse.Event(
                cmd.sessionId(),
                currentIndex,
                NetEventConverter.toEventInfo(event)
            ));
            client.subscriptions.setEventIndex(cmd.sessionId(), currentIndex + 1);
        }
    }

    private void handleStepBackward(ClientState client, DebugCommand.StepBackward cmd) {
        var debugSessionOpt = sessionRegistry.getSession(cmd.sessionId());
        if (debugSessionOpt.isEmpty()) return;

        long currentIndex = client.subscriptions.getEventIndex(cmd.sessionId());
        if (currentIndex > 0) {
            currentIndex--;
            client.subscriptions.setEventIndex(cmd.sessionId(), currentIndex);

            // Recompute state up to this point (using cache for O(interval) instead of O(n))
            var events = debugSessionOpt.get().eventStore().events();
            var computed = client.subscriptions.computeStateAt(cmd.sessionId(), events, (int) currentIndex);

            send(client, new DebugResponse.MarkingSnapshot(
                cmd.sessionId(),
                computed.marking(),
                computed.enabledTransitions(),
                computed.inFlightTransitions()
            ));
        }
    }

    private void handleSetBreakpoint(ClientState client, DebugCommand.SetBreakpoint cmd) {
        client.subscriptions.addBreakpoint(cmd.sessionId(), cmd.breakpoint());
        send(client, new DebugResponse.BreakpointSet(cmd.sessionId(), cmd.breakpoint()));
    }

    private void handleClearBreakpoint(ClientState client, DebugCommand.ClearBreakpoint cmd) {
        client.subscriptions.removeBreakpoint(cmd.sessionId(), cmd.breakpointId());
        send(client, new DebugResponse.BreakpointCleared(cmd.sessionId(), cmd.breakpointId()));
    }

    private void handleListBreakpoints(ClientState client, DebugCommand.ListBreakpoints cmd) {
        var breakpoints = client.subscriptions.getBreakpoints(cmd.sessionId());
        send(client, new DebugResponse.BreakpointList(cmd.sessionId(), breakpoints));
    }

    // ======================== Helper Methods ========================

    private void send(ClientState client, DebugResponse response) {
        client.sink.send(response);
    }

    private void sendError(ClientState client, String code, String message, String sessionId) {
        send(client, new DebugResponse.Error(code, message, sessionId));
    }

    /**
     * Sends events in paginated batches to avoid a single massive WebSocket frame.
     */
    private void sendInBatches(ClientState client, String sessionId, long startIndex,
                               List<DebugResponse.NetEventInfo> events) {
        if (events.isEmpty()) {
            send(client, new DebugResponse.EventBatch(sessionId, startIndex, List.of(), false));
            return;
        }
        for (int i = 0; i < events.size(); i += BATCH_SIZE) {
            int end = Math.min(i + BATCH_SIZE, events.size());
            var chunk = events.subList(i, end);
            boolean hasMore = end < events.size();
            send(client, new DebugResponse.EventBatch(sessionId, startIndex + i, chunk, hasMore));
        }
    }

    /**
     * Computed state from replaying a sequence of events: marking, enabled transitions, in-flight transitions.
     */
    public record ComputedState(
        Map<String, List<DebugResponse.TokenInfo>> marking,
        List<String> enabledTransitions,
        List<String> inFlightTransitions
    ) {}

    /**
     * Computes marking, enabled transitions, and in-flight transitions in a single pass over the event list.
     */
    public static ComputedState computeState(List<NetEvent> events) {
        var marking = new HashMap<String, ArrayList<DebugResponse.TokenInfo>>();
        var enabled = new HashSet<String>();
        var inFlight = new HashSet<String>();
        applyEvents(marking, enabled, inFlight, events);
        return toImmutableState(marking, enabled, inFlight);
    }

    /**
     * Applies a list of events to mutable accumulator collections.
     *
     * <p>Shared by {@link #computeState(List)} and {@link MarkingCache#replayDelta}.
     */
    static void applyEvents(
            Map<String, ArrayList<DebugResponse.TokenInfo>> marking,
            Set<String> enabled,
            Set<String> inFlight,
            List<NetEvent> events) {
        for (var event : events) {
            switch (event) {
                case NetEvent.TokenAdded e ->
                    marking.computeIfAbsent(e.placeName(), _ -> new ArrayList<>())
                        .add(NetEventConverter.tokenInfo(e.token()));
                case NetEvent.TokenRemoved e -> {
                    var tokens = marking.get(e.placeName());
                    if (tokens != null && !tokens.isEmpty()) {
                        tokens.removeFirst();
                    }
                }
                case NetEvent.MarkingSnapshot e -> {
                    marking.clear();
                    var converted = NetEventConverter.convertMarking(e.marking());
                    for (var entry : converted.entrySet()) {
                        marking.put(entry.getKey(), new ArrayList<>(entry.getValue()));
                    }
                }
                case NetEvent.TransitionEnabled e -> enabled.add(e.transitionName());
                case NetEvent.TransitionStarted e -> {
                    enabled.remove(e.transitionName());
                    inFlight.add(e.transitionName());
                }
                case NetEvent.TransitionCompleted e -> inFlight.remove(e.transitionName());
                case NetEvent.TransitionFailed e -> inFlight.remove(e.transitionName());
                case NetEvent.TransitionTimedOut e -> inFlight.remove(e.transitionName());
                case NetEvent.ActionTimedOut e -> inFlight.remove(e.transitionName());
                default -> {}
            }
        }
    }

    /**
     * Converts mutable accumulator collections into an immutable {@link ComputedState}.
     */
    static ComputedState toImmutableState(
            Map<String, ArrayList<DebugResponse.TokenInfo>> marking,
            Set<String> enabled,
            Set<String> inFlight) {
        var resultMarking = new HashMap<String, List<DebugResponse.TokenInfo>>();
        for (var entry : marking.entrySet()) {
            resultMarking.put(entry.getKey(), List.copyOf(entry.getValue()));
        }
        return new ComputedState(resultMarking, List.copyOf(enabled), List.copyOf(inFlight));
    }

    // ======================== Client State ========================

    /**
     * State for a single connected client.
     */
    private static class ClientState {
        final ResponseSink sink;
        final SubscriptionState subscriptions = new SubscriptionState();

        ClientState(ResponseSink sink) {
            this.sink = sink;
        }
    }

    // ======================== Subscription State ========================

    /**
     * Tracks subscription state per client.
     */
    private static class SubscriptionState {
        private final ConcurrentHashMap<String, SessionSubscription> sessionSubs = new ConcurrentHashMap<>();

        void addSubscription(String sessionId, DebugEventStore.Subscription subscription, AtomicLong eventIndex) {
            sessionSubs.put(sessionId, new SessionSubscription(subscription, eventIndex));
        }

        void cancel(String sessionId) {
            var sub = sessionSubs.remove(sessionId);
            if (sub != null && sub.subscription != null) {
                sub.subscription.cancel();
            }
        }

        void cancelAll() {
            for (var entry : sessionSubs.entrySet()) {
                if (entry.getValue().subscription != null) {
                    entry.getValue().subscription.cancel();
                }
            }
            sessionSubs.clear();
        }

        boolean isPaused(String sessionId) {
            var sub = sessionSubs.get(sessionId);
            return sub != null && sub.paused;
        }

        void setPaused(String sessionId, boolean paused) {
            var sub = sessionSubs.get(sessionId);
            if (sub != null) {
                sub.paused = paused;
            }
        }

        double getSpeed(String sessionId) {
            var sub = sessionSubs.get(sessionId);
            return sub != null ? sub.speed : 1.0;
        }

        void setSpeed(String sessionId, double speed) {
            var sub = sessionSubs.get(sessionId);
            if (sub != null) {
                sub.speed = speed;
            }
        }

        long getEventIndex(String sessionId) {
            var sub = sessionSubs.get(sessionId);
            return sub != null ? sub.eventIndex.get() : 0;
        }

        void setEventIndex(String sessionId, long index) {
            var sub = sessionSubs.get(sessionId);
            if (sub != null) {
                sub.eventIndex.set(index);
            }
        }

        ComputedState computeStateAt(String sessionId, List<NetEvent> events, int targetIndex) {
            var sub = sessionSubs.get(sessionId);
            if (sub != null) {
                return sub.markingCache.computeAt(events, targetIndex);
            }
            return computeState(events.subList(0, targetIndex));
        }

        void setFilter(String sessionId, DebugCommand.EventFilter filter) {
            var sub = sessionSubs.get(sessionId);
            if (sub != null) {
                sub.filter = filter;
            }
        }

        /**
         * Checks if an event matches the current filter for a session.
         */
        boolean matchesFilter(String sessionId, NetEvent event) {
            var sub = sessionSubs.get(sessionId);
            if (sub == null || sub.filter == null) {
                return true;
            }

            var filter = sub.filter;

            // Check event types filter
            if (filter.eventTypes() != null && !filter.eventTypes().isEmpty()) {
                String eventType = event.getClass().getSimpleName();
                if (!filter.eventTypes().contains(eventType)) {
                    return false;
                }
            }

            // Check transition names filter
            if (filter.transitionNames() != null && !filter.transitionNames().isEmpty()) {
                String transitionName = extractTransitionName(event);
                if (transitionName == null || !filter.transitionNames().contains(transitionName)) {
                    return false;
                }
            }

            // Check place names filter
            if (filter.placeNames() != null && !filter.placeNames().isEmpty()) {
                String placeName = extractPlaceName(event);
                if (placeName == null || !filter.placeNames().contains(placeName)) {
                    return false;
                }
            }

            return true;
        }

        private String extractTransitionName(NetEvent event) {
            return switch (event) {
                case NetEvent.TransitionEnabled e -> e.transitionName();
                case NetEvent.TransitionStarted e -> e.transitionName();
                case NetEvent.TransitionCompleted e -> e.transitionName();
                case NetEvent.TransitionFailed e -> e.transitionName();
                case NetEvent.TransitionTimedOut e -> e.transitionName();
                case NetEvent.ActionTimedOut e -> e.transitionName();
                case NetEvent.LogMessage e -> e.transitionName();
                default -> null;
            };
        }

        private String extractPlaceName(NetEvent event) {
            return switch (event) {
                case NetEvent.TokenAdded e -> e.placeName();
                case NetEvent.TokenRemoved e -> e.placeName();
                default -> null;
            };
        }

        void addBreakpoint(String sessionId, DebugCommand.BreakpointConfig breakpoint) {
            var sub = sessionSubs.get(sessionId);
            if (sub != null) {
                sub.breakpoints.put(breakpoint.id(), breakpoint);
            }
        }

        void removeBreakpoint(String sessionId, String breakpointId) {
            var sub = sessionSubs.get(sessionId);
            if (sub != null) {
                sub.breakpoints.remove(breakpointId);
            }
        }

        List<DebugCommand.BreakpointConfig> getBreakpoints(String sessionId) {
            var sub = sessionSubs.get(sessionId);
            if (sub != null) {
                return List.copyOf(sub.breakpoints.values());
            }
            return List.of();
        }

        /**
         * Checks if an event triggers any enabled breakpoints.
         * @return the triggered breakpoint, or null if none
         */
        DebugCommand.BreakpointConfig checkBreakpoints(String sessionId, NetEvent event) {
            var sub = sessionSubs.get(sessionId);
            if (sub == null || sub.breakpoints.isEmpty()) {
                return null;
            }

            for (var bp : sub.breakpoints.values()) {
                if (!bp.enabled()) continue;

                if (matchesBreakpoint(bp, event)) {
                    return bp;
                }
            }
            return null;
        }

        private boolean matchesBreakpoint(DebugCommand.BreakpointConfig bp, NetEvent event) {
            return switch (bp.type()) {
                case TRANSITION_ENABLED -> event instanceof NetEvent.TransitionEnabled e
                    && (bp.target() == null || bp.target().equals(e.transitionName()));
                case TRANSITION_START -> event instanceof NetEvent.TransitionStarted e
                    && (bp.target() == null || bp.target().equals(e.transitionName()));
                case TRANSITION_COMPLETE -> event instanceof NetEvent.TransitionCompleted e
                    && (bp.target() == null || bp.target().equals(e.transitionName()));
                case TRANSITION_FAIL -> event instanceof NetEvent.TransitionFailed e
                    && (bp.target() == null || bp.target().equals(e.transitionName()));
                case TOKEN_ADDED -> event instanceof NetEvent.TokenAdded e
                    && (bp.target() == null || bp.target().equals(e.placeName()));
                case TOKEN_REMOVED -> event instanceof NetEvent.TokenRemoved e
                    && (bp.target() == null || bp.target().equals(e.placeName()));
            };
        }

        private static class SessionSubscription {
            final DebugEventStore.Subscription subscription;
            final AtomicLong eventIndex;
            final MarkingCache markingCache = new MarkingCache();
            final ConcurrentHashMap<String, DebugCommand.BreakpointConfig> breakpoints = new ConcurrentHashMap<>();
            volatile boolean paused = false;
            volatile double speed = 1.0;
            volatile DebugCommand.EventFilter filter = null;

            SessionSubscription(DebugEventStore.Subscription subscription, AtomicLong eventIndex) {
                this.subscription = subscription;
                this.eventIndex = eventIndex;
            }
        }
    }
}
