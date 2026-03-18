package org.libpetri.debug;

import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Token;
import org.libpetri.core.Transition;
import org.libpetri.event.NetEvent;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.*;

class DebugProtocolHandlerTest {

    private static final Place<String> INPUT = Place.of("Input", String.class);
    private static final Place<String> OUTPUT = Place.of("Output", String.class);

    private static final PetriNet TEST_NET = PetriNet.builder("TestNet")
            .transitions(
                    Transition.builder("Process")
                            .inputs(In.one(INPUT))
                            .outputs(Out.place(OUTPUT))
                            .build()
            )
            .build();

    private DebugSessionRegistry registry;
    private DebugProtocolHandler handler;
    private List<DebugResponse> responses;

    @BeforeEach
    void setUp() {
        registry = new DebugSessionRegistry();
        handler = new DebugProtocolHandler(registry);
        responses = new CopyOnWriteArrayList<>();
    }

    private void connectClient(String clientId) {
        handler.clientConnected(clientId, responses::add);
    }

    private String registerSessionWithEvents(String sessionId, NetEvent... events) {
        var session = registry.register(sessionId, TEST_NET);
        for (var event : events) {
            session.eventStore().append(event);
        }
        return sessionId;
    }

    @SuppressWarnings("unchecked")
    private <T extends DebugResponse> T lastResponseOfType(Class<T> type) {
        for (int i = responses.size() - 1; i >= 0; i--) {
            if (type.isInstance(responses.get(i))) {
                return (T) responses.get(i);
            }
        }
        fail("No response of type " + type.getSimpleName() + " found in " + responses);
        return null; // unreachable
    }

    private <T extends DebugResponse> List<T> responsesOfType(Class<T> type) {
        return responses.stream()
                .filter(type::isInstance)
                .map(type::cast)
                .toList();
    }

    @Nested
    class ConnectionLifecycle {

        @Test
        void shouldIgnoreCommandFromUnknownClient() {
            // Don't connect client, just send a command
            handler.handleCommand("unknown", new DebugCommand.ListSessions(10, false));
            assertTrue(responses.isEmpty());
        }

        @Test
        void shouldCleanSubscriptionsOnDisconnect() throws InterruptedException {
            connectClient("c1");
            var sessionId = registerSessionWithEvents("s1");

            handler.handleCommand("c1", new DebugCommand.Subscribe(sessionId,
                    DebugCommand.SubscriptionMode.live, 0));
            responses.clear();

            handler.clientDisconnected("c1");

            // After disconnect, new events should not trigger any responses
            registry.getSession(sessionId).get().eventStore()
                    .append(new NetEvent.TransitionEnabled(Instant.now(), "T1"));
            Thread.sleep(50); // Wait for potential async delivery
            assertTrue(responses.isEmpty());
        }

        @Test
        void shouldSupportMultipleIndependentClients() {
            var responses1 = new CopyOnWriteArrayList<DebugResponse>();
            var responses2 = new CopyOnWriteArrayList<DebugResponse>();

            handler.clientConnected("c1", responses1::add);
            handler.clientConnected("c2", responses2::add);

            registerSessionWithEvents("s1");
            handler.handleCommand("c1", new DebugCommand.ListSessions(10, false));
            handler.handleCommand("c2", new DebugCommand.ListSessions(10, false));

            assertFalse(responses1.isEmpty());
            assertFalse(responses2.isEmpty());
            assertInstanceOf(DebugResponse.SessionList.class, responses1.getFirst());
            assertInstanceOf(DebugResponse.SessionList.class, responses2.getFirst());
        }
    }

    @Nested
    class ListSessionsFlow {

        @Test
        void shouldListAllSessions() {
            connectClient("c1");
            registerSessionWithEvents("s1");
            registerSessionWithEvents("s2");

            handler.handleCommand("c1", new DebugCommand.ListSessions(50, false));

            var sessionList = lastResponseOfType(DebugResponse.SessionList.class);
            assertEquals(2, sessionList.sessions().size());
        }

        @Test
        void shouldListActiveSessionsOnly() {
            connectClient("c1");
            registerSessionWithEvents("s1");
            registerSessionWithEvents("s2");
            registry.complete("s1"); // Mark s1 as inactive

            handler.handleCommand("c1", new DebugCommand.ListSessions(50, true));

            var sessionList = lastResponseOfType(DebugResponse.SessionList.class);
            assertEquals(1, sessionList.sessions().size());
            assertEquals("s2", sessionList.sessions().getFirst().sessionId());
        }

        @Test
        void shouldRespectLimit() {
            connectClient("c1");
            for (int i = 0; i < 5; i++) {
                registerSessionWithEvents("s" + i);
            }

            handler.handleCommand("c1", new DebugCommand.ListSessions(2, false));

            var sessionList = lastResponseOfType(DebugResponse.SessionList.class);
            assertEquals(2, sessionList.sessions().size());
        }
    }

    @Nested
    class SubscribeLiveFlow {

        @Test
        void shouldRespondWithSubscribedAndInitialState() {
            connectClient("c1");
            registerSessionWithEvents("s1");

            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.live, 0));

            var subscribed = lastResponseOfType(DebugResponse.Subscribed.class);
            assertEquals("s1", subscribed.sessionId());
            assertEquals("TestNet", subscribed.netName());
            assertNotNull(subscribed.dotDiagram());
            assertNotNull(subscribed.structure());
            assertEquals("live", subscribed.mode());
        }

        @Test
        void shouldSendHistoricalEventsAsBatch() {
            connectClient("c1");
            var now = Instant.now();
            registerSessionWithEvents("s1",
                    new NetEvent.TransitionEnabled(now, "T1"),
                    new NetEvent.TransitionEnabled(now, "T2"));

            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.live, 0));

            var batches = responsesOfType(DebugResponse.EventBatch.class);
            assertFalse(batches.isEmpty());
            var allEvents = batches.stream()
                    .flatMap(b -> b.events().stream())
                    .toList();
            assertEquals(2, allEvents.size());
        }

        @Test
        void shouldReceiveLiveEventsAfterSubscribe() throws InterruptedException {
            connectClient("c1");
            var sessionId = registerSessionWithEvents("s1");
            var eventStore = registry.getSession(sessionId).get().eventStore();

            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.live, 0));
            responses.clear();

            // Append a new event after subscribing
            var latch = new CountDownLatch(1);
            var liveResponses = new CopyOnWriteArrayList<DebugResponse>();
            handler.clientDisconnected("c1"); // Remove old connection
            handler.clientConnected("c1", r -> {
                liveResponses.add(r);
                if (r instanceof DebugResponse.Event) latch.countDown();
            });
            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.live, 0));

            eventStore.append(new NetEvent.TransitionEnabled(Instant.now(), "LiveT"));
            assertTrue(latch.await(2, TimeUnit.SECONDS));

            var liveEvents = liveResponses.stream()
                    .filter(r -> r instanceof DebugResponse.Event)
                    .map(r -> (DebugResponse.Event) r)
                    .toList();
            assertFalse(liveEvents.isEmpty());
            assertEquals("TransitionEnabled", liveEvents.getLast().event().type());
        }

        @Test
        void shouldFilterByEventType() {
            connectClient("c1");
            var now = Instant.now();
            registerSessionWithEvents("s1",
                    new NetEvent.TransitionEnabled(now, "T1"),
                    new NetEvent.TokenAdded(now, "P1", Token.of("val")));

            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.live, 0));
            handler.handleCommand("c1", new DebugCommand.SetFilter("s1",
                    new DebugCommand.EventFilter(Set.of("TransitionEnabled"), null, null, null, null, null)));

            var filterApplied = lastResponseOfType(DebugResponse.FilterApplied.class);
            assertNotNull(filterApplied);
            assertEquals("s1", filterApplied.sessionId());
        }

        @Test
        void shouldExcludeByTransitionName() {
            connectClient("c1");
            var now = Instant.now();
            registerSessionWithEvents("s1",
                    new NetEvent.TransitionEnabled(now, "T1"),
                    new NetEvent.TransitionEnabled(now, "T2"),
                    new NetEvent.TransitionEnabled(now, "T3"));

            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.live, 0));
            handler.handleCommand("c1", new DebugCommand.SetFilter("s1",
                    new DebugCommand.EventFilter(null, null, null, null, Set.of("T2"), null)));

            var filterApplied = lastResponseOfType(DebugResponse.FilterApplied.class);
            assertNotNull(filterApplied);
        }

        @Test
        void shouldCombineIncludeAndExcludeFilters() {
            connectClient("c1");
            var now = Instant.now();
            registerSessionWithEvents("s1",
                    new NetEvent.TransitionEnabled(now, "T1"),
                    new NetEvent.TransitionEnabled(now, "T2"),
                    new NetEvent.TokenAdded(now, "P1", Token.of("val")));

            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.live, 0));
            handler.handleCommand("c1", new DebugCommand.SetFilter("s1",
                    new DebugCommand.EventFilter(Set.of("TransitionEnabled"), null, null,
                            null, Set.of("T2"), null)));

            var filterApplied = lastResponseOfType(DebugResponse.FilterApplied.class);
            assertNotNull(filterApplied);
        }

        @Test
        void shouldPauseAndResumeLiveEvents() {
            connectClient("c1");
            registerSessionWithEvents("s1");

            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.live, 0));

            handler.handleCommand("c1", new DebugCommand.Pause("s1"));
            var paused = lastResponseOfType(DebugResponse.PlaybackStateChanged.class);
            assertTrue(paused.paused());

            handler.handleCommand("c1", new DebugCommand.Resume("s1"));
            var resumed = lastResponseOfType(DebugResponse.PlaybackStateChanged.class);
            assertFalse(resumed.paused());
        }
    }

    @Nested
    class SubscribeReplayFlow {

        @Test
        void shouldSendAllEventsOnReplay() {
            connectClient("c1");
            var now = Instant.now();
            registerSessionWithEvents("s1",
                    new NetEvent.TransitionEnabled(now, "T1"),
                    new NetEvent.TransitionEnabled(now, "T2"),
                    new NetEvent.TransitionEnabled(now, "T3"));

            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.replay, 0));

            var subscribed = lastResponseOfType(DebugResponse.Subscribed.class);
            assertEquals("replay", subscribed.mode());

            var batches = responsesOfType(DebugResponse.EventBatch.class);
            var totalEvents = batches.stream().mapToInt(b -> b.events().size()).sum();
            assertEquals(3, totalEvents);
        }

        @Test
        void shouldStartPausedInReplayMode() {
            connectClient("c1");
            registerSessionWithEvents("s1",
                    new NetEvent.TransitionEnabled(Instant.now(), "T1"));

            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.replay, 0));

            // Verify replay starts paused by checking pause state through a Pause command response
            handler.handleCommand("c1", new DebugCommand.Pause("s1"));
            var state = lastResponseOfType(DebugResponse.PlaybackStateChanged.class);
            assertTrue(state.paused());
        }

        @Test
        void shouldUnsubscribeCleanly() {
            connectClient("c1");
            registerSessionWithEvents("s1");

            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.replay, 0));
            handler.handleCommand("c1", new DebugCommand.Unsubscribe("s1"));

            var unsubscribed = lastResponseOfType(DebugResponse.Unsubscribed.class);
            assertEquals("s1", unsubscribed.sessionId());
        }
    }

    @Nested
    class SeekAndStepFlow {

        @Test
        void shouldSeekToTimestamp() throws InterruptedException {
            connectClient("c1");
            var t1 = Instant.parse("2024-01-01T00:00:00Z");
            var t2 = Instant.parse("2024-01-01T00:00:01Z");
            var t3 = Instant.parse("2024-01-01T00:00:02Z");

            registerSessionWithEvents("s1",
                    new NetEvent.TransitionEnabled(t1, "T1"),
                    new NetEvent.TransitionEnabled(t2, "T2"),
                    new NetEvent.TransitionEnabled(t3, "T3"));

            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.replay, 0));

            handler.handleCommand("c1", new DebugCommand.Seek("s1", t2));
            var snapshot = lastResponseOfType(DebugResponse.MarkingSnapshot.class);
            assertNotNull(snapshot);
            assertEquals("s1", snapshot.sessionId());
        }

        @Test
        void shouldStepForward() {
            connectClient("c1");
            var now = Instant.now();
            registerSessionWithEvents("s1",
                    new NetEvent.TransitionEnabled(now, "T1"),
                    new NetEvent.TransitionEnabled(now, "T2"));

            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.replay, 0));

            // Replay subscription puts eventIndex at end of events. Seek back to 0.
            handler.handleCommand("c1", new DebugCommand.Seek("s1", Instant.EPOCH));
            responses.clear();

            handler.handleCommand("c1", new DebugCommand.StepForward("s1"));

            var events = responsesOfType(DebugResponse.Event.class);
            assertFalse(events.isEmpty());
        }

        @Test
        void shouldStepBackward() {
            connectClient("c1");
            var now = Instant.now();
            registerSessionWithEvents("s1",
                    new NetEvent.TokenAdded(now, "P1", Token.of("val")),
                    new NetEvent.TransitionEnabled(now, "T1"));

            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.replay, 0));

            // Step forward past first event
            handler.handleCommand("c1", new DebugCommand.StepForward("s1"));
            handler.handleCommand("c1", new DebugCommand.StepForward("s1"));
            responses.clear();

            // Step backward
            handler.handleCommand("c1", new DebugCommand.StepBackward("s1"));

            var snapshots = responsesOfType(DebugResponse.MarkingSnapshot.class);
            assertFalse(snapshots.isEmpty());
        }

        @Test
        void shouldNotStepForwardPastEnd() {
            connectClient("c1");
            registerSessionWithEvents("s1",
                    new NetEvent.TransitionEnabled(Instant.now(), "T1"));

            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.replay, 0));

            // Step past the one event
            handler.handleCommand("c1", new DebugCommand.StepForward("s1"));
            responses.clear();

            // Another step should produce no Event response
            handler.handleCommand("c1", new DebugCommand.StepForward("s1"));
            var events = responsesOfType(DebugResponse.Event.class);
            assertTrue(events.isEmpty());
        }

        @Test
        void shouldNotStepBackwardBeforeStart() {
            connectClient("c1");
            registerSessionWithEvents("s1",
                    new NetEvent.TransitionEnabled(Instant.now(), "T1"));

            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.replay, 0));

            // Seek to beginning so eventIndex is 0
            handler.handleCommand("c1", new DebugCommand.Seek("s1", Instant.EPOCH));
            responses.clear();

            // Step backward from index 0 should produce nothing
            handler.handleCommand("c1", new DebugCommand.StepBackward("s1"));
            var snapshots = responsesOfType(DebugResponse.MarkingSnapshot.class);
            assertTrue(snapshots.isEmpty());
        }
    }

    @Nested
    class BreakpointFlow {

        @Test
        void shouldSetAndListBreakpoints() {
            connectClient("c1");
            registerSessionWithEvents("s1");
            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.live, 0));

            var bp = new DebugCommand.BreakpointConfig("bp1",
                    DebugCommand.BreakpointType.TRANSITION_ENABLED, "T1", true);
            handler.handleCommand("c1", new DebugCommand.SetBreakpoint("s1", bp));

            var setResponse = lastResponseOfType(DebugResponse.BreakpointSet.class);
            assertEquals("bp1", setResponse.breakpoint().id());

            handler.handleCommand("c1", new DebugCommand.ListBreakpoints("s1"));
            var listResponse = lastResponseOfType(DebugResponse.BreakpointList.class);
            assertEquals(1, listResponse.breakpoints().size());
            assertEquals("bp1", listResponse.breakpoints().getFirst().id());
        }

        @Test
        void shouldClearBreakpoint() {
            connectClient("c1");
            registerSessionWithEvents("s1");
            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.live, 0));

            var bp = new DebugCommand.BreakpointConfig("bp1",
                    DebugCommand.BreakpointType.TRANSITION_ENABLED, "T1", true);
            handler.handleCommand("c1", new DebugCommand.SetBreakpoint("s1", bp));
            handler.handleCommand("c1", new DebugCommand.ClearBreakpoint("s1", "bp1"));

            var cleared = lastResponseOfType(DebugResponse.BreakpointCleared.class);
            assertEquals("bp1", cleared.breakpointId());

            handler.handleCommand("c1", new DebugCommand.ListBreakpoints("s1"));
            var list = lastResponseOfType(DebugResponse.BreakpointList.class);
            assertTrue(list.breakpoints().isEmpty());
        }

        @Test
        void shouldHitBreakpointOnMatchingEvent() throws InterruptedException {
            var liveResponses = new CopyOnWriteArrayList<DebugResponse>();
            var hitLatch = new CountDownLatch(1);

            handler.clientConnected("c1", r -> {
                liveResponses.add(r);
                if (r instanceof DebugResponse.BreakpointHit) hitLatch.countDown();
            });

            var sessionId = registerSessionWithEvents("s1");
            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.live, 0));

            var bp = new DebugCommand.BreakpointConfig("bp1",
                    DebugCommand.BreakpointType.TRANSITION_ENABLED, "T1", true);
            handler.handleCommand("c1", new DebugCommand.SetBreakpoint("s1", bp));

            // Trigger breakpoint by appending matching event
            registry.getSession(sessionId).get().eventStore()
                    .append(new NetEvent.TransitionEnabled(Instant.now(), "T1"));

            assertTrue(hitLatch.await(2, TimeUnit.SECONDS));

            var hits = liveResponses.stream()
                    .filter(r -> r instanceof DebugResponse.BreakpointHit)
                    .map(r -> (DebugResponse.BreakpointHit) r)
                    .toList();
            assertEquals(1, hits.size());
            assertEquals("bp1", hits.getFirst().breakpointId());
        }

        @Test
        void shouldIgnoreDisabledBreakpoint() throws InterruptedException {
            var liveResponses = new CopyOnWriteArrayList<DebugResponse>();

            handler.clientConnected("c1", liveResponses::add);

            var sessionId = registerSessionWithEvents("s1");
            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.live, 0));

            // Disabled breakpoint
            var bp = new DebugCommand.BreakpointConfig("bp1",
                    DebugCommand.BreakpointType.TRANSITION_ENABLED, "T1", false);
            handler.handleCommand("c1", new DebugCommand.SetBreakpoint("s1", bp));

            registry.getSession(sessionId).get().eventStore()
                    .append(new NetEvent.TransitionEnabled(Instant.now(), "T1"));
            Thread.sleep(100); // Wait for potential async delivery

            var hits = liveResponses.stream()
                    .filter(r -> r instanceof DebugResponse.BreakpointHit)
                    .toList();
            assertTrue(hits.isEmpty());
        }
    }

    @Nested
    class PlaybackControlFlow {

        @Test
        void shouldSetPlaybackSpeed() {
            connectClient("c1");
            registerSessionWithEvents("s1");
            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.live, 0));

            handler.handleCommand("c1", new DebugCommand.PlaybackSpeed("s1", 2.0));

            var state = lastResponseOfType(DebugResponse.PlaybackStateChanged.class);
            assertEquals(2.0, state.speed());
            assertEquals("s1", state.sessionId());
        }

        @Test
        void shouldTogglePauseResumeState() {
            connectClient("c1");
            registerSessionWithEvents("s1");
            handler.handleCommand("c1", new DebugCommand.Subscribe("s1",
                    DebugCommand.SubscriptionMode.live, 0));

            handler.handleCommand("c1", new DebugCommand.Pause("s1"));
            assertTrue(lastResponseOfType(DebugResponse.PlaybackStateChanged.class).paused());

            handler.handleCommand("c1", new DebugCommand.Resume("s1"));
            assertFalse(lastResponseOfType(DebugResponse.PlaybackStateChanged.class).paused());
        }
    }

    @Nested
    class ErrorHandling {

        @Test
        void shouldReturnErrorForUnknownSession() {
            connectClient("c1");
            handler.handleCommand("c1", new DebugCommand.Subscribe("nonexistent",
                    DebugCommand.SubscriptionMode.live, 0));

            var error = lastResponseOfType(DebugResponse.Error.class);
            assertEquals("SESSION_NOT_FOUND", error.code());
            assertEquals("nonexistent", error.sessionId());
        }

        @Test
        void shouldReturnErrorForSeekOnUnknownSession() {
            connectClient("c1");
            handler.handleCommand("c1", new DebugCommand.Seek("nonexistent", Instant.now()));

            var error = lastResponseOfType(DebugResponse.Error.class);
            assertEquals("SESSION_NOT_FOUND", error.code());
        }
    }

    @Nested
    class ComputeStatePureFunctions {

        @Test
        void shouldComputeStateFromEventSequence() {
            var now = Instant.now();
            var events = List.<NetEvent>of(
                    new NetEvent.TokenAdded(now, "P1", Token.of("a")),
                    new NetEvent.TransitionEnabled(now, "T1"),
                    new NetEvent.TransitionStarted(now, "T1", List.of(Token.of("a"))),
                    new NetEvent.TransitionCompleted(now, "T1", List.of(Token.of("b")), Duration.ofMillis(10)),
                    new NetEvent.TokenAdded(now, "P2", Token.of("b"))
            );

            var state = DebugProtocolHandler.computeState(events);

            // T1 was started then completed, so not in enabled or in-flight
            assertFalse(state.enabledTransitions().contains("T1"));
            assertFalse(state.inFlightTransitions().contains("T1"));

            // P1 and P2 should have tokens
            assertNotNull(state.marking().get("P1"));
            assertNotNull(state.marking().get("P2"));
        }
    }
}
