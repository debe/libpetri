package org.libpetri.debug;

import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.debug.DebugResponse.NetStructure;
import org.libpetri.debug.DebugResponse.PlaceInfo;
import org.libpetri.debug.DebugResponse.TransitionInfo;
import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CyclicBarrier;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.*;

class DebugSessionRegistryTest {

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

    @Test
    void shouldRegisterSession() {
        var registry = new DebugSessionRegistry();

        var session = registry.register("session-1", TEST_NET);

        assertNotNull(session);
        assertEquals("session-1", session.sessionId());
        assertEquals("TestNet", session.netName());
        assertTrue(session.active());
        assertNotNull(session.dotDiagram());
        assertNotNull(session.eventStore());
    }

    @Test
    void shouldGetSessionById() {
        var registry = new DebugSessionRegistry();
        registry.register("session-1", TEST_NET);

        var session = registry.getSession("session-1");

        assertTrue(session.isPresent());
        assertEquals("session-1", session.get().sessionId());
    }

    @Test
    void shouldReturnEmptyForUnknownSession() {
        var registry = new DebugSessionRegistry();

        var session = registry.getSession("unknown");

        assertTrue(session.isEmpty());
    }

    @Test
    void shouldListSessions() {
        var registry = new DebugSessionRegistry();
        registry.register("session-1", TEST_NET);
        registry.register("session-2", TEST_NET);
        registry.register("session-3", TEST_NET);

        var sessions = registry.listSessions(10);

        assertEquals(3, sessions.size());
    }

    @Test
    void shouldListSessionsOrderedByStartTime() throws InterruptedException {
        var registry = new DebugSessionRegistry();
        registry.register("session-1", TEST_NET);
        Thread.sleep(10);
        registry.register("session-2", TEST_NET);
        Thread.sleep(10);
        registry.register("session-3", TEST_NET);

        var sessions = registry.listSessions(10);

        // Most recent first
        assertEquals("session-3", sessions.get(0).sessionId());
        assertEquals("session-2", sessions.get(1).sessionId());
        assertEquals("session-1", sessions.get(2).sessionId());
    }

    @Test
    void shouldLimitSessionList() {
        var registry = new DebugSessionRegistry();
        for (int i = 0; i < 10; i++) {
            registry.register("session-" + i, TEST_NET);
        }

        var sessions = registry.listSessions(3);

        assertEquals(3, sessions.size());
    }

    @Test
    void shouldCompleteSession() {
        var registry = new DebugSessionRegistry();
        registry.register("session-1", TEST_NET);

        registry.complete("session-1");

        var session = registry.getSession("session-1");
        assertTrue(session.isPresent());
        assertFalse(session.get().active());
    }

    @Test
    void shouldListActiveSessions() {
        var registry = new DebugSessionRegistry();
        registry.register("session-1", TEST_NET);
        registry.register("session-2", TEST_NET);
        registry.register("session-3", TEST_NET);
        registry.complete("session-2");

        var activeSessions = registry.listActiveSessions(10);

        assertEquals(2, activeSessions.size());
        assertTrue(activeSessions.stream().allMatch(DebugSessionRegistry.DebugSession::active));
    }

    @Test
    void shouldRemoveSession() {
        var registry = new DebugSessionRegistry();
        registry.register("session-1", TEST_NET);

        var removed = registry.remove("session-1");

        assertTrue(removed.isPresent());
        assertEquals("session-1", removed.get().sessionId());
        assertTrue(registry.getSession("session-1").isEmpty());
    }

    @Test
    void shouldEvictOldSessionsWhenAtCapacity() {
        var registry = new DebugSessionRegistry(3);
        registry.register("session-1", TEST_NET);
        registry.register("session-2", TEST_NET);
        registry.register("session-3", TEST_NET);
        registry.complete("session-1"); // Mark as inactive

        // This should evict session-1 (oldest inactive)
        registry.register("session-4", TEST_NET);

        assertEquals(3, registry.size());
        assertTrue(registry.getSession("session-1").isEmpty());
        assertTrue(registry.getSession("session-4").isPresent());
    }

    @Test
    void shouldCreateSessionSummary() {
        var registry = new DebugSessionRegistry();
        var session = registry.register("session-1", TEST_NET);

        var summary = registry.summaryOf(session);

        assertEquals("session-1", summary.sessionId());
        assertEquals("TestNet", summary.netName());
        assertTrue(summary.active());
        assertEquals(0, summary.eventCount());
    }

    @Test
    void shouldGenerateDotDiagram() {
        var registry = new DebugSessionRegistry();
        var session = registry.register("session-1", TEST_NET);

        var diagram = session.dotDiagram();

        assertNotNull(diagram);
        assertTrue(diagram.contains("digraph"));
        assertTrue(diagram.contains("Input"));
        assertTrue(diagram.contains("Output"));
        assertTrue(diagram.contains("Process"));
    }

    @Test
    void shouldUseCustomEventStoreFactory() {
        var customStoreCreated = new java.util.concurrent.atomic.AtomicBoolean(false);
        EventStoreFactory factory = sessionId -> {
            customStoreCreated.set(true);
            return new DebugEventStore(sessionId);
        };

        var registry = new DebugSessionRegistry(50, factory);
        registry.register("session-1", TEST_NET);

        assertTrue(customStoreCreated.get(), "Custom factory should be called during registration");
    }

    @Test
    void shouldStorePlaceAndTransitionInfo() {
        var registry = new DebugSessionRegistry();
        var session = registry.register("session-1", TEST_NET);

        // Check places
        assertNotNull(session.places());
        var placesData = session.places().data();
        assertTrue(placesData.containsKey("Input"));
        assertTrue(placesData.containsKey("Output"));

        var inputInfo = placesData.get("Input");
        assertTrue(inputInfo.isStart(), "Input should be a start place");
        assertFalse(inputInfo.isEnd(), "Input should not be an end place");

        var outputInfo = placesData.get("Output");
        assertFalse(outputInfo.isStart(), "Output should not be a start place");
        assertTrue(outputInfo.isEnd(), "Output should be an end place");

        // Check transitions
        assertNotNull(session.transitions());
        assertEquals(1, session.transitions().size());
        assertTrue(session.transitions().stream().anyMatch(t -> t.name().equals("Process")));
    }

    // ======================== Completion Listener Tests ========================

    @Test
    void shouldNotifyCompletionListenersOnComplete() {
        var notified = new ArrayList<String>();
        SessionCompletionListener listener = session -> notified.add(session.sessionId());

        var registry = new DebugSessionRegistry(50, DebugEventStore::new, List.of(listener));
        registry.register("session-1", TEST_NET);

        registry.complete("session-1");

        assertEquals(1, notified.size());
        assertEquals("session-1", notified.getFirst());
    }

    @Test
    void shouldNotifyMultipleListeners() {
        var notified1 = new ArrayList<String>();
        var notified2 = new ArrayList<String>();

        var registry = new DebugSessionRegistry(50, DebugEventStore::new, List.of(
            session -> notified1.add(session.sessionId()),
            session -> notified2.add(session.sessionId())
        ));
        registry.register("session-1", TEST_NET);
        registry.complete("session-1");

        assertEquals(1, notified1.size());
        assertEquals(1, notified2.size());
    }

    @Test
    void shouldContinueNotifyingAfterListenerException() {
        var notified = new ArrayList<String>();

        var registry = new DebugSessionRegistry(50, DebugEventStore::new, List.of(
            session -> { throw new RuntimeException("boom"); },
            session -> notified.add(session.sessionId())
        ));
        registry.register("session-1", TEST_NET);
        registry.complete("session-1");

        assertEquals(1, notified.size(), "Second listener should still be called");
    }

    @Test
    void shouldNotNotifyListenersForNonExistentSession() {
        var notified = new ArrayList<String>();
        var registry = new DebugSessionRegistry(50, DebugEventStore::new,
            List.of(session -> notified.add(session.sessionId())));

        registry.complete("non-existent");

        assertTrue(notified.isEmpty());
    }

    // ======================== registerImported Tests ========================

    @Test
    void shouldRegisterImportedSession() {
        var registry = new DebugSessionRegistry();
        var structure = new NetStructure(
            List.of(new PlaceInfo("Input", "p_Input", "String", true, false, false)),
            List.of(new TransitionInfo("Process", "t_Process"))
        );
        var eventStore = new DebugEventStore("imported-1");

        var session = registry.registerImported("imported-1", "TestNet", "digraph{}", structure, eventStore, Instant.now());

        assertNotNull(session);
        assertFalse(session.active());
        assertNotNull(session.importedStructure());
        assertEquals("TestNet", session.netName());
        assertNull(session.places());
        assertTrue(session.transitions().isEmpty());
    }

    @Test
    void shouldFindImportedSession() {
        var registry = new DebugSessionRegistry();
        var structure = new NetStructure(List.of(), List.of());
        var eventStore = new DebugEventStore("imported-1");

        registry.registerImported("imported-1", "TestNet", "digraph{}", structure, eventStore, Instant.now());

        var found = registry.getSession("imported-1");
        assertTrue(found.isPresent());
        assertEquals("TestNet", found.get().netName());
    }

    // ======================== buildNetStructure Tests ========================

    @Test
    void shouldBuildNetStructureFromLiveSession() {
        var registry = new DebugSessionRegistry();
        var session = registry.register("session-1", TEST_NET);

        var structure = session.buildNetStructure();

        assertNotNull(structure);
        assertFalse(structure.places().isEmpty());
        assertFalse(structure.transitions().isEmpty());

        var placeNames = structure.places().stream().map(PlaceInfo::name).toList();
        assertTrue(placeNames.contains("Input"));
        assertTrue(placeNames.contains("Output"));

        var transitionNames = structure.transitions().stream().map(TransitionInfo::name).toList();
        assertTrue(transitionNames.contains("Process"));
    }

    @Test
    void shouldReturnImportedStructureForImportedSession() {
        var registry = new DebugSessionRegistry();
        var structure = new NetStructure(
            List.of(new PlaceInfo("P1", "p_P1", "String", true, false, false)),
            List.of(new TransitionInfo("T1", "t_T1"))
        );
        var eventStore = new DebugEventStore("imported-1");
        var session = registry.registerImported("imported-1", "TestNet", "digraph{}", structure, eventStore, Instant.now());

        var built = session.buildNetStructure();

        assertSame(structure, built);
    }

    // ======================== Tags + endTime Tests (libpetri 1.6.0) ========================

    @Test
    void shouldRegisterSessionWithTags() {
        var registry = new DebugSessionRegistry();

        registry.register("session-1", TEST_NET, Map.of("channel", "voice", "env", "staging"));

        assertEquals(Map.of("channel", "voice", "env", "staging"), registry.tagsFor("session-1"));
    }

    @Test
    void shouldDefaultToEmptyTagsWithoutTagsArg() {
        var registry = new DebugSessionRegistry();

        registry.register("session-1", TEST_NET);

        assertEquals(Map.of(), registry.tagsFor("session-1"));
    }

    @Test
    void shouldReturnEmptyTagsForUnknownSession() {
        var registry = new DebugSessionRegistry();

        assertEquals(Map.of(), registry.tagsFor("never-registered"));
    }

    @Test
    void shouldSetTagAfterRegistration() {
        var registry = new DebugSessionRegistry();
        registry.register("session-1", TEST_NET);

        registry.tag("session-1", "channel", "text");
        registry.tag("session-1", "experiment", "abc");

        assertEquals(Map.of("channel", "text", "experiment", "abc"), registry.tagsFor("session-1"));
    }

    @Test
    void shouldReplaceExistingTagValue() {
        var registry = new DebugSessionRegistry();
        registry.register("session-1", TEST_NET, Map.of("channel", "voice"));

        registry.tag("session-1", "channel", "text");

        assertEquals(Map.of("channel", "text"), registry.tagsFor("session-1"));
    }

    @Test
    void shouldNoOpWhenTaggingUnknownSession() {
        var registry = new DebugSessionRegistry();

        // No session ever registered under this id — tag() must not create an orphan entry.
        registry.tag("never-registered", "channel", "voice");

        assertTrue(registry.tagsFor("never-registered").isEmpty());
        // listSessions must not be fooled into filtering against the orphan either.
        assertTrue(registry.listSessions(10, Map.of("channel", "voice")).isEmpty());
    }

    @Test
    void shouldNoOpWhenTaggingRemovedSession() {
        var registry = new DebugSessionRegistry();
        registry.register("session-1", TEST_NET);
        registry.remove("session-1");

        // Removed session — tag() must not resurrect the tag map.
        registry.tag("session-1", "channel", "voice");

        assertTrue(registry.tagsFor("session-1").isEmpty());
    }

    @Test
    void shouldFilterSessionsByTag() {
        var registry = new DebugSessionRegistry();
        registry.register("text-1", TEST_NET, Map.of("channel", "text"));
        registry.register("voice-1", TEST_NET, Map.of("channel", "voice"));
        registry.register("voice-2", TEST_NET, Map.of("channel", "voice"));

        var voices = registry.listSessions(10, Map.of("channel", "voice"));

        assertEquals(2, voices.size());
        assertTrue(voices.stream().allMatch(s -> s.sessionId().startsWith("voice")));
    }

    @Test
    void shouldFilterWithAndSemanticsAcrossMultipleTagKeys() {
        var registry = new DebugSessionRegistry();
        registry.register("s1", TEST_NET, Map.of("channel", "voice", "env", "staging"));
        registry.register("s2", TEST_NET, Map.of("channel", "voice", "env", "prod"));
        registry.register("s3", TEST_NET, Map.of("channel", "text", "env", "staging"));

        var filtered = registry.listSessions(10, Map.of("channel", "voice", "env", "staging"));

        assertEquals(1, filtered.size());
        assertEquals("s1", filtered.get(0).sessionId());
    }

    @Test
    void shouldReturnAllSessionsForEmptyFilter() {
        var registry = new DebugSessionRegistry();
        registry.register("s1", TEST_NET, Map.of("channel", "voice"));
        registry.register("s2", TEST_NET, Map.of("channel", "text"));

        var all = registry.listSessions(10, Map.of());

        assertEquals(2, all.size());
    }

    @Test
    void shouldNotMatchWhenFilterKeyValueDiffers() {
        var registry = new DebugSessionRegistry();
        registry.register("s1", TEST_NET, Map.of("channel", "voice", "env", "staging"));

        var result = registry.listSessions(10, Map.of("channel", "voice", "env", "prod"));

        assertTrue(result.isEmpty(), "AND-match must reject when any filter value differs");
    }

    @Test
    void shouldNotMatchWhenFilterKeyMissingFromSession() {
        var registry = new DebugSessionRegistry();
        registry.register("s1", TEST_NET, Map.of("channel", "voice"));

        var result = registry.listSessions(10, Map.of("env", "staging"));

        assertTrue(result.isEmpty(), "AND-match must reject when a filter key is absent from session tags");
    }

    @Test
    void shouldFilterActiveSessionsByTag() {
        var registry = new DebugSessionRegistry();
        registry.register("active-voice", TEST_NET, Map.of("channel", "voice"));
        registry.register("completed-voice", TEST_NET, Map.of("channel", "voice"));
        registry.register("active-text", TEST_NET, Map.of("channel", "text"));
        registry.complete("completed-voice");

        var activeVoices = registry.listActiveSessions(10, Map.of("channel", "voice"));

        assertEquals(1, activeVoices.size());
        assertEquals("active-voice", activeVoices.get(0).sessionId());
    }

    @Test
    void shouldStampEndTimeOnComplete() {
        var registry = new DebugSessionRegistry();
        var session = registry.register("session-1", TEST_NET);
        assertNull(session.endTime(), "Active session should have null endTime");

        registry.complete("session-1");

        var completed = registry.getSession("session-1").orElseThrow();
        assertNotNull(completed.endTime(), "Completed session should have endTime");
        assertFalse(completed.active());
    }

    @Test
    void shouldPreserveEndTimeOnSecondComplete() throws InterruptedException {
        var registry = new DebugSessionRegistry();
        registry.register("session-1", TEST_NET);

        registry.complete("session-1");
        var firstEnd = registry.getSession("session-1").orElseThrow().endTime();

        Thread.sleep(5);
        registry.complete("session-1");
        var secondEnd = registry.getSession("session-1").orElseThrow().endTime();

        assertEquals(firstEnd, secondEnd, "Second complete() must not overwrite endTime");
    }

    @Test
    void shouldComputeDurationForCompletedSession() {
        var registry = new DebugSessionRegistry();
        registry.register("session-1", TEST_NET);

        registry.complete("session-1");

        var completed = registry.getSession("session-1").orElseThrow();
        var duration = completed.duration();
        assertTrue(duration.isPresent());
        assertTrue(duration.get().toNanos() >= 0);
    }

    @Test
    void shouldReturnEmptyDurationForActiveSession() {
        var registry = new DebugSessionRegistry();
        var session = registry.register("session-1", TEST_NET);

        assertTrue(session.duration().isEmpty());
    }

    @Test
    void shouldClearTagsOnRemove() {
        var registry = new DebugSessionRegistry();
        registry.register("session-1", TEST_NET, Map.of("channel", "voice"));

        registry.remove("session-1");

        assertEquals(Map.of(), registry.tagsFor("session-1"));
    }

    @Test
    void shouldBuildSummaryWithTagsEndTimeAndDuration() {
        var registry = new DebugSessionRegistry();
        registry.register("session-1", TEST_NET, Map.of("channel", "voice"));
        registry.complete("session-1");

        var session = registry.getSession("session-1").orElseThrow();
        var summary = registry.summaryOf(session);

        assertEquals("session-1", summary.sessionId());
        assertEquals(Map.of("channel", "voice"), summary.tags());
        assertNotNull(summary.endTime());
        assertNotNull(summary.durationMs());
        assertFalse(summary.active());
    }

    @Test
    void shouldBuildSummaryWithEmptyTagsAndAbsentEndTimeForActiveSession() {
        var registry = new DebugSessionRegistry();
        var session = registry.register("session-1", TEST_NET);

        var summary = registry.summaryOf(session);

        assertEquals(Map.of(), summary.tags());
        assertNull(summary.endTime());
        assertNull(summary.durationMs());
        assertTrue(summary.active());
    }

    @Test
    void shouldRegisterImportedSessionWithTagsAndEndTime() {
        var registry = new DebugSessionRegistry();
        var structure = new NetStructure(
            List.of(new PlaceInfo("P1", "p_P1", "String", true, false, false)),
            List.of(new TransitionInfo("T1", "t_T1"))
        );
        var eventStore = new DebugEventStore("imported-1");
        var startTime = Instant.now().minusSeconds(60);
        var endTime = Instant.now();

        var session = registry.registerImported(
            "imported-1", "TestNet", "digraph{}", structure, eventStore,
            startTime, endTime, Map.of("channel", "voice", "source", "s3"));

        assertFalse(session.active());
        assertEquals(endTime, session.endTime());
        assertTrue(session.duration().isPresent());
        assertEquals(Duration.between(startTime, endTime), session.duration().get());
        assertEquals(Map.of("channel", "voice", "source", "s3"), registry.tagsFor("imported-1"));
    }

    @Test
    void shouldKeepBackwardCompatibleRegisterImportedWithoutTags() {
        var registry = new DebugSessionRegistry();
        var structure = new NetStructure(List.of(), List.of());
        var eventStore = new DebugEventStore("imported-1");

        var session = registry.registerImported("imported-1", "TestNet", "digraph{}", structure, eventStore, Instant.now());

        assertNull(session.endTime());
        assertEquals(Map.of(), registry.tagsFor("imported-1"));
    }

    @Test
    void shouldCleanupTagsOnEviction() {
        var registry = new DebugSessionRegistry(2);
        registry.register("session-1", TEST_NET, Map.of("channel", "voice"));
        registry.register("session-2", TEST_NET, Map.of("channel", "text"));
        registry.complete("session-1");

        registry.register("session-3", TEST_NET, Map.of("channel", "voice"));

        assertTrue(registry.getSession("session-1").isEmpty());
        assertEquals(Map.of(), registry.tagsFor("session-1"));
        assertEquals(Map.of("channel", "text"), registry.tagsFor("session-2"));
        assertEquals(Map.of("channel", "voice"), registry.tagsFor("session-3"));
    }

    @Test
    void shouldHandleConcurrentTaggingAndComplete() throws Exception {
        var registry = new DebugSessionRegistry();
        registry.register("s1", TEST_NET);

        int threadCount = 8;
        var barrier = new CyclicBarrier(threadCount);
        ExecutorService executor = Executors.newFixedThreadPool(threadCount);
        try {
            for (int i = 0; i < threadCount; i++) {
                final int idx = i;
                executor.submit(() -> {
                    try {
                        barrier.await();
                        if (idx % 2 == 0) {
                            registry.tag("s1", "k" + idx, "v");
                        } else {
                            registry.complete("s1");
                        }
                    } catch (Exception e) {
                        throw new RuntimeException(e);
                    }
                });
            }
        } finally {
            executor.shutdown();
            assertTrue(executor.awaitTermination(5, TimeUnit.SECONDS),
                "concurrent tasks should finish within timeout");
        }

        var session = registry.getSession("s1").orElseThrow();
        assertFalse(session.active(), "session should be marked complete");
        assertNotNull(session.endTime(), "endTime should be stamped after complete()");
        var tags = registry.tagsFor("s1");
        assertEquals(4, tags.size(), "four even-indexed threads tagged the session");
        for (var k : List.of("k0", "k2", "k4", "k6")) {
            assertEquals("v", tags.get(k), "missing tag " + k);
        }
    }
}
