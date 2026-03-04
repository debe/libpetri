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

import java.time.Instant;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

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

        var summary = session.toSummary();

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
}
