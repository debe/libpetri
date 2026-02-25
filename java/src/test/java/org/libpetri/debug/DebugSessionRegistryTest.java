package org.libpetri.debug;

import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.*;

class DebugSessionRegistryTest {

    private static final Place<String> INPUT = Place.of("Input", String.class);
    private static final Place<String> OUTPUT = Place.of("Output", String.class);

    private static final PetriNet TEST_NET = PetriNet.builder("TestNet")
            .transitions(
                    Transition.builder("Process")
                            .input(INPUT)
                            .output(OUTPUT)
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
        assertNotNull(session.mermaidDiagram());
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
    void shouldGenerateMermaidDiagram() {
        var registry = new DebugSessionRegistry();
        var session = registry.register("session-1", TEST_NET);

        var diagram = session.mermaidDiagram();

        assertNotNull(diagram);
        assertTrue(diagram.contains("flowchart"));
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

    @Test
    void shouldCleanUpMMapFilesOnEviction(@TempDir Path tempDir) {
        EventStoreFactory mmapFactory = sessionId -> MMapEventStore.open(sessionId, tempDir);
        var registry = new DebugSessionRegistry(2, mmapFactory);

        registry.register("session-1", TEST_NET);
        registry.register("session-2", TEST_NET);
        registry.complete("session-1"); // Mark as inactive so it's evicted first

        // Verify file exists before eviction
        var file1 = tempDir.resolve("session-1.events");
        assertTrue(file1.toFile().exists(), "MMap file should exist before eviction");

        // This should evict session-1 (oldest inactive) and delete its file
        registry.register("session-3", TEST_NET);

        assertEquals(2, registry.size());
        assertTrue(registry.getSession("session-1").isEmpty(), "session-1 should be evicted");
        assertFalse(file1.toFile().exists(), "MMap file should be deleted after eviction");
    }

    @Test
    void shouldCleanUpMMapFilesOnRemoval(@TempDir Path tempDir) {
        EventStoreFactory mmapFactory = sessionId -> MMapEventStore.open(sessionId, tempDir);
        var registry = new DebugSessionRegistry(50, mmapFactory);

        registry.register("session-1", TEST_NET);
        var file1 = tempDir.resolve("session-1.events");
        assertTrue(file1.toFile().exists(), "MMap file should exist before removal");

        registry.remove("session-1");

        assertFalse(file1.toFile().exists(), "MMap file should be deleted after removal");
    }
}
