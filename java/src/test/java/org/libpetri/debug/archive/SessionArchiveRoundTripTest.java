package org.libpetri.debug.archive;

import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Token;
import org.libpetri.core.Transition;
import org.libpetri.debug.DebugSessionRegistry;
import org.libpetri.event.NetEvent;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.time.Duration;
import java.time.Instant;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class SessionArchiveRoundTripTest {

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
    void shouldRoundTripArchive() throws IOException {
        var registry = new DebugSessionRegistry();
        var session = registry.register("test-session", TEST_NET);

        var now = Instant.now();
        session.eventStore().append(new NetEvent.ExecutionStarted(now, "TestNet", "exec-1"));
        session.eventStore().append(new NetEvent.TransitionEnabled(now.plusMillis(10), "Process"));
        session.eventStore().append(new NetEvent.TransitionStarted(now.plusMillis(20), "Process",
                List.of(Token.of("hello"))));
        session.eventStore().append(new NetEvent.TransitionCompleted(now.plusMillis(50), "Process",
                List.of(Token.of("world")), Duration.ofMillis(30)));
        session.eventStore().append(new NetEvent.TokenAdded(now.plusMillis(50), "Output", Token.of("world")));

        // Write archive
        var writer = new SessionArchiveWriter();
        var buf = new ByteArrayOutputStream();
        writer.write(session, buf);
        byte[] archiveBytes = buf.toByteArray();
        assertTrue(archiveBytes.length > 0, "Archive should not be empty");

        // Read metadata only
        var reader = new SessionArchiveReader();
        var metadata = reader.readMetadata(new ByteArrayInputStream(archiveBytes));
        assertEquals(SessionArchive.CURRENT_VERSION, metadata.version());
        assertEquals("test-session", metadata.sessionId());
        assertEquals("TestNet", metadata.netName());
        assertEquals(5, metadata.eventCount());
        assertNotNull(metadata.dotDiagram());
        assertNotNull(metadata.structure());
        assertFalse(metadata.structure().places().isEmpty());
        assertFalse(metadata.structure().transitions().isEmpty());

        // Read full archive
        var imported = reader.readFull(new ByteArrayInputStream(archiveBytes));
        assertEquals("test-session", imported.metadata().sessionId());
        assertEquals(5, imported.eventStore().eventCount());

        // Verify events
        var events = imported.eventStore().events();
        assertEquals(5, events.size());
        assertInstanceOf(NetEvent.ExecutionStarted.class, events.get(0));
        assertInstanceOf(NetEvent.TransitionEnabled.class, events.get(1));
        assertInstanceOf(NetEvent.TransitionStarted.class, events.get(2));
        assertInstanceOf(NetEvent.TransitionCompleted.class, events.get(3));
        assertInstanceOf(NetEvent.TokenAdded.class, events.get(4));

        // Verify event details survived round-trip
        var started = (NetEvent.TransitionStarted) events.get(2);
        assertEquals("Process", started.transitionName());
    }

    @Test
    void shouldRoundTripEmptySession() throws IOException {
        var registry = new DebugSessionRegistry();
        var session = registry.register("empty-session", TEST_NET);

        var writer = new SessionArchiveWriter();
        var buf = new ByteArrayOutputStream();
        writer.write(session, buf);

        var reader = new SessionArchiveReader();
        var imported = reader.readFull(new ByteArrayInputStream(buf.toByteArray()));

        assertEquals("empty-session", imported.metadata().sessionId());
        assertEquals(0, imported.eventStore().eventCount());
        assertEquals(0, imported.metadata().eventCount());
    }

    @Test
    void shouldPreserveNetStructure() throws IOException {
        var registry = new DebugSessionRegistry();
        var session = registry.register("struct-session", TEST_NET);

        var writer = new SessionArchiveWriter();
        var buf = new ByteArrayOutputStream();
        writer.write(session, buf);

        var reader = new SessionArchiveReader();
        var metadata = reader.readMetadata(new ByteArrayInputStream(buf.toByteArray()));

        var structure = metadata.structure();
        assertNotNull(structure);

        // Verify places
        var placeNames = structure.places().stream().map(p -> p.name()).toList();
        assertTrue(placeNames.contains("Input"));
        assertTrue(placeNames.contains("Output"));

        // Verify transitions
        var transitionNames = structure.transitions().stream().map(t -> t.name()).toList();
        assertTrue(transitionNames.contains("Process"));

        // Verify graph IDs
        var processTransition = structure.transitions().stream()
                .filter(t -> t.name().equals("Process"))
                .findFirst().orElseThrow();
        assertEquals("t_Process", processTransition.graphId());
    }

    @Test
    void shouldHandleLargeEventsThatExceedInitialBuffer() throws IOException {
        var registry = new DebugSessionRegistry();
        var session = registry.register("large-events", TEST_NET);

        var now = Instant.now();
        // Create a LogMessage with a message > 512 bytes to exercise buffer growth in reader
        var largeMessage = "x".repeat(1024);
        session.eventStore().append(new NetEvent.ExecutionStarted(now, "TestNet", "exec-1"));
        session.eventStore().append(new NetEvent.LogMessage(
                now.plusMillis(10), "Process", "test.Logger", "INFO", largeMessage, null, null));
        session.eventStore().append(new NetEvent.TransitionEnabled(now.plusMillis(20), "Process"));

        var writer = new SessionArchiveWriter();
        var buf = new ByteArrayOutputStream();
        writer.write(session, buf);

        var reader = new SessionArchiveReader();
        var imported = reader.readFull(new ByteArrayInputStream(buf.toByteArray()));

        assertEquals(3, imported.eventStore().eventCount());
        var events = imported.eventStore().events();
        assertInstanceOf(NetEvent.LogMessage.class, events.get(1));
        var logEvent = (NetEvent.LogMessage) events.get(1);
        assertEquals(largeMessage, logEvent.message());
    }

    @Test
    void shouldRegisterImportedSessionInRegistry() throws IOException {
        // Create and archive a session
        var registry = new DebugSessionRegistry();
        var session = registry.register("original", TEST_NET);
        session.eventStore().append(new NetEvent.TransitionEnabled(Instant.now(), "Process"));

        var writer = new SessionArchiveWriter();
        var buf = new ByteArrayOutputStream();
        writer.write(session, buf);

        // Import into a fresh registry
        var importRegistry = new DebugSessionRegistry();
        var reader = new SessionArchiveReader();
        var imported = reader.readFull(new ByteArrayInputStream(buf.toByteArray()));

        var importedSession = importRegistry.registerImported(
                imported.metadata().sessionId(),
                imported.metadata().netName(),
                imported.metadata().dotDiagram(),
                imported.metadata().structure(),
                imported.eventStore(),
                imported.metadata().startTime()
        );

        assertNotNull(importedSession);
        assertFalse(importedSession.active(), "Imported sessions should be inactive");
        assertNotNull(importedSession.importedStructure());
        assertEquals(1, importedSession.eventStore().eventCount());

        // Should be discoverable
        var found = importRegistry.getSession("original");
        assertTrue(found.isPresent());
        assertEquals("TestNet", found.get().netName());
    }
}
