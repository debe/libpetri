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
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Round-trip tests for the libpetri 1.7.0 v2 archive format. These focus on the
 * format-version-specific behavior (richer header, pre-computed metadata, mixed bucket
 * coexistence) — the v1 round-trip is exercised by {@link SessionArchiveRoundTripTest}.
 */
class SessionArchiveV2Test {

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

    // ======================== v2 round-trip ========================

    @Test
    void shouldDefaultToV2Format() throws IOException {
        var session = registerWithEvents("default-v2", Map.of("channel", "voice"));

        var archive = writeAndReadHeader(session);

        assertEquals(SessionArchive.CURRENT_VERSION, archive.version(), "default writer should emit current version");
        assertEquals(2, archive.version(), "current version should be 2 in libpetri 1.7.0");
        assertInstanceOf(SessionArchive.V2.class, archive,
            "default writer should produce a V2 record so callers can pattern-match on tags/endTime/metadata");
    }

    @Test
    void shouldRoundTripTagsAndEndTime() throws IOException {
        var registry = new DebugSessionRegistry();
        var session = registry.register("voice-1", TEST_NET, Map.of("channel", "voice", "env", "staging"));
        appendNonErrorEvents(session);
        registry.complete("voice-1");
        var completed = registry.getSession("voice-1").orElseThrow();

        var imported = writeAndReadFull(completed);

        // Pattern match to the v2 subtype to access v2-only fields with type safety.
        var v2 = assertInstanceOf(SessionArchive.V2.class, imported.metadata());
        assertEquals("voice-1", v2.sessionId());
        assertEquals(Map.of("channel", "voice", "env", "staging"), v2.tags());
        assertNotNull(v2.endTime(), "endTime should be preserved across the round-trip");
        assertNotNull(v2.durationMs(), "durationMs derived from start/end should be available");
        assertTrue(v2.durationMs() >= 0);
    }

    @Test
    void shouldRoundTripPreComputedMetadata() throws IOException {
        var registry = new DebugSessionRegistry();
        var session = registry.register("metadata-1", TEST_NET);

        // Mix of event types so the histogram has multiple buckets.
        var t0 = Instant.parse("2026-04-15T10:00:00Z");
        session.eventStore().append(new NetEvent.ExecutionStarted(t0, "TestNet", "exec-1"));
        session.eventStore().append(new NetEvent.TransitionEnabled(t0.plusMillis(10), "Process"));
        session.eventStore().append(new NetEvent.TransitionStarted(t0.plusMillis(20), "Process",
                List.of(Token.of("hello"))));
        session.eventStore().append(new NetEvent.TransitionStarted(t0.plusMillis(30), "Process",
                List.of(Token.of("world"))));
        session.eventStore().append(new NetEvent.TransitionCompleted(t0.plusMillis(50), "Process",
                List.of(Token.of("done")), Duration.ofMillis(20)));

        var imported = writeAndReadFull(session);
        var v2 = assertInstanceOf(SessionArchive.V2.class, imported.metadata());
        var metadata = v2.metadata();

        assertNotNull(metadata, "v2 archive must carry pre-computed metadata");
        assertEquals(1L, metadata.eventTypeHistogram().get("ExecutionStarted"));
        assertEquals(1L, metadata.eventTypeHistogram().get("TransitionEnabled"));
        assertEquals(2L, metadata.eventTypeHistogram().get("TransitionStarted"));
        assertEquals(1L, metadata.eventTypeHistogram().get("TransitionCompleted"));
        assertNull(metadata.eventTypeHistogram().get("TokenAdded"), "absent types should not appear");
        assertEquals(t0, metadata.firstEventTime());
        assertEquals(t0.plusMillis(50), metadata.lastEventTime());
        assertFalse(metadata.hasErrors(), "no error events were appended");
    }

    @Test
    void shouldDetectErrorsInMetadata() throws IOException {
        var registry = new DebugSessionRegistry();
        var session = registry.register("err-1", TEST_NET);
        var t0 = Instant.parse("2026-04-15T10:00:00Z");

        session.eventStore().append(new NetEvent.ExecutionStarted(t0, "TestNet", "exec-1"));
        session.eventStore().append(new NetEvent.TransitionFailed(
                t0.plusMillis(10), "Process", "boom", "java.lang.IllegalStateException"));

        var imported = writeAndReadFull(session);
        var v2 = assertInstanceOf(SessionArchive.V2.class, imported.metadata());
        assertTrue(v2.metadata().hasErrors(), "TransitionFailed must flag hasErrors");
    }

    @Test
    void shouldDetectErrorLogLevelInMetadata() throws IOException {
        var registry = new DebugSessionRegistry();
        var session = registry.register("err-log", TEST_NET);
        var t0 = Instant.parse("2026-04-15T10:00:00Z");
        session.eventStore().append(new NetEvent.LogMessage(
                t0, "Process", "test.Logger", "ERROR", "kaboom", null, null));

        var imported = writeAndReadFull(session);
        var v2 = assertInstanceOf(SessionArchive.V2.class, imported.metadata());
        assertTrue(v2.metadata().hasErrors(), "LogMessage at ERROR level must flag hasErrors");
    }

    @Test
    void shouldRoundTripEmptySessionAsV2() throws IOException {
        var registry = new DebugSessionRegistry();
        var session = registry.register("empty-v2", TEST_NET, Map.of("channel", "text"));

        var imported = writeAndReadFull(session);
        var v2 = assertInstanceOf(SessionArchive.V2.class, imported.metadata());

        assertEquals(0, v2.eventCount());
        assertEquals(0, imported.eventStore().eventCount());
        assertEquals(Map.of("channel", "text"), v2.tags());
        assertNull(v2.endTime(), "active session must have no endTime");
        assertNull(v2.durationMs(), "active session must have no duration");
        assertNotNull(v2.metadata(), "metadata should never be null even for empty sessions");
        assertTrue(v2.metadata().eventTypeHistogram().isEmpty());
        assertNull(v2.metadata().firstEventTime());
    }

    // ======================== mixed v1/v2 reading ========================

    @Test
    void shouldReadV1ArchiveAfterRefactor() throws IOException {
        var registry = new DebugSessionRegistry();
        var session = registry.register("legacy-v1", TEST_NET);
        session.eventStore().append(new NetEvent.TransitionEnabled(Instant.now(), "Process"));

        var writer = new SessionArchiveWriter();
        var buf = new ByteArrayOutputStream();
        writer.writeV1(session, buf);

        var imported = new SessionArchiveReader().readFull(new ByteArrayInputStream(buf.toByteArray()));

        var v1 = assertInstanceOf(SessionArchive.V1.class, imported.metadata());
        assertEquals(1, v1.version());
        assertEquals("legacy-v1", v1.sessionId());
        assertEquals(1, imported.eventStore().eventCount());

        // v2-only accessors return defaults for v1 archives via the sealed interface.
        assertEquals(Map.of(), v1.tags());
        assertNull(v1.endTime());
        assertNull(v1.metadata(), "v1 has no pre-computed metadata; callers should use SessionMetadata.fromEvents()");
    }

    @Test
    void shouldReadMixedV1AndV2InSameBucket() throws IOException {
        var registry = new DebugSessionRegistry();

        var v1Session = registry.register("legacy", TEST_NET);
        v1Session.eventStore().append(new NetEvent.TransitionEnabled(Instant.now(), "Process"));
        var v1Bytes = new ByteArrayOutputStream();
        new SessionArchiveWriter().writeV1(v1Session, v1Bytes);

        var v2Session = registry.register("modern", TEST_NET, Map.of("channel", "voice"));
        v2Session.eventStore().append(new NetEvent.TransitionEnabled(Instant.now(), "Process"));
        var v2Bytes = new ByteArrayOutputStream();
        new SessionArchiveWriter().write(v2Session, v2Bytes);

        var reader = new SessionArchiveReader();
        var v1Read = reader.readFull(new ByteArrayInputStream(v1Bytes.toByteArray()));
        var v2Read = reader.readFull(new ByteArrayInputStream(v2Bytes.toByteArray()));

        assertInstanceOf(SessionArchive.V1.class, v1Read.metadata());
        assertInstanceOf(SessionArchive.V2.class, v2Read.metadata());
        assertEquals("legacy", v1Read.metadata().sessionId());
        assertEquals("modern", v2Read.metadata().sessionId());
        assertEquals(Map.of("channel", "voice"), v2Read.metadata().tags());
        assertEquals(Map.of(), v1Read.metadata().tags(), "v1 default tag accessor must be empty");
    }

    @Test
    void shouldRejectUnsupportedVersion() throws IOException {
        // Hand-craft a header with version=99 by abusing the V2 record's lenient deserializer.
        // We can't use writeV1/write because both pin the version. Instead, write a header
        // by directly encoding bytes. Easier: construct a malformed V2 instance and check
        // that the deserializer rejects unknown versions on read.
        var v2Json = "{\"version\":99,\"sessionId\":\"x\",\"netName\":\"n\",\"dotDiagram\":\"\","
                + "\"startTime\":\"2026-04-15T10:00:00Z\",\"eventCount\":0,"
                + "\"structure\":{\"places\":[],\"transitions\":[]}}";
        var headerBytes = v2Json.getBytes(java.nio.charset.StandardCharsets.UTF_8);

        var raw = new ByteArrayOutputStream();
        try (var dataOut = new java.io.DataOutputStream(
                new net.jpountz.lz4.LZ4FrameOutputStream(raw))) {
            dataOut.writeInt(headerBytes.length);
            dataOut.write(headerBytes);
        }

        var reader = new SessionArchiveReader();
        var ex = assertThrows(IOException.class,
            () -> reader.readMetadata(new ByteArrayInputStream(raw.toByteArray())));
        assertTrue(ex.getMessage().contains("Unsupported archive version"),
            "expected unsupported-version error, got: " + ex.getMessage());
        assertTrue(ex.getMessage().contains("99"));
    }

    // ======================== SessionMetadata.fromEvents (v1 fallback) ========================

    @Test
    void sessionMetadataFromEventsShouldComputeOnDemandForV1() {
        var registry = new DebugSessionRegistry();
        var session = registry.register("v1-fallback", TEST_NET);
        var t0 = Instant.parse("2026-04-15T10:00:00Z");
        session.eventStore().append(new NetEvent.ExecutionStarted(t0, "TestNet", "exec-1"));
        session.eventStore().append(new NetEvent.TransitionFailed(
                t0.plusMillis(20), "Process", "x", "T"));

        var metadata = SessionMetadata.fromEvents(session.eventStore().events());

        assertEquals(t0, metadata.firstEventTime());
        assertEquals(t0.plusMillis(20), metadata.lastEventTime());
        assertTrue(metadata.hasErrors());
        assertEquals(1L, metadata.eventTypeHistogram().get("ExecutionStarted"));
        assertEquals(1L, metadata.eventTypeHistogram().get("TransitionFailed"));
    }

    // ======================== helpers ========================

    private DebugSessionRegistry.DebugSession registerWithEvents(String id, Map<String, String> tags) {
        var registry = new DebugSessionRegistry();
        var session = registry.register(id, TEST_NET, tags);
        appendNonErrorEvents(session);
        return session;
    }

    private void appendNonErrorEvents(DebugSessionRegistry.DebugSession session) {
        var t0 = Instant.parse("2026-04-15T10:00:00Z");
        session.eventStore().append(new NetEvent.ExecutionStarted(t0, "TestNet", "exec-1"));
        session.eventStore().append(new NetEvent.TransitionStarted(t0.plusMillis(10), "Process",
                List.of(Token.of("hello"))));
        session.eventStore().append(new NetEvent.TransitionCompleted(t0.plusMillis(50), "Process",
                List.of(Token.of("world")), Duration.ofMillis(40)));
    }

    private SessionArchive writeAndReadHeader(DebugSessionRegistry.DebugSession session) throws IOException {
        var buf = new ByteArrayOutputStream();
        new SessionArchiveWriter().write(session, buf);
        return new SessionArchiveReader().readMetadata(new ByteArrayInputStream(buf.toByteArray()));
    }

    private SessionArchiveReader.ImportedSession writeAndReadFull(DebugSessionRegistry.DebugSession session) throws IOException {
        var buf = new ByteArrayOutputStream();
        new SessionArchiveWriter().write(session, buf);
        return new SessionArchiveReader().readFull(new ByteArrayInputStream(buf.toByteArray()));
    }
}
