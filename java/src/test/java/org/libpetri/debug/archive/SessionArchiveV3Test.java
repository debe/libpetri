package org.libpetri.debug.archive;

import org.libpetri.core.Arc.In;
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
 * Round-trip + typed-token reconstruction tests for the libpetri 1.8.0 v3 archive format.
 *
 * <p>The writer always emits structured token JSON (see
 * {@link org.libpetri.debug.NetEventSerializer}). This test suite asserts:
 * <ul>
 *   <li>{@code write()} defaults to v3.</li>
 *   <li>Record, enum, primitive, and unit tokens round-trip with their concrete type.</li>
 *   <li>Legacy (v1/v2 header) archives remain readable by the v3-capable reader.</li>
 * </ul>
 */
class SessionArchiveV3Test {

    private static final Place<TestMessage> INPUT = Place.of("Input", TestMessage.class);

    private static final PetriNet TEST_NET = PetriNet.builder("TestNet")
            .transitions(
                    Transition.builder("Process")
                            .inputs(In.one(INPUT))
                            .build()
            )
            .build();

    // ======================== default-version contract ========================

    @Test
    void shouldDefaultToV3Format() throws IOException {
        var session = registerEmpty("default-v3", Map.of("channel", "voice"));
        var archive = writeDefaultAndReadHeader(session);
        assertEquals(3, archive.version(), "write() default must emit current version (v3)");
        assertInstanceOf(SessionArchive.V3.class, archive,
            "pattern-match target: consumers of 1.8.0+ archives should see V3 subtype");
    }

    @Test
    void shouldRoundTripV3HeaderFields() throws IOException {
        var registry = new DebugSessionRegistry();
        var session = registry.register("v3-hdr", TEST_NET, Map.of("channel", "voice", "env", "staging"));
        appendMixedEvents(session);
        registry.complete("v3-hdr");
        var completed = registry.getSession("v3-hdr").orElseThrow();

        var v3 = assertInstanceOf(SessionArchive.V3.class, writeDefaultAndReadFull(completed).metadata());
        assertEquals("v3-hdr", v3.sessionId());
        assertEquals(Map.of("channel", "voice", "env", "staging"), v3.tags());
        assertNotNull(v3.endTime());
        assertNotNull(v3.metadata(), "v3 must carry pre-computed metadata");
        assertTrue(v3.metadata().eventTypeHistogram().containsKey("TokenAdded"));
    }

    // ======================== typed token round-trips ========================

    @Test
    void recordTokensRoundTripWithConcreteType() throws IOException {
        var session = registerEmpty("record-tokens", Map.of("channel", "text"));
        var original = new TestMessage("USER", "hello world", 7);
        session.eventStore().append(
            new NetEvent.TokenAdded(Instant.parse("2026-04-17T10:00:00Z"), "Input", Token.of(original)));

        var imported = writeDefaultAndReadFull(session);
        var added = firstEvent(imported, NetEvent.TokenAdded.class);

        var value = added.token().value();
        assertInstanceOf(TestMessage.class, value, "record token must hydrate as its original type");
        assertEquals(original, value);
    }

    @Test
    void enumTokensRoundTripWithConcreteType() throws IOException {
        var session = registerEmpty("enum-tokens", Map.of());
        session.eventStore().append(
            new NetEvent.TokenAdded(Instant.parse("2026-04-17T10:00:00Z"), "Input",
                Token.of(TestMode.VOICE)));

        var imported = writeDefaultAndReadFull(session);
        var added = firstEvent(imported, NetEvent.TokenAdded.class);

        assertEquals(TestMode.VOICE, added.token().value(),
            "enum token must hydrate to the enum constant, not its name() string");
    }

    @Test
    void primitiveTokensRoundTripWithOriginalType() throws IOException {
        var session = registerEmpty("primitive-tokens", Map.of());
        var t0 = Instant.parse("2026-04-17T10:00:00Z");
        session.eventStore().append(new NetEvent.TokenAdded(t0, "P", Token.of("hello")));
        session.eventStore().append(new NetEvent.TokenAdded(t0.plusMillis(1), "P", Token.of(42)));
        session.eventStore().append(new NetEvent.TokenAdded(t0.plusMillis(2), "P", Token.of(3.14)));

        var imported = writeDefaultAndReadFull(session);
        var events = imported.eventStore().events().stream()
            .filter(e -> e instanceof NetEvent.TokenAdded).toList();

        assertEquals("hello", ((NetEvent.TokenAdded) events.get(0)).token().value());
        assertEquals(42, ((NetEvent.TokenAdded) events.get(1)).token().value(),
            "Integer tokens must round-trip as Integer, not long or BigInteger");
        assertEquals(3.14, ((NetEvent.TokenAdded) events.get(2)).token().value());
    }

    @Test
    void unitTokensRoundTripAsNullValue() throws IOException {
        var session = registerEmpty("unit-tokens", Map.of());
        session.eventStore().append(
            new NetEvent.TokenAdded(Instant.parse("2026-04-17T10:00:00Z"), "P", Token.unit()));

        var imported = writeDefaultAndReadFull(session);
        var added = firstEvent(imported, NetEvent.TokenAdded.class);
        assertNull(added.token().value(),
            "unit tokens must hydrate with null value (Token.of() disallows null)");
    }

    @Test
    void transitionStartedAndCompletedCarryStructuredTokens() throws IOException {
        var session = registerEmpty("transition-tokens", Map.of());
        var t0 = Instant.parse("2026-04-17T10:00:00Z");
        var consumed = new TestMessage("USER", "search sofa", 11);
        session.eventStore().append(new NetEvent.TransitionStarted(t0, "T", List.of(Token.of(consumed))));
        session.eventStore().append(new NetEvent.TransitionCompleted(t0.plusMillis(50), "T",
            List.of(Token.of(new TestMessage("ASSISTANT", "sure", 4))), Duration.ofMillis(50)));

        var imported = writeDefaultAndReadFull(session);
        var started = firstEvent(imported, NetEvent.TransitionStarted.class);
        var completed = firstEvent(imported, NetEvent.TransitionCompleted.class);

        assertEquals(consumed, started.consumedTokens().getFirst().value(),
            "transition event tokens must use the same structured format");
        assertInstanceOf(TestMessage.class, completed.producedTokens().getFirst().value());
    }

    // ======================== back-compat ========================

    @Test
    void shouldReadV2ArchiveOnV3CapableReader() throws IOException {
        var session = registerEmpty("v2-on-v3", Map.of("channel", "text"));
        session.eventStore().append(
            new NetEvent.TokenAdded(Instant.parse("2026-04-17T10:00:00Z"), "Input",
                Token.of(new TestMessage("USER", "hi", 2))));

        var buf = new ByteArrayOutputStream();
        new SessionArchiveWriter().writeV2(session, buf);
        var imported = new SessionArchiveReader().readFull(new ByteArrayInputStream(buf.toByteArray()));

        var v2 = assertInstanceOf(SessionArchive.V2.class, imported.metadata());
        assertEquals(2, v2.version());

        // The new writer emits v3 token bodies regardless of header — deliberately. Old (1.7.0)
        // readers of a 1.8.0-produced v2 archive would choke; the v3-capable reader on the same
        // classpath reconstructs the typed token.
        var added = firstEvent(imported, NetEvent.TokenAdded.class);
        assertInstanceOf(TestMessage.class, added.token().value());
    }

    @Test
    void shouldRejectUnknownVersion() throws IOException {
        var header = "{\"version\":42,\"sessionId\":\"x\",\"netName\":\"n\",\"dotDiagram\":\"\","
            + "\"startTime\":\"2026-04-15T10:00:00Z\",\"eventCount\":0,"
            + "\"structure\":{\"places\":[],\"transitions\":[]}}";
        var headerBytes = header.getBytes(java.nio.charset.StandardCharsets.UTF_8);

        var raw = new ByteArrayOutputStream();
        try (var dataOut = new java.io.DataOutputStream(
                new net.jpountz.lz4.LZ4FrameOutputStream(raw))) {
            dataOut.writeInt(headerBytes.length);
            dataOut.write(headerBytes);
        }

        var ex = assertThrows(IOException.class,
            () -> new SessionArchiveReader().readMetadata(new ByteArrayInputStream(raw.toByteArray())));
        assertTrue(ex.getMessage().contains("Unsupported archive version"));
        assertTrue(ex.getMessage().contains("42"));
    }

    // ======================== helpers + fixtures ========================

    /** Record-shaped token payload; Jackson serializes records via component accessors. */
    public record TestMessage(String kind, String text, int length) {}

    /** Enum-shaped token payload. */
    public enum TestMode { TEXT, VOICE }

    private DebugSessionRegistry.DebugSession registerEmpty(String id, Map<String, String> tags) {
        return new DebugSessionRegistry().register(id, TEST_NET, tags);
    }

    private void appendMixedEvents(DebugSessionRegistry.DebugSession session) {
        var t0 = Instant.parse("2026-04-17T10:00:00Z");
        session.eventStore().append(new NetEvent.ExecutionStarted(t0, "TestNet", "exec-1"));
        session.eventStore().append(new NetEvent.TokenAdded(t0.plusMillis(5), "Input",
            Token.of(new TestMessage("USER", "x", 1))));
    }

    private SessionArchive writeDefaultAndReadHeader(DebugSessionRegistry.DebugSession session) throws IOException {
        var buf = new ByteArrayOutputStream();
        new SessionArchiveWriter().write(session, buf);
        return new SessionArchiveReader().readMetadata(new ByteArrayInputStream(buf.toByteArray()));
    }

    private SessionArchiveReader.ImportedSession writeDefaultAndReadFull(DebugSessionRegistry.DebugSession session) throws IOException {
        var buf = new ByteArrayOutputStream();
        new SessionArchiveWriter().write(session, buf);
        return new SessionArchiveReader().readFull(new ByteArrayInputStream(buf.toByteArray()));
    }

    @SuppressWarnings("unchecked")
    private <T extends NetEvent> T firstEvent(SessionArchiveReader.ImportedSession imported, Class<T> type) {
        return (T) imported.eventStore().events().stream()
            .filter(type::isInstance)
            .findFirst()
            .orElseThrow(() -> new AssertionError("no " + type.getSimpleName() + " in archive"));
    }
}
