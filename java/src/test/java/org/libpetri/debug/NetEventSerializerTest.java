package org.libpetri.debug;

import org.libpetri.core.Token;
import org.libpetri.event.NetEvent;
import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.time.Instant;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

class NetEventSerializerTest {

    private final NetEventSerializer serializer = new NetEventSerializer();

    @Test
    void shouldRoundTripExecutionStarted() {
        var event = new NetEvent.ExecutionStarted(Instant.now(), "TestNet", "exec-1");
        var result = serializer.deserialize(serializer.serialize(event));
        assertInstanceOf(NetEvent.ExecutionStarted.class, result);
        var e = (NetEvent.ExecutionStarted) result;
        assertEquals("TestNet", e.netName());
        assertEquals("exec-1", e.executionId());
    }

    @Test
    void shouldRoundTripExecutionCompleted() {
        var event = new NetEvent.ExecutionCompleted(Instant.now(), "TestNet", "exec-1", Duration.ofMillis(500));
        var result = serializer.deserialize(serializer.serialize(event));
        assertInstanceOf(NetEvent.ExecutionCompleted.class, result);
        var e = (NetEvent.ExecutionCompleted) result;
        assertEquals(Duration.ofMillis(500), e.totalDuration());
    }

    @Test
    void shouldRoundTripTransitionEnabled() {
        var event = new NetEvent.TransitionEnabled(Instant.now(), "T1");
        var result = serializer.deserialize(serializer.serialize(event));
        assertInstanceOf(NetEvent.TransitionEnabled.class, result);
        assertEquals("T1", ((NetEvent.TransitionEnabled) result).transitionName());
    }

    @Test
    void shouldRoundTripTransitionClockRestarted() {
        var event = new NetEvent.TransitionClockRestarted(Instant.now(), "T1");
        var result = serializer.deserialize(serializer.serialize(event));
        assertInstanceOf(NetEvent.TransitionClockRestarted.class, result);
    }

    @Test
    void shouldRoundTripTransitionStarted() {
        var event = new NetEvent.TransitionStarted(Instant.now(), "T1", List.of(Token.of("hello")));
        var result = serializer.deserialize(serializer.serialize(event));
        assertInstanceOf(NetEvent.TransitionStarted.class, result);
        var e = (NetEvent.TransitionStarted) result;
        assertEquals("T1", e.transitionName());
        assertEquals(1, e.consumedTokens().size());
    }

    @Test
    void shouldRoundTripTransitionCompleted() {
        var event = new NetEvent.TransitionCompleted(Instant.now(), "T1", List.of(Token.of("out")), Duration.ofMillis(100));
        var result = serializer.deserialize(serializer.serialize(event));
        assertInstanceOf(NetEvent.TransitionCompleted.class, result);
    }

    @Test
    void shouldRoundTripTransitionFailed() {
        var event = new NetEvent.TransitionFailed(Instant.now(), "T1", "boom", "java.lang.RuntimeException");
        var result = serializer.deserialize(serializer.serialize(event));
        assertInstanceOf(NetEvent.TransitionFailed.class, result);
        var e = (NetEvent.TransitionFailed) result;
        assertEquals("boom", e.errorMessage());
    }

    @Test
    void shouldRoundTripTransitionTimedOut() {
        var event = new NetEvent.TransitionTimedOut(Instant.now(), "T1", Duration.ofSeconds(5), Duration.ofSeconds(6));
        var result = serializer.deserialize(serializer.serialize(event));
        assertInstanceOf(NetEvent.TransitionTimedOut.class, result);
    }

    @Test
    void shouldRoundTripActionTimedOut() {
        var event = new NetEvent.ActionTimedOut(Instant.now(), "T1", Duration.ofSeconds(3));
        var result = serializer.deserialize(serializer.serialize(event));
        assertInstanceOf(NetEvent.ActionTimedOut.class, result);
    }

    @Test
    void shouldRoundTripTokenAdded() {
        var event = new NetEvent.TokenAdded(Instant.now(), "P1", Token.of("value"));
        var result = serializer.deserialize(serializer.serialize(event));
        assertInstanceOf(NetEvent.TokenAdded.class, result);
        assertEquals("P1", ((NetEvent.TokenAdded) result).placeName());
    }

    @Test
    void shouldRoundTripTokenRemoved() {
        var event = new NetEvent.TokenRemoved(Instant.now(), "P1", Token.of(42));
        var result = serializer.deserialize(serializer.serialize(event));
        assertInstanceOf(NetEvent.TokenRemoved.class, result);
    }

    @Test
    void shouldRoundTripLogMessage() {
        var event = new NetEvent.LogMessage(
            Instant.now(), "T1", "com.example.Foo", "WARN", "something happened",
            "java.lang.RuntimeException", "oops"
        );
        var result = serializer.deserialize(serializer.serialize(event));
        assertInstanceOf(NetEvent.LogMessage.class, result);
        var e = (NetEvent.LogMessage) result;
        assertEquals("T1", e.transitionName());
        assertEquals("com.example.Foo", e.loggerName());
        assertEquals("WARN", e.level());
        assertEquals("something happened", e.message());
        assertEquals("java.lang.RuntimeException", e.throwable());
        assertEquals("oops", e.throwableMessage());
    }

    @Test
    void shouldRoundTripLogMessageWithNullThrowable() {
        var event = new NetEvent.LogMessage(
            Instant.now(), "T1", "com.example.Foo", "INFO", "hello", null, null
        );
        var result = serializer.deserialize(serializer.serialize(event));
        assertInstanceOf(NetEvent.LogMessage.class, result);
        var e = (NetEvent.LogMessage) result;
        assertNull(e.throwable());
        assertNull(e.throwableMessage());
    }

    @Test
    void shouldRoundTripMarkingSnapshot() {
        var event = new NetEvent.MarkingSnapshot(
            Instant.now(),
            Map.of("P1", List.of(Token.of("a"), Token.of("b")))
        );
        var result = serializer.deserialize(serializer.serialize(event));
        assertInstanceOf(NetEvent.MarkingSnapshot.class, result);
        var e = (NetEvent.MarkingSnapshot) result;
        assertTrue(e.marking().containsKey("P1"));
        assertEquals(2, e.marking().get("P1").size());
    }

    @Test
    void shouldThrowOnInvalidBytes() {
        assertThrows(NetEventSerializer.NetEventSerializationException.class,
            () -> serializer.deserialize(new byte[]{1, 2, 3}));
    }

    // --- Tests for non-serializable token values (mirroring Conversation-like domain objects) ---

    /** Simulates a domain object with no public getters or Jackson annotations. */
    @SuppressWarnings("unused")
    static class OpaqueValue {
        private final String secret = "hidden";
        @Override public String toString() { return "OpaqueValue{censored}"; }
    }

    @Test
    void shouldSerializeTokenRemovedWithNonSerializableValue() {
        var event = new NetEvent.TokenRemoved(Instant.now(), "P1", Token.of(new OpaqueValue()));
        byte[] bytes = serializer.serialize(event);
        var result = serializer.deserialize(bytes);
        assertInstanceOf(NetEvent.TokenRemoved.class, result);
        assertEquals("P1", ((NetEvent.TokenRemoved) result).placeName());
    }

    @Test
    void shouldSerializeTokenAddedWithNonSerializableValue() {
        var event = new NetEvent.TokenAdded(Instant.now(), "P1", Token.of(new OpaqueValue()));
        byte[] bytes = serializer.serialize(event);
        var result = serializer.deserialize(bytes);
        assertInstanceOf(NetEvent.TokenAdded.class, result);
        assertEquals("P1", ((NetEvent.TokenAdded) result).placeName());
    }

    @Test
    void shouldSerializeTransitionStartedWithNonSerializableTokens() {
        var event = new NetEvent.TransitionStarted(Instant.now(), "T1",
            List.of(Token.of(new OpaqueValue()), Token.of(new OpaqueValue())));
        byte[] bytes = serializer.serialize(event);
        var result = serializer.deserialize(bytes);
        assertInstanceOf(NetEvent.TransitionStarted.class, result);
        var e = (NetEvent.TransitionStarted) result;
        assertEquals("T1", e.transitionName());
        assertEquals(2, e.consumedTokens().size());
    }

    @Test
    void shouldSerializeTransitionCompletedWithNonSerializableTokens() {
        var event = new NetEvent.TransitionCompleted(Instant.now(), "T1",
            List.of(Token.of(new OpaqueValue())), Duration.ofMillis(50));
        byte[] bytes = serializer.serialize(event);
        var result = serializer.deserialize(bytes);
        assertInstanceOf(NetEvent.TransitionCompleted.class, result);
    }

    @Test
    void shouldSerializeMarkingSnapshotWithNonSerializableTokens() {
        var event = new NetEvent.MarkingSnapshot(Instant.now(),
            Map.of("P1", List.of(Token.of(new OpaqueValue())),
                   "P2", List.of(Token.of(new OpaqueValue()), Token.of("simple"))));
        byte[] bytes = serializer.serialize(event);
        var result = serializer.deserialize(bytes);
        assertInstanceOf(NetEvent.MarkingSnapshot.class, result);
        var e = (NetEvent.MarkingSnapshot) result;
        assertTrue(e.marking().containsKey("P1"));
        assertTrue(e.marking().containsKey("P2"));
        assertEquals(2, e.marking().get("P2").size());
    }

    @Test
    void shouldSerializeTokenWithNullValue() {
        var event = new NetEvent.TokenAdded(Instant.now(), "P1", Token.unit());
        byte[] bytes = serializer.serialize(event);
        var result = serializer.deserialize(bytes);
        assertInstanceOf(NetEvent.TokenAdded.class, result);
    }
}
