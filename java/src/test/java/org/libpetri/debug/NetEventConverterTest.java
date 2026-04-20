package org.libpetri.debug;

import org.libpetri.core.Token;
import org.libpetri.debug.DebugResponse.NetEventInfo;
import org.libpetri.debug.DebugResponse.TokenInfo;
import org.libpetri.event.NetEvent;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.time.Instant;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

class NetEventConverterTest {

    private static final Instant NOW = Instant.parse("2024-01-15T10:30:00Z");

    @Nested
    class ToEventInfo {

        @Test
        void shouldConvertLifecycleEvents() {
            var started = new NetEvent.ExecutionStarted(NOW, "MyNet", "exec-1");
            var info = NetEventConverter.toEventInfo(started);

            assertEquals("ExecutionStarted", info.type());
            assertEquals(NOW.toString(), info.timestamp());
            assertNull(info.transitionName());
            assertNull(info.placeName());
            assertEquals("MyNet", info.details().get("netName"));
            assertEquals("exec-1", info.details().get("executionId"));

            var completed = new NetEvent.ExecutionCompleted(NOW, "MyNet", "exec-1", Duration.ofMillis(500));
            var completedInfo = NetEventConverter.toEventInfo(completed);
            assertEquals("ExecutionCompleted", completedInfo.type());
            assertEquals(500L, completedInfo.details().get("totalDurationMs"));
        }

        @Test
        void shouldConvertTransitionEvents() {
            var enabled = new NetEvent.TransitionEnabled(NOW, "T1");
            var info = NetEventConverter.toEventInfo(enabled);
            assertEquals("TransitionEnabled", info.type());
            assertEquals("T1", info.transitionName());
            assertNull(info.placeName());

            var clockRestarted = new NetEvent.TransitionClockRestarted(NOW, "T2");
            assertEquals("TransitionClockRestarted", NetEventConverter.toEventInfo(clockRestarted).type());

            var started = new NetEvent.TransitionStarted(NOW, "T1", List.of(Token.of("val")));
            var startedInfo = NetEventConverter.toEventInfo(started);
            assertEquals("TransitionStarted", startedInfo.type());
            assertInstanceOf(List.class, startedInfo.details().get("consumedTokens"));

            var completed = new NetEvent.TransitionCompleted(NOW, "T1", List.of(Token.of("out")), Duration.ofMillis(42));
            var completedInfo = NetEventConverter.toEventInfo(completed);
            assertEquals("TransitionCompleted", completedInfo.type());
            assertEquals(42L, completedInfo.details().get("durationMs"));

            var failed = new NetEvent.TransitionFailed(NOW, "T1", "boom", "java.lang.RuntimeException");
            var failedInfo = NetEventConverter.toEventInfo(failed);
            assertEquals("TransitionFailed", failedInfo.type());
            assertEquals("boom", failedInfo.details().get("errorMessage"));
            assertEquals("java.lang.RuntimeException", failedInfo.details().get("exceptionType"));
        }

        @Test
        void shouldConvertTimeoutEvents() {
            var transitionTimeout = new NetEvent.TransitionTimedOut(NOW, "T1", Duration.ofMillis(1000), Duration.ofMillis(1200));
            var info = NetEventConverter.toEventInfo(transitionTimeout);
            assertEquals("TransitionTimedOut", info.type());
            assertEquals("T1", info.transitionName());
            assertEquals(1000L, info.details().get("deadlineMs"));
            assertEquals(1200L, info.details().get("actualDurationMs"));

            var actionTimeout = new NetEvent.ActionTimedOut(NOW, "T2", Duration.ofMillis(500));
            var actionInfo = NetEventConverter.toEventInfo(actionTimeout);
            assertEquals("ActionTimedOut", actionInfo.type());
            assertEquals(500L, actionInfo.details().get("timeoutMs"));
        }

        @Test
        void shouldConvertTokenEvents() {
            var token = Token.of("hello");
            var added = new NetEvent.TokenAdded(NOW, "P1", token);
            var info = NetEventConverter.toEventInfo(added);
            assertEquals("TokenAdded", info.type());
            assertNull(info.transitionName());
            assertEquals("P1", info.placeName());
            assertInstanceOf(TokenInfo.class, info.details().get("token"));

            var removed = new NetEvent.TokenRemoved(NOW, "P1", token);
            var removedInfo = NetEventConverter.toEventInfo(removed);
            assertEquals("TokenRemoved", removedInfo.type());
            assertEquals("P1", removedInfo.placeName());
        }

        @Test
        void shouldConvertMarkingSnapshot() {
            var token = Token.of("data");
            var marking = Map.<String, List<Token<?>>>of("P1", List.of(token));
            var snapshot = new NetEvent.MarkingSnapshot(NOW, marking);
            var info = NetEventConverter.toEventInfo(snapshot);

            assertEquals("MarkingSnapshot", info.type());
            assertNull(info.transitionName());
            assertNull(info.placeName());
            assertInstanceOf(Map.class, info.details().get("marking"));
        }

        @Test
        void shouldConvertLogMessageWithAndWithoutThrowable() {
            var withoutThrowable = new NetEvent.LogMessage(NOW, "T1", "com.example.Foo", "INFO", "hello", null, null);
            var info = NetEventConverter.toEventInfo(withoutThrowable);
            assertEquals("LogMessage", info.type());
            assertEquals("T1", info.transitionName());
            assertEquals("hello", info.details().get("message"));
            assertEquals("INFO", info.details().get("level"));
            assertFalse(info.details().containsKey("throwable"));
            assertFalse(info.details().containsKey("throwableMessage"));

            var withThrowable = new NetEvent.LogMessage(NOW, "T1", "com.example.Foo", "ERROR", "oops",
                "java.lang.RuntimeException", "boom");
            var throwInfo = NetEventConverter.toEventInfo(withThrowable);
            assertEquals("java.lang.RuntimeException", throwInfo.details().get("throwable"));
            assertEquals("boom", throwInfo.details().get("throwableMessage"));
        }
    }

    @Nested
    class CompactMode {

        @Test
        void toEventInfoCompactShouldOmitTokenValues() {
            var token = Token.of("hello");
            var added = new NetEvent.TokenAdded(NOW, "P1", token);
            var info = NetEventConverter.toEventInfo(added, true);

            assertEquals("TokenAdded", info.type());
            assertEquals("P1", info.placeName());
            var tokenInfo = (TokenInfo) info.details().get("token");
            assertEquals("String", tokenInfo.type());
            assertNull(tokenInfo.value());
        }

        @Test
        void convertMarkingCompactShouldOmitTokenValues() {
            var token = Token.of("data");
            var marking = Map.<String, List<Token<?>>>of("P1", List.of(token));
            var result = NetEventConverter.convertMarking(marking, true);

            assertEquals(1, result.size());
            var tokens = result.get("P1");
            assertEquals(1, tokens.size());
            assertEquals("String", tokens.getFirst().type());
            assertNull(tokens.getFirst().value());
        }

        @Test
        void convertMarkingFullShouldIncludeTokenValues() {
            var token = Token.of("data");
            var marking = Map.<String, List<Token<?>>>of("P1", List.of(token));
            var result = NetEventConverter.convertMarking(marking, false);

            var tokens = result.get("P1");
            assertEquals("String", tokens.getFirst().type());
            assertEquals("data", tokens.getFirst().value());
        }
    }

    @Nested
    class TokenInfoConversion {

        @Test
        void shouldReturnFullValueWithoutPreview() {
            var longValue = "x".repeat(200);
            var token = Token.of(longValue);
            var info = NetEventConverter.tokenInfo(token);
            assertEquals("String", info.type());
            assertEquals(longValue, info.value());
        }

        @Test
        void shouldHandleUnitToken() {
            var unit = Token.unit();
            var info = NetEventConverter.tokenInfo(unit);
            assertEquals("null", info.type());
            assertEquals("null", info.value());
        }

        @Test
        void compactTokenInfoShouldReturnTypeOnly() {
            var token = Token.of("hello");
            var info = NetEventConverter.compactTokenInfo(token);
            assertEquals("String", info.type());
            assertNull(info.value());
            assertNotNull(info.timestamp());
        }

        @Test
        void shouldProjectRecordIntoStructuredField() {
            var msg = new SampleMessage("USER", "hi", 2);
            var info = NetEventConverter.tokenInfo(Token.of(msg));

            assertEquals("SampleMessage", info.type());
            // toString stays as the human-friendly display form
            assertTrue(info.value().contains("SampleMessage"));
            // Structured field is a JsonNode-like projection — consumers read named components
            assertNotNull(info.structured(), "records with public accessors must project");
            var structured = info.structured().toString();
            assertTrue(structured.contains("USER"));
            assertTrue(structured.contains("hi"));
        }

        @Test
        void shouldEmitEnumNameInStructuredField() {
            var info = NetEventConverter.tokenInfo(Token.of(SampleMode.VOICE));

            assertEquals("SampleMode", info.type());
            assertEquals("VOICE", info.structured(),
                "enums surface as the name() string so LLM responses stay compact");
        }

        @Test
        void shouldPassPrimitivesThroughStructured() {
            assertEquals(42, NetEventConverter.tokenInfo(Token.of(42)).structured());
            assertEquals("hello", NetEventConverter.tokenInfo(Token.of("hello")).structured());
            assertEquals(true, NetEventConverter.tokenInfo(Token.of(true)).structured());
        }

        @Test
        void shouldNotPopulateStructuredForUnitTokens() {
            var info = NetEventConverter.tokenInfo(Token.unit());
            assertNull(info.structured(),
                "unit tokens have no meaningful payload — structured stays null");
        }

        @Test
        void shouldLeaveStructuredNullForOpaqueBeans() {
            var info = NetEventConverter.tokenInfo(Token.of(new OpaqueBean()));

            assertEquals("OpaqueBean", info.type());
            assertNull(info.structured(),
                "Jackson-empty beans must not inflate the response with an empty object");
        }
    }

    public record SampleMessage(String kind, String text, int length) {}

    public enum SampleMode { TEXT, VOICE }

    /** Has no public getters and no Jackson annotations → Jackson produces an empty node. */
    public static final class OpaqueBean {
        @SuppressWarnings("unused")
        private final String secret = "hidden";
        @Override public String toString() { return "OpaqueBean{***}"; }
    }
}
