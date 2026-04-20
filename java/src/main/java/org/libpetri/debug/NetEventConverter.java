package org.libpetri.debug;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.SerializationFeature;
import com.fasterxml.jackson.datatype.jsr310.JavaTimeModule;

import org.libpetri.core.Token;
import org.libpetri.event.NetEvent;
import org.libpetri.debug.DebugResponse.NetEventInfo;
import org.libpetri.debug.DebugResponse.TokenInfo;

import java.time.Instant;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * Converts CTPN NetEvent instances to serializable DebugResponse types.
 */
public final class NetEventConverter {

    /**
     * Shared mapper used to produce the {@code structured} field on {@link TokenInfo}. Separate
     * from {@link NetEventSerializer#SHARED_MAPPER} so we can run with stricter settings here:
     * {@code FAIL_ON_EMPTY_BEANS} disabled keeps non-Jackson-friendly domain objects from
     * exploding the conversion; {@code WRITE_DATES_AS_TIMESTAMPS} disabled gives LLM-facing
     * consumers readable ISO-8601 instants instead of epoch millis.
     */
    private static final ObjectMapper STRUCTURE_MAPPER = new ObjectMapper()
        .registerModule(new JavaTimeModule())
        .disable(SerializationFeature.FAIL_ON_EMPTY_BEANS)
        .disable(SerializationFeature.WRITE_DATES_AS_TIMESTAMPS);

    private NetEventConverter() {}

    /**
     * Attempts to project a token value into a JSON-object-friendly representation (Map / List /
     * JsonNode / primitive) so that downstream serializers emit typed fields rather than a
     * toString string. Returns {@code null} when Jackson throws or would produce an empty node —
     * callers fall back to the existing {@code value} string.
     *
     * <h2>Shape choices</h2>
     * <ul>
     *   <li>{@code null} values return {@code null} (there is nothing structured to show).</li>
     *   <li>Enums are projected to their {@link Enum#name()} — compact and unambiguous.</li>
     *   <li>Strings and boxed primitives pass through unchanged (Jackson emits them as-is).</li>
     *   <li>Records / POJOs round-trip via Jackson; Void tokens never reach this branch.</li>
     * </ul>
     */
    private static Object structuredValue(Object value) {
        if (value == null) return null;
        if (value instanceof Enum<?> e) return e.name();
        if (value instanceof String || value instanceof Number || value instanceof Boolean
                || value instanceof Character) {
            return value;
        }
        try {
            JsonNode tree = STRUCTURE_MAPPER.valueToTree(value);
            // Drop `{}` nodes (opaque beans, private-field only) — the caller's `value` string
            // already carries the toString, adding `"structured": {}` is pure token-budget waste.
            if (tree == null || tree.isNull() || (tree.isObject() && tree.isEmpty())) {
                return null;
            }
            return tree;
        } catch (RuntimeException ex) {
            return null;
        }
    }

    /**
     * Converts a NetEvent to a serializable NetEventInfo.
     *
     * @param event the event to convert
     * @return serializable event info with full token values
     */
    public static NetEventInfo toEventInfo(NetEvent event) {
        return toEventInfo(event, false);
    }

    /**
     * Converts a NetEvent to a serializable NetEventInfo.
     *
     * @param event   the event to convert
     * @param compact if true, token values are omitted (type only)
     * @return serializable event info
     */
    public static NetEventInfo toEventInfo(NetEvent event, boolean compact) {
        return switch (event) {
            case NetEvent.ExecutionStarted e -> new NetEventInfo(
                "ExecutionStarted",
                e.timestamp().toString(),
                null,
                null,
                Map.of(
                    "netName", e.netName(),
                    "executionId", e.executionId()
                )
            );

            case NetEvent.ExecutionCompleted e -> new NetEventInfo(
                "ExecutionCompleted",
                e.timestamp().toString(),
                null,
                null,
                Map.of(
                    "netName", e.netName(),
                    "executionId", e.executionId(),
                    "totalDurationMs", e.totalDuration().toMillis()
                )
            );

            case NetEvent.TransitionEnabled e -> new NetEventInfo(
                "TransitionEnabled",
                e.timestamp().toString(),
                e.transitionName(),
                null,
                Map.of()
            );

            case NetEvent.TransitionClockRestarted e -> new NetEventInfo(
                "TransitionClockRestarted",
                e.timestamp().toString(),
                e.transitionName(),
                null,
                Map.of()
            );

            case NetEvent.TransitionStarted e -> new NetEventInfo(
                "TransitionStarted",
                e.timestamp().toString(),
                e.transitionName(),
                null,
                Map.of(
                    "consumedTokens", tokenList(e.consumedTokens(), compact)
                )
            );

            case NetEvent.TransitionCompleted e -> new NetEventInfo(
                "TransitionCompleted",
                e.timestamp().toString(),
                e.transitionName(),
                null,
                Map.of(
                    "producedTokens", tokenList(e.producedTokens(), compact),
                    "durationMs", e.duration().toMillis()
                )
            );

            case NetEvent.TransitionFailed e -> new NetEventInfo(
                "TransitionFailed",
                e.timestamp().toString(),
                e.transitionName(),
                null,
                Map.of(
                    "errorMessage", e.errorMessage(),
                    "exceptionType", e.exceptionType()
                )
            );

            case NetEvent.TransitionTimedOut e -> new NetEventInfo(
                "TransitionTimedOut",
                e.timestamp().toString(),
                e.transitionName(),
                null,
                Map.of(
                    "deadlineMs", e.deadline().toMillis(),
                    "actualDurationMs", e.actualDuration().toMillis()
                )
            );

            case NetEvent.ActionTimedOut e -> new NetEventInfo(
                "ActionTimedOut",
                e.timestamp().toString(),
                e.transitionName(),
                null,
                Map.of(
                    "timeoutMs", e.timeout().toMillis()
                )
            );

            case NetEvent.TokenAdded e -> new NetEventInfo(
                "TokenAdded",
                e.timestamp().toString(),
                null,
                e.placeName(),
                Map.of(
                    "token", compact ? compactTokenInfo(e.token()) : tokenInfo(e.token())
                )
            );

            case NetEvent.TokenRemoved e -> new NetEventInfo(
                "TokenRemoved",
                e.timestamp().toString(),
                null,
                e.placeName(),
                Map.of(
                    "token", compact ? compactTokenInfo(e.token()) : tokenInfo(e.token())
                )
            );

            case NetEvent.MarkingSnapshot e -> new NetEventInfo(
                "MarkingSnapshot",
                e.timestamp().toString(),
                null,
                null,
                Map.of(
                    "marking", convertMarking(e.marking(), compact)
                )
            );

            case NetEvent.LogMessage e -> {
                var details = new HashMap<String, Object>();
                details.put("loggerName", e.loggerName());
                details.put("level", e.level());
                details.put("message", e.message());
                if (e.throwable() != null) {
                    details.put("throwable", e.throwable());
                }
                if (e.throwableMessage() != null) {
                    details.put("throwableMessage", e.throwableMessage());
                }
                yield new NetEventInfo(
                    "LogMessage",
                    e.timestamp().toString(),
                    e.transitionName(),
                    null,
                    details
                );
            }
        };
    }

    /**
     * Converts a Token to serializable TokenInfo with full value.
     *
     * @param token the token to convert
     * @return token info with full value
     */
    public static TokenInfo tokenInfo(Token<?> token) {
        Object value = token.value();
        String type = value != null ? value.getClass().getSimpleName() : "null";
        String fullValue = value != null ? value.toString() : "null";
        Instant createdAt = token.createdAt();

        return new TokenInfo(
            null,
            type,
            fullValue,
            structuredValue(value),
            createdAt != null ? createdAt.toString() : null
        );
    }

    /**
     * Converts a Token to compact TokenInfo (class name only, no value).
     *
     * @param token the token to convert
     * @return token info with type only
     */
    public static TokenInfo compactTokenInfo(Token<?> token) {
        Object value = token.value();
        String type = value != null ? value.getClass().getSimpleName() : "null";
        Instant createdAt = token.createdAt();
        return new TokenInfo(null, type, null,
            createdAt != null ? createdAt.toString() : null);
    }

    /**
     * Converts a list of tokens to token info list.
     */
    private static List<TokenInfo> tokenList(List<Token<?>> tokens, boolean compact) {
        return tokens.stream()
            .map(compact ? NetEventConverter::compactTokenInfo : NetEventConverter::tokenInfo)
            .toList();
    }

    /**
     * Converts a marking map to serializable form with full token values.
     */
    public static Map<String, List<TokenInfo>> convertMarking(Map<String, List<Token<?>>> marking) {
        return convertMarking(marking, false);
    }

    /**
     * Converts a marking map to serializable form.
     *
     * @param marking the marking to convert
     * @param compact if true, token values are omitted (type only)
     * @return serializable marking
     */
    public static Map<String, List<TokenInfo>> convertMarking(Map<String, List<Token<?>>> marking, boolean compact) {
        Function<Token<?>, TokenInfo> mapper = compact ? NetEventConverter::compactTokenInfo : NetEventConverter::tokenInfo;
        var result = new HashMap<String, List<TokenInfo>>();
        for (var entry : marking.entrySet()) {
            result.put(entry.getKey(), entry.getValue().stream().map(mapper).toList());
        }
        return result;
    }

}
