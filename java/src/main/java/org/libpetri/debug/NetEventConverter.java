package org.libpetri.debug;

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

    private NetEventConverter() {}

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
