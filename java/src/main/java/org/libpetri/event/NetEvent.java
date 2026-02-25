package org.libpetri.event;

import java.time.Duration;
import java.time.Instant;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.libpetri.core.Token;

/**
 * Events emitted during Petri Net execution.
 *
 * <p>This sealed hierarchy captures all observable state changes during net execution,
 * enabling event sourcing, debugging, monitoring, and replay capabilities.
 *
 * <h2>Event Categories</h2>
 * <ul>
 *   <li><strong>Execution lifecycle:</strong> {@link ExecutionStarted}, {@link ExecutionCompleted}</li>
 *   <li><strong>Transition lifecycle:</strong> {@link TransitionEnabled}, {@link TransitionClockRestarted},
 *       {@link TransitionStarted}, {@link TransitionCompleted}, {@link TransitionFailed}, {@link TransitionTimedOut}, {@link ActionTimedOut}</li>
 *   <li><strong>Token movement:</strong> {@link TokenAdded}, {@link TokenRemoved}</li>
 *   <li><strong>Checkpointing:</strong> {@link MarkingSnapshot}</li>
 * </ul>
 *
 * <h2>Immutability</h2>
 * <p>All events are immutable records. Collections are defensively copied in compact
 * constructors to ensure thread-safety and safe replay.
 *
 * <h2>Pattern Matching</h2>
 * <p>The sealed hierarchy enables exhaustive pattern matching in Java 21+:
 * <pre>{@code
 * switch (event) {
 *     case TransitionStarted e -> log.info("Started: {}", e.transitionName());
 *     case TransitionCompleted e -> log.info("Completed: {} in {}", e.transitionName(), e.duration());
 *     case TransitionFailed e -> log.error("Failed: {}: {}", e.transitionName(), e.errorMessage());
 *     // ... handle all event types
 * }
 * }</pre>
 *
 * @see EventStore
 */
public sealed interface NetEvent {

    /**
     * Returns the timestamp when this event occurred.
     *
     * @return event timestamp
     */
    Instant timestamp();

    // ======================== Execution Lifecycle ========================

    /**
     * Emitted when net execution begins.
     *
     * @param timestamp when execution started
     * @param netName name of the Petri net being executed
     * @param executionId unique identifier for this execution run
     */
    record ExecutionStarted(
        Instant timestamp,
        String netName,
        String executionId
    ) implements NetEvent {}

    /**
     * Emitted when net execution completes (reaches quiescent state).
     *
     * <p>Completion may indicate successful termination or deadlock.
     *
     * @param timestamp when execution completed
     * @param netName name of the Petri net
     * @param executionId unique identifier for this execution run
     * @param totalDuration total execution time
     */
    record ExecutionCompleted(
        Instant timestamp,
        String netName,
        String executionId,
        Duration totalDuration
    ) implements NetEvent {}

    // ======================== Transition Lifecycle ========================

    /**
     * Emitted when a transition becomes enabled.
     *
     * <p>A transition is enabled when all input arcs have matching tokens,
     * all read arcs have tokens, and all inhibitor arcs' places are empty.
     *
     * @param timestamp when the transition became enabled
     * @param transitionName name of the enabled transition
     */
    record TransitionEnabled(
        Instant timestamp,
        String transitionName
    ) implements NetEvent {}

    /**
     * Emitted when a timed transition's clock is restarted.
     *
     * <p>This occurs when a transition was already enabled, remains enabled,
     * but one of its input places was reset (cleared and refilled via a reset arc).
     * The transition's enablement timestamp is reset to the current time,
     * effectively restarting its countdown timer.
     *
     * @param timestamp when the clock was restarted
     * @param transitionName name of the transition whose clock was restarted
     */
    record TransitionClockRestarted(
        Instant timestamp,
        String transitionName
    ) implements NetEvent {}

    /**
     * Emitted when a transition starts firing.
     *
     * <p>At this point, input tokens have been consumed and the transition's
     * action is executing asynchronously.
     *
     * @param timestamp when firing started
     * @param transitionName name of the firing transition
     * @param consumedTokens tokens consumed from input places
     */
    record TransitionStarted(
        Instant timestamp,
        String transitionName,
        List<Token<?>> consumedTokens
    ) implements NetEvent {
        /** Defensive copy to ensure immutability. */
        public TransitionStarted {
            consumedTokens = List.copyOf(consumedTokens);
        }
    }

    /**
     * Emitted when a transition completes firing successfully.
     *
     * <p>At this point, output tokens have been produced and added to output places.
     *
     * @param timestamp when firing completed
     * @param transitionName name of the completed transition
     * @param producedTokens tokens produced to output places
     * @param duration time spent executing the transition action
     */
    record TransitionCompleted(
        Instant timestamp,
        String transitionName,
        List<Token<?>> producedTokens,
        Duration duration
    ) implements NetEvent {
        /** Defensive copy to ensure immutability. */
        public TransitionCompleted {
            producedTokens = List.copyOf(producedTokens);
        }
    }

    /**
     * Emitted when a transition fails during execution.
     *
     * <p>The transition's action threw an exception. Input tokens were consumed
     * but no output tokens were produced.
     *
     * @param timestamp when failure occurred
     * @param transitionName name of the failed transition
     * @param errorMessage exception message
     * @param exceptionType fully-qualified exception class name
     */
    record TransitionFailed(
        Instant timestamp,
        String transitionName,
        String errorMessage,
        String exceptionType
    ) implements NetEvent {}

    /**
     * Emitted when a transition exceeds its deadline.
     *
     * <p>The transition's action did not complete within the configured deadline.
     *
     * @param timestamp when timeout occurred
     * @param transitionName name of the timed-out transition
     * @param deadline configured deadline that was exceeded
     * @param actualDuration time elapsed before timeout
     */
    record TransitionTimedOut(
        Instant timestamp,
        String transitionName,
        Duration deadline,
        Duration actualDuration
    ) implements NetEvent {}

    /**
     * Emitted when a transition's action exceeds its Out.Timeout duration.
     *
     * <p>The transition's async action did not complete within the timeout
     * specified in the output structure (Out.Timeout). Tokens were routed
     * to the timeout branch instead of the normal output.
     *
     * @param timestamp when timeout occurred
     * @param transitionName name of the transition whose action timed out
     * @param timeout the configured action timeout duration
     */
    record ActionTimedOut(
        Instant timestamp,
        String transitionName,
        Duration timeout
    ) implements NetEvent {}

    // ======================== Token Movement ========================

    /**
     * Emitted when a token is added to a place.
     *
     * <p>This occurs when a transition completes and produces output tokens.
     *
     * @param timestamp when the token was added
     * @param placeName name of the destination place
     * @param token the token that was added
     */
    record TokenAdded(
        Instant timestamp,
        String placeName,
        Token<?> token
    ) implements NetEvent {}

    /**
     * Emitted when a token is removed from a place.
     *
     * <p>This occurs when a transition fires and consumes input tokens,
     * or when a reset arc clears tokens from a place.
     *
     * @param timestamp when the token was removed
     * @param placeName name of the source place
     * @param token the token that was removed
     */
    record TokenRemoved(
        Instant timestamp,
        String placeName,
        Token<?> token
    ) implements NetEvent {}

    // ======================== Log Capture ========================

    /**
     * Captured log message from a transition action's SLF4J logging.
     *
     * <p>When log capture is enabled, log messages emitted by transition actions
     * (via SLF4J) are captured and stored as events, making them visible in the
     * debug UI alongside Petri net events.
     *
     * @param timestamp when the log message was emitted
     * @param transitionName name of the transition whose action emitted the log
     * @param loggerName the SLF4J logger name
     * @param level log level (TRACE, DEBUG, INFO, WARN, ERROR)
     * @param message the formatted log message
     * @param throwable exception class name, or null if no exception
     * @param throwableMessage exception message, or null if no exception
     */
    record LogMessage(
        Instant timestamp,
        String transitionName,
        String loggerName,
        String level,
        String message,
        String throwable,
        String throwableMessage
    ) implements NetEvent {}

    // ======================== Checkpointing ========================

    /**
     * Snapshot of the complete marking for checkpointing.
     *
     * <p>This event captures the full token distribution across all places,
     * enabling state recovery and debugging.
     *
     * @param timestamp when the snapshot was taken
     * @param marking map of place names to their tokens
     */
    record MarkingSnapshot(
        Instant timestamp,
        Map<String, List<Token<?>>> marking
    ) implements NetEvent {
        /** Deep defensive copy to ensure immutability. */
        public MarkingSnapshot {
            marking = marking.entrySet().stream()
                .collect(Collectors.toUnmodifiableMap(
                    Map.Entry::getKey,
                    e -> List.copyOf(e.getValue())
                ));
        }
    }
}
