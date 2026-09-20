package org.libpetri.event;

import java.time.Duration;
import java.time.Instant;
import java.util.List;
import java.util.Map;
import java.util.Optional;
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

    /**
     * Returns the instance prefix derived from a place or transition name
     * per {@code spec/11-modular-composition.md} <b>MOD-041</b>: the
     * substring before the <b>last</b> {@code "/"}, or
     * {@link Optional#empty()} when the name is not part of any composed
     * subnet instance (no {@code "/"}).
     *
     * <p>This helper is duplicated inside the event package (rather than
     * delegated to {@code org.libpetri.export.SubnetPrefixes}) to keep the
     * event subsystem dependency-free of the export layer per the
     * package-isolation contract.
     *
     * @param name place or transition name (may be null)
     * @return derived instance prefix, or empty
     */
    static Optional<String> instancePrefixOf(String name) {
        if (name == null) return Optional.empty();
        int idx = name.lastIndexOf('/');
        if (idx <= 0) return Optional.empty();
        return Optional.of(name.substring(0, idx));
    }

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
    ) implements NetEvent {
        /** Derived instance prefix per [MOD-041]; empty when not part of any composed instance. */
        public Optional<String> instancePrefix() { return NetEvent.instancePrefixOf(transitionName); }
    }

    /**
     * Emitted when a timed transition's clock is restarted.
     *
     * <p>This occurs when a transition was enabled, another transition's firing took
     * tokens it needed (through that firing's input or reset arcs, leaving it disabled
     * once the tokens were gone), and the firing's outputs refilled its places before the
     * executor next re-evaluated it. The firing re-enables it, so its enablement timestamp
     * is reset to the current time and its countdown starts over (TIME-011, TIME-012).
     * When the executor observes the transition disabled in between, as with an
     * asynchronous action, the re-enablement is reported as {@link TransitionEnabled}.
     *
     * @param timestamp when the clock was restarted
     * @param transitionName name of the transition whose clock was restarted
     */
    record TransitionClockRestarted(
        Instant timestamp,
        String transitionName
    ) implements NetEvent {
        /** Derived instance prefix per [MOD-041]; empty when not part of any composed instance. */
        public Optional<String> instancePrefix() { return NetEvent.instancePrefixOf(transitionName); }
    }

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
        /** Derived instance prefix per [MOD-041]; empty when not part of any composed instance. */
        public Optional<String> instancePrefix() { return NetEvent.instancePrefixOf(transitionName); }
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
        /** Derived instance prefix per [MOD-041]; empty when not part of any composed instance. */
        public Optional<String> instancePrefix() { return NetEvent.instancePrefixOf(transitionName); }
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
    ) implements NetEvent {
        /** Derived instance prefix per [MOD-041]; empty when not part of any composed instance. */
        public Optional<String> instancePrefix() { return NetEvent.instancePrefixOf(transitionName); }
    }

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
    ) implements NetEvent {
        /** Derived instance prefix per [MOD-041]; empty when not part of any composed instance. */
        public Optional<String> instancePrefix() { return NetEvent.instancePrefixOf(transitionName); }
    }

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
    ) implements NetEvent {
        /** Derived instance prefix per [MOD-041]; empty when not part of any composed instance. */
        public Optional<String> instancePrefix() { return NetEvent.instancePrefixOf(transitionName); }
    }

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
    ) implements NetEvent {
        /** Derived instance prefix per [MOD-041]; empty when not part of any composed instance. */
        public Optional<String> instancePrefix() { return NetEvent.instancePrefixOf(placeName); }
    }

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
    ) implements NetEvent {
        /** Derived instance prefix per [MOD-041]; empty when not part of any composed instance. */
        public Optional<String> instancePrefix() { return NetEvent.instancePrefixOf(placeName); }
    }

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
    ) implements NetEvent {
        /** Derived instance prefix per [MOD-041]; empty when not part of any composed instance. */
        public Optional<String> instancePrefix() { return NetEvent.instancePrefixOf(transitionName); }
    }

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
        /**
         * Deep defensive copy, in <b>ascending code-point order of the place name</b> — the
         * same canonical order {@link org.libpetri.runtime.Marking#snapshot()} produces, per
         * <b>CORE-073</b> and <b>EVT-014</b>.
         *
         * <p>The rule follows the form: it applies wherever a marking snapshot is rendered into
         * an ordered medium, and an event written into a session archive ([EVT-025]) is one.
         * Canonicalising the returned snapshot and then discarding that order on the way into
         * an event would fix the case nobody persists and leave the case everyone does — an
         * archive is the more durable artefact and so the likelier to be diffed, hashed or
         * compared against a golden file.
         *
         * <p><b>Not {@code Collectors.toUnmodifiableMap}</b>, which this used to be. That
         * collects into a {@code Map.ofEntries}-backed map, and Java's immutable maps randomise
         * their iteration order with a salt fixed once per JVM — so the same marking produced a
         * <i>different</i> key order on every run of the same program, not merely an arbitrary
         * one. That is the shape of unordered container to watch for: an ordinary hash map is
         * arbitrary but stable within a process, where this changes the artefact run to run.
         *
         * <p>[EVT-025] makes event bodies per-language and explicitly not byte-compatible, so
         * cross-language byte equality is <b>not</b> claimed here. What is required is
         * reproducibility across runs of this implementation: an archive written twice from
         * identical run data must not differ.
         */
        public MarkingSnapshot {
            var canonical = new java.util.TreeMap<String, List<Token<?>>>(
                org.libpetri.core.internal.CodePointOrder.COMPARATOR);
            marking.forEach((place, tokens) -> canonical.put(place, List.copyOf(tokens)));
            marking = java.util.Collections.unmodifiableSortedMap(canonical);
        }
    }
}
