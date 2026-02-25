package org.libpetri.event;

import java.util.List;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.function.Predicate;
import java.util.stream.Stream;

import static java.lang.System.Logger.Level;

/**
 * Storage for events emitted during Petri net execution.
 *
 * <p>The event store captures the complete execution history, enabling:
 * <ul>
 *   <li>Debugging and tracing execution flow</li>
 *   <li>Event sourcing and replay</li>
 *   <li>Monitoring and metrics collection</li>
 *   <li>Audit logging</li>
 * </ul>
 *
 * <h2>Decoration Chain</h2>
 * <p>In production, event stores are composed as decorators:
 * <pre>
 * TracingEventStore → LoggingEventStore → DebugEventStore (or NoopEventStore)
 * </pre>
 * <p>Each decorator calls {@code delegate.append(event)} to pass events down the chain.
 *
 * <h2>Default Method Efficiency</h2>
 * <p>The default query methods ({@link #stream()}, {@link #filter(Predicate)},
 * {@link #transitionEvents(String)}, {@link #failures()}) all call {@link #events()} which
 * returns an O(n) snapshot copy. Concrete implementations may override for efficiency.
 *
 * <h2>Thread Safety</h2>
 * <p>{@link #append(NetEvent)} must be thread-safe. Events are emitted from the NetExecutor
 * orchestrator thread, action threads (via {@code LogCaptureScope} appender), and timeout scheduler threads.
 *
 * <h2>Implementations</h2>
 * <ul>
 *   <li>{@link #inMemory()} - Thread-safe in-memory store for testing and simple use cases</li>
 *   <li>{@link #noop()} - Zero-allocation no-op store for performance-critical execution</li>
 * </ul>
 *
 * <h2>Usage</h2>
 * <pre>{@code
 * // With event capture
 * var store = EventStore.inMemory();
 * try (var executor = NetExecutor.builder(net, initial)
 *         .eventStore(store)
 *         .build()) {
 *     executor.run();
 * }
 *
 * // Query events
 * store.transitionEvents("MyTransition").forEach(System.out::println);
 * store.failures().forEach(e -> log.error("Failed: {}", e));
 *
 * // Without event capture (best performance)
 * try (var executor = NetExecutor.builder(net, initial)
 *         .eventStore(EventStore.noop())
 *         .build()) {
 *     executor.run();
 * }
 * }</pre>
 *
 * @see NetEvent
 */
public interface EventStore {

    /**
     * Appends an event to the store.
     *
     * <p>Must be thread-safe as events may be emitted from multiple threads.
     *
     * @param event the event to append
     */
    void append(NetEvent event);

    /**
     * Returns all events in chronological order.
     *
     * @return immutable list of all events
     */
    List<NetEvent> events();

    /**
     * Returns whether this store is enabled.
     *
     * <p>When {@code false}, the executor skips event creation entirely
     * to avoid allocation overhead. Use {@link #noop()} for this behavior.
     *
     * @return {@code true} if events should be captured
     */
    default boolean isEnabled() {
        return true;
    }

    // ======================== Query Methods ========================

    /**
     * Returns a stream of all events for filtering and transformation.
     *
     * @return stream of events
     */
    default Stream<NetEvent> stream() {
        return events().stream();
    }

    /**
     * Returns events matching a predicate.
     *
     * @param predicate filter condition
     * @return list of matching events
     */
    default List<NetEvent> filter(Predicate<NetEvent> predicate) {
        return stream().filter(predicate).toList();
    }

    /**
     * Returns events of a specific type.
     *
     * @param <T> event type
     * @param eventType the event class to filter by
     * @return list of events of the specified type
     */
    default <T extends NetEvent> List<T> eventsOfType(Class<T> eventType) {
        return stream()
            .filter(eventType::isInstance)
            .map(eventType::cast)
            .toList();
    }

    /**
     * Returns all events for a specific transition.
     *
     * @param transitionName name of the transition
     * @return list of events related to the transition
     */
    default List<NetEvent> transitionEvents(String transitionName) {
        return stream()
            .filter(e -> switch (e) {
                case NetEvent.TransitionEnabled t -> t.transitionName().equals(transitionName);
                case NetEvent.TransitionClockRestarted t -> t.transitionName().equals(transitionName);
                case NetEvent.TransitionStarted t -> t.transitionName().equals(transitionName);
                case NetEvent.TransitionCompleted t -> t.transitionName().equals(transitionName);
                case NetEvent.TransitionFailed t -> t.transitionName().equals(transitionName);
                case NetEvent.TransitionTimedOut t -> t.transitionName().equals(transitionName);
                case NetEvent.ActionTimedOut t -> t.transitionName().equals(transitionName);
                case NetEvent.LogMessage t -> t.transitionName().equals(transitionName);
                default -> false;
            })
            .toList();
    }

    /**
     * Returns all failure events (failed, timed-out transitions, and action timeouts).
     *
     * @return list of failure events
     */
    default List<NetEvent> failures() {
        return stream()
            .filter(e -> e instanceof NetEvent.TransitionFailed
                      || e instanceof NetEvent.TransitionTimedOut
                      || e instanceof NetEvent.ActionTimedOut)
            .toList();
    }

    /**
     * Returns the number of events captured.
     *
     * @return event count
     */
    default int size() {
        return events().size();
    }

    /**
     * Checks if any events have been captured.
     *
     * @return {@code true} if no events exist
     */
    default boolean isEmpty() {
        return events().isEmpty();
    }

    // ======================== Factory Methods ========================

    /**
     * Creates a thread-safe in-memory event store.
     *
     * <p>Suitable for testing and simple use cases. Events are stored in
     * a {@link ConcurrentLinkedQueue} for lock-free append.
     *
     * @return new in-memory store
     */
    static EventStore inMemory() {
        return new InMemoryEventStore();
    }

    /**
     * Returns a no-op event store that discards all events.
     *
     * <p>Use this for maximum performance when event capture is not needed.
     * When {@link #isEnabled()} returns {@code false}, the executor skips
     * event object creation entirely.
     *
     * @return singleton no-op store
     */
    static EventStore noop() {
        return NoopEventStore.INSTANCE;
    }

    /**
     * Creates a logging event store that logs all events.
     *
     * <p>This store logs events at appropriate levels:
     * <ul>
     *   <li>Failures and timeouts at WARN level</li>
     *   <li>Transition lifecycle at DEBUG level</li>
     *   <li>Token movement at TRACE level</li>
     * </ul>
     *
     * <p>Events are not stored - use {@link #logging(EventStore)} to both
     * log and store events.
     *
     * @return new logging-only store
     */
    static EventStore logging() {
        return new LoggingEventStore(noop());
    }

    /**
     * Creates a logging event store that delegates to another store.
     *
     * <p>This combines logging with another store's behavior. Events are
     * logged and then passed to the delegate.
     *
     * @param delegate the store to delegate to after logging
     * @return new logging store wrapping the delegate
     */
    static EventStore logging(EventStore delegate) {
        return new LoggingEventStore(delegate);
    }
}

/**
 * Thread-safe in-memory event store implementation using lock-free queue.
 *
 * <p>Uses {@link ConcurrentLinkedQueue} for O(1) lock-free append.
 * The {@link #events()} method creates a snapshot copy (O(n)) but is
 * typically called rarely (at end of execution for analysis).
 */
final class InMemoryEventStore implements EventStore {

    private final ConcurrentLinkedQueue<NetEvent> events = new ConcurrentLinkedQueue<>();

    @Override
    public void append(NetEvent event) {
        events.add(event);  // O(1) lock-free
    }

    @Override
    public List<NetEvent> events() {
        return List.copyOf(events);  // O(n) snapshot
    }

    /**
     * Clears all stored events.
     *
     * <p>Useful for test reuse without creating new store instances.
     */
    public void clear() {
        events.clear();
    }

    @Override
    public int size() {
        return events.size();
    }

    @Override
    public boolean isEmpty() {
        return events.isEmpty();
    }
}

/**
 * No-op event store that discards all events.
 */
final class NoopEventStore implements EventStore {

    static final NoopEventStore INSTANCE = new NoopEventStore();

    private NoopEventStore() {}

    @Override
    public void append(NetEvent event) {
        // No-op - zero allocation
    }

    @Override
    public List<NetEvent> events() {
        return List.of();
    }

    @Override
    public boolean isEnabled() {
        return false;
    }

    @Override
    public int size() {
        return 0;
    }

    @Override
    public boolean isEmpty() {
        return true;
    }
}

/**
 * Event store that logs all events and delegates to another store.
 *
 * <p>Logging levels:
 * <ul>
 *   <li>WARN: {@link NetEvent.TransitionFailed}, {@link NetEvent.TransitionTimedOut}</li>
 *   <li>INFO: {@link NetEvent.ExecutionStarted}, {@link NetEvent.ExecutionCompleted}</li>
 *   <li>DEBUG: {@link NetEvent.TransitionEnabled}, {@link NetEvent.TransitionStarted},
 *       {@link NetEvent.TransitionCompleted}</li>
 *   <li>TRACE: {@link NetEvent.TokenAdded}, {@link NetEvent.TokenRemoved},
 *       {@link NetEvent.MarkingSnapshot}</li>
 * </ul>
 */
final class LoggingEventStore implements EventStore {

    private static final System.Logger LOG = System.getLogger(LoggingEventStore.class.getName());

    private final EventStore delegate;

    LoggingEventStore(EventStore delegate) {
        this.delegate = delegate;
    }

    @Override
    public void append(NetEvent event) {
        logEvent(event);
        delegate.append(event);
    }

    @Override
    public List<NetEvent> events() {
        return delegate.events();
    }

    @Override
    public boolean isEnabled() {
        return true;
    }

    @Override
    public int size() {
        return delegate.size();
    }

    @Override
    public boolean isEmpty() {
        return delegate.isEmpty();
    }

    private void logEvent(NetEvent event) {
        if (!LOG.isLoggable(Level.DEBUG) && !isWarnOrInfo(event)) return;
        switch (event) {
            case NetEvent.ExecutionStarted e ->
                LOG.log(Level.INFO, "[{0}] Execution started: net={1}", e.executionId(), e.netName());

            case NetEvent.ExecutionCompleted e ->
                LOG.log(Level.INFO, "[{0}] Execution completed: net={1}, duration={2}",
                    e.executionId(), e.netName(), e.totalDuration());

            case NetEvent.TransitionEnabled e ->
                LOG.log(Level.DEBUG, "Transition enabled: {0}", e.transitionName());

            case NetEvent.TransitionClockRestarted e ->
                LOG.log(Level.DEBUG, "Transition clock restarted: {0}", e.transitionName());

            case NetEvent.TransitionStarted e ->
                LOG.log(Level.DEBUG, "Transition started: {0}, consumed {1} tokens",
                    e.transitionName(), e.consumedTokens().size());

            case NetEvent.TransitionCompleted e ->
                LOG.log(Level.DEBUG, "Transition completed: {0}, produced {1} tokens, duration={2}",
                    e.transitionName(), e.producedTokens().size(), e.duration());

            case NetEvent.TransitionFailed e ->
                LOG.log(Level.WARNING, "Transition FAILED: {0}, error={1} ({2})",
                    e.transitionName(), e.errorMessage(), e.exceptionType());

            case NetEvent.TransitionTimedOut e ->
                LOG.log(Level.WARNING, "Transition TIMED OUT: {0}, deadline={1}, actual={2}",
                    e.transitionName(), e.deadline(), e.actualDuration());

            case NetEvent.ActionTimedOut e ->
                LOG.log(Level.WARNING, "Action TIMED OUT: {0}, timeout={1}",
                    e.transitionName(), e.timeout());

            case NetEvent.TokenAdded e ->
                LOG.log(Level.TRACE, "Token added to {0}: {1}", e.placeName(), e.token());

            case NetEvent.TokenRemoved e ->
                LOG.log(Level.TRACE, "Token removed from {0}: {1}", e.placeName(), e.token());

            case NetEvent.MarkingSnapshot e ->
                LOG.log(Level.TRACE, "Marking snapshot: {0} places", e.marking().size());

            case NetEvent.LogMessage e ->
                LOG.log(Level.TRACE, "Log captured [{0}] {1}: {2}", e.level(), e.loggerName(), e.message());
        }
    }

    private static boolean isWarnOrInfo(NetEvent event) {
        return switch (event) {
            case NetEvent.ExecutionStarted _, NetEvent.ExecutionCompleted _,
                 NetEvent.TransitionFailed _, NetEvent.TransitionTimedOut _,
                 NetEvent.ActionTimedOut _ -> true;
            default -> false;
        };
    }
}
