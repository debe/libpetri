/**
 * Event sourcing infrastructure for Petri net execution.
 *
 * <p>This package provides a complete event system for capturing, storing,
 * and querying execution history of Typed Colored Time Petri Nets.
 *
 * <h2>Package Contents</h2>
 * <dl>
 *   <dt>{@link org.libpetri.event.NetEvent}</dt>
 *   <dd>Sealed interface hierarchy of 10 event types covering execution lifecycle,
 *       transition lifecycle, token movement, and checkpointing. Enables exhaustive
 *       pattern matching in Java 21+.</dd>
 *
 *   <dt>{@link org.libpetri.event.EventStore}</dt>
 *   <dd>Storage interface for events with built-in query methods. Provides two
 *       implementations: in-memory (for testing) and no-op (for performance).</dd>
 * </dl>
 *
 * <h2>Event Categories</h2>
 * <table border="1">
 *   <caption>Event types by category</caption>
 *   <tr><th>Category</th><th>Events</th></tr>
 *   <tr><td>Execution Lifecycle</td><td>ExecutionStarted, ExecutionCompleted</td></tr>
 *   <tr><td>Transition Lifecycle</td><td>TransitionEnabled, TransitionStarted, TransitionCompleted, TransitionFailed, TransitionTimedOut</td></tr>
 *   <tr><td>Token Movement</td><td>TokenAdded, TokenRemoved</td></tr>
 *   <tr><td>Checkpointing</td><td>MarkingSnapshot</td></tr>
 * </table>
 *
 * <h2>Immutability and Thread Safety</h2>
 * <p>All events are immutable records with defensive copies of collections.
 * The in-memory store uses {@link java.util.concurrent.CopyOnWriteArrayList}
 * for thread-safe access during concurrent execution.
 *
 * <h2>Usage Example</h2>
 * <pre>{@code
 * // Capture events during execution
 * var store = EventStore.inMemory();
 * try (var executor = NetExecutor.builder(net, initial)
 *         .eventStore(store)
 *         .build()) {
 *     executor.run();
 * }
 *
 * // Query and analyze
 * var failures = store.failures();
 * var searchEvents = store.transitionEvents("Search");
 * var completions = store.eventsOfType(NetEvent.TransitionCompleted.class);
 *
 * // Pattern matching on events
 * for (var event : store.events()) {
 *     switch (event) {
 *         case NetEvent.TransitionCompleted e ->
 *             log.info("Completed {} in {}", e.transitionName(), e.duration());
 *         case NetEvent.TransitionFailed e ->
 *             log.error("Failed {}: {}", e.transitionName(), e.errorMessage());
 *         default -> {}
 *     }
 * }
 * }</pre>
 *
 * <h2>Performance Considerations</h2>
 * <p>For performance-critical execution where event history is not needed,
 * use {@link org.libpetri.event.EventStore#noop()} to completely
 * disable event creation and storage.
 *
 * @see org.libpetri.runtime.NetExecutor
 */
package org.libpetri.event;
