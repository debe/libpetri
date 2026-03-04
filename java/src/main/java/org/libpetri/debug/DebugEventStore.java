package org.libpetri.debug;

import java.lang.System.Logger;
import java.lang.System.Logger.Level;
import java.time.Instant;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Consumer;

import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;

/**
 * EventStore implementation that supports live tailing and historical replay.
 *
 * <p>This store extends the basic event storage capabilities with:
 * <ul>
 *   <li><strong>Live tailing:</strong> Subscribe to receive events as they occur</li>
 *   <li><strong>Time-range queries:</strong> Retrieve events within a time window for replay</li>
 *   <li><strong>Thread-safe:</strong> Lock-free append and subscription management</li>
 * </ul>
 *
 * <h2>Usage Example</h2>
 * <pre>{@code
 * // Create debug store
 * var debugStore = new DebugEventStore("session-123");
 *
 * // Subscribe for live tailing
 * var subscription = debugStore.subscribe(event -> {
 *     System.out.println("Received: " + event);
 * });
 *
 * // Use with NetExecutor
 * var executor = NetExecutor.builder(net, initial)
 *     .eventStore(debugStore)
 *     .build();
 *
 * // Later: unsubscribe
 * subscription.cancel();
 *
 * // Query historical events
 * var recentEvents = debugStore.eventsSince(Instant.now().minusSeconds(60));
 * }</pre>
 *
 * <h2>Thread Safety</h2>
 * <p>{@link #append(NetEvent)} is called from multiple threads concurrently:
 * <ul>
 *   <li>The orchestrator thread (lifecycle events via {@code NetExecutor.emitEvent()})</li>
 *   <li>Action threads ({@link LogCaptureScope} appender → {@code eventStore::append} for LogMessage events)</li>
 *   <li>CompletableFuture scheduler threads ({@code emitEvent(ActionTimedOut)} in timeout handlers)</li>
 * </ul>
 *
 * <p>This is safe because storage uses a {@link ConcurrentLinkedQueue} (lock-free O(1) append)
 * and subscribers are managed via {@link CopyOnWriteArrayList} (optimized for rare modifications).
 * Subscriber broadcast is dispatched asynchronously via a single-threaded virtual-thread executor,
 * so slow subscribers (e.g., WebSocket writes) never block the orchestrator thread. FIFO ordering
 * is preserved because the executor is single-threaded.
 *
 * <p>The eviction loop ({@code retainedCount} check + poll + decrement) is non-atomic across its
 * three operations, so under contention the queue may briefly exceed {@code maxEvents} by a few
 * entries. This is acceptable for a debug tool.
 *
 * @see EventStore
 * @see DebugSessionRegistry
 */
public class DebugEventStore implements EventStore, AutoCloseable {

    private static final Logger LOG = System.getLogger(DebugEventStore.class.getName());

    /** Default maximum number of events to retain before evicting the oldest. */
    public static final int DEFAULT_MAX_EVENTS = 10_000;

    private final ConcurrentLinkedQueue<NetEvent> events = new ConcurrentLinkedQueue<>();
    private final CopyOnWriteArrayList<Consumer<NetEvent>> subscribers = new CopyOnWriteArrayList<>();
    private final ExecutorService broadcastExecutor = Executors.newSingleThreadExecutor(
            Thread.ofVirtual().name("debug-broadcast-", 0).factory()
    );
    private final String sessionId;
    private final int maxEvents;
    private final AtomicLong eventCount = new AtomicLong(0);
    private final AtomicLong evictedCount = new AtomicLong(0);
    private final AtomicInteger retainedCount = new AtomicInteger(0);

    /**
     * Creates a new debug event store for the specified session with the default capacity.
     *
     * @param sessionId unique identifier for this debug session
     */
    public DebugEventStore(String sessionId) {
        this(sessionId, DEFAULT_MAX_EVENTS);
    }

    /**
     * Creates a new debug event store with a specified maximum capacity.
     *
     * <p>When the store reaches {@code maxEvents}, the oldest events are evicted
     * to make room for new ones. Use {@link #evictedCount()} to track how many
     * events have been dropped.
     *
     * @param sessionId unique identifier for this debug session
     * @param maxEvents maximum number of events to retain (must be positive)
     */
    public DebugEventStore(String sessionId, int maxEvents) {
        if (maxEvents <= 0) {
            throw new IllegalArgumentException("maxEvents must be positive, got: " + maxEvents);
        }
        this.sessionId = sessionId;
        this.maxEvents = maxEvents;
    }

    /**
     * Returns the session ID this store is associated with.
     *
     * @return the session ID
     */
    public String sessionId() {
        return sessionId;
    }

    /**
     * Returns the total number of events captured.
     *
     * @return event count
     */
    public long eventCount() {
        return eventCount.get();
    }

    // ======================== EventStore Implementation ========================

    /**
     * Appends an event and schedules broadcast to all subscribers.
     *
     * <p>Storage is synchronous and lock-free. Subscriber broadcast is dispatched
     * asynchronously to a single-threaded executor, so slow subscribers never block
     * the calling thread. Event ordering is preserved across broadcasts.
     *
     * @param event the event to append
     */
    @Override
    public void append(NetEvent event) {
        events.add(event);
        eventCount.incrementAndGet();
        retainedCount.incrementAndGet();

        // Evict oldest events when capacity is exceeded (O(1) size check)
        while (retainedCount.get() > maxEvents) {
            if (events.poll() != null) {
                evictedCount.incrementAndGet();
                retainedCount.decrementAndGet();
            }
        }

        // Broadcast to all subscribers asynchronously (never blocks the orchestrator)
        if (!subscribers.isEmpty()) {
            try {
                broadcastExecutor.execute(() -> {
                    for (Consumer<NetEvent> subscriber : subscribers) {
                        try {
                            subscriber.accept(event);
                        } catch (Exception e) {
                            LOG.log(Level.WARNING, "Subscriber threw exception during event broadcast", e);
                        }
                    }
                });
            } catch (java.util.concurrent.RejectedExecutionException _) {
                // Executor shut down via close() — events are still stored but not broadcast
            }
        }
    }

    @Override
    public List<NetEvent> events() {
        return List.copyOf(events);
    }

    @Override
    public boolean isEnabled() {
        return true;
    }

    @Override
    public int size() {
        return retainedCount.get();
    }

    @Override
    public boolean isEmpty() {
        return events.isEmpty();
    }

    // ======================== Live Tailing ========================

    /**
     * Subscribes to receive events as they occur.
     *
     * <p>The listener will be called for each new event. Existing events
     * are not replayed - use {@link #eventsSince(Instant)} for historical data.
     *
     * <p>The returned {@link Subscription} should be cancelled when no longer
     * needed to prevent memory leaks.
     *
     * @param listener callback for each new event
     * @return subscription that can be cancelled
     */
    public Subscription subscribe(Consumer<NetEvent> listener) {
        subscribers.add(listener);
        return new Subscription() {
            @Override
            public void cancel() {
                subscribers.remove(listener);
            }

            @Override
            public boolean isActive() {
                return subscribers.contains(listener);
            }
        };
    }

    /**
     * Returns the number of active subscribers.
     *
     * @return subscriber count
     */
    public int subscriberCount() {
        return subscribers.size();
    }

    // ======================== Historical Replay ========================

    /**
     * Returns all events since the specified timestamp.
     *
     * <p>Useful for replay from a specific point in time.
     *
     * @param from the start timestamp (inclusive)
     * @return list of events since the timestamp
     */
    public List<NetEvent> eventsSince(Instant from) {
        return events.stream()
            .filter(e -> !e.timestamp().isBefore(from))
            .toList();
    }

    /**
     * Returns all events within a time range.
     *
     * <p>Useful for replay of a specific time window.
     *
     * @param from the start timestamp (inclusive)
     * @param to the end timestamp (exclusive)
     * @return list of events within the range
     */
    public List<NetEvent> eventsBetween(Instant from, Instant to) {
        return events.stream()
            .filter(e -> !e.timestamp().isBefore(from) && e.timestamp().isBefore(to))
            .toList();
    }

    /**
     * Returns events starting from a specific index.
     *
     * <p>Useful for resuming replay from a known position. The index is based on
     * the total number of events appended (including evicted ones). If {@code fromIndex}
     * refers to an evicted event, all currently retained events are returned.
     *
     * <p><strong>Performance:</strong> O(n) iterator skip where n = {@code fromIndex - evictedCount}.
     * Acceptable for debug UI seek operations which are infrequent and human-initiated.
     *
     * @param fromIndex the starting index (0-based, absolute)
     * @return list of events from the index onwards
     */
    public List<NetEvent> eventsFrom(int fromIndex) {
        // Adjust for evicted events: skip only events that are still in the queue
        long evicted = evictedCount.get();
        int adjustedSkip = (int) Math.max(0, fromIndex - evicted);

        if (adjustedSkip <= 0) {
            return events();
        }

        Iterator<NetEvent> it = events.iterator();
        int skipped = 0;
        while (it.hasNext() && skipped < adjustedSkip) {
            it.next();
            skipped++;
        }

        var result = new java.util.ArrayList<NetEvent>();
        while (it.hasNext()) {
            result.add(it.next());
        }
        return List.copyOf(result);
    }

    /**
     * Returns the number of events that have been evicted from the store.
     *
     * @return evicted event count
     */
    public long evictedCount() {
        return evictedCount.get();
    }

    /**
     * Returns the maximum number of events this store will retain.
     *
     * @return max event capacity
     */
    public int maxEvents() {
        return maxEvents;
    }

    /**
     * Returns an iterator over all retained events.
     *
     * <p>This provides zero-allocation traversal for archive writers that need to
     * iterate events without creating an intermediate list copy. The iterator
     * reflects the events in the queue at the time of creation.
     *
     * @return iterator over retained events
     */
    public java.util.Iterator<NetEvent> eventIterator() {
        return events.iterator();
    }

    // ======================== Lifecycle ========================

    /**
     * Closes this event store by shutting down the broadcast executor.
     *
     * <p>Equivalent to {@link #shutdownBroadcast()}. Implementing {@link AutoCloseable}
     * ensures the broadcast executor is cleaned up when the store is evicted from
     * {@link DebugSessionRegistry}.
     */
    @Override
    public void close() {
        shutdownBroadcast();
    }

    /**
     * Shuts down the broadcast executor, waiting up to 2 seconds for pending broadcasts to complete.
     *
     * <p>Called when the store is no longer needed. After shutdown, new events are
     * still stored but not broadcast.
     */
    public void shutdownBroadcast() {
        broadcastExecutor.shutdown();
        try {
            if (!broadcastExecutor.awaitTermination(2, java.util.concurrent.TimeUnit.SECONDS)) {
                broadcastExecutor.shutdownNow();
            }
        } catch (InterruptedException e) {
            broadcastExecutor.shutdownNow();
            Thread.currentThread().interrupt();
        }
    }

    // ======================== Subscription Interface ========================

    /**
     * Handle for managing a live event subscription.
     */
    public interface Subscription {
        /**
         * Cancels the subscription, stopping event delivery.
         */
        void cancel();

        /**
         * Checks if the subscription is still active.
         *
         * @return true if active
         */
        boolean isActive();
    }
}
