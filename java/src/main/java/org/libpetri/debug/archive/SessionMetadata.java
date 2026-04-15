package org.libpetri.debug.archive;

import com.fasterxml.jackson.annotation.JsonInclude;
import org.libpetri.event.NetEvent;

import java.time.Instant;
import java.util.Map;
import java.util.TreeMap;
import java.util.function.Supplier;

/**
 * Pre-computed aggregate statistics attached to a v2 session archive header.
 *
 * <p>These are computed once during archive write time by a single-pass scan of the
 * event store. Readers can answer {@code hasErrors}, {@code eventTypeHistogram},
 * and first/last timestamp queries without iterating the event stream — enabling
 * cheap triage, sampling, and listing of many archives.
 *
 * <p>For v1 archives (no pre-computed metadata), {@link #fromEvents(Iterable)}
 * provides a lazy on-demand computation path.
 *
 * @param eventTypeHistogram count of events per {@link NetEvent} subtype name
 *                           (e.g., {@code TransitionStarted -> 412})
 * @param firstEventTime timestamp of the oldest event in the session, or {@code null}
 *                       if the session had no events
 * @param lastEventTime timestamp of the newest event in the session, or {@code null}
 *                      if the session had no events
 * @param hasErrors true if the session contains at least one error-signal event
 *                  ({@link NetEvent.TransitionFailed}, {@link NetEvent.TransitionTimedOut},
 *                  {@link NetEvent.ActionTimedOut}, or a {@link NetEvent.LogMessage}
 *                  at level {@code ERROR})
 */
@JsonInclude(JsonInclude.Include.NON_NULL)
public record SessionMetadata(
    Map<String, Long> eventTypeHistogram,
    Instant firstEventTime,
    Instant lastEventTime,
    boolean hasErrors
) {
    /**
     * Canonical constructor — normalizes the histogram map to an immutable
     * {@link TreeMap} copy so downstream code gets deterministic iteration order
     * (important for prompt-caching-friendly JSON output).
     */
    public SessionMetadata {
        eventTypeHistogram = eventTypeHistogram == null
            ? Map.of()
            : Map.copyOf(new TreeMap<>(eventTypeHistogram));
    }

    /** Returns a {@code SessionMetadata} with no data — useful for v1 imports with no computed stats. */
    public static SessionMetadata empty() {
        return new SessionMetadata(Map.of(), null, null, false);
    }

    /**
     * Computes metadata from an event sequence in a single pass. Safe to call on
     * both small live event stores and large archive streams since it allocates
     * only a {@link TreeMap} and tracks three scalars.
     *
     * <p>Use this as a fallback when a v1 archive is loaded and the caller needs
     * the aggregate stats after the fact.
     *
     * @param events event iterable (each {@code iterator()} call must produce a fresh walk)
     * @return metadata aggregating every event in the iterable
     */
    public static SessionMetadata fromEvents(Iterable<NetEvent> events) {
        return computeFrom(events::iterator);
    }

    /**
     * Computes metadata by invoking the supplier once and walking the returned iterator.
     * Exists so the archive writer can reuse the same scan logic with its single-shot
     * event iterator without building an {@link Iterable} wrapper.
     */
    public static SessionMetadata computeFrom(Supplier<java.util.Iterator<NetEvent>> iteratorSupplier) {
        var histogram = new TreeMap<String, Long>();
        Instant first = null;
        Instant last = null;
        boolean hasErrors = false;

        var it = iteratorSupplier.get();
        while (it.hasNext()) {
            var event = it.next();
            var type = event.getClass().getSimpleName();
            histogram.merge(type, 1L, Long::sum);

            var ts = eventTimestamp(event);
            if (ts != null) {
                if (first == null) {
                    first = ts;
                }
                last = ts;
            }

            if (isErrorEvent(event)) {
                hasErrors = true;
            }
        }

        return new SessionMetadata(histogram, first, last, hasErrors);
    }

    private static Instant eventTimestamp(NetEvent event) {
        return switch (event) {
            case NetEvent.ExecutionStarted e -> e.timestamp();
            case NetEvent.ExecutionCompleted e -> e.timestamp();
            case NetEvent.TransitionEnabled e -> e.timestamp();
            case NetEvent.TransitionClockRestarted e -> e.timestamp();
            case NetEvent.TransitionStarted e -> e.timestamp();
            case NetEvent.TransitionCompleted e -> e.timestamp();
            case NetEvent.TransitionFailed e -> e.timestamp();
            case NetEvent.TransitionTimedOut e -> e.timestamp();
            case NetEvent.ActionTimedOut e -> e.timestamp();
            case NetEvent.TokenAdded e -> e.timestamp();
            case NetEvent.TokenRemoved e -> e.timestamp();
            case NetEvent.LogMessage e -> e.timestamp();
            case NetEvent.MarkingSnapshot e -> e.timestamp();
        };
    }

    private static boolean isErrorEvent(NetEvent event) {
        return switch (event) {
            case NetEvent.TransitionFailed _ -> true;
            case NetEvent.TransitionTimedOut _ -> true;
            case NetEvent.ActionTimedOut _ -> true;
            case NetEvent.LogMessage log -> "ERROR".equalsIgnoreCase(log.level());
            default -> false;
        };
    }
}
