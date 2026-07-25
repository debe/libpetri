package org.libpetri.runtime;

import java.util.*;
import java.util.stream.Collectors;

import org.libpetri.core.Place;
import org.libpetri.core.Token;

/**
 * Mutable marking (token state) of a Petri Net during execution.
 *
 * <p>A marking represents the distribution of tokens across places at a given
 * point in time. This class provides the runtime state container used by
 * {@link NetExecutor} during net execution.
 *
 * <h2>Threading Model</h2>
 * <p>This class is <strong>not thread-safe</strong>. All access must be from
 * the orchestrator thread (the thread calling {@link NetExecutor#run()}).
 * Transition actions must not access the marking directly.
 *
 * <h2>Token Ordering</h2>
 * <p>Tokens in each place are maintained in FIFO order using {@link ArrayDeque}.
 * When a transition fires, it consumes the oldest token first.
 *
 * <h2>Type Safety</h2>
 * <p>All operations are type-safe via generics. The place's type parameter
 * ensures only compatible tokens can be added or retrieved.
 *
 * @see NetExecutor
 * @see Place
 * @see Token
 */
public final class Marking {
    /** Place → FIFO queue of tokens. */
    private final Map<Place<?>, ArrayDeque<Token<?>>> tokens;

    private Marking(Map<Place<?>, ArrayDeque<Token<?>>> tokens) {
        this.tokens = tokens;
    }

    /**
     * Creates an empty marking with no tokens.
     *
     * @return empty marking
     */
    public static Marking empty() {
        return new Marking(new HashMap<>());
    }

    /**
     * Creates a marking from an initial token distribution.
     *
     * @param initial map of places to their initial tokens
     * @return marking with initial tokens
     */
    public static Marking from(Map<Place<?>, List<Token<?>>> initial) {
        var tokens = new HashMap<Place<?>, ArrayDeque<Token<?>>>();
        initial.forEach((place, list) -> {
            list.forEach((token) -> {
                if (!place.accepts(token)) {
                    throw new IllegalArgumentException("Place " + place + " does not accept token " + token);
                }
            });
            tokens.put(place, new ArrayDeque<>(list));
        });
        return new Marking(tokens);
    }

    // ======================== Bulk Operations ========================

    /**
     * Removes all tokens from all places.
     * Package-private for use by PrecompiledNetExecutor to sync from ring buffers.
     */
    void clear() {
        tokens.clear();
    }

    // ======================== Token Addition ========================

    /**
     * Adds a token to a place.
     *
     * <p>The token is added to the end of the FIFO queue for the place.
     *
     * @param <T> token value type
     * @param place destination place
     * @param token token to add
     */
    public <T> void addToken(Place<T> place, Token<T> token) {
        tokens.computeIfAbsent(place, _ -> new ArrayDeque<>()).addLast(token);
    }

    // ======================== Token Removal ========================

    /**
     * Removes and returns the oldest token from a place.
     *
     * <p>Returns {@code null} if the place has no tokens. This avoids
     * {@link Optional} allocation on hot paths.
     *
     * @param <T> token value type
     * @param place source place
     * @return oldest token, or {@code null} if empty
     */
    @SuppressWarnings("unchecked")
    public <T> Token<T> removeFirst(Place<T> place) {
        var queue = tokens.get(place);
        if (queue == null || queue.isEmpty()) {
            return null;
        }
        return (Token<T>) queue.removeFirst();
    }

    /**
     * Removes and returns the first (oldest) token in a place satisfying
     * {@code predicate}, preserving the FIFO order of the rest.
     *
     * <p>Returns {@code null} if no token matches. Used by ν-net joins to
     * consume the name-matched token rather than the oldest (NU-020).
     *
     * @param <T>       token value type
     * @param place     source place
     * @param predicate token test
     * @return the first matching token, or {@code null}
     */
    @SuppressWarnings("unchecked")
    public <T> Token<T> removeFirstMatching(Place<T> place, java.util.function.Predicate<Token<?>> predicate) {
        var queue = tokens.get(place);
        if (queue == null || queue.isEmpty()) {
            return null;
        }
        var it = queue.iterator();
        while (it.hasNext()) {
            var token = it.next();
            if (predicate.test(token)) {
                it.remove();
                return (Token<T>) token;
            }
        }
        return null;
    }

    /**
     * Removes and returns all tokens from a place.
     *
     * <p>Used for reset arcs that clear all tokens from a place.
     *
     * @param <T> token value type
     * @param place source place
     * @return list of all removed tokens (empty if place was empty)
     */
    @SuppressWarnings("unchecked")
    public <T> List<Token<T>> removeAll(Place<T> place) {
        var queue = tokens.remove(place);
        if (queue == null || queue.isEmpty()) {
            return List.of();
        }
        return (List<Token<T>>) (List<?>) new ArrayList<>(queue);
    }

    // ======================== Token Inspection ========================

    /**
     * Returns an unmodifiable view of all tokens in a place.
     *
     * <p>Zero-copy operation - returns a view, not a copy.
     *
     * @param <T> token value type
     * @param place place to inspect
     * @return unmodifiable collection of tokens (empty if place has no tokens)
     */
    @SuppressWarnings("unchecked")
    public <T> Collection<Token<T>> peekTokens(Place<T> place) {
        var queue = tokens.get(place);
        if (queue == null) return List.of();
        return (Collection<Token<T>>) (Collection<?>) Collections.unmodifiableCollection(queue);
    }

    /**
     * Returns the oldest token in a place without removing it.
     *
     * <p>Returns {@code null} if the place has no tokens.
     *
     * @param <T> token value type
     * @param place place to inspect
     * @return oldest token, or {@code null} if empty
     */
    @SuppressWarnings("unchecked")
    public <T> Token<T> peekFirst(Place<T> place) {
        var queue = tokens.get(place);
        return queue == null || queue.isEmpty() ? null : (Token<T>) queue.peekFirst();
    }

    /**
     * Checks if a place has any tokens.
     *
     * @param <T> token value type
     * @param place place to check
     * @return {@code true} if the place has at least one token
     */
    public <T> boolean hasTokens(Place<T> place) {
        var queue = tokens.get(place);
        return queue != null && !queue.isEmpty();
    }

    /**
     * Returns the number of tokens in a place.
     *
     * @param <T> token value type
     * @param place place to count
     * @return token count (0 if place has no tokens)
     */
    public <T> int tokenCount(Place<T> place) {
        var queue = tokens.get(place);
        return queue == null ? 0 : queue.size();
    }

    // ======================== Snapshotting ========================

    /**
     * Creates a snapshot of the current marking for event emission.
     * Only includes non-empty places.
     *
     * <p>Package-private — used by executors for {@link org.libpetri.event.NetEvent.MarkingSnapshot} events.
     *
     * @return map of place names to their tokens (defensive copies)
     */
    Map<String, List<Token<?>>> snapshot() {
        var result = new HashMap<String, List<Token<?>>>();
        for (var entry : tokens.entrySet()) {
            if (!entry.getValue().isEmpty()) {
                result.put(entry.getKey().name(), List.copyOf(entry.getValue()));
            }
        }
        return result;
    }

    /**
     * Returns an independent copy of this marking.
     *
     * <p>Tokens are immutable, so the copy shares them; only the per-place queues are new. The
     * executors use this to publish an owned snapshot that a monitoring thread can then read
     * without racing the live marking.
     *
     * <p><b>Not thread-safe.</b> Call only from the thread that owns this marking (the
     * orchestrator). It iterates the backing map and queues directly; a concurrent structural
     * change on another thread can make it throw or spin. Cross-thread observation goes through
     * the executor's published snapshot, not through calling this on a live marking.
     *
     * @return an independent marking that shares only the (immutable) tokens
     */
    public Marking copy() {
        var copied = new HashMap<Place<?>, ArrayDeque<Token<?>>>();
        for (var entry : tokens.entrySet()) {
            var queue = entry.getValue();
            if (queue == null || queue.isEmpty()) continue;
            copied.put(entry.getKey(), new ArrayDeque<>(queue));
        }
        return new Marking(copied);
    }

    // ======================== Debugging ========================

    /**
     * Returns a concise string representation showing place names and token counts.
     *
     * <p>Example: {@code Marking{Ready: 1, Processing: 2}}
     *
     * @return concise marking description
     */
    @Override
    public String toString() {
        return tokens.entrySet().stream()
            .filter(e -> !e.getValue().isEmpty())
            .map(e -> e.getKey().name() + ": " + e.getValue().size())
            .collect(Collectors.joining(", ", "Marking{", "}"));
    }

    /**
     * Returns a detailed multi-line description for debugging.
     *
     * <p>Shows each place with token counts and value types. Useful for
     * understanding the current state during debugging.
     *
     * <p>Example output:
     * <pre>
     * Marking:
     *   Ready: 1 token(s) [UserRequest]
     *   Processing: 2 token(s) [Task, Task]
     * </pre>
     *
     * @return detailed marking description
     */
    public String inspect() {
        if (tokens.isEmpty()) return "Marking is empty";
        return tokens.entrySet().stream()
            .filter(e -> !e.getValue().isEmpty())
            .map(e -> {
                var place = e.getKey();
                var toks = e.getValue();
                var types = toks.stream()
                    .map(t -> t.value() == null ? "null" : t.value().getClass().getSimpleName())
                    .collect(Collectors.joining(", "));
                return "  %s: %d token(s) [%s]".formatted(place.name(), toks.size(), types);
            })
            .collect(Collectors.joining("\n", "Marking:\n", ""));
    }
}
