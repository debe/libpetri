package org.libpetri.core;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Collects output tokens produced by a transition action.
 *
 * <p>Thread safety is provided by returning this through {@link java.util.concurrent.CompletionStage} -
 * the happens-before relationship is implicit in how the future delivers results.
 *
 * <h3>Example</h3>
 * <pre>{@code
 * .action((in, out) -> {
 *     Request request = in.value(requestPlace);
 *     out.add(responsePlace, process(request));
 *     return CompletableFuture.completedFuture(out);
 * })
 * }</pre>
 *
 * @see TokenInput for reading input tokens
 */
public final class TokenOutput {

    private final List<Entry> entries = new ArrayList<>();

    /**
     * Add a token to an output place.
     *
     * @param place the output place
     * @param value the token value
     * @return this for chaining
     */
    public <T> TokenOutput add(Place<T> place, T value) {
        entries.add(new Entry(place, Token.of(value)));
        return this;
    }

    /**
     * Add a token to an output place.
     *
     * @param place the output place
     * @param token the token
     * @return this for chaining
     */
    public <T> TokenOutput add(Place<T> place, Token<T> token) {
        entries.add(new Entry(place, token));
        return this;
    }

    /**
     * Returns all collected outputs.
     */
    public List<Entry> entries() {
        return entries;
    }

    /**
     * Check if any outputs were produced.
     */
    public boolean isEmpty() {
        return entries.isEmpty();
    }

    /**
     * Clears all collected outputs for reuse.
     */
    public void clear() {
        entries.clear();
    }

    /**
     * Returns the set of places that received tokens.
     * Used by the executor for output validation.
     */
    public Set<Place<?>> placesWithTokens() {
        var set = new HashSet<Place<?>>(entries.size() * 2);
        for (var entry : entries) set.add(entry.place());
        return set;
    }

    /**
     * An output entry: place + token pair.
     */
    public record Entry(Place<?> place, Token<?> token) {}

}
