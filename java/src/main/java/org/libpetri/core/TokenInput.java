package org.libpetri.core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Consumed input tokens bound to their source places.
 *
 * <p>Passed to {@link TransitionAction#execute} as the {@code in} parameter,
 * providing type-safe read access to tokens consumed from input places.
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
 * @see TokenOutput for collecting output tokens
 */
public final class TokenInput {
    private final Map<Place<?>, List<Token<?>>> tokens = new HashMap<>();

    /**
     * Add a token (used by executor when firing transition).
     */
    public <T> TokenInput add(Place<T> place, Token<T> token) {
        tokens.computeIfAbsent(place, _ -> new ArrayList<>()).add(token);
        return this;
    }

    /**
     * Get all tokens for a place.
     */
    @SuppressWarnings("unchecked")
    public <T> List<Token<T>> getAll(Place<T> place) {
        var list = tokens.get(place);
        if (list == null) return List.of();
        return (List<Token<T>>) (List<?>) Collections.unmodifiableList(list);
    }

    /**
     * Get the first token for a place.
     * @throws IllegalArgumentException if no tokens for this place
     */
    @SuppressWarnings("unchecked")
    public <T> Token<T> get(Place<T> place) {
        var list = tokens.get(place);
        if (list == null || list.isEmpty()) {
            throw new IllegalArgumentException("No token for place: " + place.name());
        }
        return (Token<T>) list.getFirst();
    }

    /**
     * Get the first token's value for a place.
     * @throws IllegalArgumentException if no tokens for this place
     */
    public <T> T value(Place<T> place) {
        return get(place).value();
    }

    /**
     * Get all token values for a place.
     */
    public <T> List<T> values(Place<T> place) {
        return getAll(place).stream().map(Token::value).toList();
    }

    /**
     * Get token count for a place.
     */
    public int count(Place<?> place) {
        return getAll(place).size();
    }

    /**
     * Check if any tokens exist for a place.
     */
    public boolean has(Place<?> place) {
        return !getAll(place).isEmpty();
    }
}
