package org.libpetri.core;

import java.time.Instant;

/**
 * An immutable token carrying a typed value through the Petri net.
 * <p>
 * Tokens are the "data carriers" of the net. They flow from place to place
 * as transitions fire, carrying typed payloads that represent the state of
 * a computation or workflow.
 * <p>
 * Tokens are immutable and include a creation timestamp for timing analysis
 * and debugging.
 *
 * <h3>Example</h3>
 * <pre>{@code
 * Token<Request> token = Token.of(new Request("search", "laptop"));
 * Request value = token.value();
 * Instant created = token.createdAt();
 * }</pre>
 *
 * <h3>Unit Tokens</h3>
 * For control flow where no data is needed, use {@link #unit()} which returns
 * a cached singleton to avoid allocation.
 *
 * @param <T> the type of value this token carries
 * @param value the typed payload (may be null for unit tokens)
 * @param createdAt timestamp when the token was created
 */
public record Token<T>(
    T value,
    Instant createdAt
) {
    private static final Token<Void> UNIT = new Token<>(null, Instant.EPOCH);

    /**
     * Creates a token with the given value and current timestamp.
     *
     * @param <T> the type of the value
     * @param value the payload to carry
     * @return a new token with the value and current time
     */
    public static <T> Token<T> of(T value) {
        return new Token<>(value, Instant.now());
    }

    /**
     * Returns a unit token (marker with no meaningful value).
     * <p>
     * Unit tokens are used for pure control flow where the presence of
     * a token matters but it carries no data. Returns a cached singleton.
     *
     * @param <T> the phantom type (allows unit tokens in any typed place)
     * @return the cached unit token singleton
     */
    @SuppressWarnings("unchecked")
    public static <T> Token<T> unit() {
        return (Token<T>) UNIT;
    }

    /**
     * Checks if this token's value is an instance of the given type.
     *
     * @param type the class to check against
     * @return true if value is non-null and is an instance of type
     */
    public boolean isType(Class<?> type) {
        return value != null && type.isInstance(value);
    }

    /**
     * Checks if this is the unit token (no meaningful value).
     *
     * @return true if this is the singleton unit token
     */
    public boolean isUnit() {
        return this == UNIT;
    }
}
