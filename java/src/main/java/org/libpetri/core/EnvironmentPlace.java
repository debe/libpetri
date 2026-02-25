package org.libpetri.core;

/**
 * Marker wrapper for a place that can receive tokens from external threads.
 *
 * <p>Environment places enable reactive Petri nets where external events
 * (user input, WebSocket messages, timers) inject tokens that the net
 * responds to. The executor wakes immediately upon token injection.
 *
 * <h2>Concurrency Model</h2>
 * <ul>
 *   <li>External threads call {@code NetExecutor.inject(EnvironmentPlace, Token)}</li>
 *   <li>Events queue in a lock-free structure</li>
 *   <li>Orchestrator thread applies them on next loop iteration</li>
 *   <li>Happens-before guaranteed via queue semantics + Semaphore signaling</li>
 * </ul>
 *
 * <h2>Formal Semantics</h2>
 * <p>Environment places model the boundary between the controlled net and
 * its environment. In state class graph analysis:
 * <ul>
 *   <li>Environment places can have unbounded tokens (non-deterministic input)</li>
 *   <li>Analysis must consider arbitrary token arrivals</li>
 *   <li>Different analysis modes control how environment places are treated</li>
 * </ul>
 *
 * <h3>Example</h3>
 * <pre>{@code
 * // Define environment place
 * var inputEnv = EnvironmentPlace.of(Place.of("UserInput", String.class));
 *
 * // Use in executor
 * var executor = NetExecutor.builder(net, Map.of())
 *     .environmentPlaces(inputEnv)
 *     .longRunning(true)
 *     .build();
 *
 * // Inject from any thread
 * executor.inject(inputEnv, Token.of("hello"));
 * }</pre>
 *
 * @param <T> the token type (inherited from wrapped place)
 * @param place the underlying place
 */
public record EnvironmentPlace<T>(Place<T> place) {

    /**
     * Creates an environment place wrapper around an existing place.
     *
     * @param <T> the token type
     * @param place the place to mark as environment
     * @return a new environment place wrapper
     */
    public static <T> EnvironmentPlace<T> of(Place<T> place) {
        return new EnvironmentPlace<>(place);
    }

    /**
     * Returns the name of the underlying place.
     *
     * @return the place name
     */
    public String name() {
        return place.name();
    }

    /**
     * Returns the token type of the underlying place.
     *
     * @return the token type class
     */
    public Class<T> tokenType() {
        return place.tokenType();
    }

    /**
     * Checks if this environment place accepts the given token.
     *
     * @param token the token to check
     * @return true if the token is compatible with this place's type
     */
    public boolean accepts(Token<?> token) {
        return place.accepts(token);
    }
}
