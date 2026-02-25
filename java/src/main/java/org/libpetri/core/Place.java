package org.libpetri.core;

/**
 * A typed place in the Petri Net that holds tokens of a specific type.
 * <p>
 * Places are the "state containers" of a Petri net. They hold tokens that
 * represent data or resources flowing through the net. Each place is typed,
 * meaning it only accepts tokens whose values are instances of the declared type.
 * <p>
 * Places use record equality (name + tokenType), so two places with the same
 * name and type are considered equal.
 *
 * <h3>Example</h3>
 * <pre>{@code
 * Place<Request> requests = Place.of("Requests", Request.class);
 * Place<Response> responses = Place.of("Responses", Response.class);
 * }</pre>
 *
 * @param <T> the type of token values this place accepts
 * @param name label for display/debugging/export
 * @param tokenType the class of accepted token values (for runtime type checking)
 */
public record Place<T>(
    String name,
    Class<T> tokenType
) {
    /**
     * Creates a place that accepts tokens of a specific type.
     *
     * @param <T> the type of token values
     * @param name label for display/debugging/export
     * @param tokenType the class of accepted token values
     * @return a new typed place
     */
    public static <T> Place<T> of(String name, Class<T> tokenType) {
        return new Place<>(name, tokenType);
    }

    /**
     * Checks if this place accepts the given token based on type compatibility.
     * Null values are accepted by any place.
     *
     * @param token the token to check
     * @return true if the token's value is null or an instance of this place's type
     */
    public boolean accepts(Token<?> token) {
        return token.value() == null || tokenType.isInstance(token.value());
    }
}
