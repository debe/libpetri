package org.libpetri.analysis;

import org.libpetri.core.Place;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.StringJoiner;

/**
 * Immutable snapshot of a Petri net marking for state space analysis.
 * <p>
 * A marking assigns a non-negative integer (token count) to each place.
 * This class captures only places with tokens > 0, making it memory-efficient
 * and suitable as a HashMap key for state space exploration.
 *
 * <h3>Identity</h3>
 * Two MarkingStates are equal if they have the same token counts for all places
 * (using Place identity, not name-based comparison).
 *
 * <h3>Example</h3>
 * <pre>{@code
 * var state = MarkingState.builder()
 *     .tokens(requestPlace, 2)
 *     .tokens(responsePlace, 1)
 *     .build();
 *
 * int count = state.tokens(requestPlace);  // 2
 * boolean has = state.hasTokens(responsePlace);  // true
 * }</pre>
 */
public final class MarkingState {

    private final Map<Place<?>, Integer> tokenCounts;
    private final int hashCode;

    private MarkingState(Map<Place<?>, Integer> tokenCounts) {
        this.tokenCounts = Map.copyOf(tokenCounts);
        this.hashCode = this.tokenCounts.hashCode();
    }

    /**
     * Returns the token count for the given place.
     *
     * @param place the place to query
     * @return token count (0 if place has no tokens)
     */
    public int tokens(Place<?> place) {
        return tokenCounts.getOrDefault(place, 0);
    }

    /**
     * Checks if the given place has at least one token.
     *
     * @param place the place to check
     * @return true if tokens(place) > 0
     */
    public boolean hasTokens(Place<?> place) {
        return tokens(place) > 0;
    }

    /**
     * Checks if any of the given places has at least one token.
     *
     * @param places the places to check
     * @return true if any place has tokens
     */
    public boolean hasTokensInAny(Set<Place<?>> places) {
        for (var place : places) {
            if (hasTokens(place)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Returns all places that have tokens in this marking.
     *
     * @return unmodifiable set of places with tokens > 0
     */
    public Set<Place<?>> placesWithTokens() {
        return tokenCounts.keySet();
    }

    /**
     * Returns the internal token count map (unmodifiable).
     *
     * @return map from place to token count
     */
    public Map<Place<?>, Integer> asMap() {
        return tokenCounts;
    }

    /**
     * Checks if this marking is empty (no tokens anywhere).
     *
     * @return true if all places have 0 tokens
     */
    public boolean isEmpty() {
        return tokenCounts.isEmpty();
    }

    /**
     * Returns the total number of tokens across all places.
     *
     * @return sum of all token counts
     */
    public int totalTokens() {
        int sum = 0;
        for (var count : tokenCounts.values()) {
            sum += count;
        }
        return sum;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof MarkingState other)) return false;
        return tokenCounts.equals(other.tokenCounts);
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    @Override
    public String toString() {
        if (tokenCounts.isEmpty()) {
            return "{}";
        }
        var joiner = new StringJoiner(", ", "{", "}");
        tokenCounts.entrySet().stream()
            .sorted((a, b) -> a.getKey().name().compareTo(b.getKey().name()))
            .forEach(e -> joiner.add(e.getKey().name() + ":" + e.getValue()));
        return joiner.toString();
    }

    /**
     * Creates a new builder for constructing a MarkingState.
     *
     * @return a new builder
     */
    public static Builder builder() {
        return new Builder();
    }

    /**
     * Creates an empty marking (no tokens anywhere).
     *
     * @return the empty marking state
     */
    public static MarkingState empty() {
        return new MarkingState(Map.of());
    }

    /**
     * Builder for constructing MarkingState instances.
     */
    public static final class Builder {
        private final Map<Place<?>, Integer> tokenCounts = new HashMap<>();

        private Builder() {}

        /**
         * Sets the token count for a place.
         * Only stores if count > 0.
         *
         * @param place the place
         * @param count the token count (must be >= 0)
         * @return this builder
         */
        public Builder tokens(Place<?> place, int count) {
            if (count < 0) {
                throw new IllegalArgumentException("Token count cannot be negative: " + count);
            }
            if (count > 0) {
                tokenCounts.put(place, count);
            } else {
                tokenCounts.remove(place);
            }
            return this;
        }

        /**
         * Adds tokens to a place (increments existing count).
         *
         * @param place the place
         * @param count the number of tokens to add (must be >= 0)
         * @return this builder
         */
        public Builder addTokens(Place<?> place, int count) {
            if (count < 0) {
                throw new IllegalArgumentException("Token count cannot be negative: " + count);
            }
            if (count > 0) {
                tokenCounts.merge(place, count, Integer::sum);
            }
            return this;
        }

        /**
         * Removes tokens from a place (decrements existing count).
         *
         * @param place the place
         * @param count the number of tokens to remove
         * @return this builder
         * @throws IllegalStateException if place has insufficient tokens
         */
        public Builder removeTokens(Place<?> place, int count) {
            int current = tokenCounts.getOrDefault(place, 0);
            int newCount = current - count;
            if (newCount < 0) {
                throw new IllegalStateException(
                    "Cannot remove " + count + " tokens from " + place.name() + " (has " + current + ")"
                );
            }
            if (newCount == 0) {
                tokenCounts.remove(place);
            } else {
                tokenCounts.put(place, newCount);
            }
            return this;
        }

        /**
         * Copies all token counts from another marking state.
         *
         * @param other the marking state to copy from
         * @return this builder
         */
        public Builder copyFrom(MarkingState other) {
            tokenCounts.putAll(other.tokenCounts);
            return this;
        }

        /**
         * Builds the immutable MarkingState.
         *
         * @return a new MarkingState
         */
        public MarkingState build() {
            return new MarkingState(tokenCounts);
        }
    }
}
