package org.libpetri.core;

/**
 * Input specification with cardinality.
 * CPN-compliant: cardinality determines how many tokens to consume.
 *
 * <p>Inputs are always AND-joined (all must be satisfied to enable transition).
 * XOR on inputs is modeled via multiple transitions (conflict).
 *
 * <p>This is a sealed hierarchy enabling pattern matching:
 * <ul>
 *   <li>{@link One} - Consume exactly 1 token (standard)</li>
 *   <li>{@link Exactly} - Consume exactly N tokens (batching)</li>
 *   <li>{@link All} - Consume all available tokens (must be 1+)</li>
 *   <li>{@link AtLeast} - Wait for N+ tokens, consume all when enabled</li>
 * </ul>
 *
 * <h3>Usage Examples</h3>
 * <pre>{@code
 * // Single token from each (AND-join)
 * In.one(p1), In.one(p2)
 *
 * // Batch: exactly 10 orders
 * In.exactly(10, orderPlace)
 *
 * // Drain: all available
 * In.all(queuePlace)
 *
 * // Accumulate: wait for 5+, take all
 * In.atLeast(5, bufferPlace)
 *
 * // Mixed cardinality
 * In.one(headerPlace), In.atLeast(1, lineItemPlace)
 * }</pre>
 *
 * @see Out for output specifications
 */
public sealed interface In permits In.One, In.Exactly, In.All, In.AtLeast {

    /**
     * Returns the place this input spec refers to.
     *
     * @return the input place
     */
    Place<?> place();

    /**
     * Consume exactly 1 token (standard CPN semantics).
     */
    record One(Place<?> place) implements In {}

    /**
     * Consume exactly N tokens (batching).
     * Transition enables when N+ tokens available, consumes exactly N.
     */
    record Exactly(Place<?> place, int count) implements In {
        public Exactly {
            if (count < 1) {
                throw new IllegalArgumentException("count must be >= 1, got: " + count);
            }
        }
    }

    /**
     * Consume all available tokens (must be 1+).
     * Transition enables when 1+ tokens available, consumes all.
     */
    record All(Place<?> place) implements In {}

    /**
     * Wait for N+ tokens, consume all when enabled.
     * Transition enables when minimum+ tokens available, consumes all.
     */
    record AtLeast(Place<?> place, int minimum) implements In {
        public AtLeast {
            if (minimum < 1) {
                throw new IllegalArgumentException("minimum must be >= 1, got: " + minimum);
            }
        }
    }

    // ==================== Factory Methods ====================

    /**
     * Creates an input spec that consumes exactly 1 token.
     *
     * @param place the input place
     * @return One input spec
     */
    static One one(Place<?> place) {
        return new One(place);
    }

    /**
     * Creates an input spec that consumes exactly N tokens.
     * Transition enables when N+ tokens available.
     *
     * @param count number of tokens to consume (must be >= 1)
     * @param place the input place
     * @return Exactly input spec
     */
    static Exactly exactly(int count, Place<?> place) {
        return new Exactly(place, count);
    }

    /**
     * Creates an input spec that consumes all available tokens.
     * Transition enables when 1+ tokens available.
     *
     * @param place the input place
     * @return All input spec
     */
    static All all(Place<?> place) {
        return new All(place);
    }

    /**
     * Creates an input spec that waits for N+ tokens and consumes all.
     * Transition enables when minimum+ tokens available, consumes all.
     *
     * @param minimum minimum tokens required to enable (must be >= 1)
     * @param place the input place
     * @return AtLeast input spec
     */
    static AtLeast atLeast(int minimum, Place<?> place) {
        return new AtLeast(place, minimum);
    }

    // ==================== Helper Methods ====================

    /**
     * Returns the minimum number of tokens required to enable.
     *
     * @return minimum token count for enablement
     */
    default int requiredCount() {
        return switch (this) {
            case One _ -> 1;
            case Exactly e -> e.count();
            case All _ -> 1;
            case AtLeast a -> a.minimum();
        };
    }

    /**
     * Returns the actual number of tokens to consume given the available count.
     *
     * <p>This differs from {@link #requiredCount()} which only tells you
     * the minimum needed for enablement. This method tells you how many
     * tokens will actually be consumed during firing:
     * <ul>
     *   <li>{@link One}: always consumes 1</li>
     *   <li>{@link Exactly}: always consumes exactly count</li>
     *   <li>{@link All}: consumes all available</li>
     *   <li>{@link AtLeast}: consumes all available (when enabled, i.e., >= minimum)</li>
     * </ul>
     *
     * @param available the number of tokens currently available in the place
     * @return the number of tokens to consume
     * @throws IllegalArgumentException if available is less than {@link #requiredCount()}
     */
    default int consumptionCount(int available) {
        if (available < requiredCount()) {
            throw new IllegalArgumentException(
                "Cannot consume from '%s': available=%d, required=%d"
                    .formatted(place().name(), available, requiredCount()));
        }
        return switch (this) {
            case One _ -> 1;
            case Exactly e -> e.count();
            case All _ -> available;
            case AtLeast _ -> available;
        };
    }
}
