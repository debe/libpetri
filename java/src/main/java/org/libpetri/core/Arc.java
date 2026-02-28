package org.libpetri.core;

import java.time.Duration;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Arc types connecting places to transitions in the Petri net.
 * <p>
 * Arcs define the flow of tokens and the conditions for transition enablement.
 * This is a sealed hierarchy with four arc types:
 * <ul>
 *   <li>{@link In} - input specifications with cardinality (consumes tokens)</li>
 *   <li>{@link Inhibitor} - blocks if tokens present</li>
 *   <li>{@link Read} - requires tokens without consuming</li>
 *   <li>{@link Reset} - removes all tokens when firing</li>
 * </ul>
 *
 * <p>{@link Out} is nested here for cohesion but does NOT extend {@code Arc}
 * since composite outputs (AND/XOR) have no single place.
 *
 * <h3>Arc Semantics Summary</h3>
 * <table>
 *   <tr><th>Arc Type</th><th>Requires Token?</th><th>Consumes?</th><th>Effect</th></tr>
 *   <tr><td>In</td><td>Yes</td><td>Yes</td><td>Token consumed on fire</td></tr>
 *   <tr><td>Out</td><td>No</td><td>No</td><td>Token produced on complete</td></tr>
 *   <tr><td>Inhibitor</td><td>No (blocks if present)</td><td>No</td><td>Disables transition</td></tr>
 *   <tr><td>Read</td><td>Yes</td><td>No</td><td>Token remains</td></tr>
 *   <tr><td>Reset</td><td>No</td><td>Yes (all)</td><td>All tokens removed on fire</td></tr>
 * </table>
 */
public sealed interface Arc permits Arc.In, Arc.Inhibitor, Arc.Read, Arc.Reset {

    /**
     * Returns the place this arc connects to.
     *
     * @return the connected place
     */
    Place<?> place();

    // ==================== Input Specifications ====================

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
    sealed interface In extends Arc permits In.One, In.Exactly, In.All, In.AtLeast {

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

    // ==================== Output Specifications ====================

    /**
     * Output specification with explicit split semantics.
     * Supports composite structures (XOR of ANDs, AND of XORs, etc.)
     *
     * <p>This is a sealed hierarchy enabling pattern matching and formal analysis.
     * The structure encodes the contract that the runtime enforces:
     * <ul>
     *   <li>{@link And} - ALL children must receive tokens</li>
     *   <li>{@link Xor} - EXACTLY ONE child receives token</li>
     *   <li>{@link Place} - Leaf node representing a single output place</li>
     *   <li>{@link Timeout} - Timeout branch that activates if action exceeds duration</li>
     * </ul>
     *
     * <h3>Usage Examples</h3>
     * <pre>{@code
     * // Simple XOR (flat)
     * Out.xor(successPlace, errorPlace)
     *
     * // Simple AND (flat)
     * Out.and(p1, p2, p3)
     *
     * // XOR of ANDs (choose one branch, produce to all in branch)
     * Out.xor(
     *     Out.and(headerPlace, bodyPlace),     // Branch A
     *     Out.and(errorPlace, logPlace)        // Branch B
     * )
     *
     * // AND of XORs (multiple independent choices)
     * Out.and(
     *     Out.xor(formatA, formatB),           // Choice 1
     *     Out.xor(destA, destB)                // Choice 2
     * )
     * }</pre>
     *
     * @see In for input specifications
     */
    sealed interface Out permits Out.And, Out.Xor, Out.Place, Out.Timeout, Out.ForwardInput {

        /**
         * AND-split: ALL children must receive tokens.
         * Validation fails if any child is not satisfied.
         */
        record And(List<Out> children) implements Out {
            public And {
                if (children == null) {
                    throw new IllegalArgumentException("AND children cannot be null");
                }
                if (children.isEmpty()) {
                    throw new IllegalArgumentException("AND requires at least 1 child");
                }
                if (children.stream().anyMatch(c -> c == null)) {
                    throw new IllegalArgumentException("AND children cannot contain null elements");
                }
                children = List.copyOf(children);
            }
        }

        /**
         * XOR-split: EXACTLY ONE child receives token.
         * Validation fails if zero or more than one child is satisfied.
         */
        record Xor(List<Out> children) implements Out {
            public Xor {
                if (children == null) {
                    throw new IllegalArgumentException("XOR children cannot be null");
                }
                if (children.size() < 2) {
                    throw new IllegalArgumentException("XOR requires at least 2 children");
                }
                if (children.stream().anyMatch(c -> c == null)) {
                    throw new IllegalArgumentException("XOR children cannot contain null elements");
                }
                children = List.copyOf(children);
            }
        }

        /**
         * Leaf node: a single output place.
         */
        record Place(org.libpetri.core.Place<?> place) implements Out {}

        /**
         * Timeout branch - activates if action exceeds duration.
         *
         * <p>When an action doesn't complete within the specified duration,
         * the action is cancelled and tokens are produced to the child output(s).
         *
         * <p>This is part of the output structure, not a separate concern.
         * The executor interprets Timeout nodes and enforces them.
         *
         * <h3>Usage Example</h3>
         * <pre>{@code
         * .outputs(Out.xor(
         *     successPlace,
         *     Out.timeout(Duration.ofSeconds(5), timeoutPlace),  // Timeout branch
         *     errorPlace
         * ))
         * }</pre>
         */
        record Timeout(Duration after, Out child) implements Out {
            public Timeout {
                if (after == null || after.isNegative() || after.isZero()) {
                    throw new IllegalArgumentException("Timeout must be positive: " + after);
                }
                if (child == null) {
                    throw new IllegalArgumentException("Timeout child cannot be null");
                }
            }
        }

        /**
         * Forward a consumed input token to an output place.
         * Used in timeout branches to retry with original input data.
         *
         * <p>The 'from' place must be an input place of the transition.
         * The value consumed from 'from' at transition start is produced to 'to' on timeout.
         *
         * <h3>Usage Example</h3>
         * <pre>{@code
         * .inputs(In.one(queryPlace))
         * .outputs(Out.xor(
         *     resultPlace,
         *     Out.timeout(Duration.ofSeconds(10),
         *         Out.forwardInput(queryPlace, retryPlace))
         * ))
         * }</pre>
         */
        record ForwardInput(org.libpetri.core.Place<?> from, org.libpetri.core.Place<?> to) implements Out {
            public ForwardInput {
                if (from == null || to == null) {
                    throw new IllegalArgumentException("ForwardInput places cannot be null");
                }
            }
        }

        // ==================== Factory Methods ====================

        /**
         * Creates an AND-split with the given children.
         * All children must be satisfied for validation to pass.
         *
         * @param children the child output specs
         * @return AND output spec
         */
        static And and(Out... children) {
            return new And(List.of(children));
        }

        /**
         * Creates an AND-split with the given places.
         * All places must receive tokens for validation to pass.
         *
         * @param places the output places
         * @return AND output spec
         */
        static And and(org.libpetri.core.Place<?>... places) {
            return new And(Arrays.stream(places).<Out>map(Out.Place::new).toList());
        }

        /**
         * Creates a XOR-split with the given children.
         * Exactly one child must be satisfied for validation to pass.
         *
         * @param children the child output specs
         * @return XOR output spec
         */
        static Xor xor(Out... children) {
            return new Xor(List.of(children));
        }

        /**
         * Creates a XOR-split with the given places.
         * Exactly one place must receive a token for validation to pass.
         *
         * @param places the output places
         * @return XOR output spec
         */
        static Xor xor(org.libpetri.core.Place<?>... places) {
            return new Xor(Arrays.stream(places).<Out>map(Out.Place::new).toList());
        }

        /**
         * Creates a leaf output spec for a single place.
         *
         * @param p the output place
         * @return Place output spec
         */
        static Place place(org.libpetri.core.Place<?> p) {
            return new Place(p);
        }

        /**
         * Creates a timeout output spec with the given duration and child output.
         *
         * <p>If the action doesn't complete within the specified duration,
         * the action is cancelled and tokens are produced to the child output(s).
         *
         * @param after the timeout duration
         * @param child the output spec to use on timeout
         * @return Timeout output spec
         */
        static Timeout timeout(Duration after, Out child) {
            return new Timeout(after, child);
        }

        /**
         * Creates a timeout output spec with the given duration and place.
         *
         * <p>If the action doesn't complete within the specified duration,
         * the action is cancelled and a token is produced to the specified place.
         *
         * @param after the timeout duration
         * @param p the place to produce to on timeout
         * @return Timeout output spec
         */
        static Timeout timeout(Duration after, org.libpetri.core.Place<?> p) {
            return new Timeout(after, place(p));
        }

        /**
         * Creates a forward-input output spec for timeout branches.
         *
         * <p>When the transition times out, the value consumed from the 'from' input place
         * is produced to the 'to' output place. This enables retry patterns where the
         * original input data needs to be forwarded to a retry handler.
         *
         * @param from the input place whose consumed value will be forwarded
         * @param to the output place to produce the forwarded value to
         * @return ForwardInput output spec
         */
        static ForwardInput forwardInput(org.libpetri.core.Place<?> from, org.libpetri.core.Place<?> to) {
            return new ForwardInput(from, to);
        }

        // ==================== Instance Methods ====================

        /**
         * Collects all leaf places from this output spec (flattened).
         * Useful for TransitionContext validation of allowed outputs.
         *
         * @return unmodifiable set of all places in this spec
         */
        default Set<org.libpetri.core.Place<?>> allPlaces() {
            return switch (this) {
                case Place p -> Set.of(p.place());
                case ForwardInput f -> Set.of(f.to());
                case And a -> a.children().stream()
                    .flatMap(c -> c.allPlaces().stream())
                    .collect(Collectors.toUnmodifiableSet());
                case Xor x -> x.children().stream()
                    .flatMap(c -> c.allPlaces().stream())
                    .collect(Collectors.toUnmodifiableSet());
                case Timeout t -> t.child().allPlaces();
            };
        }

        /**
         * Enumerates all possible output branches for structural analysis.
         *
         * <p>This method is used by the {@code StateClassGraph} analyzer to expand
         * XOR outputs into virtual transitions (one per branch). Each branch represents
         * a distinct possible outcome of firing the transition.
         *
         * <ul>
         *   <li>AND = single branch containing all child places (Cartesian product)</li>
         *   <li>XOR = one branch per alternative child</li>
         *   <li>Nested = Cartesian product for AND, union for XOR</li>
         * </ul>
         *
         * <h3>Examples</h3>
         * <pre>{@code
         * Out.and(a, b).enumerateBranches()           // [{a, b}]
         * Out.xor(a, b).enumerateBranches()           // [{a}, {b}]
         * Out.xor(Out.and(a,b), Out.and(c,d))         // [{a,b}, {c,d}]
         * Out.and(Out.xor(a,b), Out.xor(c,d))         // [{a,c}, {a,d}, {b,c}, {b,d}]
         * }</pre>
         *
         * @return list of branches, where each branch is a set of places
         */
        default List<Set<org.libpetri.core.Place<?>>> enumerateBranches() {
            return switch (this) {
                case Place p -> List.of(Set.of(p.place()));
                case ForwardInput f -> List.of(Set.<org.libpetri.core.Place<?>>of(f.to()));

                case And and -> {
                    List<Set<org.libpetri.core.Place<?>>> result = List.of(Set.of());
                    for (Out child : and.children()) {
                        result = crossProduct(result, child.enumerateBranches());
                    }
                    yield result;
                }

                case Xor xor -> {
                    var result = new ArrayList<Set<org.libpetri.core.Place<?>>>();
                    for (Out child : xor.children()) {
                        result.addAll(child.enumerateBranches());
                    }
                    yield result;
                }

                case Timeout t -> t.child().enumerateBranches();
            };
        }

        /**
         * Computes the Cartesian product of two branch lists.
         * Each resulting branch is the union of one branch from each input list.
         */
        private static List<Set<org.libpetri.core.Place<?>>> crossProduct(
                List<Set<org.libpetri.core.Place<?>>> a,
                List<Set<org.libpetri.core.Place<?>>> b) {
            var result = new ArrayList<Set<org.libpetri.core.Place<?>>>();
            for (var setA : a) {
                for (var setB : b) {
                    var merged = new HashSet<org.libpetri.core.Place<?>>(setA);
                    merged.addAll(setB);
                    result.add(Set.copyOf(merged));
                }
            }
            return result;
        }
    }

    // ==================== Arc Types ====================

    /**
     * Inhibitor arc: blocks transition if place has matching tokens.
     *
     * @param <T> The type of token that blocks
     */
    record Inhibitor<T>(Place<T> place) implements Arc {
        /** Check if a token matches (and would block firing). */
        public boolean matches(Token<?> token) {
            return place.accepts(token);
        }
    }

    /**
     * Read arc: requires token but doesn't consume it.
     *
     * @param <T> The type of token value required
     */
    record Read<T>(Place<T> place) implements Arc {
        /**
         * Check if a token matches this read arc's type requirements.
         */
        public boolean matches(Token<?> token) {
            return place.accepts(token);
        }
    }

    /**
     * Reset arc: removes ALL tokens from place when transition fires.
     * Does not require tokens to be present (unlike Input arc).
     *
     * @param <T> The type of tokens to remove
     */
    record Reset<T>(Place<T> place) implements Arc {}
}
