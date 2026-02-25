package org.libpetri.core;

import java.util.function.Predicate;

/**
 * Arc types connecting places to transitions in the Petri net.
 * <p>
 * Arcs define the flow of tokens and the conditions for transition enablement.
 * This is a sealed hierarchy with five arc types:
 * <ul>
 *   <li>{@link Input} - consumes tokens (required for enabling)</li>
 *   <li>{@link Output} - produces tokens</li>
 *   <li>{@link Inhibitor} - blocks if tokens present</li>
 *   <li>{@link Read} - requires tokens without consuming</li>
 *   <li>{@link Reset} - removes all tokens when firing</li>
 * </ul>
 *
 * <h3>Arc Semantics Summary</h3>
 * <table>
 *   <tr><th>Arc Type</th><th>Requires Token?</th><th>Consumes?</th><th>Effect</th></tr>
 *   <tr><td>Input</td><td>Yes</td><td>Yes</td><td>Token consumed on fire</td></tr>
 *   <tr><td>Output</td><td>No</td><td>No</td><td>Token produced on complete</td></tr>
 *   <tr><td>Inhibitor</td><td>No (blocks if present)</td><td>No</td><td>Disables transition</td></tr>
 *   <tr><td>Read</td><td>Yes</td><td>No</td><td>Token remains</td></tr>
 *   <tr><td>Reset</td><td>No</td><td>Yes (all)</td><td>All tokens removed on fire</td></tr>
 * </table>
 */
public sealed interface Arc permits Arc.Input, Arc.Output, Arc.Inhibitor, Arc.Read, Arc.Reset {

    /**
     * Returns the place this arc connects to.
     *
     * @return the connected place
     */
    Place<?> place();

    /**
     * Input arc: consumes token from place when transition fires.
     * Optionally includes a guard predicate for colored Petri net semantics.
     *
     * @param <T> The type of token value expected
     * @param place The source place
     * @param guard Optional predicate - only tokens where guard returns true can be consumed
     */
    record Input<T>(Place<T> place, Predicate<T> guard) implements Arc {

        /** Input arc without guard (accepts any token of correct type). */
        public Input(Place<T> place) {
            this(place, null);
        }

        /**
         * Check if a token matches this input arc's requirements (type + guard).
         */
        @SuppressWarnings("unchecked")
        public boolean matches(Token<?> token) {
            if (!place.accepts(token)) return false;
            if (guard == null) return true;
            return guard.test((T) token.value());
        }

        /** Returns true if this arc has a guard predicate. */
        public boolean hasGuard() {
            return guard != null;
        }
    }

    /**
     * Output arc: produces token to place when transition fires.
     *
     * @param <T> The type of token value to produce
     */
    record Output<T>(Place<T> place) implements Arc {}

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
