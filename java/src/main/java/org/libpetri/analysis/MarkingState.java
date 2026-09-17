package org.libpetri.analysis;

import org.libpetri.core.Place;
import org.libpetri.core.internal.CodePointOrder;

import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.Arrays;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Objects;
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
 * <h3>Order</h3>
 * {@link #placesWithTokens()} lists places in the order the builder first saw them, as the
 * TypeScript reference does; a marking derived through {@link Builder#copyFrom} keeps its
 * source's order. Equality ignores the order, reports read it ([VER-022] port traces).
 *
 * <h3>Representation</h3>
 * The places in that order, a parallel {@code int[]} of counts, and an open-addressing index from
 * hash to position ({@code byte}, {@code char} or {@code int} slots as the place count needs, load
 * at most one half): one per state class. Lookup is O(1) expected, building O(n); a marking whose
 * builder only changed counts shares its source's place array and index.
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

    private static final Place<?>[] NO_PLACES = new Place<?>[0];
    private static final int[] NO_COUNTS = new int[0];
    private static final MarkingState EMPTY = new MarkingState(NO_PLACES, NO_COUNTS);

    /** The marked places, in the order the builder first saw them. Never written after construction. */
    private final Place<?>[] places;
    /** {@code counts[i]} tokens on {@code places[i]}, each at least one. */
    private final int[] counts;
    /**
     * Open-addressing index from a place's hash to its position plus one (0 is an empty slot): a
     * {@code byte[]}, {@code char[]} or {@code int[]} as the number of places needs, or
     * {@code null} for at most one place, which a comparison finds. Never written after
     * construction, so markings with the same places in the same order share it.
     */
    private final Object slots;
    private final int hashCode;

    private MarkingState(Place<?>[] places, int[] counts) {
        this(places, counts, index(places));
    }

    private MarkingState(Place<?>[] places, int[] counts, Object slots) {
        this.places = places;
        this.counts = counts;
        this.slots = slots;
        // Map.hashCode's definition, which does not depend on the order.
        int h = 0;
        for (int i = 0; i < places.length; i++) {
            h += places[i].hashCode() ^ counts[i];
        }
        this.hashCode = h;
    }

    private static int spread(int h) {
        return h ^ (h >>> 16);
    }

    private static Object index(Place<?>[] places) {
        int n = places.length;
        if (n <= 1) {
            return null;
        }
        // The smallest power of two at least twice the place count: a load of at most one half.
        int capacity = Integer.highestOneBit(n * 2 - 1) << 1;
        int mask = capacity - 1;
        if (n < 0x80) {
            var table = new byte[capacity];
            for (int i = 0; i < n; i++) {
                int j = spread(places[i].hashCode()) & mask;
                while (table[j] != 0) {
                    j = (j + 1) & mask;
                }
                table[j] = (byte) (i + 1);
            }
            return table;
        }
        if (n < 0xFFFF) {
            var table = new char[capacity];
            for (int i = 0; i < n; i++) {
                int j = spread(places[i].hashCode()) & mask;
                while (table[j] != 0) {
                    j = (j + 1) & mask;
                }
                table[j] = (char) (i + 1);
            }
            return table;
        }
        var table = new int[capacity];
        for (int i = 0; i < n; i++) {
            int j = spread(places[i].hashCode()) & mask;
            while (table[j] != 0) {
                j = (j + 1) & mask;
            }
            table[j] = i + 1;
        }
        return table;
    }

    /** The position of {@code place}, or -1 when it holds no token. */
    private int indexOf(Object place) {
        var ps = places;
        var s = slots;
        if (s == null) {
            return ps.length == 1 && (ps[0] == place || ps[0].equals(place)) ? 0 : -1;
        }
        if (place == null) {
            return -1;
        }
        int h = spread(place.hashCode());
        if (s instanceof byte[] table) {
            int mask = table.length - 1;
            for (int j = h & mask; ; j = (j + 1) & mask) {
                int e = table[j];
                if (e == 0) {
                    return -1;
                }
                var p = ps[e - 1];
                if (p == place || p.equals(place)) {
                    return e - 1;
                }
            }
        }
        if (s instanceof char[] table) {
            int mask = table.length - 1;
            for (int j = h & mask; ; j = (j + 1) & mask) {
                int e = table[j];
                if (e == 0) {
                    return -1;
                }
                var p = ps[e - 1];
                if (p == place || p.equals(place)) {
                    return e - 1;
                }
            }
        }
        var table = (int[]) s;
        int mask = table.length - 1;
        for (int j = h & mask; ; j = (j + 1) & mask) {
            int e = table[j];
            if (e == 0) {
                return -1;
            }
            var p = ps[e - 1];
            if (p == place || p.equals(place)) {
                return e - 1;
            }
        }
    }

    /**
     * Returns the token count for the given place.
     *
     * @param place the place to query
     * @return token count (0 if place has no tokens)
     */
    public int tokens(Place<?> place) {
        int i = indexOf(place);
        return i < 0 ? 0 : counts[i];
    }

    /**
     * Checks if the given place has at least one token.
     *
     * @param place the place to check
     * @return true if tokens(place) > 0
     */
    public boolean hasTokens(Place<?> place) {
        return indexOf(place) >= 0;
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
     * Returns all places that have tokens in this marking, in the order the builder first saw
     * them. A place set again keeps its position; one removed and set again moves to the end.
     *
     * @return unmodifiable set of places with tokens > 0, in insertion order
     */
    public Set<Place<?>> placesWithTokens() {
        return new PlacesInOrder();
    }

    /** {@link #placesWithTokens()}: iterates {@link #places}, answers membership from the index. */
    private final class PlacesInOrder extends AbstractSet<Place<?>> {
        @Override
        public Iterator<Place<?>> iterator() {
            return new Iterator<>() {
                private int next;

                @Override
                public boolean hasNext() {
                    return next < places.length;
                }

                @Override
                public Place<?> next() {
                    if (next >= places.length) {
                        throw new NoSuchElementException();
                    }
                    return places[next++];
                }
            };
        }

        @Override
        public int size() {
            return places.length;
        }

        @Override
        public boolean contains(Object o) {
            return indexOf(o) >= 0;
        }
    }

    /**
     * Returns the token counts as an unmodifiable map, iterating in the order of
     * {@link #placesWithTokens()}.
     *
     * @return map from place to token count
     */
    public Map<Place<?>, Integer> asMap() {
        return new CountMap();
    }

    /** {@link #asMap()}: a read-only view over the arrays. */
    private final class CountMap extends AbstractMap<Place<?>, Integer> {
        @Override
        public Set<Entry<Place<?>, Integer>> entrySet() {
            return new AbstractSet<>() {
                @Override
                public Iterator<Entry<Place<?>, Integer>> iterator() {
                    return new Iterator<>() {
                        private int next;

                        @Override
                        public boolean hasNext() {
                            return next < places.length;
                        }

                        @Override
                        public Entry<Place<?>, Integer> next() {
                            if (next >= places.length) {
                                throw new NoSuchElementException();
                            }
                            int i = next++;
                            return Map.entry(places[i], counts[i]);
                        }
                    };
                }

                @Override
                public int size() {
                    return places.length;
                }
            };
        }

        @Override
        public int size() {
            return places.length;
        }

        @Override
        public boolean containsKey(Object key) {
            return indexOf(key) >= 0;
        }

        @Override
        public Integer get(Object key) {
            int i = indexOf(key);
            return i < 0 ? null : counts[i];
        }
    }

    /**
     * Checks if this marking is empty (no tokens anywhere).
     *
     * @return true if all places have 0 tokens
     */
    public boolean isEmpty() {
        return places.length == 0;
    }

    /**
     * Returns the total number of tokens across all places.
     *
     * @return sum of all token counts
     */
    public int totalTokens() {
        int sum = 0;
        for (int count : counts) {
            sum += count;
        }
        return sum;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof MarkingState other)) return false;
        if (hashCode != other.hashCode || places.length != other.places.length) return false;
        var theirs = other.places;
        for (int i = 0; i < places.length; i++) {
            // Markings built along the same path list their places alike, which spares the lookup.
            int count = theirs[i] == places[i] ? other.counts[i] : other.tokens(places[i]);
            if (count != counts[i]) return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    /**
     * The marking as {@code {name:count, …}}, its places in code-point order of their names
     * ({@link CodePointOrder}), as every implementation prints a marking in a report.
     */
    @Override
    public String toString() {
        if (places.length == 0) {
            return "{}";
        }
        var order = new Integer[places.length];
        for (int i = 0; i < order.length; i++) {
            order[i] = i;
        }
        Arrays.sort(order, (a, b) -> CodePointOrder.compare(places[a].name(), places[b].name()));
        var joiner = new StringJoiner(", ", "{", "}");
        for (int i : order) {
            joiner.add(places[i].name() + ":" + counts[i]);
        }
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
        return EMPTY;
    }

    /**
     * Builder for constructing MarkingState instances.
     *
     * <p>A place set again keeps its position; one removed and set again moves to the end.
     *
     * <p>The state-class graph derives two markings per edge from a marking it holds, and the
     * builder is shaped for that. {@link #copyFrom} into an empty builder copies the counts and
     * borrows the source's places and index. A removal leaves a zero count where the place was
     * rather than shifting the rest, and a place the source lacks is appended. A lookup is then
     * the source's O(1) lookup plus a scan of at most {@code SCAN_LIMIT} appended places, after
     * which the builder indexes them, and {@link #build} is O(n), reusing the source's place array
     * and index when only counts changed.
     */
    public static final class Builder {
        /** Appended places a lookup scans before the builder indexes them. */
        private static final int SCAN_LIMIT = 16;

        /** Positions below {@code base.places.length} are the base's. Shared while {@link #borrowed}. */
        private Place<?>[] places = NO_PLACES;
        /** Parallel to {@link #places}; 0 marks a removed place. */
        private int[] counts = NO_COUNTS;
        private int size;
        private int removed;
        /** The marking whose index finds the positions below its length; {@code null} before any. */
        private MarkingState base;
        /** Whether {@link #places} is {@code base.places}, which must not be written. */
        private boolean borrowed;

        private Builder() {}

        private int baseLength() {
            return base == null ? 0 : base.places.length;
        }

        /** The position of the place while it holds tokens, or -1. */
        private int find(Place<?> place) {
            int from = 0;
            if (base != null) {
                int at = base.indexOf(place);
                if (at >= 0 && counts[at] > 0) {
                    return at;
                }
                from = base.places.length;
            }
            for (int i = from; i < size; i++) {
                if (places[i] == place && counts[i] > 0) {
                    return i;
                }
            }
            for (int i = from; i < size; i++) {
                if (counts[i] > 0 && places[i].equals(place)) {
                    return i;
                }
            }
            return -1;
        }

        private void append(Place<?> place, int count) {
            if (size - baseLength() >= SCAN_LIMIT) {
                rebase();
            }
            if (borrowed || size == places.length) {
                places = Arrays.copyOf(places, Math.max(4, size + (size >> 1) + 1));
                borrowed = false;
            }
            if (size == counts.length) {
                counts = Arrays.copyOf(counts, places.length);
            }
            places[size] = place;
            counts[size++] = count;
        }

        /** Compacts into a new base, so that every place is found through an index again. */
        private void rebase() {
            var built = build();
            base = built;
            places = built.places;
            counts = built.counts.clone();
            size = places.length;
            removed = 0;
            borrowed = true;
        }

        private void set(Place<?> place, int count) {
            int at = find(place);
            if (count > 0) {
                if (at >= 0) {
                    counts[at] = count;
                } else {
                    append(place, count);
                }
            } else if (at >= 0) {
                counts[at] = 0;
                removed++;
            }
        }

        /**
         * Sets the token count for a place.
         * Only stores if count > 0.
         *
         * @param place the place
         * @param count the token count (must be >= 0)
         * @return this builder
         */
        public Builder tokens(Place<?> place, int count) {
            Objects.requireNonNull(place, "place");
            if (count < 0) {
                throw new IllegalArgumentException("Token count cannot be negative: " + count);
            }
            set(place, count);
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
            Objects.requireNonNull(place, "place");
            if (count < 0) {
                throw new IllegalArgumentException("Token count cannot be negative: " + count);
            }
            if (count > 0) {
                int at = find(place);
                if (at >= 0) {
                    counts[at] += count;
                } else {
                    append(place, count);
                }
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
            Objects.requireNonNull(place, "place");
            int at = find(place);
            int current = at < 0 ? 0 : counts[at];
            int newCount = current - count;
            if (newCount < 0) {
                throw new IllegalStateException(
                    "Cannot remove " + count + " tokens from " + place.name() + " (has " + current + ")"
                );
            }
            set(place, newCount);
            return this;
        }

        /**
         * Copies all token counts from another marking state, its places in its order after
         * the ones this builder already holds.
         *
         * @param other the marking state to copy from
         * @return this builder
         */
        public Builder copyFrom(MarkingState other) {
            if (size == 0) {
                base = other;
                places = other.places;
                borrowed = true;
                counts = other.counts.clone();
                size = places.length;
                removed = 0;
                return this;
            }
            for (int i = 0; i < other.places.length; i++) {
                set(other.places[i], other.counts[i]);
            }
            return this;
        }

        /**
         * Builds the immutable MarkingState.
         *
         * @return a new MarkingState
         */
        public MarkingState build() {
            int live = size - removed;
            if (live == 0) {
                return EMPTY;
            }
            if (borrowed && removed == 0) {
                // Only counts changed: the base's places and index serve as they are.
                return new MarkingState(base.places, counts.clone(), base.slots);
            }
            var ps = new Place<?>[live];
            var cs = new int[live];
            int k = 0;
            for (int i = 0; i < size; i++) {
                if (counts[i] > 0) {
                    ps[k] = places[i];
                    cs[k++] = counts[i];
                }
            }
            return new MarkingState(ps, cs);
        }
    }
}
