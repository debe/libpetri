package org.libpetri.core;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

/**
 * ν-net join correlation: a subset of a transition's <b>input</b> places that
 * must be correlated by <b>name equality</b> (spec NU-020).
 *
 * <p>The transition is enabled only when there exists a single {@link NameId}
 * {@code n} such that every correlated input supplies (at least) its required
 * token count whose projected name equals {@code n}. On firing, exactly those
 * name-matched tokens are consumed.
 *
 * <p>This is the single <i>decidable</i> predicate — equality of opaque names —
 * and is deliberately NOT a general guard: it correlates the name dimension
 * <i>across</i> places (composition-structural, like cardinality) rather than
 * evaluating an arbitrary boolean per token.
 *
 * <h3>Example</h3>
 * <pre>{@code
 * var join = Transition.builder("join")
 *     .inputs(In.one(branchA), In.one(branchB))
 *     .match(MatchSpec.builder()
 *         .key(branchA, (Msg m) -> NameId.of(m.correlationId()))
 *         .key(branchB, (Msg m) -> NameId.of(m.correlationId()))
 *         .build())
 *     .outputs(Out.place(merged))
 *     .action(ctx -> { ... })
 *     .build();
 * }</pre>
 */
public final class MatchSpec {

    /**
     * One correlated input: the place plus its name projection.
     *
     * @param place the correlated input place
     * @param key   the {@code value -> NameId} projection (erased to {@code Object})
     */
    public record MatchKey(Place<?> place, Function<Object, NameId> key) {

        /**
         * Projects a token value to its name, or {@code null} when the value's
         * type does not match the declared key type (treated as "no name").
         *
         * @param value the token value
         * @return the projected name, or {@code null}
         */
        public NameId extract(Object value) {
            try {
                return key.apply(value);
            } catch (ClassCastException e) {
                return null;
            }
        }
    }

    private final List<MatchKey> keys;

    private MatchSpec(List<MatchKey> keys) {
        this.keys = List.copyOf(keys);
    }

    /** The correlated inputs. */
    public List<MatchKey> keys() {
        return keys;
    }

    /** True when {@code place} is one of the correlated inputs. */
    public boolean correlates(Place<?> place) {
        return keys.stream().anyMatch(k -> k.place().equals(place));
    }

    /**
     * Returns the name projection for {@code place}, or {@code null} when the
     * place is not correlated by this spec.
     */
    public Function<Object, NameId> keyFor(Place<?> place) {
        return keys.stream()
            .filter(k -> k.place().equals(place))
            .map(MatchKey::key)
            .findFirst()
            .orElse(null);
    }

    /**
     * Returns a copy with every correlated place mapped through {@code mapper}
     * (the name projections are preserved). Used by composition to follow place
     * renames so a composed join still correlates the right inputs.
     *
     * @param mapper place rename function
     * @return a remapped spec
     */
    public MatchSpec remap(Function<Place<?>, Place<?>> mapper) {
        List<MatchKey> remapped = new ArrayList<>(keys.size());
        for (var k : keys) {
            remapped.add(new MatchKey(mapper.apply(k.place()), k.key()));
        }
        return new MatchSpec(remapped);
    }

    /** Starts building a {@code MatchSpec}. */
    public static Builder builder() {
        return new Builder();
    }

    /** Builder for {@link MatchSpec}. */
    public static final class Builder {
        private final List<MatchKey> keys = new ArrayList<>();

        private Builder() {}

        /**
         * Adds a correlated input place together with its name projection.
         *
         * @param place the correlated input place
         * @param key   the projection from the place's typed payload to a name
         * @param <T>   the payload type
         * @return this builder
         */
        @SuppressWarnings("unchecked")
        public <T> Builder key(Place<T> place, Function<? super T, NameId> key) {
            keys.add(new MatchKey(place, value -> key.apply((T) value)));
            return this;
        }

        /**
         * Builds the spec.
         *
         * @return the match spec
         * @throws IllegalArgumentException when fewer than two inputs are
         *     correlated (a match over a single place is just a guard)
         */
        public MatchSpec build() {
            if (keys.size() < 2) {
                throw new IllegalArgumentException(
                    "MatchSpec must correlate at least 2 input places, got " + keys.size());
            }
            return new MatchSpec(keys);
        }
    }
}
