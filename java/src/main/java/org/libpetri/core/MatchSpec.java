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
 *
 * <h3>Relay targets (NU-054)</h3>
 * A join MAY hand the name it matched on to an <b>output</b> place through
 * {@link Builder#relayTo}: a join chain ({@code e: C1, D1 -> P5} feeding a later join on
 * {@code P5}) or a correlated self-loop (a join writing the name back onto one of its own
 * keys). A relay target must be an output of the transition and is declared once (checked
 * when the transition is built). The executor checks, as part of output validation
 * ([IO-015]), that every token a firing writes into a relay target projects to the matched
 * name; the EXTENDED analysis fragment reads the join as threading that name onward.
 *
 * <pre>{@code
 * MatchSpec.builder()
 *     .key(c1, (Msg m) -> NameId.of(m.caseId()))
 *     .key(d1, (Msg m) -> NameId.of(m.caseId()))
 *     .relayTo(p5, (Msg m) -> NameId.of(m.caseId()))
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
    private final List<MatchKey> relays;

    private MatchSpec(List<MatchKey> keys, List<MatchKey> relays) {
        this.keys = List.copyOf(keys);
        this.relays = List.copyOf(relays);
    }

    /** The correlated inputs. */
    public List<MatchKey> keys() {
        return keys;
    }

    /**
     * The relay targets (NU-054): output places onto which the join writes the name it
     * matched, each with the projection that reads a produced token's name. Empty for a join
     * that drains the name. Relay targets do not count as correlated inputs.
     */
    public List<MatchKey> relays() {
        return relays;
    }

    /**
     * Returns the relay projection for {@code place}, or {@code null} when the place is not
     * a relay target of this spec (NU-054).
     */
    public Function<Object, NameId> relayFor(Place<?> place) {
        for (var r : relays) {
            if (r.place().equals(place)) return r.key();
        }
        return null;
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
     * Returns a copy with every correlated place and every relay target mapped
     * through {@code mapper} (the name projections are preserved). Used by
     * composition to follow place renames so a composed join still correlates the
     * right inputs and relays to the right outputs (NU-030, NU-054).
     *
     * @param mapper place rename function
     * @return a remapped spec
     */
    public MatchSpec remap(Function<Place<?>, Place<?>> mapper) {
        List<MatchKey> remapped = new ArrayList<>(keys.size());
        for (var k : keys) {
            remapped.add(new MatchKey(mapper.apply(k.place()), k.key()));
        }
        List<MatchKey> remappedRelays = new ArrayList<>(relays.size());
        for (var r : relays) {
            remappedRelays.add(new MatchKey(mapper.apply(r.place()), r.key()));
        }
        return new MatchSpec(remapped, remappedRelays);
    }

    /** Starts building a {@code MatchSpec}. */
    public static Builder builder() {
        return new Builder();
    }

    /** Builder for {@link MatchSpec}. */
    public static final class Builder {
        private final List<MatchKey> keys = new ArrayList<>();
        private final List<MatchKey> relays = new ArrayList<>();

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
         * Declares a relay target (NU-054): an output place onto which the join writes the
         * name it matched, with the projection that reads a produced token's name. It may be
         * one of the join's own keys (a correlated self-loop). It must be an output of the
         * transition and declared once; both are checked when the transition is built.
         *
         * @param place the output place the matched name is relayed to
         * @param key   the projection from the place's typed payload to a name
         * @param <T>   the payload type
         * @return this builder
         */
        @SuppressWarnings("unchecked")
        public <T> Builder relayTo(Place<T> place, Function<? super T, NameId> key) {
            relays.add(new MatchKey(place, value -> key.apply((T) value)));
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
            return new MatchSpec(keys, relays);
        }
    }
}
