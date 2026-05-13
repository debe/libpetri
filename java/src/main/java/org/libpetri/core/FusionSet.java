package org.libpetri.core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

/**
 * A declaration that N typed places are to be treated as a single canonical
 * place in the resulting flat {@link PetriNet}, per {@code spec/11-modular-composition.md}
 * requirements <b>MOD-060</b> (fusion set declaration) and <b>MOD-061</b>
 * (fusion resolution at build).
 *
 * <p>Fusion is <b>orthogonal to subnet composition</b>: composition merges
 * places via port-binding (one instance port place ↔ one caller place per
 * binding); fusion merges N places at once via N-ary equivalence, applied
 * <b>after</b> all {@code compose(...)} calls have flattened subnet instances
 * into the enclosing {@link PetriNet.Builder}. Fusion is the mechanism for
 * modeling shared cross-instance state — e.g., a global rate limiter shared
 * by three instances of a leaky-bucket subnet — without expressing the
 * shared resource as an interface port on every subnet.
 *
 * <h2>Canonical member</h2>
 * <p>The <b>first declared member</b> is the canonical place; the others
 * are non-canonical and get substituted away at {@link PetriNet.Builder#build()}
 * time. The canonical member's name and identity survive into the resulting
 * flat net; non-canonical members do not appear in the built net's place set.
 *
 * <h2>Token-type homogeneity (MOD-060)</h2>
 * <p>All members of a fusion set MUST share the same {@link Place#tokenType()}.
 * This is enforced at {@link FusionSet} construction time (not at
 * {@code fuse()} or {@code build()} time), so a malformed declaration fails
 * at the earliest possible point. Mixing, e.g., {@code Place<String>} with
 * {@code Place<Integer>} raises {@link IllegalArgumentException}.
 *
 * <h2>Initial token preservation (future-proofing)</h2>
 * <p>Per [MOD-061], if non-canonical members had initial markings, the
 * canonical place would inherit the <b>sum</b> of initial tokens across all
 * members. The current libpetri Java {@link PetriNet.Builder} API does not
 * declare initial markings on places — initial markings live on the executor
 * side via {@code BitmapNetExecutor.create(net, initialTokens)}. Callers
 * supplying initial-token maps to the executor for a fused net should
 * concentrate tokens on the canonical place themselves; this rule is
 * documented here for forward compatibility.
 *
 * <h2>Identity</h2>
 * <p>{@code FusionSet} is immutable after construction. The {@link #members()}
 * list is unmodifiable; iteration order is the declaration order, with the
 * first element guaranteed to be the canonical member.
 *
 * <h2>Single-member sets</h2>
 * <p>A fusion set with a single member is degenerate but allowed: it is a
 * no-op at fusion-resolution time (the canonical member maps to itself, no
 * substitution occurs). This matches the structural semantics of an N-ary
 * equivalence with N=1.
 *
 * @see PetriNet.Builder#fuse(FusionSet...)
 */
public final class FusionSet {

    private final String name;
    private final List<Place<?>> members;
    private final Class<?> tokenType;

    private FusionSet(String name, List<Place<?>> members, Class<?> tokenType) {
        this.name = name;
        this.members = List.copyOf(members);
        this.tokenType = tokenType;
    }

    /**
     * Optional human-readable name for this fusion set; used in error messages
     * (e.g., overlap detection at {@link PetriNet.Builder#build()}).
     */
    public String name() {
        return name;
    }

    /**
     * Returns the canonical member — by convention, the first declared member.
     * The canonical place's identity survives into the resulting flat net.
     */
    public Place<?> canonical() {
        return members.get(0);
    }

    /** Returns the unmodifiable, declaration-ordered list of all members. */
    public List<Place<?>> members() {
        return members;
    }

    /**
     * Returns all members <i>except</i> the canonical member, in declaration
     * order. These are the places that get substituted away at
     * {@link PetriNet.Builder#build()} time.
     */
    public List<Place<?>> nonCanonical() {
        if (members.size() <= 1) return List.of();
        return Collections.unmodifiableList(members.subList(1, members.size()));
    }

    /**
     * The common {@link Place#tokenType()} shared by all members, established
     * by the homogeneity check at construction time.
     */
    public Class<?> tokenType() {
        return tokenType;
    }

    @Override
    public String toString() {
        return "FusionSet[" + name + ", canonical=" + canonical().name()
            + ", members=" + members.size() + "]";
    }

    // ============================================================
    //  Static factories
    // ============================================================

    /** Returns a fresh {@link Builder} with the given human-readable name. */
    public static Builder builder(String name) {
        return new Builder(name);
    }

    /**
     * Convenience factory: builds a fusion set whose first member is
     * {@code first} (the canonical) and whose remaining members are
     * {@code rest}, all sharing the type {@code <T>}.
     *
     * <p>The varargs form ensures static-type homogeneity at the call site
     * (the compiler checks every {@code rest} entry is a {@code Place<T>});
     * the runtime homogeneity check at {@link Builder#build()} is then a
     * defence-in-depth no-op for this entry point.
     */
    @SafeVarargs
    public static <T> FusionSet of(String name, Place<T> first, Place<T>... rest) {
        var builder = builder(name).member(first);
        for (var p : rest) builder.member(p);
        return builder.build();
    }

    // ============================================================
    //  Builder
    // ============================================================

    /**
     * Fluent builder for {@link FusionSet}.
     *
     * <p>Members are appended in call order; the first member becomes the
     * canonical place. Type homogeneity is validated at {@link #build()}
     * time, not at each {@link #member(Place)} call, so partial construction
     * does not throw — only a finalised malformed set does.
     */
    public static final class Builder {
        private final String name;
        private final List<Place<?>> members = new ArrayList<>();

        private Builder(String name) {
            this.name = Objects.requireNonNull(name, "name");
        }

        /**
         * Appends a member to the fusion set. The first member becomes the
         * canonical place per the convention documented on {@link FusionSet}.
         *
         * <p>The {@code <T>} parameter is for compile-time guidance only:
         * callers writing typed code at the same call site benefit from the
         * compiler checking {@code Place<T>} at each member, but mixed-type
         * sequences are accepted by this method individually and rejected
         * collectively at {@link #build()}.
         *
         * @param place the member place (non-null)
         */
        public <T> Builder member(Place<T> place) {
            Objects.requireNonNull(place, "place");
            members.add(place);
            return this;
        }

        /**
         * Builds the immutable {@link FusionSet}. Validates:
         * <ul>
         *   <li>The set is non-empty (single-member sets are accepted as a
         *       structurally degenerate no-op per [MOD-060]; the empty set is
         *       rejected as malformed).</li>
         *   <li>Every member's {@link Place#tokenType()} equals the first
         *       member's token type — heterogeneous sets are rejected per
         *       [MOD-060].</li>
         * </ul>
         *
         * @return a fresh, immutable {@link FusionSet}
         * @throws IllegalArgumentException when the set is empty or members
         *         have mismatched token types
         */
        public FusionSet build() {
            if (members.isEmpty()) {
                throw new IllegalArgumentException(
                    "FusionSet '" + name + "': must have at least one member (MOD-060)");
            }
            var expectedType = members.get(0).tokenType();
            for (int i = 1; i < members.size(); i++) {
                var m = members.get(i);
                if (!m.tokenType().equals(expectedType)) {
                    throw new IllegalArgumentException(
                        "FusionSet '" + name + "': member '" + m.name()
                            + "' has token type " + m.tokenType().getName()
                            + " but expected " + expectedType.getName()
                            + " (first member '" + members.get(0).name()
                            + "' establishes the type per MOD-060)");
                }
            }
            return new FusionSet(name, members, expectedType);
        }
    }
}
