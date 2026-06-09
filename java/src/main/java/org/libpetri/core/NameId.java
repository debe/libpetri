package org.libpetri.core;

/**
 * An opaque correlation identity (a ν-name) for ν-net fork/join (spec NU-001).
 *
 * <p>A {@code NameId} is carried by a token so that a fork can mint a fresh name
 * and a later join can re-merge exactly the siblings that share it (see
 * {@link MatchSpec}). The only operation defined on names is <b>equality</b>;
 * the {@link Comparable} implementation exists solely for the deterministic
 * match tie-break (NU-020) and carries no domain meaning.
 *
 * <p>Identity is a <i>projection</i> of the token payload, not a separate field
 * on {@link Token}: a {@link MatchSpec} declares the {@code value -> NameId}
 * key, and the fork mints a fresh name into the payload via
 * {@link TransitionContext#freshName()}. This keeps {@code Token} (and the
 * event/archive formats) unchanged while still giving the analyzer a
 * name-symmetric uninterpreted sort to reason about.
 *
 * @param value the underlying identity string
 */
public record NameId(String value) implements Comparable<NameId> {

    public NameId {
        if (value == null) {
            throw new IllegalArgumentException("NameId value cannot be null");
        }
    }

    /**
     * Creates a name from the given string.
     *
     * @param value the identity string
     * @return a new name
     */
    public static NameId of(String value) {
        return new NameId(value);
    }

    /**
     * Total order for the deterministic match tie-break (NU-020). Uses
     * {@link String#compareTo} (UTF-16 code-unit order), which is byte-identical to
     * the Rust and TypeScript ports for ASCII/BMP names — including every
     * executor-minted name ({@code "{transition}#{n}"}). For supplementary-plane
     * (astral) code points in user-supplied correlation keys the order can differ
     * from Rust's UTF-8/code-point order; NU-001 requires only per-implementation
     * consistency, which holds.
     */
    @Override
    public int compareTo(NameId other) {
        return this.value.compareTo(other.value);
    }

    @Override
    public String toString() {
        return value;
    }
}
