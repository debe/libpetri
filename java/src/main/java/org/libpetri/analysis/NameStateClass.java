package org.libpetri.analysis;

import java.util.List;
import java.util.Objects;

/**
 * A name-aware state class (NU-050, Route B): the base count + DBM
 * {@link StateClass} plus the abstract {@link NameMarking} partition layer. The
 * base class is reused verbatim, so the timing/zone dimension is untouched —
 * name&times;time composition is automatic. Dedup is by {@code (base, nameKey)}
 * where {@code nameKey} is the symmetry-canonical name-partition key.
 */
final class NameStateClass {

    final StateClass base;
    final NameMarking names;
    private final String nameKey;

    NameStateClass(StateClass base, NameMarking names, List<String> colouredOrder) {
        this.base = base;
        this.names = names;
        this.nameKey = names.canonicalKey(colouredOrder);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof NameStateClass other)) return false;
        return base.equals(other.base) && nameKey.equals(other.nameKey);
    }

    @Override
    public int hashCode() {
        return Objects.hash(base, nameKey);
    }
}
