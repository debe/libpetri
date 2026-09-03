package org.libpetri.analysis;

import java.util.List;

/**
 * A name-aware state class (NU-050, Route B): the base count + DBM
 * {@link StateClass} plus the abstract {@link NameMarking} partition layer. The
 * base class is reused verbatim, so the timing/zone dimension is untouched —
 * name&times;time composition is automatic.
 *
 * <p>Both layers are interned by {@link NameStateClassGraph#build} ([VER-012]), and the pair of
 * intern ids is what identifies a class: the base id covers marking, zone and the class-relative
 * earliest-ready times, the name id covers the symmetry-canonical partition key. The class object
 * itself carries no equality, so nothing can dedup on {@code (base, nameKey)} and hand one arrival
 * another's earliest-ready times, which the NU-052 prune reads.
 */
final class NameStateClass {

    final StateClass base;
    final NameMarking names;
    private final String nameKey;

    NameStateClass(StateClass base, NameMarking names, List<String> colouredOrder) {
        this(base, names, names.canonicalKey(colouredOrder));
    }

    /** As above with a precomputed key — used when sharing an interned name layer. */
    NameStateClass(StateClass base, NameMarking names, String nameKey) {
        this.base = base;
        this.names = names;
        this.nameKey = nameKey;
    }

    String nameKey() {
        return nameKey;
    }
}
