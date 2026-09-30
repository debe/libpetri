package org.libpetri.core;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;

/**
 * NU-020: a match names each correlated input once. Two keys on one place made Route B remove
 * the matched name twice where the executor consumes it once, and prove a reachable place
 * unreachable. IO-002 / IO-004: an input requiring no token cannot be built at all in Java (the
 * {@link Arc.In.Exactly} and {@link Arc.In.AtLeast} records check it), so the zero-count join
 * key that Route B read as always satisfied in Rust has no Java counterpart.
 */
class MatchSpecKeysTest {

    private static final Place<String> A = Place.of("A", String.class);
    private static final Place<String> B = Place.of("B", String.class);
    private static final Place<String> MERGED = Place.of("merged", String.class);

    @Test
    void aPlaceKeyedTwiceIsRejectedByTheBuilder() {
        var ex = assertThrows(IllegalArgumentException.class,
            () -> MatchSpec.builder().key(A, NameId::of).key(A, NameId::of).build());
        assertTrue(ex.getMessage().contains("MatchSpec correlates input place 'A' twice"), ex.getMessage());
    }

    @Test
    void aPlaceKeyedTwiceAfterARemapIsRejectedByTheTransition() {
        var twice = MatchSpec.builder().key(A, NameId::of).key(B, NameId::of).build()
            .remap(p -> p.equals(B) ? A : p);
        var ex = assertThrows(IllegalArgumentException.class, () -> Transition.builder("join")
            .inputs(Arc.In.one(A), Arc.In.one(B))
            .outputs(Arc.Out.place(MERGED))
            .match(twice)
            .build());
        assertTrue(ex.getMessage().contains("MatchSpec correlates input place 'A' twice"), ex.getMessage());
    }

    /**
     * Keys compare by name, not by {@link Place} equality: the ν analysis identifies correlated
     * places by name, so two distinct places sharing one would read as one coloured place there.
     * The message says the places differ in type rather than claiming one place was keyed twice.
     */
    @Test
    void twoDistinctPlacesSharingANameAreRejectedAsSuch() {
        var aInt = Place.of("A", Integer.class);
        var ex = assertThrows(IllegalArgumentException.class, () -> Transition.builder("join")
            .inputs(Arc.In.one(A), Arc.In.one(aInt))
            .outputs(Arc.Out.place(MERGED))
            .match(MatchSpec.builder().key(A, NameId::of).key(aInt, (Integer i) -> NameId.of("" + i)).build())
            .build());
        assertTrue(ex.getMessage().contains("MatchSpec correlates two input places named 'A' "
            + "(token types java.lang.String and java.lang.Integer)"), ex.getMessage());
    }

    @Test
    void anInputRequiringNoTokenCannotBeBuilt() {
        assertThrows(IllegalArgumentException.class, () -> new Arc.In.Exactly(B, 0));
        assertThrows(IllegalArgumentException.class, () -> new Arc.In.AtLeast(B, 0));
    }

    /**
     * Relay targets compare by name too (NU-054): the ν analysis identifies them by name, so two
     * distinct places sharing one would read as one coloured place there.
     */
    @Test
    void twoRelayTargetsSharingANameAreRejected() {
        var outInt = Place.of("out", Integer.class);
        var outStr = Place.of("out", String.class);
        var ex = assertThrows(IllegalArgumentException.class, () -> Transition.builder("join")
            .inputs(Arc.In.one(A), Arc.In.one(B))
            .outputs(Arc.Out.and(Arc.Out.place(outStr), Arc.Out.place(outInt)))
            .match(MatchSpec.builder().key(A, NameId::of).key(B, NameId::of)
                .relayTo(outStr, NameId::of).relayTo(outInt, (Integer i) -> NameId.of("" + i)).build())
            .build());
        assertTrue(ex.getMessage().contains("relay targets are two places named 'out' "
            + "(token types java.lang.String and java.lang.Integer)"), ex.getMessage());
    }
}
