package org.libpetri.core;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;
import org.libpetri.core.internal.SubnetRewriter;

/**
 * NU-054 declaration: relay targets on a {@link MatchSpec} — build-time rejections (AC1) and
 * remapping under composition like the keys (NU-030, NU-060).
 */
class MatchSpecRelayTest {

    private static final Place<String> C1 = Place.of("C1", String.class);
    private static final Place<String> D1 = Place.of("D1", String.class);
    private static final Place<String> P5 = Place.of("P5", String.class);
    private static final Place<String> OTHER = Place.of("OTHER", String.class);

    private static NameId byName(String s) {
        return NameId.of(s);
    }

    private static MatchSpec.Builder keys() {
        return MatchSpec.builder().key(C1, MatchSpecRelayTest::byName).key(D1, MatchSpecRelayTest::byName);
    }

    @Test
    void relayTargetNotAnOutput_rejectedAtBuild() {
        var ex = assertThrows(IllegalArgumentException.class, () -> Transition.builder("e")
            .inputs(Arc.In.one(C1), Arc.In.one(D1))
            .outputs(Arc.Out.place(P5))
            .match(keys().relayTo(OTHER, MatchSpecRelayTest::byName).build())
            .build());
        assertEquals("Transition 'e': relay target 'OTHER' is not an output of the transition (NU-054)",
            ex.getMessage());
    }

    @Test
    void relayTargetOfATransitionWithNoOutputs_rejectedAtBuild() {
        var ex = assertThrows(IllegalArgumentException.class, () -> Transition.builder("e")
            .inputs(Arc.In.one(C1), Arc.In.one(D1))
            .match(keys().relayTo(P5, MatchSpecRelayTest::byName).build())
            .build());
        assertEquals("Transition 'e': relay target 'P5' is not an output of the transition (NU-054)",
            ex.getMessage());
    }

    @Test
    void relayTargetDeclaredTwice_rejectedAtBuild() {
        var ex = assertThrows(IllegalArgumentException.class, () -> Transition.builder("e")
            .inputs(Arc.In.one(C1), Arc.In.one(D1))
            .outputs(Arc.Out.place(P5))
            .match(keys()
                .relayTo(P5, MatchSpecRelayTest::byName)
                .relayTo(P5, MatchSpecRelayTest::byName)
                .build())
            .build());
        assertEquals("Transition 'e': relay target 'P5' is declared twice (NU-054)", ex.getMessage());
    }

    @Test
    void relayTargets_acceptedOnOneBranchOnOwnKeyAndForwarded() {
        // One XOR branch is enough; a key is allowed (self-loop); a ForwardInput target counts.
        var t = Transition.builder("B")
            .inputs(Arc.In.one(C1), Arc.In.one(D1))
            .outputs(Arc.Out.xor(Arc.Out.and(P5, D1), Arc.Out.forwardInput(C1, OTHER)))
            .match(keys()
                .relayTo(P5, MatchSpecRelayTest::byName)
                .relayTo(D1, MatchSpecRelayTest::byName)
                .relayTo(OTHER, MatchSpecRelayTest::byName)
                .build())
            .build();
        assertEquals(List.of(P5, D1, OTHER), t.matchSpec().relays().stream().map(MatchSpec.MatchKey::place).toList());
        assertEquals(2, t.matchSpec().keys().size(), "relays do not count as keys");
        assertNotNull(t.matchSpec().relayFor(P5));
    }

    @Test
    void relayDoesNotCountTowardsTwoCorrelatedInputs() {
        var ex = assertThrows(IllegalArgumentException.class, () -> MatchSpec.builder()
            .key(C1, MatchSpecRelayTest::byName)
            .relayTo(P5, MatchSpecRelayTest::byName)
            .build());
        assertEquals("MatchSpec must correlate at least 2 input places, got 1", ex.getMessage());
    }

    private static Transition relayJoin() {
        return Transition.builder("e")
            .inputs(Arc.In.one(C1), Arc.In.one(D1))
            .outputs(Arc.Out.place(P5))
            .match(keys().relayTo(P5, MatchSpecRelayTest::byName).build())
            .build();
    }

    private static List<String> relayNames(Transition t) {
        return t.matchSpec().relays().stream().map(r -> r.place().name()).toList();
    }

    @Test
    void relayTargets_remappedByInstancePrefix() {
        var body = PetriNet.builder("sub").transitions(relayJoin()).build();
        var placeRemap = SubnetRewriter.newPlaceRemap();
        var renamed = SubnetRewriter.renameNet(body, "inst", placeRemap, SubnetRewriter.newTransitionRemap());
        var t = renamed.transitions().iterator().next();
        assertEquals(List.of("inst/P5"), relayNames(t));
        assertEquals("NAME", t.matchSpec().relays().get(0).key().apply("NAME").value(),
            "the projection is preserved");
    }

    @Test
    void relayTargets_remappedByPortBinding() {
        var host = Place.of("HOST_P5", String.class);
        var t = SubnetRewriter.substitutePlaces(relayJoin(), Map.of(P5, host));
        assertEquals(List.of("HOST_P5"), relayNames(t));
    }

    @Test
    void relayTargets_remappedByFusion() {
        var canonical = Place.of("FUSED", String.class);
        var fused = SubnetRewriter.applyFusion(List.of(relayJoin()), Map.of(P5, canonical), p -> "Fusion set 'f'");
        assertEquals(List.of("FUSED"), relayNames(fused.iterator().next()));
    }
}
