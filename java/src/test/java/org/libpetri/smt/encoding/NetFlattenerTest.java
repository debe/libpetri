package org.libpetri.smt.encoding;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.core.*;
import org.libpetri.fixtures.PaperNetworks;
import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

class NetFlattenerTest {

    @Test
    void flattenBasicTpn_assignsStablePlaceIndices() {
        var net = PaperNetworks.createBasicTpn();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());

        // Places should be sorted by name
        for (int i = 1; i < flatNet.places().size(); i++) {
            assertTrue(
                flatNet.places().get(i - 1).name().compareTo(flatNet.places().get(i).name()) <= 0,
                "Places should be sorted by name"
            );
        }

        // Reverse lookup should be consistent
        for (int i = 0; i < flatNet.places().size(); i++) {
            assertEquals(i, flatNet.indexOf(flatNet.places().get(i)));
        }
    }

    @Test
    void flattenBasicTpn_correctPlaceAndTransitionCount() {
        var net = PaperNetworks.createBasicTpn();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());

        // BasicTPN has 9 places: Pending, Ready, Validated, Understood, Informed, Promoted, Found, Drafted, Answered
        // (net.places() may be incomplete for new-API transitions, but flatten collects all)
        assertEquals(9, flatNet.placeCount());
        // BasicTPN has no XOR, so transitions should be 1:1 = 7
        assertEquals(7, flatNet.transitionCount());
    }

    @Test
    void flattenExtendedTpn_expandsXorBranches() {
        var net = PaperNetworks.createExtendedTpn();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());

        // ExtendedTPN has 2 XOR transitions (Search, Compose), each with 2 branches
        // So we should have 11 original + 2 extra = 13 flat transitions
        // (Search -> 2 branches, Compose -> 2 branches, rest are 1:1)
        int xorExpansion = 0;
        for (var ft : flatNet.transitions()) {
            if (ft.branchIndex() >= 0) {
                xorExpansion++;
            }
        }
        // Search has 2 branches, Compose has 2 branches = 4 total expanded
        assertEquals(4, xorExpansion, "Should have 4 XOR-expanded transitions");
    }

    @Test
    void flattenTransition_preVectorCorrect() {
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);
        var p3 = Place.of("C", String.class);

        var t = Transition.builder("T")
            .inputs(In.one(p1), In.exactly(3, p2))
            .outputs(Out.place(p3))
            .build();

        var net = PetriNet.builder("Test").transitions(t).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());

        assertEquals(1, flatNet.transitionCount());
        var ft = flatNet.transitions().getFirst();

        int idxA = flatNet.indexOf(p1);
        int idxB = flatNet.indexOf(p2);
        int idxC = flatNet.indexOf(p3);

        assertEquals(1, ft.preVector()[idxA]);
        assertEquals(3, ft.preVector()[idxB]);
        assertEquals(0, ft.preVector()[idxC]);
        assertEquals(0, ft.postVector()[idxA]);
        assertEquals(0, ft.postVector()[idxB]);
        assertEquals(1, ft.postVector()[idxC]);
    }

    @Test
    void flattenTransition_consumeAllFlagSet() {
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);

        var t = Transition.builder("T")
            .inputs(In.all(p1))
            .outputs(Out.place(p2))
            .build();

        var net = PetriNet.builder("Test").transitions(t).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());

        var ft = flatNet.transitions().getFirst();
        int idxA = flatNet.indexOf(p1);
        assertTrue(ft.consumeAll()[idxA], "consumeAll should be true for In.all()");
        assertEquals(1, ft.preVector()[idxA], "pre should be 1 (minimum) for In.all()");
    }

    @Test
    void flattenTransition_inhibitorAndReadArcs() {
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);
        var p3 = Place.of("C", String.class);
        var p4 = Place.of("D", String.class);

        var t = Transition.builder("T")
            .inputs(In.one(p1))
            .inhibitor(p2)
            .read(p3)
            .outputs(Out.place(p4))
            .build();

        var net = PetriNet.builder("Test").transitions(t).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());

        var ft = flatNet.transitions().getFirst();
        int idxB = flatNet.indexOf(p2);
        int idxC = flatNet.indexOf(p3);

        assertArrayEquals(new int[]{idxB}, ft.inhibitorPlaces());
        assertArrayEquals(new int[]{idxC}, ft.readPlaces());
    }

    @Test
    void flattenWithEnvironmentBounds() {
        var envPlace = Place.of("Env", String.class);
        var env = EnvironmentPlace.of(envPlace);
        var output = Place.of("Out", String.class);

        var t = Transition.builder("T")
            .inputs(In.one(envPlace))
            .outputs(Out.place(output))
            .build();

        var net = PetriNet.builder("Test").transitions(t).build();
        var flatNet = NetFlattener.flatten(net, Set.of(env), EnvironmentAnalysisMode.bounded(3));

        assertEquals(3, flatNet.environmentBounds().get(envPlace));
    }

    @Test
    void flattenXorTransition_createsSeparateFlatTransitions() {
        var input = Place.of("In", String.class);
        var out1 = Place.of("Out1", String.class);
        var out2 = Place.of("Out2", String.class);

        var t = Transition.builder("Choice")
            .inputs(In.one(input))
            .outputs(Out.xor(out1, out2))
            .build();

        var net = PetriNet.builder("Test").transitions(t).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());

        assertEquals(2, flatNet.transitionCount(), "XOR with 2 branches should expand to 2 flat transitions");

        var ft0 = flatNet.transitions().get(0);
        var ft1 = flatNet.transitions().get(1);

        // Both should consume from input
        int inIdx = flatNet.indexOf(input);
        assertEquals(1, ft0.preVector()[inIdx]);
        assertEquals(1, ft1.preVector()[inIdx]);

        // Each should produce to different output
        int out1Idx = flatNet.indexOf(out1);
        int out2Idx = flatNet.indexOf(out2);

        // One produces to out1, other to out2
        boolean branch0HasOut1 = ft0.postVector()[out1Idx] == 1;
        boolean branch1HasOut1 = ft1.postVector()[out1Idx] == 1;
        assertTrue(branch0HasOut1 ^ branch1HasOut1, "Exactly one branch should output to Out1");
    }
}
