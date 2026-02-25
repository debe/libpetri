package org.libpetri.smt.invariant;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.*;
import org.libpetri.smt.encoding.IncidenceMatrix;
import org.libpetri.smt.encoding.NetFlattener;
import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

class PInvariantComputerTest {

    @Test
    void circularNet_findsConservationInvariant() {
        // A -> B -> A (token-conserving circular net)
        var pA = Place.of("A", String.class);
        var pB = Place.of("B", String.class);

        var t1 = Transition.builder("Forward")
            .inputs(In.one(pA))
            .outputs(Out.place(pB))
            .build();
        var t2 = Transition.builder("Back")
            .inputs(In.one(pB))
            .outputs(Out.place(pA))
            .build();

        var net = PetriNet.builder("Circular").transitions(t1, t2).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);

        var marking = MarkingState.builder().tokens(pA, 1).build();
        var invariants = PInvariantComputer.compute(matrix, flatNet, marking);

        assertFalse(invariants.isEmpty(), "Should find at least one P-invariant");

        // The invariant should be A + B = 1 (or proportional)
        var inv = invariants.getFirst();
        int idxA = flatNet.indexOf(pA);
        int idxB = flatNet.indexOf(pB);

        assertEquals(inv.weights()[idxA], inv.weights()[idxB],
            "Weights should be equal for circular net");
        assertEquals(1, inv.constant(), "Constant should be 1 (initial A=1, B=0)");
    }

    @Test
    void pipelineNet_findsInvariant() {
        // A -> B -> C (simple pipeline)
        var pA = Place.of("A", String.class);
        var pB = Place.of("B", String.class);
        var pC = Place.of("C", String.class);

        var t1 = Transition.builder("T1")
            .inputs(In.one(pA))
            .outputs(Out.place(pB))
            .build();
        var t2 = Transition.builder("T2")
            .inputs(In.one(pB))
            .outputs(Out.place(pC))
            .build();

        var net = PetriNet.builder("Pipeline").transitions(t1, t2).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);

        var marking = MarkingState.builder().tokens(pA, 2).build();
        var invariants = PInvariantComputer.compute(matrix, flatNet, marking);

        // A + B + C = 2 (conservation law)
        assertFalse(invariants.isEmpty(), "Pipeline should have a conservation invariant");
        var inv = invariants.getFirst();
        assertEquals(2, inv.constant(), "Total tokens should be 2");
    }

    @Test
    void isCoveredByInvariants_trueForConservingNet() {
        var pA = Place.of("A", String.class);
        var pB = Place.of("B", String.class);

        var t1 = Transition.builder("T1").inputs(In.one(pA)).outputs(Out.place(pB)).build();
        var t2 = Transition.builder("T2").inputs(In.one(pB)).outputs(Out.place(pA)).build();

        var net = PetriNet.builder("Circular").transitions(t1, t2).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);

        var marking = MarkingState.builder().tokens(pA, 1).build();
        var invariants = PInvariantComputer.compute(matrix, flatNet, marking);

        assertTrue(PInvariantComputer.isCoveredByInvariants(invariants, flatNet.placeCount()),
            "All places in circular net should be covered by invariants");
    }

    @Test
    void emptyNet_noInvariants() {
        var p = Place.of("A", String.class);
        var net = PetriNet.builder("Empty").places(p).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);

        var invariants = PInvariantComputer.compute(matrix, flatNet, MarkingState.empty());
        // Net with no transitions — PInvariantComputer short-circuits (T==0),
        // returning empty list. All places are trivially bounded but the
        // Farkas algorithm has no columns to eliminate.
        assertTrue(invariants.isEmpty(), "No transitions means no P-invariants computed");
    }
}
