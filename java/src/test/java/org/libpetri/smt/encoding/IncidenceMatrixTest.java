package org.libpetri.smt.encoding;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.core.*;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

class IncidenceMatrixTest {

    @Test
    void simpleNet_incidenceMatrixCorrect() {
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);

        var t = Transition.builder("T")
            .inputs(In.one(p1))
            .outputs(Out.place(p2))
            .build();

        var net = PetriNet.builder("Test").transitions(t).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);

        int idxA = flatNet.indexOf(p1);
        int idxB = flatNet.indexOf(p2);

        assertEquals(1, matrix.numTransitions());
        assertEquals(2, matrix.numPlaces());

        // T consumes from A, produces to B
        assertEquals(1, matrix.pre()[0][idxA]);
        assertEquals(0, matrix.pre()[0][idxB]);
        assertEquals(0, matrix.post()[0][idxA]);
        assertEquals(1, matrix.post()[0][idxB]);
        assertEquals(-1, matrix.incidence()[0][idxA]);
        assertEquals(1, matrix.incidence()[0][idxB]);
    }

    @Test
    void transposedIncidence_dimensionsCorrect() {
        var p1 = Place.of("A", String.class);
        var p2 = Place.of("B", String.class);
        var p3 = Place.of("C", String.class);

        var t1 = Transition.builder("T1")
            .inputs(In.one(p1))
            .outputs(Out.place(p2))
            .build();
        var t2 = Transition.builder("T2")
            .inputs(In.one(p2))
            .outputs(Out.place(p3))
            .build();

        var net = PetriNet.builder("Test").transitions(t1, t2).build();
        var flatNet = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var matrix = IncidenceMatrix.from(flatNet);

        int[][] ct = matrix.transposedIncidence();
        assertEquals(3, ct.length, "C^T should have P rows");
        assertEquals(2, ct[0].length, "C^T should have T columns");
    }

    @Test
    void circularNet_incidenceMatrixSumsToZeroPerRow() {
        // A -> B -> A (circular)
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

        // For a circular net, the sum of incidence columns (across all transitions)
        // for each place should equal 0 (tokens are conserved)
        int[][] ct = matrix.transposedIncidence();
        for (int p = 0; p < matrix.numPlaces(); p++) {
            int sum = 0;
            for (int t = 0; t < matrix.numTransitions(); t++) {
                sum += ct[p][t];
            }
            assertEquals(0, sum, "Place " + p + " should have zero net token change in circular net");
        }
    }
}
