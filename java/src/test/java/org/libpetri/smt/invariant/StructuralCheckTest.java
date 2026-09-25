package org.libpetri.smt.invariant;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.*;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.NetFlattener;
import org.junit.jupiter.api.Test;

import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Commoner's condition needs EVERY minimal siphon, each holding a trap marked under the
 * initial marking ([VER-020]). Each witness below is dead at its initial marking with a
 * token stranded, and a search that commits to one input per producer misses its siphon.
 */
class StructuralCheckTest {

    private static final Place<Integer> G = Place.of("g", Integer.class);
    private static final Place<Integer> H = Place.of("h", Integer.class);
    private static final Place<Integer> X = Place.of("x", Integer.class);
    private static final Place<Integer> Y = Place.of("y", Integer.class);

    /** x -> y -> x, each step also consuming and returning its own guard place. */
    private static FlatNet guardedRing() {
        var t1 = Transition.builder("t1").inputs(In.one(G), In.one(X)).outputs(Out.and(Y, G)).build();
        var t2 = Transition.builder("t2").inputs(In.one(H), In.one(Y)).outputs(Out.and(X, H)).build();
        return NetFlattener.flatten(PetriNet.builder("guarded-ring").transitions(t1, t2).build(),
            Set.of(), EnvironmentAnalysisMode.ignore());
    }

    @Test
    void findsASiphonThatOnlyASecondInputReaches() {
        // Growing each siphon by the FIRST input of a producer reaches only {g} and {h}.
        var flat = guardedRing();
        var names = StructuralCheck.findMinimalSiphons(flat, 10_000).stream()
            .map(s -> {
                var n = new TreeSet<String>();
                s.forEach(i -> n.add(flat.places().get(i).name()));
                return String.join(",", n);
            })
            .toList();
        assertTrue(names.contains("x,y"), names.toString());

        var dead = MarkingState.builder().tokens(G, 1).tokens(H, 1).build();
        assertInstanceOf(StructuralCheck.Result.PotentialDeadlock.class, StructuralCheck.check(flat, dead));
        var live = MarkingState.builder().tokens(G, 1).tokens(H, 1).tokens(X, 1).build();
        assertInstanceOf(StructuralCheck.Result.NoPotentialDeadlock.class, StructuralCheck.check(flat, live));
    }

    @Test
    void doesNotPadASiphonWithEveryInputOfAProducer() {
        // t1: a + c -> b + c, t2: b -> a. The minimal siphon {a, b} is empty at {c:1}.
        var a = Place.of("a", Integer.class);
        var b = Place.of("b", Integer.class);
        var c = Place.of("c", Integer.class);
        var t1 = Transition.builder("t1").inputs(In.one(a), In.one(c)).outputs(Out.and(b, c)).build();
        var t2 = Transition.builder("t2").inputs(In.one(b)).outputs(Out.place(a)).build();
        var flat = NetFlattener.flatten(PetriNet.builder("stranded").transitions(t1, t2).build(),
            Set.of(), EnvironmentAnalysisMode.ignore());
        assertInstanceOf(StructuralCheck.Result.PotentialDeadlock.class,
            StructuralCheck.check(flat, MarkingState.builder().tokens(c, 1).build()));
    }

    @Test
    void anExhaustedSearchIsInconclusive() {
        assertNull(StructuralCheck.findMinimalSiphons(guardedRing(), 1));
    }
}
