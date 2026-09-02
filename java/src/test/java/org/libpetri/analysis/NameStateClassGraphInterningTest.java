package org.libpetri.analysis;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.time.Duration;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.function.IntUnaryOperator;

import org.junit.jupiter.api.Test;
import org.libpetri.core.Arc;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;

/**
 * VER-012 interning: hash-consing the base class and the name layer in
 * {@link NameStateClassGraph#build} must not change the explored quotient graph
 * ({@code Interning.lean}, {@code interned_keys_eq}).
 *
 * <p>Two things are pinned. The base intern key must carry {@code readyEarliest} alongside
 * marking and zone: two arrivals at one zone can disagree on it, and the NU-052 conflict prune
 * reads it ({@code equivariance_is_necessary} is the shape of that hole). And the name-layer
 * successor step must be equivariant under a renaming of symbols, which is what lets a class
 * be explored from a renamed representative.
 */
class NameStateClassGraphInterningTest {

    private static final Place<String> P = Place.of("P", String.class);
    private static final Place<String> C1 = Place.of("C1", String.class);
    private static final Place<String> C2 = Place.of("C2", String.class);
    private static final Place<String> Q = Place.of("Q", String.class);
    private static final Place<String> OUT = Place.of("OUT", String.class);
    private static final Place<String> OUT_H = Place.of("OUT_H", String.class);
    private static final Place<String> DEAD = Place.of("DEAD", String.class);
    private static final Place<String> DRAINED = Place.of("DRAINED", String.class);
    /** Never marked: keeps {@code J} structurally a ν-join without ever enabling it. */
    private static final Place<String> R = Place.of("R", String.class);

    /**
     * Two routes to one (marking, zone) that disagree on {@code readyEarliest} under different
     * name layers. {@code MC} co-mints one name into {@code C1}, {@code C2} and enables {@code H}
     * fresh (ready in 5 s); {@code M1} then {@code M2} mint two names and leave {@code H}
     * persistent through {@code M2}'s unbounded delay (ready now). {@code H} (priority 10) and
     * {@code L} (priority 0) compete for {@code Q}. {@code J} is gated on the never-marked
     * {@code R} so the meeting class enables exactly {@code H} and {@code L}, both fresh at the
     * point each route enables them, and the two zones agree constraint for constraint.
     *
     * @param withDrain add the EXTENDED coloured drain {@code D} (for the Consume role)
     */
    private static PetriNet fixture(boolean withDrain) {
        var mc = Transition.builder("MC")
            .inputs(Arc.In.exactly(2, P))
            .outputs(Arc.Out.and(C1, C2, Q))
            .build();
        var m1 = Transition.builder("M1")
            .inputs(Arc.In.one(P))
            .outputs(Arc.Out.and(C1, Q))
            .build();
        var m2 = Transition.builder("M2")
            .inputs(Arc.In.one(P))
            .timing(Timing.delayed(Duration.ofSeconds(3)))
            .outputs(Arc.Out.place(C2))
            .build();
        var h = Transition.builder("H")
            .inputs(Arc.In.one(Q))
            .timing(Timing.delayed(Duration.ofSeconds(5)))
            .priority(10)
            .outputs(Arc.Out.place(OUT_H))
            .build();
        var l = Transition.builder("L")
            .inputs(Arc.In.one(Q))
            .outputs(Arc.Out.place(DEAD))
            .build();
        var j = Transition.builder("J")
            .inputs(Arc.In.one(C1), Arc.In.one(C2), Arc.In.one(R))
            .match(MatchSpec.builder()
                .key(C1, (String s) -> NameId.of(s))
                .key(C2, (String s) -> NameId.of(s))
                .build())
            .outputs(Arc.Out.place(OUT))
            .build();
        var builder = PetriNet.builder("interning").transitions(mc, m1, m2, h, l, j);
        if (withDrain) {
            builder.transition(Transition.builder("D")
                .inputs(Arc.In.one(C1))
                .outputs(Arc.Out.place(DRAINED))
                .build());
        }
        return StructureOnly.bind(builder.build());
    }

    private static int target(NameStateClassGraph graph, int from, String transition) {
        for (var e : graph.edges()) {
            if (e.from() == from && e.transitionName().equals(transition)) {
                return e.to();
            }
        }
        throw new AssertionError("no edge " + transition + " out of class " + from);
    }

    private static boolean hasEdge(NameStateClassGraph graph, int from, String transition) {
        return graph.edges().stream()
            .anyMatch(e -> e.from() == from && e.transitionName().equals(transition));
    }

    @Test
    void internedBaseKeepsEachArrivalsReadyEarliest() {
        var net = fixture(false);
        var fragment = NameFragment.classify(net, FragmentMode.BASE, Set.of());
        var initial = MarkingState.builder().tokens(P, 2).build();
        var graph = NameStateClassGraph.build(
            net, initial, fragment, 10_000, Set.of(), EnvironmentAnalysisMode.ignore(),
            PrioritySemantics.CONFLICT);

        int same = target(graph, 0, "MC");          // one name in C1 and C2
        int mid = target(graph, 0, "M1");
        int diff = target(graph, mid, "M2");        // two names
        assertNotEquals(same, diff, "different name partitions are different classes");
        assertEquals(graph.markingOf(same), graph.markingOf(diff), "same base marking");

        assertTrue(hasEdge(graph, same, "L"),
            "H is freshly enabled here (ready in 5 s), so L is not pre-empted");
        assertFalse(hasEdge(graph, diff, "L"),
            "H has been enabled since M1 and may be ready now, so L is pre-empted: an interned "
            + "base must not hand this class the other arrival's readyEarliest");
        assertNotSame(graph.classAt(same).base, graph.classAt(diff).base,
            "the two arrivals disagree on readyEarliest, so they must not share a base");
    }

    private static NameMarking rename(NameMarking nm, List<String> places, IntUnaryOperator sigma) {
        var out = new NameMarking();
        for (var p : places) {
            for (int s : nm.symbolsIn(p)) {
                out.add(p, sigma.applyAsInt(s), nm.countOf(p, s));
            }
        }
        return out;
    }

    private static List<String> successorKeys(
            NameFragment fragment, String transition, NameMarking names, Set<Place<?>> outputs, int fresh) {
        var keys = new ArrayList<String>();
        for (var nm : NameStateClassGraph.nameSuccessors(
                fragment.role(transition), names, outputs, fragment, new int[]{fresh})) {
            keys.add(nm.canonicalKey(fragment.colouredOrder));
        }
        Collections.sort(keys);
        return keys;
    }

    @Test
    void nameSuccessorsAreEquivariantUnderRenaming() {
        // The hypothesis Interning.lean rests on: a renamed layer (same canonical key) has
        // successors with the same canonical keys, for every role, given fresh counters.
        var fragment = NameFragment.classify(fixture(true), FragmentMode.EXTENDED, Set.of());
        var names = new NameMarking();
        names.add(C1.name(), 3, 1);
        names.add(C2.name(), 3, 1);
        names.add(C2.name(), 7, 1);
        var renamed = rename(names, List.of(C1.name(), C2.name()), s -> s == 3 ? 11 : s == 7 ? 2 : s);
        assertEquals(names.canonicalKey(fragment.colouredOrder), renamed.canonicalKey(fragment.colouredOrder));

        Set<Place<?>> outputs = Set.of(C1, C2, Q);
        for (var t : List.of("MC", "J", "H", "D")) {
            assertEquals(
                successorKeys(fragment, t, names, outputs, 8),
                successorKeys(fragment, t, renamed, outputs, 12),
                t);
        }
    }
}
