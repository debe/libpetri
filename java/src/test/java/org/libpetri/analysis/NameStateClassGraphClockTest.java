package org.libpetri.analysis;

import org.junit.jupiter.api.Test;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;

import java.time.Duration;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [TIME-012] on a ν-join: a firing that takes the join's matched name out of a key place breaks
 * the binding in the intermediate marking even when the count stays, so the join's clock
 * restarts. Mirrors {@code name_state_class_graph.rs},
 * {@code a_broken_binding_in_the_intermediate_marking_restarts_the_join_clock}.
 */
class NameStateClassGraphClockTest {

    @Test
    void aBrokenBindingInTheIntermediateMarkingRestartsTheJoinClock() {
        var s0 = Place.of("s0", String.class);
        var s1 = Place.of("s1", String.class);
        var go = Place.of("go", String.class);
        var a = Place.of("A", String.class);
        var b = Place.of("B", String.class);
        var out = Place.of("OUT", String.class);
        var m0 = Transition.builder("M0").inputs(In.one(s0)).outputs(Out.place(a))
            .timing(Timing.deadline(Duration.ofMillis(1))).build();
        var m1 = Transition.builder("M1").inputs(In.one(s1)).outputs(Out.and(a, b))
            .timing(Timing.deadline(Duration.ofMillis(1))).build();
        var j = Transition.builder("J")
            .inputs(In.one(a), In.one(b))
            .match(MatchSpec.builder().key(a, NameId::of).key(b, NameId::of).build())
            .outputs(Out.place(out))
            .timing(Timing.delayed(Duration.ofMillis(10)))
            .build();
        var r = Transition.builder("R").inputs(In.one(a), In.one(go)).outputs(Out.place(a))
            .timing(Timing.delayed(Duration.ofMillis(3))).build();
        var net = StructureOnly.bind(PetriNet.builder("broken_binding").transitions(m0, m1, j, r).build());
        var fragment = NameFragment.classify(net, FragmentMode.EXTENDED, Set.of(), AllMints.of(net));
        assertNotNull(fragment);
        var initial = MarkingState.builder().tokens(s0, 1).tokens(s1, 1).tokens(go, 1).build();
        var graph = NameStateClassGraph.build(net, initial, fragment, 10_000, Set.of(),
            EnvironmentAnalysisMode.ignore(), PrioritySemantics.NONE);
        assertTrue(graph.isComplete());
        var ready = new TreeSet<Long>();
        for (var e : graph.edges()) {
            if (!e.transitionName().equals("R")) continue;
            var base = graph.classAt(e.to()).base;
            for (int k = 0; k < base.enabledTransitions().size(); k++) {
                if (base.enabledTransitions().get(k).name().equals("J")) {
                    ready.add(Math.round(base.readyEarliest()[k] * 1000));
                }
            }
        }
        assertTrue(ready.contains(10L), "taking the matched name restarts J: " + ready);
        assertTrue(ready.first() <= 8, "taking the other name keeps J's clock: " + ready);
    }
}
