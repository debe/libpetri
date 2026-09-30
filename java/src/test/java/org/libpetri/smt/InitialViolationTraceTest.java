package org.libpetri.smt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The fixpoint query reports a violation of the initial marking itself as the empty firing
 * sequence: one marking (M0), no transition, confirmed — with the replay on or off. It used
 * to report VIOLATED with no trace at all (the refutation proof has no step to decode), which
 * no one can replay.
 */
class InitialViolationTraceTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final Place<Object> P = Place.of("p", Object.class);
    private static final Place<Object> Q = Place.of("q", Object.class);
    private static final Place<Object> R = Place.of("r", Object.class);

    private static PetriNet net() {
        return StructureOnly.bind(PetriNet.builder("initial")
            .transition(Transition.builder("t").inputs(In.one(P)).outputs(Out.place(Q)).build())
            .place(R)
            .build());
    }

    @Test
    @EnabledIf("z3Available")
    void anInitialViolationOnTheFixpointQueryIsTheEmptyTrace() {
        record Case(SmtProperty property, Set<Place<?>> sinks, MarkingState marking) {}
        var pr = MarkingState.builder().tokens(P, 1).tokens(R, 1).build();
        for (var c : List.of(
                new Case(SmtProperty.placeBound(P, 0), Set.of(), pr),
                new Case(SmtProperty.mutualExclusion(P, R), Set.of(), pr),
                // Quiescent at M0 with a stranded token in r.
                new Case(SmtProperty.deadlockFree(), Set.of(Q), MarkingState.builder().tokens(R, 1).build()))) {
            for (boolean replay : new boolean[] {true, false}) {
                var r = SmtVerifier.forNet(net())
                    .initialMarking(c.marking())
                    .property(c.property())
                    .sinkPlaces(c.sinks().toArray(Place<?>[]::new))
                    .enumerationMaxClasses(0)
                    .linearBound(false)
                    .stateEquationPhase(false)
                    .firingBound(false)
                    .counterexampleReplay(replay)
                    .verify();
                var tag = c.property().description() + " (replay " + replay + "):\n" + r.report();
                assertTrue(r.isViolated(), tag);
                assertEquals(SmtVerificationResult.Route.SMT, r.route(), tag);
                assertEquals(1, r.counterexampleTrace().size(), tag);
                assertTrue(r.counterexampleTransitions().isEmpty(), tag);
                assertEquals(Boolean.TRUE, r.counterexampleConfirmed(), tag);
                assertTrue(r.report().contains("the initial marking violates the property"), tag);
            }
        }
    }
}
