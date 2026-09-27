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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [CORE-072] / [VER-001]: a place the initial marking marks and the net does not declare is an
 * inert place of the verified net. Every route sees its token: before, the flat encoding dropped
 * it, so {@code deadlockFree} was {@code Violated} by enumeration and {@code Proven} by the SMT
 * routes once the class budget sent the query there.
 */
class InertMarkedPlaceTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final Place<Object> A = Place.of("a", Object.class);
    private static final Place<Object> C = Place.of("c", Object.class);
    private static final Place<Object> D = Place.of("d", Object.class);

    /** {@code t: one(c) -> d}; {@code a} is in no arc. */
    private static PetriNet net() {
        return StructureOnly.bind(PetriNet.builder("u")
            .transition(Transition.builder("t").inputs(In.one(C)).outputs(Out.place(D)).build())
            .build());
    }

    private static MarkingState strayToken() {
        return MarkingState.builder().tokens(A, 1).build();
    }

    private static SmtVerificationResult verify(SmtProperty property, int budget) {
        return SmtVerifier.forNet(net()).initialMarking(strayToken())
            .property(property).sinkPlaces(D).enumerationMaxClasses(budget).verify();
    }

    @Test
    @EnabledIf("z3Available")
    void deadlockFree_isViolatedAtEveryClassBudget() {
        for (int budget : new int[] {0, 1, 50_000}) {
            var r = verify(SmtProperty.deadlockFree(), budget);
            assertTrue(r.isViolated(), "budget " + budget + ":\n" + r.report());
        }
        assertEquals(SmtVerificationResult.Route.ENUMERATION, verify(SmtProperty.deadlockFree(), 50_000).route());
        assertEquals(SmtVerificationResult.Route.SMT, verify(SmtProperty.deadlockFree(), 0).route());
    }

    @Test
    @EnabledIf("z3Available")
    void placeBound_countsTheStrayToken() {
        for (int budget : new int[] {0, 1, 50_000}) {
            var r = verify(SmtProperty.placeBound(A, 0), budget);
            assertTrue(r.isViolated(), "budget " + budget + ":\n" + r.report());
            var ok = verify(SmtProperty.placeBound(A, 1), budget);
            assertTrue(ok.isProven(), "budget " + budget + ":\n" + ok.report());
        }
    }

    /** The inert place is its own P-invariant: {@code a = 1}. */
    @Test
    @EnabledIf("z3Available")
    void theInertPlaceIsItsOwnInvariant() {
        var r = verify(SmtProperty.deadlockFree(), 0);
        assertEquals(SmtVerificationResult.Route.SMT, r.route(), r.report());
        assertTrue(r.report().contains("\n  a = 1\n"), r.report());
        assertTrue(r.invariants().stream().anyMatch(inv -> inv.support().size() == 1 && inv.constant() == 1),
            "an invariant over the inert place alone:\n" + r.invariants());
    }

    /** [VER-003] AC5: a property may name a place the initial marking marks. */
    @Test
    void aPropertyNamingAMarkedUndeclaredPlaceIsNotRefused() {
        var r = SmtVerifier.forNet(net()).initialMarking(strayToken())
            .property(SmtProperty.placeBound(A, 0)).enumerationMaxClasses(50_000).verify();
        assertTrue(r.isViolated(), r.report());
        var absent = SmtVerifier.forNet(net()).initialMarking(strayToken())
            .property(SmtProperty.placeBound(Place.of("nowhere", Object.class), 0)).verify();
        var unknown = assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, absent.verdict(), absent.report());
        assertTrue(unknown.reason().contains("'nowhere'"), unknown.reason());
    }

    /** [EXEC-042]: a net-declared terminal excuses the inert place as it excuses every place. */
    @Test
    @EnabledIf("z3Available")
    void aTerminalExcusesTheInertPlace() {
        var net = StructureOnly.bind(PetriNet.builder("u")
            .transition(Transition.builder("t").inputs(In.one(C)).outputs(Out.place(D)).build())
            .terminal(D)
            .build());
        var m0 = MarkingState.builder().tokens(C, 1).tokens(A, 1).build();
        for (int budget : new int[] {0, 1, 50_000}) {
            var r = SmtVerifier.forNet(net).initialMarking(m0)
                .property(SmtProperty.deadlockFree()).enumerationMaxClasses(budget).verify();
            assertTrue(r.isProven(), "budget " + budget + ":\n" + r.report());
        }
    }

    /** The encodings see the inert place; a marking over declared places leaves the net as it was. */
    @Test
    void theEncodingDeclaresTheInertPlace_andANetWithoutOneIsUnchanged() {
        var declaredOnly = MarkingState.builder().tokens(C, 1).build();
        var withStray = MarkingState.builder().tokens(C, 1).tokens(A, 1).build();
        var plain = SmtVerifier.forNet(net()).initialMarking(declaredOnly)
            .property(SmtProperty.placeBound(D, 1)).encodeScripts();
        var marked = SmtVerifier.forNet(net()).initialMarking(withStray)
            .property(SmtProperty.placeBound(D, 1)).encodeScripts();
        assertTrue(!marked.horn().equals(plain.horn()), "the stray token reaches the encoding:\n" + marked.horn());

        var plainNet = net();
        assertSame(plainNet, SmtVerifier.withInertMarkedPlaces(plainNet, declaredOnly));
        var withInert = SmtVerifier.withInertMarkedPlaces(plainNet, strayToken());
        assertEquals(java.util.List.of("c", "d", "a"), withInert.places().stream().map(Place::name).toList(),
            "the inert place follows the declared ones");
    }
}
