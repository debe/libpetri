package org.libpetri.smt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link SmtVerifier#semiflowInvariants(boolean)}: the validated P-semiflows reach the
 * encoder as extra invariants, and only when asked for.
 *
 * <p>The net is a budgeted work loop with one reset arc on a side place — the shape that
 * makes the null-space basis fold the reset place into the loop's conservation law and lose
 * it. The semiflow enumeration still finds {@code Budget + Work + Done = 1} with zero weight
 * on the reset place.
 */
class SemiflowInvariantsTest {

    static boolean z3Available() {
        try {
            new com.microsoft.z3.Context().close();
            return true;
        } catch (UnsatisfiedLinkError | NoClassDefFoundError _) {
            return false;
        }
    }

    private static final Place<String> BUDGET = Place.of("Budget", String.class);
    private static final Place<String> WORK = Place.of("Work", String.class);
    private static final Place<String> DONE = Place.of("Done", String.class);
    private static final Place<String> STAMP = Place.of("Stamp", String.class);
    private static final Place<String> SINK = Place.of("Sink", String.class);

    private static PetriNet loop() {
        var open = Transition.builder("Open")
            .inputs(In.one(BUDGET))
            .resets(STAMP)
            .outputs(Out.and(WORK, STAMP))
            .build();
        var step = Transition.builder("Step").inputs(In.one(WORK)).outputs(Out.place(DONE)).build();
        var close = Transition.builder("Close")
            .inputs(In.one(DONE))
            .outputs(Out.and(BUDGET, SINK))
            .build();
        return StructureOnly.bind(PetriNet.builder("loop").transitions(open, step, close).build());
    }

    @Test
    @EnabledIf("z3Available")
    void semiflowsAreEncodedOnlyWhenEnabled() {
        var off = SmtVerifier.forNet(loop())
            .initialMarking(m -> m.tokens(BUDGET, 1))
            .property(SmtProperty.placeBound(WORK, 1))
            .timeout(Duration.ofSeconds(30))
            .verify();
        assertFalse(off.report().contains("Semiflows encoded as invariants"), off.report());

        var on = SmtVerifier.forNet(loop())
            .initialMarking(m -> m.tokens(BUDGET, 1))
            .property(SmtProperty.placeBound(WORK, 1))
            .semiflowInvariants(true)
            .timeout(Duration.ofSeconds(30))
            .verify();
        assertTrue(on.isProven(), on.report());
        assertTrue(on.report().contains("Semiflows encoded as invariants: "), on.report());
        assertTrue(on.report().contains("Budget + Done + Work = 1")
                || on.report().contains("Work + Done + Budget = 1")
                || on.report().lines().anyMatch(l -> l.contains("Budget") && l.contains("Work")
                        && l.contains("Done") && l.contains("= 1") && !l.contains("Dropped")),
            "the loop's conservation law must survive the reset arc on Stamp\n" + on.report());
    }

    @Test
    @EnabledIf("z3Available")
    void strengtheningNeverHidesACounterexample() {
        // Sink accumulates one token per loop iteration: the bound 1 is genuinely violated.
        var result = SmtVerifier.forNet(loop())
            .initialMarking(m -> m.tokens(BUDGET, 1))
            .property(SmtProperty.placeBound(SINK, 1))
            .semiflowInvariants(true)
            .timeout(Duration.ofSeconds(30))
            .verify();
        assertTrue(result.isViolated(), result.report());
    }
}
