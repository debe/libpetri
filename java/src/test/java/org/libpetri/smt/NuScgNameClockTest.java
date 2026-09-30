package org.libpetri.smt;

import org.libpetri.analysis.AllMints;
import org.junit.jupiter.api.Test;
import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.PrioritySemantics;
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
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Route B clocks follow a ν-join's name-enabledness ([NU-020], [TIME-012]). The executor enables a
 * join only while one name is present in every correlated input, so a count-enabled join whose
 * inputs share no name has no clock and its latest bound constrains nothing. Mirrors
 * {@code rust/libpetri-verification/src/nu_scg_verifier.rs} ({@code a_name_disabled_join_has_no_clock},
 * {@code a_join_clock_starts_when_its_binding_appears}).
 */
class NuScgNameClockTest {

    private static final Place<String> SOURCE_A = Place.of("sourceA", String.class);
    private static final Place<String> SOURCE_B = Place.of("sourceB", String.class);
    private static final Place<String> SOURCE_C = Place.of("sourceC", String.class);
    private static final Place<String> BRANCH_A = Place.of("branchA", String.class);
    private static final Place<String> BRANCH_B = Place.of("branchB", String.class);
    private static final Place<String> MERGED = Place.of("merged", String.class);
    private static final Place<String> W = Place.of("W", String.class);
    private static final Place<String> BAD = Place.of("BAD", String.class);

    private static Timing ms(long n) {
        return Timing.deadline(Duration.ofMillis(n));
    }

    /**
     * {@code forkA} and {@code forkB} mint one name each by 1 ms, {@code forkC} co-mints one name
     * into both at {@code exact(5)} when {@code withCoMint}, {@code join} matches the two on the
     * name, {@code watchdog: W -> BAD}.
     */
    private static PetriNet clockedJoinNet(Timing joinTiming, Timing watchdogTiming, boolean withCoMint) {
        var ts = new ArrayList<Transition>();
        ts.add(Transition.builder("forkA").inputs(In.one(SOURCE_A)).outputs(Out.place(BRANCH_A)).timing(ms(1)).build());
        ts.add(Transition.builder("forkB").inputs(In.one(SOURCE_B)).outputs(Out.place(BRANCH_B)).timing(ms(1)).build());
        ts.add(Transition.builder("join")
            .inputs(In.one(BRANCH_A), In.one(BRANCH_B))
            .match(MatchSpec.builder().key(BRANCH_A, NameId::of).key(BRANCH_B, NameId::of).build())
            .outputs(Out.place(MERGED))
            .timing(joinTiming)
            .build());
        ts.add(Transition.builder("watchdog").inputs(In.one(W)).outputs(Out.place(BAD)).timing(watchdogTiming).build());
        if (withCoMint) {
            ts.add(Transition.builder("forkC").inputs(In.one(SOURCE_C)).outputs(Out.and(BRANCH_A, BRANCH_B))
                .timing(Timing.exact(Duration.ofMillis(5))).build());
        }
        return StructureOnly.bind(PetriNet.builder("clocked_join").transitions(ts.toArray(Transition[]::new)).build());
    }

    private static NuScgVerifier.Outcome strict(PetriNet net, MarkingState initial, SmtProperty property) {
        return NuScgVerifier.verify(net, initial, property, Set.of(), Set.of(), EnvironmentAnalysisMode.ignore(),
            10_000, FragmentMode.BASE, Set.of(), AllMints.of(net), PrioritySemantics.NONE, List.of());
    }

    @Test
    void aNameDisabledJoinHasNoClock() {
        var net = clockedJoinNet(Timing.window(Duration.ZERO, Duration.ofMillis(5)),
            Timing.delayed(Duration.ofMillis(10)), false);
        var initial = MarkingState.builder().tokens(SOURCE_A, 1).tokens(SOURCE_B, 1).tokens(W, 1).build();
        var out = strict(net, initial, SmtProperty.unreachable(Set.of(BAD)));
        assertInstanceOf(SmtVerificationResult.Verdict.Violated.class, out.verdict(), out.note());
        assertFalse(out.transitions().contains("join"), out.transitions().toString());
        for (boolean noReaping : new boolean[] {true, false}) {
            var result = SmtVerifier.forNet(net).mintTransitions(AllMints.names(net))
                .initialMarking(initial)
                .property(SmtProperty.unreachable(Set.of(BAD)))
                .assumeNoReaping(noReaping)
                .timeout(Duration.ofSeconds(30))
                .verify();
            assertEquals(SmtVerificationResult.Route.NU_SCG, result.route(), result.report());
            assertTrue(result.isViolated(), "noReaping=" + noReaping + "\n" + result.report());
        }
    }

    @Test
    void aJoinClockStartsWhenItsBindingAppears() {
        var net = clockedJoinNet(Timing.delayed(Duration.ofMillis(10)), Timing.exact(Duration.ofMillis(12)), true);
        var initial = MarkingState.builder()
            .tokens(SOURCE_A, 1).tokens(SOURCE_B, 1).tokens(SOURCE_C, 1).tokens(W, 1).build();
        var out = strict(net, initial, SmtProperty.mutualExclusion(MERGED, W));
        assertInstanceOf(SmtVerificationResult.Verdict.Proven.class, out.verdict(), out.note());
    }
}
