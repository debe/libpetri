package org.libpetri.smt.z3;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

import java.util.Set;

import org.junit.jupiter.api.Test;
import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.smt.encoding.NetFlattener;

/**
 * Z3-free conformance for the name-coloured fragment gate
 * ({@link NameColouredEncoder#buildPlan}). Pins nu-1: a budget-inflating ν-net (a
 * join refunding more budget than a mint consumes) must fall back to the sound
 * over-approximation rather than take the exact, caveat-dropped name-coloured path.
 */
class NameColouredEncoderTest {

    /**
     * A budget-bounded mint→join net (same-mint scatter-gather). The mint consumes
     * 1 budget and stamps the fresh colour into both correlated inputs; the join
     * refunds 1 budget (conserving) or 2 (inflating, into a second budget place).
     */
    private static PetriNet mintJoinNet(boolean inflating) {
        var budget1 = Place.of("budget1", Integer.class);
        var budget2 = Place.of("budget2", Integer.class);
        var a = Place.of("branchA", String.class);
        var b = Place.of("branchB", String.class);

        var mint = Transition.builder("mint")
            .inputs(Arc.In.one(budget1))
            .outputs(Arc.Out.and(a, b))
            .build();
        Arc.Out joinOut = inflating ? Arc.Out.and(budget1, budget2) : Arc.Out.place(budget1);
        var join = Transition.builder("join")
            .inputs(Arc.In.one(a), Arc.In.one(b))
            .match(MatchSpec.builder()
                .key(a, (String s) -> NameId.of(s))
                .key(b, (String s) -> NameId.of(s))
                .build())
            .outputs(joinOut)
            .build();
        return PetriNet.builder("mintJoin").transitions(mint, join).build();
    }

    private static NameColouredEncoder.ColouredPlan planFor(PetriNet net) {
        var flat = NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
        var initial = MarkingState.builder()
            .tokens(Place.of("budget1", Integer.class), 1)
            .build();
        return NameColouredEncoder.buildPlan(net, flat, initial, Set.of("budget1", "budget2"));
    }

    @Test
    void budgetConservingJoinTakesExactPath() {
        // Refund (1) == mint cost (1): live names ≤ k, so the exact name-coloured
        // encoding is used.
        assertNotNull(planFor(mintJoinNet(false)));
    }

    @Test
    void budgetInflatingJoinFallsBackToOverApprox() {
        // nu-1: a join refunding 2 budget for a 1-budget mint inflates the pool
        // above k — the k-colour encoder would UNDER-approximate and report a false
        // `Proven`. buildPlan must reject it (null → sound over-approximation).
        assertNull(planFor(mintJoinNet(true)));
    }
}
