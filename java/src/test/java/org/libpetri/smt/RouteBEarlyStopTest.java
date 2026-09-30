package org.libpetri.smt;

import org.libpetri.analysis.AllMints;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.jupiter.api.Test;
import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.PrioritySemantics;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * [VER-012]: Route B checks each class against a reachability-safety property as it is
 * discovered and stops at the first violating one. The witness is the one the finished (or
 * truncated) graph gives; only the class count changes. Quiescence properties build in full.
 */
class RouteBEarlyStopTest {

    private static final Place<String> ORDER_CLERK = Place.of("order_clerk", String.class);

    private static NuScgVerifier.Outcome routeB(
            PetriNet net, MarkingState m0, SmtProperty property, Set<Place<?>> sinks, int maxClasses,
            boolean earlyStop) {
        var outcome = NuScgVerifier.verify(net, m0, property, sinks, Set.of(), EnvironmentAnalysisMode.ignore(),
            maxClasses, FragmentMode.EXTENDED, Set.of(), AllMints.of(net), PrioritySemantics.CONFLICT, List.of(), earlyStop);
        assertNotNull(outcome, "the net is in Route B's fragment");
        return outcome;
    }

    @Test
    void fig11b_atTheDefaultCap_isViolatedAfterAHandfulOfClasses() {
        var r = SmtVerifier.forNet(TruncatedPrefixTest.fig11b()).mintTransitions(AllMints.names(TruncatedPrefixTest.fig11b())).initialMarking(TruncatedPrefixTest.twoClerks())
            .property(SmtProperty.placeBound(ORDER_CLERK, 2))
            .verify();
        assertTrue(r.isViolated(), r.report());
        assertEquals(SmtVerificationResult.Route.NU_SCG, r.route(), r.report());
        assertEquals(List.of("create_order", "create_order", "create_order"), r.counterexampleTransitions());
        var m = java.util.regex.Pattern.compile("Route B stopped at the first violating class after (\\d+) classes "
            + "\\(VER-012\\)\\.").matcher(r.report());
        assertTrue(m.find(), r.report());
        int classes = Integer.parseInt(m.group(1));
        assertTrue(classes < 50, "a handful of classes, not the 100 000 cap: " + classes);
        assertTrue(r.report().contains("Name-partition state classes: " + classes + "\n"), r.report());
    }

    @Test
    void fig11b_aQuiescencePropertyStillExploresToTheCap() {
        var out = routeB(TruncatedPrefixTest.fig11b(), TruncatedPrefixTest.twoClerks(), SmtProperty.deadlockFree(),
            Set.of(), 50, true);
        assertInstanceOf(SmtVerificationResult.Verdict.Unknown.class, out.verdict());
        assertTrue(out.classCount() >= 50, "built to the cap: " + out.classCount());
        var reference = routeB(TruncatedPrefixTest.fig11b(), TruncatedPrefixTest.twoClerks(),
            SmtProperty.deadlockFree(), Set.of(), 50, false);
        assertEquals(reference.classCount(), out.classCount());
    }

    /** Early stop and the full build give the same verdict, trace and transitions. */
    @Test
    void theEarlyStopWitnessIsTheFullBuildWitness() {
        record Case(String name, PetriNet net, MarkingState m0, SmtProperty property, int cap) {}
        var chain = JoinRelayTest.chain(true);
        var fig12c = JoinRelayTest.fig12c(true);
        var n1 = JoinRelayTest.n1Corr(true);
        var cases = List.of(
            new Case("fig11b bound, truncating", TruncatedPrefixTest.fig11b(), TruncatedPrefixTest.twoClerks(),
                SmtProperty.placeBound(ORDER_CLERK, 2), 2_000),
            new Case("fig11b bound 5, truncating", TruncatedPrefixTest.fig11b(), TruncatedPrefixTest.twoClerks(),
                SmtProperty.placeBound(ORDER_CLERK, 5), 2_000),
            new Case("chain done reachable, closing", chain.build(), marking(chain, Map.of("S", 1)),
                SmtProperty.unreachable(Set.of(chain.p("done"))), 100_000),
            new Case("fig12c OR bound 1, closing", fig12c.build(), marking(fig12c, Map.of("R", 2)),
                SmtProperty.placeBound(fig12c.p("OR"), 1), 100_000),
            new Case("n1 mutual exclusion, closing", n1.build(), marking(n1, Map.of("SUPPLY", 2)),
                SmtProperty.mutualExclusion(n1.p("p"), n1.p("Y2")), 100_000));
        for (var c : cases) {
            var early = routeB(c.net, c.m0, c.property, Set.of(), c.cap, true);
            var full = routeB(c.net, c.m0, c.property, Set.of(), c.cap, false);
            assertTrue(full.verdict() instanceof SmtVerificationResult.Verdict.Violated, c.name + ": " + full.verdict());
            assertEquals(full.verdict(), early.verdict(), c.name);
            assertEquals(full.transitions(), early.transitions(), c.name);
            assertEquals(full.trace(), early.trace(), c.name);
            assertTrue(early.classCount() <= full.classCount(), c.name);
            assertTrue(early.note().contains("Route B stopped at the first violating class after "
                + early.classCount() + " classes (VER-012)."), c.name + ": " + early.note());
            System.out.println("[VER-012 early stop] " + c.name + ": " + early.classCount() + " vs "
                + full.classCount() + " classes, " + early.transitions());
        }
    }

    @Test
    void aSafetyPropertyThatHolds_buildsTheWholeGraph() {
        var n = JoinRelayTest.chainIndependentD();
        var m0 = marking(n, Map.of("S", 1, "S2", 1));
        var early = routeB(n.build(), m0, SmtProperty.unreachable(Set.of(n.p("done"))), Set.of(), 100_000, true);
        var full = routeB(n.build(), m0, SmtProperty.unreachable(Set.of(n.p("done"))), Set.of(), 100_000, false);
        assertInstanceOf(SmtVerificationResult.Verdict.Proven.class, early.verdict());
        assertEquals(full.classCount(), early.classCount());
        assertEquals(NuScgVerifier.NOTE_EXACT, early.note());
    }

    private static MarkingState marking(JoinRelayTest.Net n, Map<String, Integer> m0) {
        var b = MarkingState.builder();
        m0.forEach((p, c) -> b.tokens(n.p(p), c));
        return b.build();
    }
}
