package org.libpetri.analysis;

import org.libpetri.fixtures.StructureOnly;
import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.core.TransitionAction;
import org.libpetri.fixtures.PaperNetworks;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;
import java.util.concurrent.CompletableFuture;

import static org.junit.jupiter.api.Assertions.*;

class XorBranchAnalysisTest {

    private static TimePetriNetAnalyzer.XorBranchAnalysis analysis;
    private static StateClassGraph scg;

    @BeforeAll
    static void setUp() {
        var net = PaperNetworks.createExtendedTpn();
        var pending = net.places().stream()
                .filter(p -> p.name().equals("Pending"))
                .findFirst()
                .orElseThrow();
        scg = StateClassGraph.build(
                StructureOnly.bind(net),
                MarkingState.builder().tokens(pending, 1).build(),
                10_000
        );

        analysis = TimePetriNetAnalyzer.analyzeXorBranches(scg);
    }

    @Test
    void shouldIdentifyXorTransitions() {
        var xorTransitions = analysis.xorTransitions();
        assertFalse(xorTransitions.isEmpty());

        // Extended TPN has Search (found|searchFail) and Compose (drafted|composeFail) as XOR
        var xorNames = xorTransitions.stream().map(Transition::name).toList();
        assertTrue(xorNames.contains("Search"), "Search should be XOR: " + xorNames);
        assertTrue(xorNames.contains("Compose"), "Compose should be XOR: " + xorNames);
    }

    @Test
    void shouldReportBranchCoveragePerTransition() {
        for (var t : analysis.xorTransitions()) {
            var info = analysis.branchInfo(t);
            assertTrue(info.isPresent(), "Branch info should exist for " + t.name());
            assertTrue(info.get().totalBranches() >= 2,
                    t.name() + " should have at least 2 branches");
            assertFalse(info.get().takenBranches().isEmpty(),
                    t.name() + " should have at least one taken branch");
        }
    }

    @Test
    void shouldReportUnreachableBranches() {
        var unreachable = analysis.unreachableBranches();
        // This is informational — some branches may or may not be unreachable depending on the SCG
        assertNotNull(unreachable);
        // Each unreachable entry should have non-empty branch indices
        for (var entry : unreachable.entrySet()) {
            assertFalse(entry.getValue().isEmpty(),
                    entry.getKey().name() + " should have specific unreachable branch indices");
        }
    }

    @Test
    void shouldBeConsistentBetweenIsXorCompleteAndUnreachableBranches() {
        if (analysis.isXorComplete()) {
            assertTrue(analysis.unreachableBranches().isEmpty(),
                    "isXorComplete() should imply no unreachable branches");
        } else {
            assertFalse(analysis.unreachableBranches().isEmpty(),
                    "!isXorComplete() should imply some unreachable branches");
        }
    }

    @Test
    void shouldGenerateReadableReport() {
        var report = analysis.report();
        assertNotNull(report);
        assertFalse(report.isBlank());
        assertTrue(report.contains("XOR Branch Coverage"), "Report should have header");
        assertTrue(report.contains("Search") || report.contains("Compose"),
                "Report should mention XOR transitions");
        assertTrue(report.contains("RESULT:"), "Report should have result line");
    }

    // ==================== Graphs of the analyzer's rewritten net ====================

    private static final Place<Integer> IN = Place.of("in", Integer.class);
    private static final Place<Integer> A = Place.of("a", Integer.class);
    private static final Place<Integer> B = Place.of("b", Integer.class);
    private static final Place<Integer> Q = Place.of("q", Integer.class);
    private static final Place<Integer> R = Place.of("r", Integer.class);
    private static final Place<Integer> DONE = Place.of("done", Integer.class);

    private static final TransitionAction NOOP = ctx -> CompletableFuture.completedFuture(null);

    private static TimePetriNetAnalyzer.XorBranchAnalysis analyzed(PetriNet net) {
        var result = TimePetriNetAnalyzer.forNet(net)
            .initialMarking(m -> m.tokens(IN, 1).tokens(Q, 1))
            .goalPlaces(R, DONE)
            .build()
            .analyze();
        return TimePetriNetAnalyzer.analyzeXorBranches(result.stateClassGraph());
    }

    /**
     * [VER-004]: {@code u} inhibits on {@code t}'s output {@code a}, so the analyzer verifies
     * {@code t} in two steps and its branches are taken by {@code complete:t}. They are reported
     * under {@code t}, and the caller's own {@code t} finds them.
     */
    @Test
    void aSplitXorTransitionReportsItsBranchesUnderItsOwnName() {
        var t = Transition.builder("t").inputs(Arc.In.one(IN))
            .outputs(Arc.Out.xor(Arc.Out.place(A), Arc.Out.place(B))).action(NOOP).build();
        var u = Transition.builder("u").inputs(Arc.In.one(Q)).inhibitors(A)
            .outputs(Arc.Out.place(R)).action(NOOP).build();
        var xor = analyzed(PetriNet.builder("split-xor").transitions(t, u).build());

        assertEquals(List.of("t"), xor.xorTransitions().stream().map(Transition::name).toList());
        var info = xor.branchInfo(t).orElseThrow(() -> new AssertionError("no entry for t: " + xor.report()));
        assertEquals(2, info.totalBranches());
        assertEquals(Set.of(0, 1), info.takenBranches());
        assertFalse(xor.report().contains("complete:"), xor.report());
    }

    /**
     * [EXEC-042]: the terminal rewrite rebuilds every transition, so the graph's {@code t} is not
     * the caller's instance. It is found by name.
     */
    @Test
    void aXorTransitionOfANetWithATerminalIsFoundByName() {
        var t = Transition.builder("t").inputs(Arc.In.one(IN))
            .outputs(Arc.Out.xor(Arc.Out.place(A), Arc.Out.place(B))).action(NOOP).build();
        var w = Transition.builder("w").inputs(Arc.In.one(A))
            .outputs(Arc.Out.place(DONE)).action(NOOP).build();
        var xor = analyzed(PetriNet.builder("terminal-xor").transitions(t, w).terminal(DONE).build());

        var info = xor.branchInfo(t).orElseThrow(() -> new AssertionError("no entry for t: " + xor.report()));
        assertEquals(Set.of(0, 1), info.takenBranches());
    }

    /**
     * The L4 check expects the caller's transitions, and a completion step counts as its
     * transition firing, so the missing list never names {@code complete:t} ([VER-004]).
     */
    @Test
    void l4NamesTheCallersTransitionsOfASplitNet() {
        var t = Transition.builder("t").inputs(Arc.In.one(IN))
            .outputs(Arc.Out.xor(Arc.Out.place(A), Arc.Out.place(B))).action(NOOP).build();
        var u = Transition.builder("u").inputs(Arc.In.one(Q)).inhibitors(A)
            .outputs(Arc.Out.place(R)).action(NOOP).build();
        var result = TimePetriNetAnalyzer.forNet(PetriNet.builder("split-xor").transitions(t, u).build())
            .initialMarking(m -> m.tokens(IN, 1).tokens(Q, 1))
            .goalPlaces(A)
            .build()
            .analyze();
        var missing = result.report().lines().filter(l -> l.contains("Terminal SCC missing transitions")).toList();
        assertFalse(missing.isEmpty(), result.report());
        assertTrue(missing.stream().noneMatch(l -> l.contains("complete:")), result.report());
    }
}
