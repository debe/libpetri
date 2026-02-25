package org.libpetri.analysis;

import org.libpetri.core.Transition;
import org.libpetri.fixtures.PaperNetworks;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

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
                net,
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
}
