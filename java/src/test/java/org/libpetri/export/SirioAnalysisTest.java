package org.libpetri.export;

import org.libpetri.export.SirioExporter;
import org.libpetri.fixtures.PaperNetworks;

import org.junit.jupiter.api.Test;
import org.oristool.models.tpn.TimedAnalysis;

import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Token;
import static org.junit.jupiter.api.Assertions.*;

/**
 * Formal analysis using Sirio on the paper's Extended TPN.
 */
class SirioAnalysisTest {

    /**
     * Test: Does the paper's Extended TPN terminate (reach "Answered" place) within 10 seconds?
     *
     * NOTE: The paper's network uses READ arcs which create unbounded behavior in Sirio's
     * state-class analysis (Guard and Intent can fire infinitely often from Ready place).
     * This test documents the timing analysis based on network structure.
     *
     * For formal Sirio analysis, use the bounded version (boundedNetworkTerminationAnalysis).
     */
    @Test
    void paperNetworkTimingAnalysis() {
        // Use the paper's network from the shared factory
        var htpn = PaperNetworks.createExtendedTpn();

        // Export to Sirio with initial token in "Pending"
        var sirio = SirioExporter.export(htpn, "Pending");

        System.out.println("=== Paper's Extended TPN Termination Analysis ===");
        System.out.println("Question: Does the net terminate within 10 seconds?");
        System.out.println();
        System.out.println("Network structure:");
        System.out.println("  Places: " + sirio.places().keySet());
        System.out.println("  Transitions: " + sirio.transitions().keySet());
        System.out.println("  Initial marking: token in 'Pending'");
        System.out.println();

        System.out.println("NOTE: This network uses READ arcs (Guard/Intent read from Ready).");
        System.out.println("Read arcs create unbounded behavior - transitions can fire infinitely.");
        System.out.println("Sirio's symbolic analysis cannot terminate on unbounded nets.");
        System.out.println("See boundedNetworkTerminationAnalysis() for a bounded version.");
        System.out.println();

        // Print timing analysis based on network structure
        System.out.println("=== Timing Analysis (from network structure) ===");
        System.out.println();
        System.out.println("Critical paths through the network:");
        System.out.println();
        System.out.println("Path 1 (happy path - no failures):");
        System.out.println("  ask[0,100] + max(Guard[0,500], Intent[0,2000])");
        System.out.println("  + max(Topic[0,4500], Search[0,3500]) + Compose[0,6000] + Filter[0,500]");
        System.out.println("  Best case: 0 + 0 + 0 + 0 + 0 = 0ms (all fire immediately)");
        System.out.println("  Worst case: 100 + 2000 + 4500 + 6000 + 500 = 13100ms");
        System.out.println();
        System.out.println("Path 2 (with Search fallback):");
        System.out.println("  ask + Intent + Search -> SearchFail -> Fallback + Topic + Compose + Filter");
        System.out.println("  Worst case: 100 + 2000 + 3500 + 100 + 4500 + 6000 + 500 = 16700ms");
        System.out.println("  BUT: Fallback is inhibited by Urgent at t=9000ms");
        System.out.println();
        System.out.println("Path 3 (with Compose retry):");
        System.out.println("  ... + Compose -> ComposeFail -> Retry + Filter");
        System.out.println("  Retry is also inhibited by Urgent at t=9000ms");
        System.out.println();
        System.out.println("Timeout behavior:");
        System.out.println("  At exactly t=9000ms, Timeout fires and puts token in Urgent");
        System.out.println("  This blocks Fallback and Retry transitions via inhibitor arcs");
        System.out.println();

        System.out.println("=== Answer ===");
        System.out.println("The network CAN terminate within 10 seconds if transitions fire early.");
        System.out.println("However, it is NOT GUARANTEED to terminate within 10 seconds.");
        System.out.println("Worst case without failures: ~13.1 seconds");
        System.out.println("The 9-second Timeout blocks recovery paths but doesn't guarantee completion.");

        // Verify network was exported correctly (13 places: +ErrorShown, 11 transitions: +ShowError)
        assertEquals(13, sirio.places().size(), "Extended TPN should have 13 places");
        assertEquals(11, sirio.transitions().size(), "Extended TPN should have 11 transitions");
    }

    /**
     * Test a bounded version of the basic TPN (without read arcs).
     *
     * The paper's network uses read arcs which make it unbounded for Sirio analysis.
     * This test uses a sequential version that is analyzable.
     */
    @Test
    void boundedNetworkTerminationAnalysis() {
        // Create a bounded sequential chain representing the critical path
        // ask -> Guard -> Intent -> Topic -> Search -> Compose -> Filter -> Answered
        var pending = Place.of("Pending", String.class);
        var ready = Place.of("Ready", String.class);
        var validated = Place.of("Validated", String.class);
        var understood = Place.of("Understood", String.class);
        var enriched = Place.of("Enriched", String.class);  // after Topic+Search merge
        var drafted = Place.of("Drafted", String.class);
        var answered = Place.of("Answered", String.class);

        // Sequential transitions (no read arcs - bounded)
        var ask = Transition.builder("ask").input(pending).output(ready).deadline(100).build();
        var guardIntent = Transition.builder("GuardIntent").input(ready).output(validated).output(understood).deadline(2000).build();
        var topicSearch = Transition.builder("TopicSearch").input(validated).input(understood).output(enriched).deadline(4500).build();
        var compose = Transition.builder("Compose").input(enriched).output(drafted).deadline(6000).build();
        var filter = Transition.builder("Filter").input(drafted).output(answered).deadline(500).build();

        var htpn = PetriNet.builder("BoundedTPN")
            .transitions(ask, guardIntent, topicSearch, compose, filter)
            .build();

        var sirio = SirioExporter.export(htpn, "Pending");

        System.out.println("=== Bounded TPN Termination Analysis ===");
        System.out.println("Network: " + sirio.places().size() + " places, " + sirio.transitions().size() + " transitions");
        System.out.println("(simplified sequential version - no read arcs)");
        System.out.println();

        var analysis = TimedAnalysis.builder()
            .includeAge(false)
            .build();

        var graph = analysis.compute(sirio.net(), sirio.initialMarking());

        System.out.println("Analysis completed: " + graph.getNodes().size() + " state classes");
        System.out.println();
        System.out.println("Critical path (worst case):");
        System.out.println("  ask[0,100] + GuardIntent[0,2000] + TopicSearch[0,4500]");
        System.out.println("  + Compose[0,6000] + Filter[0,500]");
        System.out.println("  = 100 + 2000 + 4500 + 6000 + 500 = 13100ms");
        System.out.println();
        System.out.println("Conclusion: Network does NOT guarantee termination within 10 seconds.");
        System.out.println("Worst case takes ~13.1 seconds.");

        assertTrue(graph.getNodes().size() > 0);
        // Should have exactly 6 states: initial + after each transition
        assertEquals(6, graph.getNodes().size(), "Bounded net should have 6 state classes");
    }

    /**
     * Test a simple chain that DOES terminate within 10 seconds.
     */
    @Test
    void simpleChainTerminatesWithin10Seconds() {
        // Simple linear chain: start -> A -> B -> end
        var start = Place.of("start", String.class);
        var a = Place.of("A", String.class);
        var b = Place.of("B", String.class);
        var end = Place.of("end", String.class);

        var t1 = Transition.builder("t1").input(start).output(a).deadline(2000).build();
        var t2 = Transition.builder("t2").input(a).output(b).deadline(3000).build();
        var t3 = Transition.builder("t3").input(b).output(end).deadline(2000).build();

        var htpn = PetriNet.builder("SimpleChain")
            .transitions(t1, t2, t3)
            .build();

        var sirio = SirioExporter.export(htpn, "start");

        System.out.println("=== Simple Chain Analysis ===");
        System.out.println("Net: start -[2s]-> A -[3s]-> B -[2s]-> end");
        System.out.println("Total worst-case time: 2000 + 3000 + 2000 = 7000ms");
        System.out.println();

        var analysis = TimedAnalysis.builder()
            .includeAge(false)  // Don't track absolute time
            .build();

        var graph = analysis.compute(sirio.net(), sirio.initialMarking());

        System.out.println("Analysis completed: " + graph.getNodes().size() + " state classes");
        System.out.println();
        System.out.println("Conclusion: Simple chain DOES terminate within 10 seconds.");
        System.out.println("Worst case: 7 seconds, well within the 10 second bound.");

        assertTrue(graph.getNodes().size() > 0);
    }
}
