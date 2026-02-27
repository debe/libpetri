package org.libpetri.export;

import org.oristool.models.pn.Priority;
import org.oristool.models.stpn.trees.StochasticTransitionFeature;
import org.oristool.petrinet.Marking;
import org.oristool.petrinet.Place;

import org.libpetri.core.PetriNet;

import java.util.HashMap;
import java.util.Map;

/**
 * Exports CTPN models to Sirio's PetriNet format for formal analysis.
 *
 * <p><a href="https://github.com/oris-tool/sirio">Sirio</a> (also known as ORIS)
 * is an academic tool for formal analysis of Time Petri Nets. This exporter
 * converts CTPN models to Sirio's object model for programmatic analysis.
 *
 * <h2>Sirio Capabilities</h2>
 * <ul>
 *   <li>State space exploration and reachability analysis</li>
 *   <li>Timing analysis (transient analysis with time bounds)</li>
 *   <li>Stochastic analysis with various distributions</li>
 *   <li>Deadlock and liveness detection</li>
 * </ul>
 *
 * <h2>Mapping Rules</h2>
 * <table border="1">
 *   <caption>CTPN to Sirio mapping</caption>
 *   <tr><th>CTPN Element</th><th>Sirio Element</th></tr>
 *   <tr><td>Place</td><td>Place (untyped - Sirio ignores token types)</td></tr>
 *   <tr><td>Input arc</td><td>Precondition</td></tr>
 *   <tr><td>Output arc</td><td>Postcondition</td></tr>
 *   <tr><td>Read arc</td><td>Precondition + Postcondition (test arc)</td></tr>
 *   <tr><td>Inhibitor arc</td><td>Inhibitor arc</td></tr>
 *   <tr><td>Firing interval [a, b]</td><td>Uniform distribution [a, b] or deterministic</td></tr>
 *   <tr><td>Priority</td><td>Priority feature</td></tr>
 * </table>
 *
 * <h2>Limitations</h2>
 * <ul>
 *   <li>Token types are ignored (Sirio uses untyped tokens)</li>
 *   <li>Guards on input arcs are ignored (Sirio has no equivalent)</li>
 *   <li>Reset arcs are not supported by Sirio</li>
 * </ul>
 *
 * <h2>Usage Example</h2>
 * <pre>{@code
 * // Export and analyze
 * var sirio = SirioExporter.export(net, "StartPlace");
 *
 * // Run timing analysis
 * var analysis = TimedAnalysis.builder()
 *     .includeAge(false)
 *     .build();
 * var graph = analysis.compute(sirio.net(), sirio.initialMarking());
 *
 * // Check reachability
 * var reachable = graph.getNodes().stream()
 *     .anyMatch(n -> n.getState().getTokens("EndPlace") > 0);
 * }</pre>
 *
 * @see <a href="https://github.com/oris-tool/sirio">Sirio GitHub</a>
 */
public final class SirioExporter {

    private SirioExporter() {}

    /**
     * Result of exporting a CTPN to Sirio format.
     *
     * @param net the Sirio Petri net
     * @param initialMarking initial marking (may be empty)
     * @param places map of place names to Sirio Place objects
     * @param transitions map of transition names to Sirio Transition objects
     */
    public record SirioNet(
        org.oristool.petrinet.PetriNet net,
        Marking initialMarking,
        Map<String, Place> places,
        Map<String, org.oristool.petrinet.Transition> transitions
    ) {}

    /**
     * Exports a CTPN to Sirio format with empty initial marking.
     *
     * <p>Use {@link #export(PetriNet, String)} to set initial tokens.
     *
     * @param ctpn the CTPN to export
     * @return Sirio net with empty marking
     */
    public static SirioNet export(PetriNet ctpn) {
        var sirioNet = new org.oristool.petrinet.PetriNet();
        var places = new HashMap<String, Place>();
        var transitions = new HashMap<String, org.oristool.petrinet.Transition>();

        // Collect all places from arcs (using merged accessors for old/new API compatibility)
        for (var t : ctpn.transitions()) {
            for (var place : t.inputPlaces()) {
                places.computeIfAbsent(place.name(), sirioNet::addPlace);
            }
            for (var place : t.outputPlaces()) {
                places.computeIfAbsent(place.name(), sirioNet::addPlace);
            }
            for (var arc : t.inhibitors()) {
                places.computeIfAbsent(arc.place().name(), sirioNet::addPlace);
            }
            for (var arc : t.reads()) {
                places.computeIfAbsent(arc.place().name(), sirioNet::addPlace);
            }
        }

        // Create transitions with timing
        for (var t : ctpn.transitions()) {
            var sirioTrans = sirioNet.addTransition(t.name());
            transitions.put(t.name(), sirioTrans);

            // Add time interval as uniform distribution [earliest, deadline]
            var interval = t.interval();
            var earliest = interval.earliest().toMillis();
            var latest = interval.hasFiniteDeadline()
                ? interval.deadline().toMillis()
                : Long.MAX_VALUE;

            // Sirio's uniform requires earliest < latest
            if (earliest == latest) {
                // Use deterministic timing for exact intervals
                sirioTrans.addFeature(StochasticTransitionFeature
                    .newDeterministicInstance(String.valueOf(earliest)));
            } else {
                sirioTrans.addFeature(StochasticTransitionFeature
                    .newUniformInstance(String.valueOf(earliest), String.valueOf(latest)));
            }

            // Add priority if set
            if (t.priority() != 0) {
                sirioTrans.addFeature(new Priority(t.priority()));
            }
        }

        // Create arcs (using merged accessors for old/new API compatibility)
        for (var t : ctpn.transitions()) {
            var sirioTrans = transitions.get(t.name());

            // Input arcs (preconditions) - using inputPlaces() which merges old/new APIs
            for (var inputPlace : t.inputPlaces()) {
                var place = places.get(inputPlace.name());
                sirioNet.addPrecondition(place, sirioTrans);
            }

            // Output arcs (postconditions) - using outputPlaces() which merges old/new APIs
            for (var outputPlace : t.outputPlaces()) {
                var place = places.get(outputPlace.name());
                sirioNet.addPostcondition(sirioTrans, place);
            }

            // Inhibitor arcs
            for (var arc : t.inhibitors()) {
                var place = places.get(arc.place().name());
                sirioNet.addInhibitorArc(place, sirioTrans);
            }

            // Read arcs (test arcs = precondition + postcondition)
            for (var arc : t.reads()) {
                var place = places.get(arc.place().name());
                sirioNet.addPrecondition(place, sirioTrans);
                sirioNet.addPostcondition(sirioTrans, place);
            }
        }

        return new SirioNet(sirioNet, new Marking(), places, transitions);
    }

    /**
     * Exports a CTPN to Sirio format with one token in the start place.
     *
     * @param ctpn the CTPN to export
     * @param startPlace name of the place to receive initial token
     * @return Sirio net with initial token
     */
    public static SirioNet export(PetriNet ctpn, String startPlace) {
        var result = export(ctpn);
        var place = result.places.get(startPlace);
        if (place != null) {
            result.initialMarking.addTokens(place, 1);
        }
        return result;
    }

    /**
     * Exports a CTPN to Sirio format with custom initial marking.
     *
     * @param ctpn the CTPN to export
     * @param initialTokens map of place names to token counts
     * @return Sirio net with specified initial marking
     */
    public static SirioNet export(PetriNet ctpn, Map<String, Integer> initialTokens) {
        var result = export(ctpn);
        initialTokens.forEach((placeName, count) -> {
            var place = result.places.get(placeName);
            if (place != null && count > 0) {
                result.initialMarking.addTokens(place, count);
            }
        });
        return result;
    }
}
