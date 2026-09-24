package org.libpetri.export;

import org.libpetri.core.PetriNet;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Analyzes places in a Petri net to determine start/end/environment classification.
 *
 * <p>Provides start/end classification for use in diagram export and debug tooling.
 */
public record PlaceAnalysis(Map<String, Info> data) {

    /**
     * Information about a place in the net.
     *
     * @param tokenType simple name of the token type
     * @param hasIncoming whether the place has incoming arcs
     * @param hasOutgoing whether the place has outgoing arcs
     */
    public record Info(String tokenType, boolean hasIncoming, boolean hasOutgoing) {
        /** Returns true if this place has no incoming arcs (start place). */
        public boolean isStart() { return !hasIncoming; }
        /** Returns true if this place has no outgoing arcs (end place). */
        public boolean isEnd() { return !hasOutgoing; }
    }

    /**
     * Analyzes a Petri net to extract place information.
     *
     * @param net the Petri net to analyze
     * @return the place analysis
     */
    public static PlaceAnalysis from(PetriNet net) {
        record MutableInfo(String tokenType, boolean[] flags) {
            void markIncoming() { flags[0] = true; }
            void markOutgoing() { flags[1] = true; }
            Info toInfo() { return new Info(tokenType, flags[0], flags[1]); }
        }

        var map = new LinkedHashMap<String, MutableInfo>();

        for (var t : net.transitions()) {
            for (var in : t.inputSpecs()) {
                map.computeIfAbsent(in.place().name(),
                    _ -> new MutableInfo(in.place().tokenType().getSimpleName(),
                        new boolean[2])).markOutgoing();
            }
            if (t.outputSpec() != null) {
                for (var place : t.outputSpec().allPlaces()) {
                    map.computeIfAbsent(place.name(),
                        _ -> new MutableInfo(place.tokenType().getSimpleName(),
                            new boolean[2])).markIncoming();
                }
            }
            for (var arc : t.inhibitors()) {
                map.computeIfAbsent(arc.place().name(),
                    _ -> new MutableInfo(arc.place().tokenType().getSimpleName(),
                        new boolean[2]));
            }
            for (var arc : t.reads()) {
                map.computeIfAbsent(arc.place().name(),
                    _ -> new MutableInfo(arc.place().tokenType().getSimpleName(),
                        new boolean[2])).markOutgoing();
            }
            for (var arc : t.resets()) {
                map.computeIfAbsent(arc.place().name(),
                    _ -> new MutableInfo(arc.place().tokenType().getSimpleName(),
                        new boolean[2]));
            }
        }

        return new PlaceAnalysis(map.entrySet().stream()
            .collect(Collectors.toMap(
                Map.Entry::getKey,
                e -> e.getValue().toInfo(),
                (a, b) -> a,
                LinkedHashMap::new)));
    }

    /** Returns sanitized IDs of start places. */
    public List<String> startPlaceIds() {
        return data.entrySet().stream()
            .filter(e -> e.getValue().isStart())
            .map(e -> DotExporter.sanitize(e.getKey()))
            .toList();
    }

    /** Returns sanitized IDs of end places. */
    public List<String> endPlaceIds() {
        return data.entrySet().stream()
            .filter(e -> e.getValue().isEnd())
            .map(e -> DotExporter.sanitize(e.getKey()))
            .toList();
    }

    /**
     * Determines the node category for a place, for a net without terminal places.
     *
     * @param placeName the place name
     * @param environmentPlaces set of environment place names
     * @return category string: "start", "end", "environment", or "place"
     */
    public String category(String placeName, Set<String> environmentPlaces) {
        return category(placeName, environmentPlaces, Set.of());
    }

    /**
     * Determines the node category for a place. A terminal place ([EXEC-042]) takes precedence
     * over every other category, an environment place's included: it is the net's designed end.
     *
     * @param placeName the place name
     * @param environmentPlaces set of environment place names
     * @param terminalPlaces set of terminal place names
     * @return category string: "terminal", "start", "end", "environment", or "place"
     */
    public String category(String placeName, Set<String> environmentPlaces, Set<String> terminalPlaces) {
        if (terminalPlaces.contains(placeName)) return "terminal";
        if (environmentPlaces.contains(placeName)) return "environment";
        var info = data.get(placeName);
        if (info == null) return "place";
        if (info.isStart()) return "start";
        if (info.isEnd()) return "end";
        return "place";
    }
}
