package org.libpetri.analysis;

import org.libpetri.core.Place;
import org.libpetri.core.Transition;

import java.util.Collection;
import java.util.StringJoiner;

/**
 * Shared utility methods for Petri net analysis.
 * <p>
 * This class provides common formatting and helper methods used by both
 * {@link StateSpaceAnalyzer} and {@link TimePetriNetAnalyzer}.
 */
final class AnalysisUtils {

    private AnalysisUtils() {}

    /**
     * Formats a collection of places as a bracketed, comma-separated list.
     *
     * @param places the places to format
     * @return formatted string like "[P1, P2, P3]"
     */
    static String formatPlaces(Collection<Place<?>> places) {
        var joiner = new StringJoiner(", ", "[", "]");
        for (var place : places) {
            joiner.add(place.name());
        }
        return joiner.toString();
    }

    /**
     * Formats a collection of transitions as a bracketed, comma-separated list.
     *
     * @param transitions the transitions to format
     * @return formatted string like "[T1, T2, T3]"
     */
    static String formatTransitions(Collection<Transition> transitions) {
        var joiner = new StringJoiner(", ", "[", "]");
        for (var t : transitions) {
            joiner.add(t.name());
        }
        return joiner.toString();
    }
}
