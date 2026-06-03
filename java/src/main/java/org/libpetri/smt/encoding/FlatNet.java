package org.libpetri.smt.encoding;

import org.libpetri.core.Place;

import java.util.List;
import java.util.Map;

/**
 * A flattened Petri net with indexed places and XOR-expanded transitions.
 *
 * <p>This is the intermediate representation between the high-level
 * {@link org.libpetri.core.PetriNet} and the Z3 CHC encoding.
 *
 * @param places            ordered list of places (index = position)
 * @param placeIndex        reverse lookup: place -> index
 * @param transitions       XOR-expanded flat transitions
 * @param environmentBounds for bounded environment places: place -> max tokens (null = regular)
 * @param environmentInjection environment places whose tokens the analysis MODELS as
 *     externally injected (VER-006): place -> injection bound, where a {@code null} value
 *     means unbounded ({@code AlwaysAvailable}) and an integer caps injection
 *     ({@code Bounded(k)}). Absent entries (incl. {@code Ignore} mode) are not injected.
 *     The encoder emits one injection CHC rule per entry and the incidence matrix gains
 *     one injector column per entry so closed-net P-invariants over these places are
 *     correctly discarded.
 */
public record FlatNet(
    List<Place<?>> places,
    Map<Place<?>, Integer> placeIndex,
    List<FlatTransition> transitions,
    Map<Place<?>, Integer> environmentBounds,
    Map<Place<?>, Integer> environmentInjection
) {
    /**
     * Number of places in the net.
     */
    public int placeCount() {
        return places.size();
    }

    /**
     * Number of (expanded) transitions in the net.
     */
    public int transitionCount() {
        return transitions.size();
    }

    /**
     * Returns the index of a place, or -1 if not found.
     */
    public int indexOf(Place<?> place) {
        return placeIndex.getOrDefault(place, -1);
    }
}
