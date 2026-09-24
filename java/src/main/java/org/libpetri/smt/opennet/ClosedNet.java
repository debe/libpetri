package org.libpetri.smt.opennet;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * An open net and its environment, as one closed net ([VER-022]). Built by
 * {@link OpenNetClosure#closeOpenNet}.
 */
public final class ClosedNet {

    private final PetriNet net;
    private final MarkingState initialMarking;
    private final Map<String, EnvironmentStep> environment;
    private final List<Place<?>> environmentPlaces;
    private final List<String> undeclared;
    /**
     * Every place of the closed net that a contract may name, by name: the net's own first,
     * then the environment's, then the contract's undeclared ones. The TypeScript reference
     * keys its markings and flat nets by name, Java keys them by {@link Place} equality (name
     * and token type), so the routes resolve every place the contract names through this map
     * rather than through equality ({@link #canonical}).
     */
    private final Map<String, Place<?>> placesByName;

    ClosedNet(
            PetriNet net,
            MarkingState initialMarking,
            Map<String, EnvironmentStep> environment,
            List<Place<?>> environmentPlaces,
            List<String> undeclared,
            Map<String, Place<?>> placesByName
    ) {
        this.net = net;
        this.initialMarking = initialMarking;
        this.environment = Collections.unmodifiableMap(new LinkedHashMap<>(environment));
        this.environmentPlaces = List.copyOf(environmentPlaces);
        this.undeclared = List.copyOf(undeclared);
        this.placesByName = Map.copyOf(placesByName);
    }

    /** This closure with {@code replacement} as its net; every place map stays as it is. */
    ClosedNet withNet(PetriNet replacement) {
        return new ClosedNet(replacement, initialMarking, environment, environmentPlaces, undeclared, placesByName);
    }

    /** The closed net: the subnet, the contract's environment transitions and the arrival groups' structure. */
    public PetriNet net() {
        return net;
    }

    /** The contract's initial marking plus each arrival group's sources. */
    public MarkingState initialMarking() {
        return initialMarking;
    }

    /**
     * Each environment transition by name, with what it does: the contract's own first, then
     * each arrival group's, in the order the closure added them.
     */
    public Map<String, EnvironmentStep> environment() {
        return environment;
    }

    /**
     * Places only the contract's environment transitions touch: the environment's own state.
     * A token left on one at quiescence is never stranded.
     */
    public List<Place<?>> environmentPlaces() {
        return environmentPlaces;
    }

    /**
     * Places the contract names that no arc touches, in contract order. They join the closed
     * net as places of their own, so every route resolves them. A clause over a place nothing
     * writes then counts zero there, which is the finding, not an error.
     */
    public List<String> undeclared() {
        return undeclared;
    }

    /** The closed net's place named like {@code place}, or {@code place} itself when none is. */
    Place<?> canonical(Place<?> place) {
        return placesByName.getOrDefault(place.name(), place);
    }

    /** {@link #canonical(Place)} of each place, in order. */
    List<Place<?>> canonical(Collection<? extends Place<?>> places) {
        var out = new ArrayList<Place<?>>(places.size());
        for (var p : places) {
            out.add(canonical(p));
        }
        return out;
    }
}
