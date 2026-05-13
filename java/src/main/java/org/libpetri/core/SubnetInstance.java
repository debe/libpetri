package org.libpetri.core;

import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * Lightweight, debug-UI-facing descriptor of one composed subnet instance,
 * per {@code spec/11-modular-composition.md} requirement <b>MOD-041</b>.
 *
 * <p>Created by {@link Instance#descriptor()} after a subnet has been
 * instantiated and (eventually) composed into an enclosing net. The
 * descriptor is consumed by the debug protocol's {@code Subscribed}
 * response so clients can render collapsed subnet clusters, per-instance
 * highlighting, and "show only this instance" filters in the debug UI.
 *
 * <p>This record carries only structural metadata — it is observability-only
 * and does not affect runtime behaviour of the composed flat net.
 *
 * @param prefix the instantiation prefix (e.g. {@code "buf1"} or
 *               {@code "outer/inner"} for nested instances)
 * @param defName the originating subnet definition's name
 * @param transitions full prefixed transition objects belonging to this instance
 * @param exposedPlaces full prefixed place objects exposed as ports
 * @param params the parameter value supplied at instantiation
 *               (use {@link Void} or null when unparameterised)
 * @param parentPrefix the parent instance prefix, when this is a nested instance
 */
public record SubnetInstance(
    String prefix,
    String defName,
    Set<Transition> transitions,
    Set<Place<?>> exposedPlaces,
    Object params,
    Optional<String> parentPrefix
) {
    public SubnetInstance {
        Objects.requireNonNull(prefix, "prefix");
        Objects.requireNonNull(defName, "defName");
        Objects.requireNonNull(parentPrefix, "parentPrefix");
        transitions = Set.copyOf(transitions);
        exposedPlaces = Set.copyOf(exposedPlaces);
    }
}
