package org.libpetri.examples.parser.compiler;

import org.libpetri.core.Place;
import org.libpetri.core.Transition;

import java.util.List;

/**
 * Intermediate result from compiling a grammar element.
 * Contains the start/end places and all transitions generated.
 */
public record SubNet(
    Place<ParseState> startPlace,
    Place<ParseState> endPlace,
    List<Transition> transitions
) {
    public SubNet {
        if (startPlace == null) throw new IllegalArgumentException("startPlace must not be null");
        if (endPlace == null) throw new IllegalArgumentException("endPlace must not be null");
        transitions = List.copyOf(transitions);
    }
}
