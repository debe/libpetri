package org.libpetri.examples.parser.compiler;

import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;

import java.util.Map;

/**
 * Result of compiling a grammar into a Petri net.
 * Contains the net plus metadata for driving the parser.
 */
public record CompiledParserNet(
    PetriNet net,
    Place<ParseState> startPlace,
    Place<ParseState> endPlace,
    Place<ParseState> errorPlace,
    Map<String, Place<ParseState>> productionStartPlaces,
    Map<String, Place<ParseState>> productionEndPlaces,
    int placeCount,
    int transitionCount,
    int productionCount
) {
    public CompiledParserNet {
        if (net == null) throw new IllegalArgumentException("net must not be null");
        productionStartPlaces = Map.copyOf(productionStartPlaces);
        productionEndPlaces = Map.copyOf(productionEndPlaces);
    }

    public String statistics() {
        return "CompiledParserNet[places=" + placeCount +
               ", transitions=" + transitionCount +
               ", productions=" + productionCount + "]";
    }
}
