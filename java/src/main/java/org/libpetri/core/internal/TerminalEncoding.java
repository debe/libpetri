package org.libpetri.core.internal;

import java.util.HashSet;
import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;

/**
 * The verification encoding of a net's terminal places ([EXEC-042], [VER-014]).
 *
 * <p>The runtime ends a run as soon as a terminal place is marked, and no transition fires
 * afterwards. A verifier sees the same behaviour in the net where every terminal place
 * inhibits every transition. This class builds that net; the caller adds each terminal place
 * to its sinks and declares it a conditional-sink marker for every place, which a net cannot
 * say by itself.
 *
 * <p>Internal API: not part of the public contract.
 */
public final class TerminalEncoding {

    private TerminalEncoding() {}

    /**
     * {@code net} with every terminal place inhibiting every transition, and no terminals
     * declared, so applying this twice is the same as applying it once. A net without terminal
     * places is returned as the <b>same instance</b>, so its verification scripts stay
     * byte-identical.
     *
     * <p>Transition order, place order, and each transition's own arcs are kept; the added
     * inhibitors follow the transition's own, in terminal declaration order, and one already
     * present is not repeated.
     */
    public static PetriNet inhibited(PetriNet net) {
        if (net.terminals().isEmpty()) {
            return net;
        }
        var builder = PetriNet.builder(net.name())
            .places(net.places().toArray(new Place<?>[0]));
        for (var t : net.transitions()) {
            builder.transition(withInhibitors(t, net));
        }
        // Terminals are dropped on purpose: the inhibitors now carry them.
        return builder.build();
    }

    private static Transition withInhibitors(Transition t, PetriNet net) {
        var b = Transition.builder(t.name())
            .timing(t.timing())
            .priority(t.priority())
            .action(t.action())
            .placeAlias(t.placeAlias());
        if (!t.inputSpecs().isEmpty()) {
            b.inputs(t.inputSpecs().toArray(new Arc.In[0]));
        }
        if (t.outputSpec() != null) {
            b.outputs(t.outputSpec());
        }
        var inhibited = new HashSet<Place<?>>();
        for (var arc : t.inhibitors()) {
            b.inhibitorArc(arc);
            inhibited.add(arc.place());
        }
        for (var p : net.terminals()) {
            if (inhibited.add(p)) {
                b.inhibitors(p);
            }
        }
        t.reads().forEach(b::readArc);
        t.resets().forEach(b::resetArc);
        if (t.matchSpec() != null) {
            b.match(t.matchSpec());
        }
        return b.build();
    }
}
