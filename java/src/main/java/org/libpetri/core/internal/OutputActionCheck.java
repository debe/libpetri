package org.libpetri.core.internal;

import org.libpetri.core.PetriNet;
import org.libpetri.core.Transition;
import org.libpetri.core.TransitionAction;

/**
 * CORE-043 reconciliation of declared structure against bound behaviour, shared by the
 * execution and verification entry points.
 */
public final class OutputActionCheck {

    private OutputActionCheck() {}

    /**
     * Rejects any transition that declares an output spec while carrying the built-in
     * {@link TransitionAction#passthrough()} — passthrough produces no tokens, so every firing
     * would fail output validation (IO-015) and the declared output would never arrive.
     *
     * @param net the net about to be compiled or verified
     * @throws IllegalStateException on the first such transition, naming it
     */
    public static void requireOutputProducingActions(PetriNet net) {
        for (var t : net.transitions()) {
            requireOutputProducingAction(t);
        }
    }

    /** Single-transition form of {@link #requireOutputProducingActions(PetriNet)}. */
    public static void requireOutputProducingAction(Transition t) {
        if (t.outputSpec() != null && TransitionAction.isPassthrough(t.action())) {
            throw new IllegalStateException(
                ("Transition '%s' declares an output spec but carries passthrough(), which "
                    + "produces no tokens. Every firing would fail output validation (IO-015) and "
                    + "the declared output would never arrive. Bind an action that produces it — "
                    + "TransitionAction.fork() moves the input token across — or drop the output "
                    + "spec if the transition is meant to be a sink.").formatted(t.name()));
        }
    }
}
