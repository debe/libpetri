package org.libpetri.fixtures;

import java.util.concurrent.CompletableFuture;

import org.libpetri.core.PetriNet;
import org.libpetri.core.TransitionAction;

/**
 * Marks a fixture as structure-only: analysed or verified, never executed.
 *
 * <p>[CORE-043] rejects the built-in {@link TransitionAction#passthrough()} on an
 * output-declaring transition at the verification entry points as well as at compile time, so a
 * net built for analysis alone must still carry <em>some</em> action. The stub bound here fails
 * loudly if such a fixture is ever handed to an executor.
 */
public final class StructureOnly {

    private StructureOnly() {}

    /** Never runs — these nets are analysed, not executed. */
    public static final TransitionAction ACTION = ctx -> CompletableFuture.failedFuture(
        new UnsupportedOperationException("structure-only fixture: this net is never executed"));

    /** Rebinds every transition to {@link #ACTION}, leaving the structure untouched. */
    public static PetriNet bind(PetriNet net) {
        return net.bindActions(name -> ACTION);
    }
}
