package org.libpetri.analysis;

import org.libpetri.core.PetriNet;
import org.libpetri.core.Transition;

import java.util.Set;
import java.util.stream.Collectors;

/**
 * Every transition of a net, as the declared mints (NU-010) of a test that exercises
 * something other than the mint declaration.
 */
public final class AllMints {

    private AllMints() {}

    /** The name of every transition of {@code net}, for {@code SmtVerifier.mintTransitions}. */
    public static String[] names(PetriNet net) {
        return net.transitions().stream().map(Transition::name).toArray(String[]::new);
    }

    /** The name of every transition of {@code net}. */
    public static Set<String> of(PetriNet net) {
        return net.transitions().stream().map(Transition::name).collect(Collectors.toUnmodifiableSet());
    }
}
