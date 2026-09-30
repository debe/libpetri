package org.libpetri.smt.opennet;

import java.util.Objects;
import java.util.Set;

/**
 * What the SMT route of {@link OpenNetVerifier#verifyOpenNet} tells each
 * {@link org.libpetri.smt.SmtVerifier} it runs on the closed net's untimed copy ([VER-022]):
 * which transitions model the environment, so the in-flight split leaves them atomic
 * ([VER-004]), and which transitions of the timed net are reapable, a fact the untimed copy
 * no longer carries ([TIME-013]).
 *
 * <p>Only this package can make one, so no other caller can hand a verifier either list. Naming
 * a transition an environment step exempts it from the split, and naming the reapable set
 * replaces the one read off the net, so both would otherwise let a caller switch off a
 * soundness rewrite without the report saying so. Use {@link OpenNetOptions#assumeAtomicFiring}
 * and {@link OpenNetOptions#assumeNoReaping} to state those assumptions instead.
 */
public final class ClosedNetSteps {

    private final Set<String> environment;
    private final Set<String> reapable;

    ClosedNetSteps(Set<String> environment, Set<String> reapable) {
        this.environment = Set.copyOf(Objects.requireNonNull(environment));
        this.reapable = Set.copyOf(Objects.requireNonNull(reapable));
    }

    /** The transitions modelling the environment of the closed net; the split leaves them atomic. */
    public Set<String> environment() {
        return environment;
    }

    /** The reapable transitions of the timed closed net, before its timing was dropped. */
    public Set<String> reapable() {
        return reapable;
    }
}
