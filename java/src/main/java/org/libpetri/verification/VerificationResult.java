package org.libpetri.verification;

import org.libpetri.core.PetriNet;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.SmtVerificationResult;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;

/**
 * Aggregated outcome of a {@link org.libpetri.core.SubnetDef#verify(VerificationHarness)}
 * invocation per {@code spec/11-modular-composition.md} requirement
 * <b>MOD-051</b>.
 *
 * <p>The verifier is invoked once per {@link SmtProperty} declared in the
 * harness; each invocation produces an {@link SmtVerificationResult}. This
 * record carries the per-property results plus the synthetic enclosing net
 * that was constructed for verification (useful for diagnostic output and
 * tooling to render the harness wiring).
 *
 * @param syntheticNet the synthetic enclosing net assembled by
 *                     {@code SubnetDef.verify(...)}: the renamed body of
 *                     the subnet under test, with each input port bound to
 *                     a synthetic environment place and each output port
 *                     bound to a synthetic observation place.
 * @param perProperty  per-property verification results, in the iteration
 *                     order of the harness's
 *                     {@link VerificationHarness#properties() property set}.
 */
public record VerificationResult(
    PetriNet syntheticNet,
    Map<SmtProperty, SmtVerificationResult> perProperty
) {

    public VerificationResult {
        Objects.requireNonNull(syntheticNet, "syntheticNet");
        Objects.requireNonNull(perProperty, "perProperty");
        // Preserve insertion order for deterministic per-property iteration.
        perProperty = Map.copyOf(new LinkedHashMap<>(perProperty));
    }

    /**
     * Returns true when every property in the harness was proven safe.
     * An empty harness (no properties) returns {@code true} vacuously.
     */
    public boolean allProven() {
        for (var r : perProperty.values()) {
            if (!r.isProven()) return false;
        }
        return true;
    }

    /**
     * Returns true when at least one property was violated (counter-example
     * found).
     */
    public boolean anyViolated() {
        for (var r : perProperty.values()) {
            if (r.isViolated()) return true;
        }
        return false;
    }
}
