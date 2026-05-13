package org.libpetri.verification;

import org.libpetri.core.Token;
import org.libpetri.smt.SmtProperty;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Supplier;

/**
 * Harness driving local property verification of a subnet definition per
 * {@code spec/11-modular-composition.md} requirement <b>MOD-051</b>.
 *
 * <p>The harness is a value carrier consumed by
 * {@link org.libpetri.core.SubnetDef#verify(VerificationHarness)}. It supplies
 * the three pieces of information needed to wrap a subnet in a synthetic
 * enclosing net for verification:
 *
 * <ol>
 *   <li>A {@link #params()} value of the subnet's parameter type.</li>
 *   <li>A {@link #portInputGenerators()} map from <b>input port name</b>
 *       (original / pre-prefix) to a token-source supplier. The supplier's
 *       presence is what bounds the input behavior in the synthetic harness;
 *       the supplier is invoked at synthetic-net construction time when the
 *       harness wires up the {@link org.libpetri.core.EnvironmentPlace}
 *       associated with the port. The static SMT verifier ({@link
 *       org.libpetri.smt.SmtVerifier}) consumes the resulting environment
 *       place declaration via the over-approximating environment-analysis
 *       mode; the supplier is structurally part of the harness for parity
 *       with the runtime / state-class graph story.</li>
 *   <li>A set of {@link #properties()} to check (per [VER-002] / {@link
 *       SmtProperty}).</li>
 * </ol>
 *
 * <p>Each entry in {@link #portInputGenerators()} MUST correspond to an
 * input or in-out port declared on the subnet's interface. Output-only ports
 * never appear in the generator map; instead, the harness wires them to a
 * synthetic observation place visible to the verifier.
 *
 * <h2>Identity</h2>
 * Records do defensive copies of the supplied {@code Map} and {@code Set}
 * via the compact constructor; the harness is structurally immutable.
 *
 * @param <P> parameter type carried through to the subnet under test
 * @param params parameter value supplied to
 *               {@link org.libpetri.core.SubnetDef#instantiate(String, Object)}
 *               for the system-under-test instance (may be {@code null}
 *               when {@code P} is {@link Void})
 * @param portInputGenerators map from input-port name to a token supplier
 *                            used to seed the synthetic environment place
 *                            for that port. Must not contain {@code null}
 *                            keys or values.
 * @param properties safety properties to check on the synthetic enclosing
 *                   net; an empty set is permitted but yields an empty
 *                   {@link VerificationResult#perProperty()}.
 */
public record VerificationHarness<P>(
    P params,
    Map<String, Supplier<Token<?>>> portInputGenerators,
    Set<SmtProperty> properties
) {

    public VerificationHarness {
        Objects.requireNonNull(portInputGenerators, "portInputGenerators");
        Objects.requireNonNull(properties, "properties");
        // Defensive copies — preserve insertion order for deterministic
        // iteration in verify(...) since SMT verification cost is sensitive
        // to property ordering.
        portInputGenerators = Map.copyOf(new LinkedHashMap<>(portInputGenerators));
        properties = Set.copyOf(new LinkedHashSet<>(properties));
    }

    /**
     * Convenience builder for harnesses with insertion-ordered generators
     * and properties. Mirrors the broader {@code SubnetDef.Builder} ergonomics.
     */
    public static <P> Builder<P> builder(P params) {
        return new Builder<>(params);
    }

    /** Convenience builder for unparameterised harnesses ({@code P = Void}). */
    public static Builder<Void> builder() {
        return new Builder<>(null);
    }

    public static final class Builder<P> {
        private final P params;
        private final LinkedHashMap<String, Supplier<Token<?>>> portInputGenerators = new LinkedHashMap<>();
        private final LinkedHashSet<SmtProperty> properties = new LinkedHashSet<>();

        private Builder(P params) {
            this.params = params;
        }

        public Builder<P> input(String portName, Supplier<Token<?>> generator) {
            Objects.requireNonNull(portName, "portName");
            Objects.requireNonNull(generator, "generator");
            portInputGenerators.put(portName, generator);
            return this;
        }

        public Builder<P> property(SmtProperty property) {
            Objects.requireNonNull(property, "property");
            properties.add(property);
            return this;
        }

        public VerificationHarness<P> build() {
            return new VerificationHarness<>(params, portInputGenerators, properties);
        }
    }
}
