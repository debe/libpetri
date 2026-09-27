package org.libpetri.core;

import java.util.Objects;
import java.util.function.BiFunction;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.smt.SmtVerifier;
import org.libpetri.verification.VerificationHarness;

/**
 * Options for {@link SubnetDef#verify(VerificationHarness, SubnetVerifyOptions)} ([MOD-051]).
 * Start from {@link #DEFAULT} and change what differs:
 *
 * <pre>{@code
 * SubnetVerifyOptions.DEFAULT
 *     .withEnvironmentMode(EnvironmentAnalysisMode.arrivals(2))
 *     .withConfigure((v, synth) -> v.totalBudget(Duration.ofSeconds(30))
 *         .carrierPlaces(Place.of("sut/RELAY", Order.class))
 *         .fragmentMode(FragmentMode.EXTENDED));
 * }</pre>
 *
 * @param environmentMode how injection into the synthetic environment places is modelled
 *                        ([VER-006]); default {@link EnvironmentAnalysisMode#alwaysAvailable()}
 * @param configure       called once per property with the per-property verifier, <b>after</b>
 *                        libpetri's own setup (property, environment places, environment mode),
 *                        and with the synthetic net; returns the verifier to run. It is how a
 *                        caller sets anything the verifier offers: {@code timeout},
 *                        {@code totalBudget} ([VER-013]), sink places, the state-equation and
 *                        enumeration options, and the &nu; options ({@code budgetPlaces},
 *                        {@code carrierPlaces}, {@code fragmentMode}, {@code nuMaxClasses}).
 *                        Resolve places against the synthetic net: the subnet's own places are
 *                        named {@code sut/<place>}, the ports' synthetic places
 *                        {@code harness_in_<port>} / {@code harness_out_<port>} /
 *                        {@code harness_io_<port>}. What it sets overrides libpetri's setup, as
 *                        {@code OpenNetOptions.configureSmt} does ([VER-022]); a hook that
 *                        replaces the environment mode takes responsibility for it. Cancellation
 *                        needs no hook: interrupting the thread that runs {@code verify} cancels
 *                        the running query and every later one ([VER-013]).
 */
public record SubnetVerifyOptions(
    EnvironmentAnalysisMode environmentMode,
    BiFunction<SmtVerifier, PetriNet, SmtVerifier> configure
) {

    /** Every option at its default: {@code alwaysAvailable()}, no hook. */
    public static final SubnetVerifyOptions DEFAULT =
        new SubnetVerifyOptions(EnvironmentAnalysisMode.alwaysAvailable(), (v, _) -> v);

    public SubnetVerifyOptions {
        Objects.requireNonNull(environmentMode, "environmentMode");
        Objects.requireNonNull(configure, "configure");
    }

    /** The same options with another environment mode. */
    public SubnetVerifyOptions withEnvironmentMode(EnvironmentAnalysisMode other) {
        return new SubnetVerifyOptions(other, configure);
    }

    /** The same options configuring each per-property verifier with {@code other}. */
    public SubnetVerifyOptions withConfigure(BiFunction<SmtVerifier, PetriNet, SmtVerifier> other) {
        return new SubnetVerifyOptions(environmentMode, other);
    }
}
