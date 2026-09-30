package org.libpetri.smt.opennet;

import org.libpetri.smt.SmtVerifier;

import java.time.Duration;
import java.util.Objects;
import java.util.function.UnaryOperator;

/**
 * Options for {@link OpenNetVerifier#verifyOpenNet} ([VER-022]). Start from {@link #DEFAULT}
 * and change what differs:
 *
 * <pre>{@code
 * OpenNetOptions.DEFAULT
 *     .withMaxClasses(0)                                             // skip the graph
 *     .withConfigureSmt(v -> v.timeout(Duration.ofSeconds(120)).stateEquation(true));
 * }</pre>
 *
 * @param maxClasses         class budget for the state-class graph (default 50 000, as for
 *                           [VER-017]); {@code 0} or less skips the graph
 * @param smt                whether to ask the SMT pipeline when the graph does not close
 *                           (default {@code true})
 * @param configureSmt       configures each {@link SmtVerifier} the SMT route builds (default:
 *                           unchanged)
 * @param terminationTimeout time for each firing-bound query that decides termination on the
 *                           SMT route (default 60 s)
 * @param assumeNoReaping    reads quiescence strictly, as if no {@code deadline} / {@code window}
 *                           transition were ever reaped ([TIME-013]; default {@code false}). By
 *                           default a marking where every enabled transition is reapable counts
 *                           as quiescent on both routes, as {@link SmtVerifier#assumeNoReaping}
 *                           describes; with {@code true} the report of a net with such a
 *                           transition says the verdict assumes none is reaped
 * @param assumeAtomicFiring reads every firing as one atomic step ([VER-004]; default
 *                           {@code false}). By default a transition whose output some transition
 *                           tests with an inhibitor, reset or drain, or that marks a terminal
 *                           place ([EXEC-042]), is verified as a start and a completion step on
 *                           both routes, as {@link SmtVerifier#assumeAtomicFiring} describes; the
 *                           environment's own steps stay atomic. With {@code true} the report of
 *                           a net with such a transition says the verdict assumes atomic firings
 */
public record OpenNetOptions(
    int maxClasses,
    boolean smt,
    UnaryOperator<SmtVerifier> configureSmt,
    Duration terminationTimeout,
    boolean assumeNoReaping,
    boolean assumeAtomicFiring
) {

    /** The state-class graph's default class budget, as for [VER-017]. */
    public static final int DEFAULT_MAX_CLASSES = 50_000;

    /** The firing-bound query's default time on the SMT route. */
    public static final Duration DEFAULT_TERMINATION_TIMEOUT = Duration.ofSeconds(60);

    /** Every option at its default. */
    public static final OpenNetOptions DEFAULT = new OpenNetOptions(
        DEFAULT_MAX_CLASSES, true, UnaryOperator.identity(), DEFAULT_TERMINATION_TIMEOUT, false, false);

    public OpenNetOptions {
        Objects.requireNonNull(configureSmt, "configureSmt");
        Objects.requireNonNull(terminationTimeout, "terminationTimeout");
    }

    /**
     * The options before [TIME-013]'s {@code assumeNoReaping} and [VER-004]'s
     * {@code assumeAtomicFiring}, which this leaves {@code false} both.
     */
    public OpenNetOptions(
            int maxClasses, boolean smt, UnaryOperator<SmtVerifier> configureSmt, Duration terminationTimeout) {
        this(maxClasses, smt, configureSmt, terminationTimeout, false, false);
    }

    /** The options before [VER-004]'s {@code assumeAtomicFiring}, which this leaves {@code false}. */
    public OpenNetOptions(
            int maxClasses, boolean smt, UnaryOperator<SmtVerifier> configureSmt, Duration terminationTimeout,
            boolean assumeNoReaping) {
        this(maxClasses, smt, configureSmt, terminationTimeout, assumeNoReaping, false);
    }

    /** The same options with another class budget; {@code 0} skips the graph. */
    public OpenNetOptions withMaxClasses(int other) {
        return new OpenNetOptions(other, smt, configureSmt, terminationTimeout, assumeNoReaping, assumeAtomicFiring);
    }

    /** The same options with the SMT route enabled or disabled. */
    public OpenNetOptions withSmt(boolean other) {
        return new OpenNetOptions(maxClasses, other, configureSmt, terminationTimeout, assumeNoReaping, assumeAtomicFiring);
    }

    /** The same options configuring each {@link SmtVerifier} with {@code other}. */
    public OpenNetOptions withConfigureSmt(UnaryOperator<SmtVerifier> other) {
        return new OpenNetOptions(maxClasses, smt, other, terminationTimeout, assumeNoReaping, assumeAtomicFiring);
    }

    /** The same options with another time for the firing-bound query. */
    public OpenNetOptions withTerminationTimeout(Duration other) {
        return new OpenNetOptions(maxClasses, smt, configureSmt, other, assumeNoReaping, assumeAtomicFiring);
    }

    /** The same options reading every firing as one step, or splitting in-flight actions ([VER-004]). */
    public OpenNetOptions withAssumeAtomicFiring(boolean other) {
        return new OpenNetOptions(maxClasses, smt, configureSmt, terminationTimeout, assumeNoReaping, other);
    }

    /** The same options reading quiescence strictly, or reap-aware ([TIME-013]). */
    public OpenNetOptions withAssumeNoReaping(boolean other) {
        return new OpenNetOptions(maxClasses, smt, configureSmt, terminationTimeout, other, assumeAtomicFiring);
    }
}
