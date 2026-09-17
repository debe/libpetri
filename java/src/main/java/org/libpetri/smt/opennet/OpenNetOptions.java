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
 */
public record OpenNetOptions(
    int maxClasses,
    boolean smt,
    UnaryOperator<SmtVerifier> configureSmt,
    Duration terminationTimeout
) {

    /** The state-class graph's default class budget, as for [VER-017]. */
    public static final int DEFAULT_MAX_CLASSES = 50_000;

    /** The firing-bound query's default time on the SMT route. */
    public static final Duration DEFAULT_TERMINATION_TIMEOUT = Duration.ofSeconds(60);

    /** Every option at its default. */
    public static final OpenNetOptions DEFAULT = new OpenNetOptions(
        DEFAULT_MAX_CLASSES, true, UnaryOperator.identity(), DEFAULT_TERMINATION_TIMEOUT);

    public OpenNetOptions {
        Objects.requireNonNull(configureSmt, "configureSmt");
        Objects.requireNonNull(terminationTimeout, "terminationTimeout");
    }

    /** The same options with another class budget; {@code 0} skips the graph. */
    public OpenNetOptions withMaxClasses(int other) {
        return new OpenNetOptions(other, smt, configureSmt, terminationTimeout);
    }

    /** The same options with the SMT route enabled or disabled. */
    public OpenNetOptions withSmt(boolean other) {
        return new OpenNetOptions(maxClasses, other, configureSmt, terminationTimeout);
    }

    /** The same options configuring each {@link SmtVerifier} with {@code other}. */
    public OpenNetOptions withConfigureSmt(UnaryOperator<SmtVerifier> other) {
        return new OpenNetOptions(maxClasses, smt, other, terminationTimeout);
    }

    /** The same options with another time for the firing-bound query. */
    public OpenNetOptions withTerminationTimeout(Duration other) {
        return new OpenNetOptions(maxClasses, smt, configureSmt, other);
    }
}
