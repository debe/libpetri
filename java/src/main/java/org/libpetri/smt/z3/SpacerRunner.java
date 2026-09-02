package org.libpetri.smt.z3;

import java.time.Duration;
import java.util.List;

/**
 * Runs Z3 Spacer on a HORN script through one {@code z3} process (VER-013) and
 * classifies the reply in verdict terms.
 *
 * <p>HORN/Spacer convention (shared with the Rust and TypeScript verifiers and
 * corroborated by the certificate check): with the query {@code (assert (not Error))},
 * z3 prints {@code sat} when the property is PROVEN (an inductive invariant excluding
 * every violating state exists) and {@code unsat} when it is VIOLATED (no such
 * invariant; the refutation proof carries the counterexample states).
 */
public final class SpacerRunner {

    private SpacerRunner() {}

    /** Result of a Spacer query. */
    public sealed interface QueryResult {
        /**
         * Property proven (z3 {@code sat}).
         *
         * @param invariantFormula the {@code (define-fun …)} block of the model, verbatim
         *                         (the certificate the {@link CertificateChecker}
         *                         re-validates), or {@code null} when no model printed
         */
        record Proven(String invariantFormula) implements QueryResult {}

        /**
         * Property violated (z3 {@code unsat}).
         *
         * @param answer the raw solver reply; the refutation proof in it is decoded by
         *               {@link CounterexampleDecoder}
         */
        record Violated(String answer) implements QueryResult {}

        /** Solver could not determine (timeout, resource limit, transport failure). */
        record Unknown(String reason) implements QueryResult {}
    }

    /**
     * Runs {@code smt2} with {@code fp.engine=spacer}. {@code phase} names the dump
     * files ({@code horn} or {@code horn-coloured}).
     */
    public static QueryResult run(Z3Solver solver, Duration timeout, String smt2, String phase) {
        Z3Process.Reply reply;
        try {
            reply = solver.run(smt2, phase, timeout, List.of("fp.engine=spacer"));
        } catch (Z3Process.Z3ProcessException e) {
            return new QueryResult.Unknown(e.getMessage());
        }
        String stdout = reply.stdout().strip();

        // The verdict is a LINE anywhere in the reply, never its first bytes: the
        // script asks for both (get-proof) and (get-model), one of which answers
        // `(error …)` on either branch, and a build is free to print a warning first.
        String verdict = SmtText.classifyFirstLine(stdout);
        if (verdict == null) {
            // No verdict at all: the `-T` backstop, the watchdog, an `(error …)` on
            // either stream, in that order (VER-013).
            return new QueryResult.Unknown(
                Z3Process.failureReason(reply, Z3Solver.timeoutMs(timeout)));
        }
        return switch (verdict) {
            // unsat => no inductive invariant excludes the bad state => VIOLATED.
            case "unsat" -> new QueryResult.Violated(stdout);
            // sat => an inductive invariant exists => PROVEN.
            case "sat" -> new QueryResult.Proven(SmtText.extractInvariant(stdout));
            default -> new QueryResult.Unknown("Z3 answered unknown");
        };
    }
}
