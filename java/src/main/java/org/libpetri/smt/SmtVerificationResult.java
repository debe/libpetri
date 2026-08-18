package org.libpetri.smt;

import org.libpetri.analysis.MarkingState;
import org.libpetri.smt.invariant.PInvariant;

import java.time.Duration;
import java.util.List;

/**
 * Result of SMT-based verification.
 *
 * @param verdict                  proven, violated, or unknown
 * @param report                   human-readable analysis report
 * @param invariants               P-invariants found during analysis
 * @param discoveredInvariants     IC3-synthesized inductive invariants (empty if not proven by IC3)
 * @param counterexampleTrace      marking trace to error (empty if proven)
 * @param counterexampleTransitions firing sequence to error (empty if proven)
 * @param counterexampleConfirmed  outcome of the abstract counterexample replay
 *     ({@link org.libpetri.smt.z3.AbstractReplayer}), as a TRI-STATE. The
 *     canonical definition lives on the Rust {@code VerificationResult}; this
 *     restates it:
 *     <ul>
 *       <li>{@code TRUE} — the replay chained an abstract firing run from M0 to a
 *           property-violating marking; {@code counterexampleTrace} is that run,
 *           in firing order.</li>
 *       <li>{@code FALSE} — the replay applied and did NOT confirm the
 *           counterexample. Two shapes, reported the same way:
 *           <ul>
 *             <li>it could not conclude (nothing decodable, M0 not among the
 *                 decoded states, or a budget exhausted) — VIOLATED stands,
 *                 unconfirmed, on Spacer's SAT answer alone;</li>
 *             <li>it refuted the trace outright (no firing chain reaches the
 *                 violation) — the verdict is downgraded to UNKNOWN. A refutation
 *                 is strictly more informative than "did not apply", so it reports
 *                 {@code FALSE}, never {@code null}.</li>
 *           </ul></li>
 *       <li>{@code null} — replay did not apply: a non-violated verdict that no
 *           replay touched, replay disabled via
 *           {@link SmtVerifier#counterexampleReplay(boolean)}, or the coloured
 *           &nu;-encoding / Route B path, whose state shapes are outside the flat
 *           replayer's scope.</li>
 *     </ul>
 * @param elapsed                  wall-clock time for verification
 * @param statistics               solver statistics
 */
public record SmtVerificationResult(
    Verdict verdict,
    String report,
    List<PInvariant> invariants,
    List<String> discoveredInvariants,
    List<MarkingState> counterexampleTrace,
    List<String> counterexampleTransitions,
    Boolean counterexampleConfirmed,
    Duration elapsed,
    SmtStatistics statistics
) {

    /**
     * Verification verdict.
     */
    public sealed interface Verdict {
        /**
         * Property proven safe. No reachable state violates it.
         *
         * @param method             how it was proven ("IC3/PDR", "structural", "P-invariant")
         * @param inductiveInvariant the raw IC3-synthesized inductive invariant formula (may be null)
         */
        record Proven(String method, String inductiveInvariant) implements Verdict {}

        /**
         * Property violated. A counterexample trace is available; whether replay
         * confirmed it is carried by
         * {@link SmtVerificationResult#counterexampleConfirmed()}, not by the
         * verdict.
         */
        record Violated() implements Verdict {}

        /**
         * Could not determine.
         *
         * @param reason explanation (timeout, resource limit, etc.)
         */
        record Unknown(String reason) implements Verdict {}
    }

    /**
     * Solver statistics.
     *
     * @param places             number of places in flattened net
     * @param transitions        number of transitions in flattened net
     * @param invariantsFound    number of P-invariants found
     * @param structuralResult   result of structural pre-check
     */
    public record SmtStatistics(
        int places,
        int transitions,
        int invariantsFound,
        String structuralResult
    ) {}

    /**
     * Returns true if the property was proven safe.
     */
    public boolean isProven() {
        return verdict instanceof Verdict.Proven;
    }

    /**
     * Returns true if a counterexample was found.
     */
    public boolean isViolated() {
        return verdict instanceof Verdict.Violated;
    }
}
