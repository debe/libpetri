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
         * Property violated. A counterexample trace is available.
         *
         * @param counterexampleConfirmed whether the counterexample was
         *     confirmed as a genuine run of the analysis semantics — for the
         *     flat IC3/PDR path, by {@link org.libpetri.smt.z3.AbstractReplayer}
         *     chaining the decoded states into an abstract run reaching the
         *     violation; for the &nu;-net Route B path, by construction (the
         *     trace is an explicit path of the name-aware state-class graph).
         *     {@code false} means the verdict stands but no replayable trace
         *     backs it (nothing decodable, or replay opted out).
         */
        record Violated(boolean counterexampleConfirmed) implements Verdict {}

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
