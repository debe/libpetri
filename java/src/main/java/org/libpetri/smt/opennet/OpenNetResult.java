package org.libpetri.smt.opennet;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.PetriNet;
import org.libpetri.smt.SmtVerificationResult;

import java.time.Duration;
import java.util.List;

/**
 * The outcome of {@link OpenNetVerifier#verifyOpenNet} ([VER-022]).
 *
 * @param verdict        {@code Proven}, {@code Violated} (see {@code violations}), or
 *                       {@code Unknown} with the reason. A {@code Proven} from the SMT route
 *                       carries its queries' certificates as {@code [subject] invariant} lines;
 *                       one from the enumeration route carries none, the closed graph being its
 *                       evidence
 * @param violations     every broken part found. The graph route lists clauses in contract
 *                       order, then stranded places by name, then termination; the SMT route
 *                       asks for stranding first, so it lists that, then clauses in contract
 *                       order, then termination
 * @param route          which route decided the verdict
 * @param classCount     classes the state-class graph explored; {@code 0} when it was skipped
 * @param graphComplete  whether the state-class graph closed within its budget
 * @param report         the human-readable report, byte-identical to the reference's
 * @param closedNet      the subnet closed by its environment: what every route verified
 * @param closedMarking  the closed net's initial marking
 * @param elapsed        wall-clock time for the verification
 */
public record OpenNetResult(
    SmtVerificationResult.Verdict verdict,
    List<ContractViolation> violations,
    Route route,
    int classCount,
    boolean graphComplete,
    String report,
    PetriNet closedNet,
    MarkingState closedMarking,
    Duration elapsed
) {

    public OpenNetResult {
        violations = List.copyOf(violations);
    }

    /** Which route decided the verdict. */
    public enum Route {
        /** The closed net's untimed state-class graph. */
        ENUMERATION("enumeration"),
        /** One SMT query per part of the contract, and the firing bound for termination. */
        SMT("smt");

        private final String label;

        Route(String label) {
            this.label = label;
        }

        /** {@code enumeration} or {@code smt}. */
        public String label() {
            return label;
        }
    }

    /** Whether the contract was proven. */
    public boolean isProven() {
        return verdict instanceof SmtVerificationResult.Verdict.Proven;
    }

    /** Whether a broken part was found. */
    public boolean isViolated() {
        return verdict instanceof SmtVerificationResult.Verdict.Violated;
    }
}
