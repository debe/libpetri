package org.libpetri.smt;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * CI gate for the z3 executable (VER-013).
 *
 * <p>Roughly the whole verifier suite is annotated {@code @EnabledIf("z3Available")}
 * — {@link SmtVerifierTest}, {@link VerdictParityTest}, {@link FragmentExtensionTest},
 * {@code org.libpetri.smt.z3.CertificateCheckerTest},
 * {@code org.libpetri.verification.SubnetVerifyTest} — and each predicate skips when
 * no usable {@code z3} resolves ({@code LIBPETRI_Z3} or {@code PATH}, 4.8.0 or newer).
 * So on a runner without the solver every one of those tests is silently skipped and
 * the build is still green: the feature ships unverified <em>because</em> the checks
 * did not run.
 *
 * <p>This test carries no {@code @EnabledIf} of its own — it cannot itself be
 * skipped — and turns that silent skip into a red build wherever {@code CI} is set.
 * Locally (no {@code CI} in the environment) it stays a no-op, so a developer without
 * z3 can still run the suite.
 */
class Z3BinaryGateTest {

    @Test
    void z3ExecutableMustResolveInCi() {
        boolean available = SmtVerifier.z3Available();
        if (System.getenv("CI") == null) {
            return; // developer machine: the z3-gated suites may legitimately skip
        }
        assertTrue(available, """
            No usable z3 executable resolves (PATH or LIBPETRI_Z3, >= 4.8.0), so every \
            @EnabledIf("z3Available") suite (certificate check, counterexample replay, \
            verdict parity) was skipped — the verifier is unverified. Fix the runner \
            rather than relaxing this assertion.""");
    }
}
