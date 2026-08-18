package org.libpetri.smt;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * CI gate for the Z3 native library.
 *
 * <p>Roughly the whole verifier suite is annotated {@code @EnabledIf("z3Available")}
 * — {@link SmtVerifierTest}, {@link VerdictParityTest}, {@link FragmentExtensionTest},
 * {@code org.libpetri.smt.z3.CertificateCheckerTest},
 * {@code org.libpetri.verification.SubnetVerifyTest} — and each of those predicates
 * swallows {@link UnsatisfiedLinkError} / {@link NoClassDefFoundError}. So if the
 * {@code javasmt-solver-z3} native fails to load on a runner, every one of those
 * tests is silently skipped and the build is still green: the feature ships
 * unverified <em>because</em> the checks did not run.
 *
 * <p>This test carries no {@code @EnabledIf} of its own — it cannot itself be
 * skipped — and turns that silent skip into a red build wherever {@code CI} is
 * set. Locally (no {@code CI} in the environment) it stays a no-op, so a
 * developer without the native can still run the suite.
 */
class Z3NativeGateTest {

    @Test
    void z3NativeMustLoadInCi() {
        boolean loaded;
        try {
            new com.microsoft.z3.Context().close();
            loaded = true;
        } catch (UnsatisfiedLinkError | NoClassDefFoundError _) {
            loaded = false;
        }
        if (System.getenv("CI") == null) {
            return; // developer machine: the z3-gated suites may legitimately skip
        }
        assertTrue(loaded, """
            Z3 natives did not load, so every @EnabledIf("z3Available") suite \
            (certificate check, counterexample replay, verdict parity) was \
            skipped — the verifier is unverified. Fix the javasmt-solver-z3 \
            native on this runner rather than relaxing this assertion.""");
    }
}
