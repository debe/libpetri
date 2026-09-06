package org.libpetri.smt.z3;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.invariant.PInvariant;

import java.time.Duration;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Independent certificate check for IC3/PDR proofs.
 *
 * <p>When Z3 Spacer answers {@code sat} on the CHC encoding ({@link SmtEncoder}), the
 * model it prints interprets {@code Reachable} as an inductive invariant, the proof
 * certificate. This checker re-verifies that certificate with plain (non-HORN) SMT
 * queries in a SECOND z3 run, so a PROVEN verdict no longer rests on the empirical
 * HORN sat ⇒ proven mapping alone, nor on the correctness of the P-invariant
 * strengthening: the three verification conditions below are discharged against the
 * UNSTRENGTHENED step relation ({@link SmtEncoder#encodeStepRelationSmt2}).
 *
 * <p>The candidate invariant is {@code R' := R AND Inv}, where {@code R} is the pasted
 * {@code Reachable} interpretation and {@code Inv} the validated P-invariant equalities
 * the CHC encoding strengthened its rule bodies with: a Spacer model is only guaranteed
 * inductive <em>relative to</em> that strengthening, so the conjuncts ride along in the
 * candidate, but the RELATION stays unstrengthened, which means VC1/VC2 re-prove each
 * conjunct's initiation and inductiveness from scratch. A wrong P-invariant cannot
 * weaken this check: it fails init or consecution instead.
 *
 * <ol>
 *   <li><b>VC1 (init)</b>: {@code NOT R'(M0)} is UNSAT.</li>
 *   <li><b>VC2 (consecution)</b>: {@code M >= 0 AND R'(M) AND T(M,M') AND NOT R'(M')} is UNSAT.</li>
 *   <li><b>VC3 (safety)</b>: {@code M >= 0 AND R'(M) AND Bad(M)} is UNSAT.</li>
 * </ol>
 *
 * <p>The {@code M >= 0} conjunct is the state domain: markings are token counts, so the
 * VCs range over N^P; without it a certificate inductive over N^P is refuted by a
 * negative predecessor in Z^P.
 *
 * <p>The certificate is the {@code (define-fun …)} block of the {@code (get-model)}
 * reply, pasted verbatim: auxiliary definitions stay alongside {@code Reachable}, so
 * every name resolves in the fresh script. The three VCs run under
 * {@code (push)}/{@code (pop)} in ONE script; the emitted text is byte-identical to the
 * Rust reference ({@code certificate_check.rs}).
 *
 * <p>This class never throws: a malformed certificate, a solver spawn failure, an
 * errored assert, a truncated reply all become {@link Result.Unavailable}, which the
 * caller maps to an UNKNOWN verdict.
 */
public final class CertificateChecker {

    private CertificateChecker() {}

    /** The three verification conditions of an inductive safety certificate. */
    public enum Vc {
        /** VC1: the invariant holds in the initial marking. */
        INIT("initiation (VC1)"),
        /** VC2: the invariant is preserved by every unstrengthened step. */
        CONSECUTION("consecution (VC2)"),
        /** VC3: the invariant excludes every property-violating marking. */
        SAFETY("safety (VC3)");

        private final String label;

        Vc(String label) {
            this.label = label;
        }

        /** Human-readable label naming the condition, e.g. {@code "consecution (VC2)"}. */
        public String label() {
            return label;
        }
    }

    /** Outcome of a certificate check. */
    public sealed interface Result {
        /** All three verification conditions are UNSAT: the certificate is valid. */
        record Passed() implements Result {}

        /**
         * A verification condition was not UNSAT.
         *
         * @param vc     the first failing verification condition
         * @param detail solver status and, when available, a witness marking
         */
        record Failed(Vc vc, String detail) implements Result {}

        /**
         * The check could not run to a verdict: a missing or malformed certificate, a
         * solver failure, an errored assert. Treated like a failure by the caller (the
         * verdict is not certified), but no specific VC is implicated.
         *
         * @param reason why the certificate could not be checked
         */
        record Unavailable(String reason) implements Result {}
    }

    /**
     * Re-verifies an extracted proof certificate against the unstrengthened step
     * relation.
     *
     * @param certificate    the {@code (define-fun …)} block extracted verbatim from
     *                       the Spacer model
     * @param flatNet        the flattened net the CHC system was encoded from
     * @param initialMarking the initial marking (VC1)
     * @param property       the verified property (VC3 uses its violation predicate)
     * @param sinkPlaces     expected terminal places (part of the VER-002 violation predicates)
     * @param invariants     validated P-invariants folded into the candidate and re-proven
     * @param solver         the resolved z3 executable
     * @param timeout        per-invocation solver budget
     * @return the check outcome; never throws
     */
    public static Result check(
            String certificate,
            FlatNet flatNet,
            MarkingState initialMarking,
            SmtProperty property,
            Collection<Place<?>> sinkPlaces,
            List<PInvariant> invariants,
            Z3Solver solver,
            Duration timeout
    ) {
        try {
            return doCheck(certificate, flatNet, initialMarking, property, sinkPlaces,
                invariants, solver, timeout);
        } catch (RuntimeException e) {
            return new Result.Unavailable("unexpected error during certificate check: " + e);
        }
    }

    private static Result doCheck(
            String certificate, FlatNet flatNet, MarkingState initialMarking,
            SmtProperty property, Collection<Place<?>> sinkPlaces, List<PInvariant> invariants,
            Z3Solver solver, Duration timeout
    ) {
        if (certificate == null) {
            return new Result.Unavailable(
                "no inductive invariant (define-fun block) could be extracted from the z3 model");
        }
        String shape = shapeFailure(flatNet, invariants);
        if (shape != null) {
            return new Result.Unavailable(shape);
        }
        if (!certificate.contains("(define-fun Reachable ")
                && !certificate.contains("(define-fun |Reachable| ")) {
            return new Result.Unavailable("certificate does not define Reachable");
        }

        var vcs = VerificationConditions.build(
            certificate, flatNet, initialMarking, property, sinkPlaces, invariants);

        List<String> results;
        try {
            results = runVcScript(vcs.script(), timeout, solver);
        } catch (Z3Process.Z3ProcessException | VcFailure e) {
            return new Result.Unavailable(e.getMessage());
        }
        Vc[] order = Vc.values();
        for (int i = 0; i < results.size(); i++) {
            if (!results.get(i).equals("unsat")) {
                return new Result.Failed(order[i],
                    vcs.detailFor(i, results.get(i), flatNet, timeout, solver));
            }
        }
        return new Result.Passed();
    }

    /**
     * The certificate-check script for the given inputs, exactly as {@link #check}
     * would send it (VER-013 script parity): what the cross-language golden tests diff.
     */
    public static String vcScript(
            String certificate, FlatNet flatNet, MarkingState initialMarking,
            SmtProperty property, Collection<Place<?>> sinkPlaces, List<PInvariant> invariants
    ) {
        return VerificationConditions.build(
            certificate, flatNet, initialMarking, property, sinkPlaces, invariants).script();
    }

    /** Why the net and invariants cannot be indexed safely, or {@code null}. */
    private static String shapeFailure(FlatNet flatNet, List<PInvariant> invariants) {
        int p = flatNet.placeCount();
        for (var inv : invariants) {
            if (inv.weights().length != p) {
                return "P-invariant has " + inv.weights().length + " weights for a " + p + "-place net";
            }
            for (int pid : inv.support()) {
                if (pid >= p || pid < 0) {
                    return "P-invariant support names place index " + pid + " in a " + p + "-place net";
                }
            }
        }
        return null;
    }

    /** A VC run that could not be trusted; the message is the reason. */
    private static final class VcFailure extends Exception {
        VcFailure(String message) {
            super(message);
        }
    }

    /**
     * Runs one plain-SMT script and returns the three positional {@code (check-sat)}
     * answers. Both output channels are inspected: an {@code (error …)} on EITHER
     * stream means an assert was dropped, which would silently make a VC vacuous; a
     * {@code timeout} line, a watchdog kill and a non-success exit mean the run did not
     * complete. Only a clean three-answer stdout counts.
     */
    private static List<String> runVcScript(String script, Duration timeout, Z3Solver solver)
            throws Z3Process.Z3ProcessException, VcFailure {
        var reply = solver.run(script, "certificate", timeout, List.of());
        long timeoutMs = Z3Solver.timeoutMs(timeout);
        String err = SmtText.errorLine(reply.stderr());
        if (err != null) {
            throw new VcFailure("z3 reported an error on stderr: " + err);
        }
        if (SmtText.timeoutLine(reply.stdout())) {
            throw new VcFailure("z3 hard timeout after " + Z3Process.hardTimeoutSecs(timeoutMs)
                + "s while checking the certificate");
        }
        if (reply.exit() instanceof Z3Process.Exit.Killed) {
            throw new VcFailure("z3 did not exit within " + Z3Process.watchdogMs(timeoutMs)
                + " ms while checking the certificate and was killed");
        }
        List<String> results = parseVcResults(reply.stdout());
        if (!reply.success()) {
            String status = reply.exit() instanceof Z3Process.Exit.Exited(int code)
                ? "exit status: " + code
                : "the watchdog kill";
            throw new VcFailure("z3 exited with " + status + " after answering " + results);
        }
        return results;
    }

    /**
     * Parses the three positional {@code (check-sat)} answers. Any {@code (error …)}
     * line fails the check outright (an errored assert silently vanishes from the
     * query, which could leave a VC vacuous); a {@code timeout} line is z3's {@code -T}
     * backstop, not a fourth answer.
     */
    static List<String> parseVcResults(String stdout) throws VcFailure {
        String err = SmtText.errorLine(stdout);
        if (err != null) {
            throw new VcFailure("z3 error while checking the certificate: " + err);
        }
        if (SmtText.timeoutLine(stdout)) {
            throw new VcFailure("z3 hard timeout while checking the certificate");
        }
        List<String> results = stdout.lines()
            .map(String::strip)
            .filter(l -> l.equals("sat") || l.equals("unsat") || l.equals("unknown"))
            .toList();
        if (results.size() != 3) {
            throw new VcFailure("expected 3 VC answers from z3, got " + results.size() + ": " + results);
        }
        return results;
    }

    /**
     * The assembled VC script, kept in parts so one VC can be re-run alone to describe
     * its failure (the model witness / the unknown reason).
     */
    private record VerificationConditions(List<String> prelude, List<List<String>> asserts) {

        static VerificationConditions build(
                String certificate, FlatNet flatNet, MarkingState initialMarking,
                SmtProperty property, Collection<Place<?>> sinkPlaces, List<PInvariant> invariants
        ) {
            int p = flatNet.placeCount();
            var mVars = new ArrayList<String>(p);
            var mpVars = new ArrayList<String>(p);
            for (int i = 0; i < p; i++) {
                mVars.add("m" + i);
                mpVars.add("m" + i + "p");
            }

            var prelude = new ArrayList<String>();
            prelude.add("; IC3/PDR certificate check (plain SMT-LIB2, not HORN):");
            prelude.add("; each VC below must be unsat for the certificate to stand.");
            prelude.add(certificate);
            prelude.add("");
            for (var v : mVars) {
                prelude.add("(declare-const " + v + " Int)");
            }
            for (var v : mpVars) {
                prelude.add("(declare-const " + v + " Int)");
            }

            // VC1 (init): the initial marking satisfies the candidate invariant.
            var m0 = new ArrayList<String>(p);
            for (int i = 0; i < p; i++) {
                m0.add(Integer.toString(initialMarking.tokens(flatNet.places().get(i))));
            }
            var vc1 = new ArrayList<String>();
            vc1.add("(assert (not " + candidate(m0, invariants) + "))");

            // The system lives in N^P, not Z^P: without this the VCs run over
            // negative markings the net can never hold.
            var nonNegative = new ArrayList<String>();
            for (var v : mVars) {
                nonNegative.add("(assert (>= " + v + " 0))");
            }

            // VC2 (consecution): closed under the unstrengthened step relation.
            String step = SmtEncoder.encodeStepRelationSmt2(flatNet);
            var vc2 = new ArrayList<>(nonNegative);
            vc2.add("(assert " + candidate(mVars, invariants) + ")");
            vc2.add("(assert " + step + ")");
            vc2.add("(assert (not " + candidate(mpVars, invariants) + "))");

            // VC3 (safety): excludes every property-violating state, exactly the
            // violation the CHC error rule encodes.
            String bad = SmtEncoder.encodePropertyViolation(
                flatNet, property, mVars, sinkPlaces, SmtEncoder.resolveEnvInjection(flatNet));
            var vc3 = new ArrayList<>(nonNegative);
            vc3.add("(assert " + candidate(mVars, invariants) + ")");
            vc3.add("(assert " + bad + ")");

            return new VerificationConditions(prelude, List.of(vc1, vc2, vc3));
        }

        /** The full script: the prelude, then the three VCs under push/pop. */
        String script() {
            var lines = new ArrayList<>(prelude);
            Vc[] labels = Vc.values();
            for (int i = 0; i < asserts.size(); i++) {
                lines.add("");
                lines.add("; VC" + (i + 1) + " " + labels[i].label());
                lines.add("(push)");
                lines.addAll(asserts.get(i));
                lines.add("(check-sat)");
                lines.add("(pop)");
            }
            return String.join("\n", lines);
        }

        /**
         * Describes VC {@code i}'s non-{@code unsat} answer for the downgrade reason,
         * by re-running that VC alone with model/reason extraction enabled. Best
         * effort: without it the answer is still named.
         */
        String detailFor(int i, String answer, FlatNet flatNet, Duration timeout, Z3Solver solver) {
            var lines = new ArrayList<String>();
            lines.add("(set-option :produce-models true)");
            lines.addAll(prelude);
            lines.addAll(asserts.get(i));
            lines.add("(check-sat)");
            lines.add(answer.equals("sat") ? "(get-model)" : "(get-info :reason-unknown)");
            String reply;
            try {
                reply = solver.run(String.join("\n", lines), "certificate-detail", timeout, List.of())
                    .stdout();
            } catch (Z3Process.Z3ProcessException _) {
                reply = "";
            }
            if (answer.equals("sat")) {
                String w = witness(reply, flatNet);
                return w == null
                    ? "solver returned SATISFIABLE"
                    : "solver returned SATISFIABLE (witness: " + w + ")";
            }
            String r = reasonUnknown(reply);
            return r == null ? "solver returned UNKNOWN" : "solver returned UNKNOWN (" + r + ")";
        }
    }

    /**
     * Reads the current-marking assignment out of a {@code (get-model)} reply as
     * {@code p0=2, p1=1} (place names, index order); {@code null} when no {@code m_i}
     * was defined.
     */
    static String witness(String model, FlatNet flatNet) {
        var parts = new ArrayList<String>();
        for (int i = 0; i < flatNet.placeCount(); i++) {
            String needle = "(define-fun m" + i + " () Int";
            int at = model.indexOf(needle);
            if (at < 0) {
                continue;
            }
            String rest = model.substring(at + needle.length()).stripLeading();
            String value;
            if (rest.startsWith("(")) {
                int end = SmtText.sexprEnd(rest, 0);
                if (end < 0) {
                    continue;
                }
                // A negative literal prints as `(- 1)`; flatten it back to `-1`.
                value = String.join("", rest.substring(1, end - 1).trim().split("\\s+"));
            } else {
                int end = 0;
                while (end < rest.length()
                        && !Character.isWhitespace(rest.charAt(end)) && rest.charAt(end) != ')') {
                    end++;
                }
                if (end == 0) {
                    continue;
                }
                value = rest.substring(0, end);
            }
            parts.add(flatNet.places().get(i).name() + "=" + value);
        }
        return parts.isEmpty() ? null : String.join(", ", parts);
    }

    /** Reads z3's {@code (get-info :reason-unknown)} reply, e.g. {@code timeout}. */
    static String reasonUnknown(String reply) {
        int at = reply.indexOf(":reason-unknown");
        if (at < 0) {
            return null;
        }
        String rest = reply.substring(at + ":reason-unknown".length()).stripLeading();
        int end = rest.indexOf(')');
        if (end < 0) {
            return null;
        }
        String reason = rest.substring(0, end).strip();
        if (reason.startsWith("\"") && reason.endsWith("\"") && reason.length() >= 2) {
            reason = reason.substring(1, reason.length() - 1);
        }
        reason = reason.strip();
        return reason.isEmpty() ? null : reason;
    }

    /**
     * The candidate invariant applied to a variable (or literal) vector:
     * {@code R'(vars) = (Reachable vars) AND Inv(vars)}.
     */
    private static String candidate(List<String> vars, List<PInvariant> invariants) {
        var conjuncts = new ArrayList<String>();
        conjuncts.add("(Reachable " + String.join(" ", vars) + ")");
        conjuncts.addAll(SmtEncoder.invariantConditions(invariants, vars));
        return SmtEncoder.conjoin(conjuncts);
    }
}
