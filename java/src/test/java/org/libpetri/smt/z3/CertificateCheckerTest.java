package org.libpetri.smt.z3;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.SmtVerifier;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.IncidenceMatrix;
import org.libpetri.smt.encoding.NetFlattener;
import org.libpetri.smt.invariant.PInvariant;
import org.libpetri.smt.invariant.PInvariantComputer;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

import java.time.Duration;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for {@link CertificateChecker} with hand-written SMT-LIB2 certificates.
 *
 * <p>The certificates are written by hand rather than taken from Spacer so that
 * corrupted certificates can be exercised deterministically. Every test that runs a
 * check is gated on a usable {@code z3} executable (they run in CI).
 *
 * <p>The fixture net is deliberately <b>asymmetric</b>: one transition consumes TWO
 * tokens from A and produces ONE token into B (initial marking A=2), so the exact
 * invariant is {@code A + 2*B = 2}. Swapping the roles of A and B changes the formula's
 * truth values, so a positional mix-up of the {@code define-fun} parameters cannot pass
 * unnoticed.
 */
class CertificateCheckerTest {

    private static final Place<String> A = Place.of("CertA", String.class);
    private static final Place<String> B = Place.of("CertB", String.class);

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static Z3Solver solver() {
        try {
            return Z3Solver.resolve();
        } catch (Z3Solver.Z3Unavailable e) {
            throw new AssertionError(e);
        }
    }

    /** A --(consume 2)--> T --(produce 1)--> B. Reachable: (A=2,B=0) and (A=0,B=1). */
    private static FlatNet asymmetricFlatNet() {
        var t = Transition.builder("Consume2A")
            .inputs(In.exactly(2, A))
            .outputs(Out.place(B))
            .build();
        var net = PetriNet.builder("CertNet").transitions(t).build();
        return NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
    }

    private static MarkingState initialMarking() {
        return MarkingState.builder().tokens(A, 2).build();
    }

    /** The parameter list {@code ((x!0 Int) (x!1 Int) …)} for {@code P} places. */
    private static String params(int P) {
        var sb = new StringBuilder("(");
        for (int i = 0; i < P; i++) {
            if (i > 0) {
                sb.append(' ');
            }
            sb.append("(x!").append(i).append(" Int)");
        }
        return sb.append(')').toString();
    }

    /** {@code (define-fun Reachable <params> Bool <body>)}, parameter j standing for place j. */
    private static String certificate(int P, String body) {
        return "(define-fun Reachable " + params(P) + " Bool\n    " + body + ")";
    }

    private static String v(FlatNet flat, Place<?> place) {
        return "x!" + flat.indexOf(place);
    }

    /** The exact inductive invariant of the fixture: A + 2*B = 2, A >= 0, B >= 0. */
    private static String exactInvariant(FlatNet flat) {
        String a = v(flat, A);
        String b = v(flat, B);
        return "(and (= (+ " + a + " (* 2 " + b + ")) 2) (>= " + a + " 0) (>= " + b + " 0))";
    }

    private static CertificateChecker.Result check(String cert, FlatNet flat, SmtProperty property,
                                                   List<PInvariant> invariants) {
        return CertificateChecker.check(
            cert, flat, initialMarking(), property, Set.of(), invariants, solver(),
            Duration.ofSeconds(10));
    }

    private static CertificateChecker.Result check(String cert, FlatNet flat) {
        return check(cert, flat, SmtProperty.placeBound(B, 1), List.of());
    }

    @Test
    @EnabledIf("z3Available")
    void validCertificate_passes() {
        var flat = asymmetricFlatNet();
        var result = check(certificate(flat.placeCount(), exactInvariant(flat)), flat);
        assertInstanceOf(CertificateChecker.Result.Passed.class, result,
            "exact invariant must pass all three VCs: " + result);
    }

    @Test
    @EnabledIf("z3Available")
    void parameterNamesArePositional_passes() {
        // z3 names the model parameters however it likes; the checker pastes the block
        // verbatim and applies Reachable positionally, so a body written over renamed
        // parameters (b for place 0, a for place 1) is the same certificate.
        var flat = asymmetricFlatNet();
        int ia = flat.indexOf(A);
        String[] names = new String[flat.placeCount()];
        names[ia] = "b";
        names[1 - ia] = "a";
        String cert = "(define-fun Reachable ((" + names[0] + " Int) (" + names[1] + " Int)) Bool\n    "
            + "(and (= (+ " + names[ia] + " (* 2 " + names[1 - ia] + ")) 2) (>= " + names[ia]
            + " 0) (>= " + names[1 - ia] + " 0)))";
        assertInstanceOf(CertificateChecker.Result.Passed.class, check(cert, flat));
    }

    @Test
    @EnabledIf("z3Available")
    void quotedHead_passes() {
        var flat = asymmetricFlatNet();
        String cert = "(define-fun |Reachable| " + params(flat.placeCount()) + " Bool\n    "
            + exactInvariant(flat) + ")";
        assertInstanceOf(CertificateChecker.Result.Passed.class, check(cert, flat));
    }

    @Test
    @EnabledIf("z3Available")
    void auxiliaryDefinitions_stayResolvable() {
        // The model block carries every define-fun of the model (Error, helpers); the
        // checker keeps them so a Reachable body that references one still resolves.
        var flat = asymmetricFlatNet();
        String cert = "(define-fun Error () Bool\n    false)\n"
            + "(define-fun two () Int\n    2)\n"
            + certificate(flat.placeCount(),
                "(and (= (+ " + v(flat, A) + " (* two " + v(flat, B) + ")) two) (>= "
                    + v(flat, A) + " 0) (>= " + v(flat, B) + " 0))");
        assertInstanceOf(CertificateChecker.Result.Passed.class, check(cert, flat));
    }

    @Test
    @EnabledIf("z3Available")
    void swappedInvariant_failsInit() {
        // 2*A + B = 2 — the roles of A and B swapped. On the asymmetric fixture it fails
        // VC1: I(M0) with M0=(A=2,B=0) gives 4 != 2.
        var flat = asymmetricFlatNet();
        String a = v(flat, A);
        String b = v(flat, B);
        var result = check(certificate(flat.placeCount(),
            "(and (= (+ (* 2 " + a + ") " + b + ") 2) (>= " + a + " 0) (>= " + b + " 0))"), flat);
        var failed = assertInstanceOf(CertificateChecker.Result.Failed.class, result);
        assertEquals(CertificateChecker.Vc.INIT, failed.vc(),
            "swapped roles must be caught at initiation: " + failed.detail());
        assertTrue(failed.detail().startsWith("solver returned SATISFIABLE"), failed.detail());
    }

    @Test
    @EnabledIf("z3Available")
    void trueInvariant_reachableBadState_failsSafety() {
        // Corrupted certificate: I = true. VC1 and VC2 hold trivially, but the bad
        // state B > 0 is genuinely reachable ((A=0,B=1)), so I AND Bad is SAT.
        var flat = asymmetricFlatNet();
        var result = check(certificate(flat.placeCount(), "true"), flat,
            SmtProperty.placeBound(B, 0), List.of());
        var failed = assertInstanceOf(CertificateChecker.Result.Failed.class, result);
        assertEquals(CertificateChecker.Vc.SAFETY, failed.vc(),
            "true-invariant corruption must be caught at the safety VC: " + failed.detail());
        assertTrue(failed.detail().contains("witness: "), "a SAT VC names its witness: " + failed.detail());
    }

    @Test
    @EnabledIf("z3Available")
    void weakInvariant_failsConsecution() {
        // I = (B <= 0) holds initially but is not preserved: firing the transition
        // moves (A=2,B=0) to (A=0,B=1).
        var flat = asymmetricFlatNet();
        var result = check(certificate(flat.placeCount(), "(<= " + v(flat, B) + " 0)"), flat);
        var failed = assertInstanceOf(CertificateChecker.Result.Failed.class, result);
        assertEquals(CertificateChecker.Vc.CONSECUTION, failed.vc(),
            "non-inductive invariant must be caught at consecution: " + failed.detail());
    }

    @Test
    @EnabledIf("z3Available")
    void envInjection_isPartOfStepRelation_failsConsecution() {
        // env E -> Drain -> S with alwaysAvailable injection. I = (E <= 0 AND S >= 0)
        // holds initially and is preserved by every TRANSITION step (Drain needs
        // E >= 1, unreachable under I) — only the injection step E' = E+1 breaks it.
        // A step relation missing the VER-006 injection rules would wrongly PASS.
        var e = Place.of("CertE", String.class);
        var sPlace = Place.of("CertS", String.class);
        var env = EnvironmentPlace.of(e);
        var t = Transition.builder("Drain").inputs(In.one(e)).outputs(Out.place(sPlace)).build();
        var net = PetriNet.builder("CertEnvNet").transitions(t).build();
        var flat = NetFlattener.flatten(net, Set.of(env), EnvironmentAnalysisMode.alwaysAvailable());
        String cert = certificate(flat.placeCount(),
            "(and (<= " + v(flat, e) + " 0) (>= " + v(flat, sPlace) + " 0))");
        var result = CertificateChecker.check(
            cert, flat, MarkingState.empty(), SmtProperty.placeBound(sPlace, 5), Set.of(),
            List.of(), solver(), Duration.ofSeconds(10));
        var failed = assertInstanceOf(CertificateChecker.Result.Failed.class, result);
        assertEquals(CertificateChecker.Vc.CONSECUTION, failed.vc(),
            "the injection step must be part of the checked relation: " + failed.detail());
    }

    // === Candidate strengthening: R' = I AND validated P-invariant equalities ===

    private static final Place<String> CYC_A = Place.of("CycA", String.class);
    private static final Place<String> CYC_B = Place.of("CycB", String.class);

    /** Conservation cycle A <-> B with one token: the exact law is A + B = 1. */
    private static FlatNet cycleFlatNet() {
        var t1 = Transition.builder("AtoB").inputs(In.one(CYC_A)).outputs(Out.place(CYC_B)).build();
        var t2 = Transition.builder("BtoA").inputs(In.one(CYC_B)).outputs(Out.place(CYC_A)).build();
        var net = PetriNet.builder("CycleNet").transitions(t1, t2).build();
        return NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
    }

    @Test
    @EnabledIf("z3Available")
    void strengtheningDependentCertificate_passesWithValidatedInvariants() {
        // Spacer legitimately synthesizes certificates like I = NOT(B >= 2) on a
        // conservation cycle: I alone is NOT inductive under the bare step relation
        // (from an unreachable M=(A=5,B=1) satisfying I, firing AtoB gives B'=2),
        // it is inductive only relative to A + B = 1. The candidate R' = I AND invs
        // must accept it — while the same check with no invariants folded in fails
        // consecution, which pins down WHY the candidate construction is needed.
        var flat = cycleFlatNet();
        var m0 = MarkingState.builder().tokens(CYC_A, 1).build();
        var invariants = PInvariantComputer.compute(IncidenceMatrix.from(flat), flat, m0);
        assertFalse(invariants.isEmpty(), "the cycle net must have the conservation law A+B=1");
        String cert = certificate(flat.placeCount(), "(<= " + v(flat, CYC_B) + " 1)");

        var bare = CertificateChecker.check(cert, flat, m0, SmtProperty.placeBound(CYC_B, 1),
            Set.of(), List.of(), solver(), Duration.ofSeconds(10));
        var bareFailed = assertInstanceOf(CertificateChecker.Result.Failed.class, bare,
            "without the folded-in law the certificate is not bare-inductive: " + bare);
        assertEquals(CertificateChecker.Vc.CONSECUTION, bareFailed.vc(), bareFailed.detail());

        var strengthened = CertificateChecker.check(cert, flat, m0, SmtProperty.placeBound(CYC_B, 1),
            Set.of(), invariants, solver(), Duration.ofSeconds(10));
        assertInstanceOf(CertificateChecker.Result.Passed.class, strengthened,
            "R' = I AND (A+B=1) must validate the strengthening-dependent certificate: " + strengthened);
    }

    @Test
    @EnabledIf("z3Available")
    void poisonedInvariant_wrongConstant_failsInit() {
        // A poisoned equality folded into the candidate is re-proven, not trusted:
        // A + B = 2 is false at M0=(A=1,B=0), so VC1 catches it even under I = true.
        var flat = cycleFlatNet();
        int ia = flat.indexOf(CYC_A);
        int ib = flat.indexOf(CYC_B);
        var m0 = MarkingState.builder().tokens(CYC_A, 1).build();
        int[] weights = new int[flat.placeCount()];
        weights[ia] = 1;
        weights[ib] = 1;
        var poisoned = new PInvariant(weights, 2, Set.of(ia, ib));
        var result = CertificateChecker.check(certificate(flat.placeCount(), "true"), flat, m0,
            SmtProperty.placeBound(CYC_B, 1), Set.of(), List.of(poisoned), solver(),
            Duration.ofSeconds(10));
        var failed = assertInstanceOf(CertificateChecker.Result.Failed.class, result);
        assertEquals(CertificateChecker.Vc.INIT, failed.vc(),
            "a wrong constant must fail initiation: " + failed.detail());
    }

    @Test
    @EnabledIf("z3Available")
    void poisonedInvariant_notPreserved_failsConsecution() {
        // A + 2*B = 1 holds at M0=(A=1,B=0) but firing AtoB yields (0,1) with value 2:
        // the poisoned equality fails its re-proven consecution under the bare relation.
        var flat = cycleFlatNet();
        int ia = flat.indexOf(CYC_A);
        int ib = flat.indexOf(CYC_B);
        var m0 = MarkingState.builder().tokens(CYC_A, 1).build();
        int[] weights = new int[flat.placeCount()];
        weights[ia] = 1;
        weights[ib] = 2;
        var poisoned = new PInvariant(weights, 1, Set.of(ia, ib));
        var result = CertificateChecker.check(certificate(flat.placeCount(), "true"), flat, m0,
            SmtProperty.placeBound(CYC_B, 1), Set.of(), List.of(poisoned), solver(),
            Duration.ofSeconds(10));
        var failed = assertInstanceOf(CertificateChecker.Result.Failed.class, result);
        assertEquals(CertificateChecker.Vc.CONSECUTION, failed.vc(),
            "a non-preserved equality must fail consecution: " + failed.detail());
    }

    // === Marking domain (N^P) ===

    private static final Place<String> CONS_P0 = Place.of("p0", String.class);
    private static final Place<String> CONS_P1 = Place.of("p1", String.class);

    @Test
    @EnabledIf("z3Available")
    void certificateInductiveOverNaturalsOnly_passes() {
        // p0 + p1 = 3 bounds p1 by 3 only because neither place can go negative: over
        // Z the safety VC finds (p0=-1, p1=4) and would reject a correct proof. A
        // marking is a vector of token counts, so the VCs assert M >= 0.
        var t = Transition.builder("t").inputs(In.one(CONS_P0)).outputs(Out.place(CONS_P1)).build();
        var flat = NetFlattener.flatten(PetriNet.builder("conservedPair").transitions(t).build(),
            Set.of(), EnvironmentAnalysisMode.ignore());
        var m0 = MarkingState.builder().tokens(CONS_P0, 3).build();
        String cert = certificate(flat.placeCount(),
            "(= (+ " + v(flat, CONS_P0) + " " + v(flat, CONS_P1) + ") 3)");
        var result = CertificateChecker.check(cert, flat, m0, SmtProperty.placeBound(CONS_P1, 3),
            Set.of(), List.of(), solver(), Duration.ofSeconds(10));
        assertInstanceOf(CertificateChecker.Result.Passed.class, result,
            "a certificate inductive and safe over N^P must not be rejected: " + result);
    }

    // === Unavailable outcomes (no solver needed) ===

    @Test
    void nullCertificate_unavailable() {
        var flat = asymmetricFlatNet();
        var result = CertificateChecker.check(null, flat, initialMarking(),
            SmtProperty.placeBound(B, 1), Set.of(), List.of(), null, Duration.ofSeconds(1));
        var unavailable = assertInstanceOf(CertificateChecker.Result.Unavailable.class, result);
        assertTrue(unavailable.reason().contains("no inductive invariant"), unavailable.reason());
    }

    @Test
    void certificateWithoutReachable_unavailable() {
        var flat = asymmetricFlatNet();
        var result = CertificateChecker.check("(define-fun Error () Bool false)", flat,
            initialMarking(), SmtProperty.placeBound(B, 1), Set.of(), List.of(), null,
            Duration.ofSeconds(1));
        var unavailable = assertInstanceOf(CertificateChecker.Result.Unavailable.class, result,
            "a block without a Reachable definition must not certify: " + result);
        assertEquals("certificate does not define Reachable", unavailable.reason());
    }

    @Test
    void invariantShapeMismatch_unavailable() {
        var flat = asymmetricFlatNet();
        var wrongShape = new PInvariant(new int[] {1, 1, 1}, 1, Set.of(0, 1, 2));
        var result = CertificateChecker.check(certificate(flat.placeCount(), "true"), flat,
            initialMarking(), SmtProperty.placeBound(B, 1), Set.of(), List.of(wrongShape), null,
            Duration.ofSeconds(1));
        var unavailable = assertInstanceOf(CertificateChecker.Result.Unavailable.class, result);
        assertTrue(unavailable.reason().contains("weights"), unavailable.reason());
    }

    // === Reply parsing (no solver needed) ===

    @Test
    void witness_readsModelValues() {
        var flat = asymmetricFlatNet();
        String model = "sat\n(\n  (define-fun m1 () Int\n    (- 1))\n  (define-fun m0 () Int\n    2)\n)";
        assertEquals(flat.places().get(0).name() + "=2, " + flat.places().get(1).name() + "=-1",
            CertificateChecker.witness(model, flat));
        assertNull(CertificateChecker.witness("unknown", flat));
    }

    @Test
    void reasonUnknown_readsInfoReply() {
        assertEquals("timeout", CertificateChecker.reasonUnknown("unknown\n(:reason-unknown \"timeout\")"));
        assertNull(CertificateChecker.reasonUnknown("unknown"));
    }
}
