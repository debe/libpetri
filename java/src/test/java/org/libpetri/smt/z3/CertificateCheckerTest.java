package org.libpetri.smt.z3;

import com.microsoft.z3.*;
import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.smt.SmtProperty;
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
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for {@link CertificateChecker} with hand-built certificates.
 *
 * <p>All tests construct Z3 ASTs directly, so every test is gated on native Z3
 * availability (they run in CI). The certificates are built by hand rather than
 * taken from Spacer so that corrupted certificates — and both de Bruijn
 * variable orderings — can be exercised deterministically.
 *
 * <p>The fixture net is deliberately <b>asymmetric</b>: one transition consumes
 * TWO tokens from A and produces ONE token into B (initial marking A=2), so the
 * exact invariant is {@code A + 2*B = 2}. Swapping the roles of A and B changes
 * the formula's truth values — a reversed bound-variable substitution cannot
 * pass unnoticed.
 */
class CertificateCheckerTest {

    private static final Place<String> A = Place.of("CertA", String.class);
    private static final Place<String> B = Place.of("CertB", String.class);

    static boolean z3Available() {
        try {
            new Context().close();
            return true;
        } catch (UnsatisfiedLinkError | NoClassDefFoundError _) {
            return false;
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

    private static FuncDecl<BoolSort> reachableDecl(Context ctx, int P) {
        Sort[] sorts = new Sort[P];
        for (int i = 0; i < P; i++) {
            sorts[i] = ctx.getIntSort();
        }
        return ctx.mkFuncDecl(ctx.mkSymbol("Reachable"), sorts, ctx.getBoolSort());
    }

    /**
     * Builds {@code forall vars. Reachable(args) <op> phi}.
     *
     * <p>{@code reversedHead} selects the de Bruijn arrangement of the head
     * arguments: {@code false} uses the encoder's convention (argument j is the
     * bound variable with index P-1-j, i.e. declaration order), {@code true}
     * uses the opposite (argument j has index j). Both describe the same
     * quantified statement differently — a checker that assumed one fixed
     * ordering instead of reading the head would break on one of them.
     *
     * <p>{@code phi} receives the head-argument array indexed by PLACE position,
     * so invariants are written per-place with no de Bruijn arithmetic.
     */
    private static BoolExpr certificate(
            Context ctx, FuncDecl<BoolSort> reachable, int P,
            boolean reversedHead, boolean implies,
            Function<Expr<IntSort>[], BoolExpr> phi
    ) {
        Sort[] sorts = new Sort[P];
        Symbol[] names = new Symbol[P];
        Expr<IntSort>[] headArgs = new Expr[P];
        for (int j = 0; j < P; j++) {
            sorts[j] = ctx.getIntSort();
            names[j] = ctx.mkSymbol("v" + j);
            int deBruijn = reversedHead ? j : P - 1 - j;
            headArgs[j] = (Expr<IntSort>) ctx.mkBound(deBruijn, ctx.getIntSort());
        }
        BoolExpr head = (BoolExpr) reachable.apply(headArgs);
        BoolExpr body = implies
            ? ctx.mkImplies(head, phi.apply(headArgs))
            : ctx.mkEq(head, phi.apply(headArgs));
        return ctx.mkForall(sorts, names, body, 1, null, null, null, null);
    }

    /** The exact inductive invariant of the fixture: A + 2*B = 2, A >= 0, B >= 0. */
    private static Function<Expr<IntSort>[], BoolExpr> exactInvariant(Context ctx, FlatNet flat) {
        int ia = flat.indexOf(A);
        int ib = flat.indexOf(B);
        return v -> ctx.mkAnd(
            ctx.mkEq(ctx.mkAdd(v[ia], ctx.mkMul(ctx.mkInt(2), v[ib])), ctx.mkInt(2)),
            ctx.mkGe(v[ia], ctx.mkInt(0)),
            ctx.mkGe(v[ib], ctx.mkInt(0)));
    }

    private static CertificateChecker.Result check(
            Context ctx, Expr<?> answer, FuncDecl<BoolSort> decl, FlatNet flat
    ) {
        return CertificateChecker.check(
            ctx, answer, decl, flat, initialMarking(),
            SmtProperty.placeBound(B, 1), Set.of(), List.of(), Duration.ofSeconds(10));
    }

    @Test
    @EnabledIf("z3Available")
    void validCertificate_encoderVarOrder_passes() {
        var flat = asymmetricFlatNet();
        try (var ctx = new Context()) {
            var decl = reachableDecl(ctx, flat.placeCount());
            var answer = certificate(ctx, decl, flat.placeCount(),
                /* reversedHead */ false, /* implies */ false, exactInvariant(ctx, flat));
            var result = check(ctx, answer, decl, flat);
            assertInstanceOf(CertificateChecker.Result.Passed.class, result,
                "exact invariant must pass all three VCs: " + result);
        }
    }

    @Test
    @EnabledIf("z3Available")
    void validCertificate_reversedVarOrder_passes() {
        // Same statement, opposite de Bruijn arrangement. The checker must recover
        // the variable->place mapping from the Reachable head, not assume an order.
        var flat = asymmetricFlatNet();
        try (var ctx = new Context()) {
            var decl = reachableDecl(ctx, flat.placeCount());
            var answer = certificate(ctx, decl, flat.placeCount(),
                /* reversedHead */ true, /* implies */ false, exactInvariant(ctx, flat));
            var result = check(ctx, answer, decl, flat);
            assertInstanceOf(CertificateChecker.Result.Passed.class, result,
                "reversed bound-variable order must decode identically: " + result);
        }
    }

    @Test
    @EnabledIf("z3Available")
    void swappedInvariant_failsInit() {
        // 2*A + B = 2 — the roles of A and B swapped, which is exactly what a
        // reversed substitution would produce from the correct certificate. On the
        // asymmetric fixture it already fails VC1: I(M0) with M0=(A=2,B=0) gives 4 != 2.
        var flat = asymmetricFlatNet();
        int ia = flat.indexOf(A);
        int ib = flat.indexOf(B);
        try (var ctx = new Context()) {
            var decl = reachableDecl(ctx, flat.placeCount());
            var answer = certificate(ctx, decl, flat.placeCount(), false, false,
                v -> ctx.mkAnd(
                    ctx.mkEq(ctx.mkAdd(ctx.mkMul(ctx.mkInt(2), v[ia]), v[ib]), ctx.mkInt(2)),
                    ctx.mkGe(v[ia], ctx.mkInt(0)),
                    ctx.mkGe(v[ib], ctx.mkInt(0))));
            var result = check(ctx, answer, decl, flat);
            var failed = assertInstanceOf(CertificateChecker.Result.Failed.class, result);
            assertEquals(CertificateChecker.Vc.INIT, failed.vc(),
                "swapped roles must be caught at initiation: " + failed.detail());
        }
    }

    @Test
    @EnabledIf("z3Available")
    void trueInvariant_reachableBadState_failsSafety() {
        // Corrupted certificate: I = true. VC1 and VC2 hold trivially, but the bad
        // state B > 0 is genuinely reachable ((A=0,B=1)), so I AND Bad is SAT.
        var flat = asymmetricFlatNet();
        try (var ctx = new Context()) {
            var decl = reachableDecl(ctx, flat.placeCount());
            var answer = certificate(ctx, decl, flat.placeCount(), false, false,
                _ -> ctx.mkTrue());
            var result = CertificateChecker.check(
                ctx, answer, decl, flat, initialMarking(),
                SmtProperty.placeBound(B, 0), Set.of(), List.of(), Duration.ofSeconds(10));
            var failed = assertInstanceOf(CertificateChecker.Result.Failed.class, result);
            assertEquals(CertificateChecker.Vc.SAFETY, failed.vc(),
                "true-invariant corruption must be caught at the safety VC: " + failed.detail());
        }
    }

    @Test
    @EnabledIf("z3Available")
    void weakInvariant_failsConsecution() {
        // I = (B <= 0) holds initially but is not preserved: firing the transition
        // moves (A=2,B=0) to (A=0,B=1).
        var flat = asymmetricFlatNet();
        int ib = flat.indexOf(B);
        try (var ctx = new Context()) {
            var decl = reachableDecl(ctx, flat.placeCount());
            var answer = certificate(ctx, decl, flat.placeCount(), false, false,
                v -> ctx.mkLe(v[ib], ctx.mkInt(0)));
            var result = check(ctx, answer, decl, flat);
            var failed = assertInstanceOf(CertificateChecker.Result.Failed.class, result);
            assertEquals(CertificateChecker.Vc.CONSECUTION, failed.vc(),
                "non-inductive invariant must be caught at consecution: " + failed.detail());
        }
    }

    @Test
    @EnabledIf("z3Available")
    void impliesShapedCertificate_passes() {
        // Spacer also emits `forall v. Reachable(v) => phi`.
        var flat = asymmetricFlatNet();
        try (var ctx = new Context()) {
            var decl = reachableDecl(ctx, flat.placeCount());
            var answer = certificate(ctx, decl, flat.placeCount(),
                false, /* implies */ true, exactInvariant(ctx, flat));
            var result = check(ctx, answer, decl, flat);
            assertInstanceOf(CertificateChecker.Result.Passed.class, result,
                "implies-shaped definition must be accepted: " + result);
        }
    }

    @Test
    @EnabledIf("z3Available")
    void conjunctionWrappedCertificate_passes() {
        // With multiple relations the answer is a conjunction of definitions; the
        // Reachable one must be found among them.
        var flat = asymmetricFlatNet();
        try (var ctx = new Context()) {
            var decl = reachableDecl(ctx, flat.placeCount());
            var reachableDef = certificate(ctx, decl, flat.placeCount(),
                false, false, exactInvariant(ctx, flat));
            var errorDef = ctx.mkNot(ctx.mkBoolConst("Error"));
            var answer = ctx.mkAnd(errorDef, reachableDef);
            var result = check(ctx, answer, decl, flat);
            assertInstanceOf(CertificateChecker.Result.Passed.class, result,
                "Reachable definition inside a conjunction must be found: " + result);
        }
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
        int ie = flat.indexOf(e);
        int is = flat.indexOf(sPlace);
        try (var ctx = new Context()) {
            var decl = reachableDecl(ctx, flat.placeCount());
            var answer = certificate(ctx, decl, flat.placeCount(), false, false,
                v -> ctx.mkAnd(
                    ctx.mkLe(v[ie], ctx.mkInt(0)),
                    ctx.mkGe(v[is], ctx.mkInt(0))));
            var result = CertificateChecker.check(
                ctx, answer, decl, flat, MarkingState.empty(),
                SmtProperty.placeBound(sPlace, 5), Set.of(), List.of(), Duration.ofSeconds(10));
            var failed = assertInstanceOf(CertificateChecker.Result.Failed.class, result);
            assertEquals(CertificateChecker.Vc.CONSECUTION, failed.vc(),
                "the injection step must be part of the checked relation: " + failed.detail());
        }
    }

    // === Candidate strengthening: R' = I AND validated P-invariant equalities ===

    private static final Place<String> CYC_A = Place.of("CycA", String.class);
    private static final Place<String> CYC_B = Place.of("CycB", String.class);

    /** Conservation cycle A <-> B with one token: the exact law is A + B = 1. */
    private static FlatNet cycleFlatNet() {
        var t1 = Transition.builder("AtoB")
            .inputs(In.one(CYC_A))
            .outputs(Out.place(CYC_B))
            .build();
        var t2 = Transition.builder("BtoA")
            .inputs(In.one(CYC_B))
            .outputs(Out.place(CYC_A))
            .build();
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
        int ib = flat.indexOf(CYC_B);
        var m0 = MarkingState.builder().tokens(CYC_A, 1).build();
        var invariants = PInvariantComputer.compute(IncidenceMatrix.from(flat), flat, m0);
        assertFalse(invariants.isEmpty(), "the cycle net must have the conservation law A+B=1");

        try (var ctx = new Context()) {
            var decl = reachableDecl(ctx, flat.placeCount());
            var answer = certificate(ctx, decl, flat.placeCount(), false, false,
                v -> ctx.mkLe(v[ib], ctx.mkInt(1)));

            var bare = CertificateChecker.check(
                ctx, answer, decl, flat, m0,
                SmtProperty.placeBound(CYC_B, 1), Set.of(), List.of(), Duration.ofSeconds(10));
            var bareFailed = assertInstanceOf(CertificateChecker.Result.Failed.class, bare,
                "without the folded-in law the certificate is not bare-inductive: " + bare);
            assertEquals(CertificateChecker.Vc.CONSECUTION, bareFailed.vc(), bareFailed.detail());

            var strengthened = CertificateChecker.check(
                ctx, answer, decl, flat, m0,
                SmtProperty.placeBound(CYC_B, 1), Set.of(), invariants, Duration.ofSeconds(10));
            assertInstanceOf(CertificateChecker.Result.Passed.class, strengthened,
                "R' = I AND (A+B=1) must validate the strengthening-dependent certificate: "
                    + strengthened);
        }
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

        try (var ctx = new Context()) {
            var decl = reachableDecl(ctx, flat.placeCount());
            var answer = certificate(ctx, decl, flat.placeCount(), false, false,
                _ -> ctx.mkTrue());
            var result = CertificateChecker.check(
                ctx, answer, decl, flat, m0,
                SmtProperty.placeBound(CYC_B, 1), Set.of(), List.of(poisoned),
                Duration.ofSeconds(10));
            var failed = assertInstanceOf(CertificateChecker.Result.Failed.class, result);
            assertEquals(CertificateChecker.Vc.INIT, failed.vc(),
                "a wrong constant must fail initiation: " + failed.detail());
        }
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

        try (var ctx = new Context()) {
            var decl = reachableDecl(ctx, flat.placeCount());
            var answer = certificate(ctx, decl, flat.placeCount(), false, false,
                _ -> ctx.mkTrue());
            var result = CertificateChecker.check(
                ctx, answer, decl, flat, m0,
                SmtProperty.placeBound(CYC_B, 1), Set.of(), List.of(poisoned),
                Duration.ofSeconds(10));
            var failed = assertInstanceOf(CertificateChecker.Result.Failed.class, result);
            assertEquals(CertificateChecker.Vc.CONSECUTION, failed.vc(),
                "a non-preserved equality must fail consecution: " + failed.detail());
        }
    }

    // === Marking domain (N^P) and the ground answer shape ===

    private static final Place<String> CONS_P0 = Place.of("p0", String.class);
    private static final Place<String> CONS_P1 = Place.of("p1", String.class);

    /** {@code p0(3); t: one(p0) -> p1} — the conservedPair fixture; law p0 + p1 = 3. */
    private static FlatNet conservedPairFlatNet() {
        var t = Transition.builder("t")
            .inputs(In.one(CONS_P0))
            .outputs(Out.place(CONS_P1))
            .build();
        var net = PetriNet.builder("conservedPair").transitions(t).build();
        return NetFlattener.flatten(net, Set.of(), EnvironmentAnalysisMode.ignore());
    }

    @Test
    @EnabledIf("z3Available")
    void certificateInductiveOverNaturalsOnly_passes() {
        // p0 + p1 = 3 bounds p1 by 3 only because neither place can go negative:
        // over Z the safety VC finds (p0=-1, p1=4) and would reject a correct
        // proof. A marking is a vector of token counts, so the VCs must assert
        // M >= 0 on the free current marking too.
        var flat = conservedPairFlatNet();
        int i0 = flat.indexOf(CONS_P0);
        int i1 = flat.indexOf(CONS_P1);
        var m0 = MarkingState.builder().tokens(CONS_P0, 3).build();
        try (var ctx = new Context()) {
            var decl = reachableDecl(ctx, flat.placeCount());
            var answer = certificate(ctx, decl, flat.placeCount(), false, false,
                v -> ctx.mkEq(ctx.mkAdd(v[i0], v[i1]), ctx.mkInt(3)));
            var result = CertificateChecker.check(
                ctx, answer, decl, flat, m0,
                SmtProperty.placeBound(CONS_P1, 3), Set.of(), List.of(), Duration.ofSeconds(10));
            assertInstanceOf(CertificateChecker.Result.Passed.class, result,
                "a certificate inductive and safe over N^P must not be rejected: " + result);
        }
    }

    @Test
    @EnabledIf("z3Available")
    void groundCertificate_unquantifiedHead_passes() {
        // Spacer also emits the definition WITHOUT a quantifier — `Reachable(7, 9)
        // = phi(7, 9)`, argument j standing for place j. The head's argument terms
        // are substituted positionally; discarding the shape would throw away a
        // valid proof.
        var flat = conservedPairFlatNet();
        int P = flat.placeCount();
        int i0 = flat.indexOf(CONS_P0);
        int i1 = flat.indexOf(CONS_P1);
        var m0 = MarkingState.builder().tokens(CONS_P0, 3).build();
        try (var ctx = new Context()) {
            var decl = reachableDecl(ctx, P);
            Expr<IntSort>[] args = new Expr[P];
            args[i0] = ctx.mkInt(7);
            args[i1] = ctx.mkInt(9);
            BoolExpr head = (BoolExpr) decl.apply(args);
            BoolExpr answer = ctx.mkEq(head,
                ctx.mkEq(ctx.mkAdd(args[i0], args[i1]), ctx.mkInt(3)));

            var result = CertificateChecker.check(
                ctx, answer, decl, flat, m0,
                SmtProperty.placeBound(CONS_P1, 3), Set.of(), List.of(), Duration.ofSeconds(10));
            assertInstanceOf(CertificateChecker.Result.Passed.class, result,
                "a ground Reachable definition is a certificate too: " + result);
        }
    }

    @Test
    @EnabledIf("z3Available")
    void nullAnswer_unavailable() {
        var flat = asymmetricFlatNet();
        try (var ctx = new Context()) {
            var decl = reachableDecl(ctx, flat.placeCount());
            var result = check(ctx, null, decl, flat);
            assertInstanceOf(CertificateChecker.Result.Unavailable.class, result,
                "a missing answer must not certify: " + result);
        }
    }

    @Test
    @EnabledIf("z3Available")
    void unparseableAnswer_unavailable() {
        var flat = asymmetricFlatNet();
        try (var ctx = new Context()) {
            var decl = reachableDecl(ctx, flat.placeCount());
            var result = check(ctx, ctx.mkTrue(), decl, flat);
            var unavailable = assertInstanceOf(CertificateChecker.Result.Unavailable.class, result,
                "an answer without a Reachable definition must not certify: " + result);
            assertTrue(unavailable.reason().contains("Reachable"), unavailable.reason());
        }
    }
}
