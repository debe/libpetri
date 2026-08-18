package org.libpetri.smt.z3;

import com.microsoft.z3.*;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.invariant.PInvariant;

import java.time.Duration;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

/**
 * Independent re-validation of an IC3/PDR certificate produced by Z3's Spacer engine.
 *
 * <p>A "proven" Spacer verdict rests on the inductive invariant {@code I} that
 * {@code Fixedpoint.getAnswer()} returns for the {@code Reachable} relation. This
 * checker re-derives the three verification conditions of an inductive safety
 * proof with a plain {@link Solver} — deliberately outside the Fixedpoint engine
 * that produced the certificate:
 *
 * <ol>
 *   <li><b>VC1 (init)</b>: {@code NOT I(M0)} is UNSAT — the invariant holds initially.</li>
 *   <li><b>VC2 (consecution)</b>: {@code I(M) AND M >= 0 AND T(M,M') AND NOT I(M')}
 *       is UNSAT — the invariant is preserved by every step of the
 *       {@linkplain SmtEncoder#encodeStepRelation unstrengthened} step relation.</li>
 *   <li><b>VC3 (safety)</b>: {@code I(M) AND M >= 0 AND Bad(M)} is UNSAT — the
 *       invariant excludes every property-violating marking.</li>
 * </ol>
 *
 * <p>The {@code M >= 0} conjunct is the state domain: markings are token counts,
 * so the VCs must range over N^P. The step relation constrains only {@code M'},
 * so without it a certificate inductive over N^P would be refuted by a negative
 * predecessor in Z^P.
 *
 * <p><b>Candidate:</b> the checked invariant is {@code R' := I AND invs}, where
 * {@code invs} conjoins the validated P-invariant equalities
 * {@code y*M = y*M0}. Spacer's {@code I} may be inductive only <em>relative</em>
 * to the strengthening conjuncts the CHC encoding adds to the rule bodies
 * (e.g. {@code I = NOT(p >= k)} on a conservation cycle), so checking {@code I}
 * alone against the bare step relation would reject genuine certificates.
 * Folding the equalities into the candidate — instead of into {@code T} — keeps
 * the layer independent: VC1 re-proves each equality at {@code M0} and VC2
 * re-proves its preservation under the unstrengthened relation, so a
 * numerically wrong invariant fails VC1 or VC2 here regardless of what the
 * upstream computation claimed.
 *
 * <p><b>Independence:</b> VC2 uses the step relation WITHOUT the P-invariant
 * strengthening conjuncts that the CHC encoding adds to the transition-rule
 * bodies. Nothing produced by the P-invariant computation is assumed: what is
 * folded into the candidate is proven from scratch by the VCs themselves.
 *
 * <p><b>Certificate extraction:</b> {@code getAnswer()} typically yields a
 * universally quantified definition — possibly inside a conjunction of
 * per-relation definitions — whose body relates {@code Reachable(vars)} to the
 * invariant formula via {@code =}, {@code iff}, {@code =>}, or the clausal
 * {@code (or (not (Reachable vars)) ...)} rendering. The bound-variable-to-place
 * mapping is recovered from the argument positions of the {@code Reachable}
 * application itself (Z3 de Bruijn indices number bound variables from the
 * innermost/last one), so the checker is correct for any variable ordering
 * Spacer emits. The ground shape — {@code Reachable(1, 0) = phi} with no
 * quantifier — is accepted too, by substituting the head's argument terms
 * positionally. Anything unrecognized yields {@link Result.Unavailable} — never
 * a false PASSED.
 *
 * <p>This class never throws: every Z3 or parsing failure becomes a
 * {@link Result.Unavailable}, which the caller maps to an UNKNOWN verdict.
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
         * The check could not run: missing or unparseable Spacer answer, or a Z3
         * failure. Treated like a failure by the caller (the verdict is not
         * certified), but no specific VC is implicated.
         *
         * @param reason why the certificate could not be checked
         */
        record Unavailable(String reason) implements Result {}
    }

    /**
     * Checks the Spacer certificate against the three verification conditions.
     *
     * @param ctx            the Z3 context the answer belongs to (must still be open)
     * @param answer         the raw {@code Fixedpoint.getAnswer()} expression (may be null)
     * @param reachableDecl  the {@code Reachable} relation declaration from the encoding
     * @param flatNet        the flattened net the CHC system was encoded from
     * @param initialMarking the initial marking (VC1)
     * @param property       the verified property (VC3 uses its violation predicate)
     * @param sinkPlaces     expected terminal places (part of the deadlock violation predicate)
     * @param invariants     validated P-invariants folded into the candidate
     *                       {@code R' = I AND invs} and re-proven by VC1/VC2 (not trusted)
     * @param timeout        per-VC solver timeout (null or zero = no limit)
     * @return the check outcome; never throws
     */
    public static Result check(
            Context ctx,
            Expr<?> answer,
            FuncDecl<BoolSort> reachableDecl,
            FlatNet flatNet,
            MarkingState initialMarking,
            SmtProperty property,
            Set<Place<?>> sinkPlaces,
            List<PInvariant> invariants,
            Duration timeout
    ) {
        try {
            return doCheck(ctx, answer, reachableDecl, flatNet, initialMarking, property, sinkPlaces, invariants, timeout);
        } catch (Z3Exception e) {
            return new Result.Unavailable("Z3 exception during certificate check: " + e.getMessage());
        } catch (RuntimeException e) {
            return new Result.Unavailable("unexpected error during certificate check: " + e);
        }
    }

    private static Result doCheck(
            Context ctx,
            Expr<?> answer,
            FuncDecl<BoolSort> reachableDecl,
            FlatNet flatNet,
            MarkingState initialMarking,
            SmtProperty property,
            Set<Place<?>> sinkPlaces,
            List<PInvariant> invariants,
            Duration timeout
    ) {
        if (answer == null) {
            return new Result.Unavailable("Spacer produced no certificate (getAnswer() returned null)");
        }
        int P = flatNet.placeCount();

        ParsedCertificate cert = parse(ctx, answer, reachableDecl, P);
        if (cert == null) {
            return new Result.Unavailable(
                "could not extract the Reachable invariant from the Spacer answer: " + abbreviate(answer));
        }

        // Fresh integer constants standing for an arbitrary current/next marking.
        Expr<IntSort>[] cur = new Expr[P];
        Expr<IntSort>[] next = new Expr[P];
        for (int i = 0; i < P; i++) {
            cur[i] = ctx.mkIntConst("cert_m" + i);
            next[i] = ctx.mkIntConst("cert_mp" + i);
        }

        // Candidate R'(M) = I(M) AND invs(M): Spacer's invariant conjoined with the
        // validated P-invariant equalities. The equalities are RE-PROVEN here — VC1
        // establishes them at M0, VC2 their preservation under the unstrengthened
        // step relation — never assumed.
        BoolExpr candCur = ctx.mkAnd(
            cert.instantiate(ctx, cur, "cur"),
            SmtEncoder.encodeInvariantConstraints(ctx, invariants, cur, P));
        BoolExpr candNext = ctx.mkAnd(
            cert.instantiate(ctx, next, "next"),
            SmtEncoder.encodeInvariantConstraints(ctx, invariants, next, P));

        // VC1 (init): R'(M0) — assert NOT R'(M0), require UNSAT.
        Expr<IntSort>[] m0 = new Expr[P];
        for (int i = 0; i < P; i++) {
            m0[i] = ctx.mkInt(initialMarking.tokens(flatNet.places().get(i)));
        }
        BoolExpr candInit = ctx.mkAnd(
            cert.instantiate(ctx, m0, "init"),
            SmtEncoder.encodeInvariantConstraints(ctx, invariants, m0, P));
        Result vc1 = checkUnsat(ctx, Vc.INIT, timeout, flatNet, cur, ctx.mkNot(candInit));
        if (vc1 != null) {
            return vc1;
        }

        // Domain constraint for VC2/VC3: a marking is a vector of token COUNTS, so
        // the free constants stand for a state in N^P, not Z^P. The step relation
        // only constrains M' (encodeNonNegativity on mPrimeVars), so without this
        // conjunct a certificate that is inductive over N^P — the only claim it
        // makes — is refuted by a negative "predecessor" and a correct PROVEN is
        // downgraded.
        BoolExpr nonNegCur = SmtEncoder.encodeNonNegativity(ctx, cur, P);

        // VC2 (consecution): R'(M) AND M >= 0 AND T(M,M') AND NOT R'(M'), with T the
        // UNSTRENGTHENED step relation (no P-invariant conjuncts).
        BoolExpr step = SmtEncoder.encodeStepRelation(ctx, flatNet, cur, next);
        Result vc2 = checkUnsat(ctx, Vc.CONSECUTION, timeout, flatNet, cur,
            candCur, nonNegCur, step, ctx.mkNot(candNext));
        if (vc2 != null) {
            return vc2;
        }

        // VC3 (safety): R'(M) AND M >= 0 AND Bad(M), same violation predicate as the
        // Error rule.
        BoolExpr bad = SmtEncoder.encodePropertyViolation(ctx, flatNet, property, sinkPlaces, cur, P);
        Result vc3 = checkUnsat(ctx, Vc.SAFETY, timeout, flatNet, cur, candCur, nonNegCur, bad);
        if (vc3 != null) {
            return vc3;
        }

        return new Result.Passed();
    }

    /**
     * Checks one VC with a plain solver. Returns {@code null} on UNSAT (the VC
     * holds) or a {@link Result.Failed} naming the VC otherwise.
     */
    private static Result checkUnsat(
            Context ctx, Vc vc, Duration timeout, FlatNet flatNet,
            Expr<IntSort>[] cur, BoolExpr... assertions
    ) {
        Solver solver = ctx.mkSolver();
        if (timeout != null && !timeout.isZero()) {
            Params params = ctx.mkParams();
            params.add("timeout", (int) Math.min(timeout.toMillis(), Integer.MAX_VALUE));
            solver.setParameters(params);
        }
        solver.add(assertions);
        Status status = solver.check();
        if (status == Status.UNSATISFIABLE) {
            return null;
        }
        String detail = "solver returned " + status;
        if (status == Status.SATISFIABLE) {
            String witness = describeWitness(solver, flatNet, cur);
            if (witness != null) {
                detail += " (witness: " + witness + ")";
            }
        } else {
            try {
                detail += " (" + solver.getReasonUnknown() + ")";
            } catch (Z3Exception _) {
                // Reason not available; the plain status is enough.
            }
        }
        return new Result.Failed(vc, detail);
    }

    /** Compact witness marking (place=value pairs) from a SAT model; null if unavailable. */
    private static String describeWitness(Solver solver, FlatNet flatNet, Expr<IntSort>[] cur) {
        try {
            Model model = solver.getModel();
            var sb = new StringBuilder();
            for (int i = 0; i < cur.length; i++) {
                Expr<?> value = model.evaluate(cur[i], false);
                if (value == null || !value.isIntNum()) {
                    continue;
                }
                if (!sb.isEmpty()) {
                    sb.append(", ");
                }
                sb.append(flatNet.places().get(i).name()).append("=").append(value);
                if (sb.length() > 160) {
                    sb.append(", ...");
                    break;
                }
            }
            return sb.isEmpty() ? null : sb.toString();
        } catch (Z3Exception _) {
            return null;
        }
    }

    // === Certificate extraction ===

    /**
     * The invariant formula with its quantifier's bound variables still in de
     * Bruijn form, plus the mapping from de Bruijn index to place index
     * (recovered from the {@code Reachable(vars)} argument positions).
     *
     * @param phi             invariant body (bound variables unresolved); null means {@code true}
     * @param numBound        number of bound variables of the enclosing quantifier
     *                        (0 for the ground shape)
     * @param varIndexToPlace de Bruijn index -&gt; place index; -1 for a bound
     *                        variable that does not appear in the Reachable head
     * @param groundArgs      the head's argument terms for the ground shape
     *                        (argument j is place j); null when {@code numBound > 0}
     */
    private record ParsedCertificate(
        Expr<BoolSort> phi, int numBound, int[] varIndexToPlace, Expr<?>[] groundArgs
    ) {

        /**
         * Instantiates the invariant at the given marking vector. Z3's
         * {@code substituteVars} replaces the variable with de Bruijn index
         * {@code i} by {@code to[i]}, and index 0 is the LAST bound variable —
         * the mapping recovered from the Reachable head absorbs that ordering,
         * so no positional assumption is made here. In the ground shape the
         * head's argument terms are replaced positionally instead (one
         * simultaneous substitution, so no cascading).
         */
        BoolExpr instantiate(Context ctx, Expr<IntSort>[] marking, String tag) {
            if (phi == null) {
                return ctx.mkTrue();
            }
            if (numBound == 0) {
                return groundArgs == null || groundArgs.length == 0
                    ? (BoolExpr) phi
                    : (BoolExpr) phi.substitute(groundArgs, marking);
            }
            Expr<?>[] to = new Expr[numBound];
            for (int i = 0; i < numBound; i++) {
                to[i] = varIndexToPlace[i] >= 0
                    ? marking[varIndexToPlace[i]]
                    // A bound variable that never occurs in the Reachable head:
                    // substitute a fresh constant. Solver constants are implicitly
                    // existential and every VC asserts a negated claim, so this
                    // still checks the original universal statement.
                    : ctx.mkIntConst("cert_free_" + tag + "_" + i);
            }
            return (BoolExpr) phi.substituteVars(to);
        }
    }

    /** Unpacks the Fixedpoint answer; null if no Reachable definition is recognized. */
    private static ParsedCertificate parse(
            Context ctx, Expr<?> answer, FuncDecl<BoolSort> reachableDecl, int P
    ) {
        // The answer may be a single definition or a conjunction of per-relation
        // definitions (e.g. Reachable and Error).
        Expr<?>[] candidates = answer.isAnd() ? answer.getArgs() : new Expr<?>[] {answer};
        for (Expr<?> candidate : candidates) {
            ParsedCertificate parsed;
            if (candidate instanceof Quantifier q && q.isUniversal()) {
                parsed = parseDefinition(ctx, q.getBody(), q.getNumBound(), reachableDecl, P);
            } else {
                parsed = parseDefinition(ctx, candidate, 0, reachableDecl, P);
            }
            if (parsed != null) {
                return parsed;
            }
        }
        return null;
    }

    /** Recognizes one definition body shape; null if it does not define Reachable. */
    private static ParsedCertificate parseDefinition(
            Context ctx, Expr<?> body, int numBound, FuncDecl<BoolSort> reachableDecl, int P
    ) {
        if (!body.isApp()) {
            return null;
        }

        // Shape 1: Reachable(vars) on either side of =, iff, or => — Spacer emits
        // all three across versions. The other side is the invariant formula. For
        // =>, only `Reachable(vars) => phi` is a certificate (phi over-approximates
        // the reachable states); `phi => Reachable(vars)` is an under-approximation
        // and is rejected.
        if ((body.isEq() || body.isIff() || body.isImplies()) && body.getNumArgs() == 2) {
            Expr<?> lhs = body.getArgs()[0];
            Expr<?> rhs = body.getArgs()[1];
            if (isReachableApp(lhs, reachableDecl, P)) {
                return fromHeadAndPhi(lhs, rhs, numBound);
            }
            if (!body.isImplies() && isReachableApp(rhs, reachableDecl, P)) {
                return fromHeadAndPhi(rhs, lhs, numBound);
            }
            return null;
        }

        // Shape 2: clausal implication (or ... (not (Reachable vars)) ...) — the
        // remaining literals form the invariant.
        if (body.isOr()) {
            Expr<?>[] args = body.getArgs();
            for (int i = 0; i < args.length; i++) {
                Expr<?> a = args[i];
                if (a.isNot() && a.getNumArgs() == 1 && isReachableApp(a.getArgs()[0], reachableDecl, P)) {
                    Expr<?>[] rest = new Expr<?>[args.length - 1];
                    int k = 0;
                    for (int j = 0; j < args.length; j++) {
                        if (j != i) {
                            rest[k++] = args[j];
                        }
                    }
                    Expr<?> phi = rest.length == 1
                        ? rest[0]
                        : ctx.mkOr(Arrays.copyOf(rest, rest.length, BoolExpr[].class));
                    return fromHeadAndPhi(a.getArgs()[0], phi, numBound);
                }
            }
            return null;
        }

        // Shape 3: bare `forall vars. Reachable(vars)` — the trivial invariant `true`.
        if (isReachableApp(body, reachableDecl, P)) {
            return fromHeadAndPhi(body, null, numBound);
        }
        return null;
    }

    /**
     * Builds the de-Bruijn-index-to-place mapping from the argument positions of
     * the {@code Reachable} application: argument {@code j} is place {@code j},
     * and its de Bruijn index tells which bound variable stands for it. Rejects
     * (returns null) heads whose arguments are not plain distinct bound
     * variables — an inverted mapping cannot be recovered from those.
     *
     * <p>Without an enclosing quantifier ({@code numBound == 0}) the head is
     * ground, e.g. {@code Reachable(1, 0)}: the argument terms themselves are
     * kept and substituted positionally at instantiation. Discarding this shape
     * would throw away a valid proof.
     */
    private static ParsedCertificate fromHeadAndPhi(Expr<?> head, Expr<?> phi, int numBound) {
        Expr<?>[] args = head.getArgs();
        @SuppressWarnings("unchecked")
        Expr<BoolSort> typedPhi = (Expr<BoolSort>) phi;
        if (numBound == 0) {
            for (Expr<?> arg : args) {
                if (arg.isVar()) {
                    return null; // a de Bruijn variable with no quantifier to bind it
                }
            }
            return new ParsedCertificate(typedPhi, 0, new int[0], args.clone());
        }
        int[] varIndexToPlace = new int[numBound];
        Arrays.fill(varIndexToPlace, -1);
        for (int j = 0; j < args.length; j++) {
            Expr<?> arg = args[j];
            if (!arg.isVar()) {
                return null;
            }
            int deBruijn = arg.getIndex();
            if (deBruijn < 0 || deBruijn >= numBound || varIndexToPlace[deBruijn] != -1) {
                return null;
            }
            varIndexToPlace[deBruijn] = j;
        }
        return new ParsedCertificate(typedPhi, numBound, varIndexToPlace, null);
    }

    /** Whether {@code e} is an application of the Reachable relation with full arity. */
    private static boolean isReachableApp(Expr<?> e, FuncDecl<BoolSort> reachableDecl, int P) {
        if (!e.isApp() || e.getNumArgs() != P) {
            return false;
        }
        FuncDecl<?> decl = e.getFuncDecl();
        return decl.equals(reachableDecl) || "Reachable".equals(decl.getName().toString());
    }

    private static String abbreviate(Expr<?> answer) {
        String s = String.valueOf(answer);
        return s.length() <= 200 ? s : s.substring(0, 200) + "...";
    }
}
