package org.libpetri.smt.z3;

import com.microsoft.z3.*;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.FlatTransition;
import org.libpetri.smt.invariant.PInvariant;

import java.util.List;
import java.util.Set;

/**
 * Encodes a flattened Petri net as Constrained Horn Clauses (CHC) for Z3's Spacer engine.
 *
 * <p>The encoding maps the Petri net to integer arithmetic over a state vector
 * M = (m_0, ..., m_{n-1}) where m_i is the token count of place i.
 *
 * <p>CHC rules:
 * <ul>
 *   <li><b>Reachable(M0)</b> - initial state is reachable</li>
 *   <li><b>Reachable(M') :- Reachable(M) AND enabled(M,t) AND fire(M,M',t)</b> - transition rules</li>
 *   <li><b>Error() :- Reachable(M) AND property_violation(M)</b> - safety property</li>
 * </ul>
 */
public final class SmtEncoder {

    private SmtEncoder() {}

    /**
     * Result of CHC encoding, containing both the error query expression
     * and the Reachable relation declaration (needed for invariant extraction).
     *
     * @param errorExpr     the error predicate to query
     * @param reachableDecl the Reachable relation declaration
     */
    public record EncodingResult(BoolExpr errorExpr, FuncDecl<BoolSort> reachableDecl) {}

    /**
     * Encodes the net and property as CHC rules in the given Fixedpoint.
     *
     * @param ctx            Z3 context
     * @param fp             Z3 Fixedpoint solver
     * @param flatNet        the flattened net
     * @param initialMarking the initial marking
     * @param property       the safety property to verify
     * @param invariants     P-invariants for strengthening
     * @param sinkPlaces     expected terminal places (deadlock permitted when any has a token)
     * @return the encoding result containing the error predicate and reachable declaration
     */
    public static EncodingResult encode(
            Context ctx,
            Fixedpoint fp,
            FlatNet flatNet,
            MarkingState initialMarking,
            SmtProperty property,
            List<PInvariant> invariants,
            Set<Place<?>> sinkPlaces
    ) {
        int P = flatNet.placeCount();

        // Create integer sorts for place markings
        IntSort intSort = ctx.getIntSort();
        Sort[] markingSorts = new Sort[P];
        Symbol[] markingNames = new Symbol[P];
        for (int i = 0; i < P; i++) {
            markingSorts[i] = intSort;
            markingNames[i] = ctx.mkSymbol("m" + i);
        }

        // Create the Reachable relation
        FuncDecl<BoolSort> reachable = ctx.mkFuncDecl(
            ctx.mkSymbol("Reachable"), markingSorts, ctx.getBoolSort());
        fp.registerRelation(reachable);

        // Create the Error relation (0-ary)
        FuncDecl<BoolSort> error = ctx.mkFuncDecl(
            ctx.mkSymbol("Error"), new Sort[0], ctx.getBoolSort());
        fp.registerRelation(error);

        // === Rule 1: Initial state ===
        // Reachable(m0_0, m0_1, ..., m0_{n-1})
        IntExpr[] m0 = new IntExpr[P];
        for (int i = 0; i < P; i++) {
            int tokens = initialMarking.tokens(flatNet.places().get(i));
            m0[i] = ctx.mkInt(tokens);
        }
        BoolExpr initFact = (BoolExpr) reachable.apply((Expr[]) m0);
        fp.addRule(initFact, ctx.mkSymbol("init"));

        // === Rule 2: Transition rules ===
        // For each flat transition, create a CHC rule
        IntExpr[] mVars = new IntExpr[P];   // current marking
        IntExpr[] mPrimeVars = new IntExpr[P]; // next marking

        for (int i = 0; i < P; i++) {
            mVars[i] = (IntExpr) ctx.mkBound(P - 1 - i + P, intSort);
            mPrimeVars[i] = (IntExpr) ctx.mkBound(P - 1 - i, intSort);
        }

        // We need quantified variables for the rules
        // Use mkForall with bound variables
        for (int t = 0; t < flatNet.transitionCount(); t++) {
            var ft = flatNet.transitions().get(t);
            encodeTransitionRule(ctx, fp, reachable, ft, flatNet, invariants, P, markingSorts, markingNames);
        }

        // === Rule 2b: Environment-injection rules (VER-006) ===
        // Per injected env place p: Reachable(M') :- Reachable(M) AND [M[p] < bound]
        //   AND M'[p] = M[p]+1 AND (for all q != p) M'[q] = M[q]. AlwaysAvailable
        //   (null bound) omits the guard so p grows without limit. These are NOT flat
        //   transitions, so the deadlock encoding (which iterates flatNet.transitions)
        //   never sees them and deadlock-freedom does not become trivially true.
        //   P-invariants are NOT conjoined — injection deliberately breaks conservation.
        for (var entry : flatNet.environmentInjection().entrySet()) {
            int idx = flatNet.indexOf(entry.getKey());
            if (idx >= 0) {
                encodeInjectionRule(ctx, fp, reachable, idx, entry.getValue(), P);
            }
        }

        // === Rule 3: Error rule (property violation) ===
        encodeErrorRule(ctx, fp, reachable, error, flatNet, property, sinkPlaces, P, markingSorts, markingNames);

        // Return query expression and reachable declaration for invariant extraction
        return new EncodingResult((BoolExpr) error.apply(), reachable);
    }

    private static void encodeTransitionRule(
            Context ctx, Fixedpoint fp,
            FuncDecl<BoolSort> reachable,
            FlatTransition ft, FlatNet flatNet,
            List<PInvariant> invariants,
            int P, Sort[] sorts, Symbol[] names
    ) {
        // Create variables: m_0..m_{P-1} (current), m'_0..m'_{P-1} (next)
        Symbol[] allNames = new Symbol[2 * P];
        Sort[] allSorts = new Sort[2 * P];
        Expr<IntSort>[] mVars = new Expr[P];
        Expr<IntSort>[] mPrimeVars = new Expr[P];

        // Z3 de Bruijn indexing: mkBound(k) refers to the k-th innermost (rightmost)
        // bound variable. For forall(m0, m1, ..., m_{P-1}, m'0, ..., m'_{P-1}):
        //   m'_{P-1} is innermost -> index 0
        //   m'_i     -> index P-1-i
        //   m_{P-1}  -> index P
        //   m_i      -> index 2P-1-i
        for (int i = 0; i < P; i++) {
            allNames[i] = ctx.mkSymbol("m" + i);
            allSorts[i] = ctx.getIntSort();
            allNames[P + i] = ctx.mkSymbol("m'" + i);
            allSorts[P + i] = ctx.getIntSort();

            mVars[i] = (Expr<IntSort>) ctx.mkBound(2 * P - 1 - i, ctx.getIntSort());
            mPrimeVars[i] = (Expr<IntSort>) ctx.mkBound(P - 1 - i, ctx.getIntSort());
        }

        // Build body: Reachable(M) AND enabled(M,t) AND fire(M,M',t) AND non-negativity(M')

        // 1. Reachable(M)
        BoolExpr reachBody = (BoolExpr) reachable.apply(mVars);

        // 2. enabled(M, t)
        BoolExpr enabled = encodeEnabled(ctx, ft, flatNet, mVars, P);

        // 3. fire(M, M', t) - transition relation
        BoolExpr fireRelation = encodeFire(ctx, ft, flatNet, mVars, mPrimeVars, P);

        // 4. Non-negativity of M'
        BoolExpr nonNeg = encodeNonNegativity(ctx, mPrimeVars, P);

        // 5. P-invariant constraints on M' (strengthening)
        BoolExpr invConstraints = encodeInvariantConstraints(ctx, invariants, mPrimeVars, P);

        // 6. Environment bounds on M'
        BoolExpr envBounds = encodeEnvBounds(ctx, flatNet, mPrimeVars);

        // Body conjunction
        BoolExpr body = ctx.mkAnd(reachBody, enabled, fireRelation, nonNeg, invConstraints, envBounds);

        // Head: Reachable(M')
        BoolExpr head = (BoolExpr) reachable.apply(mPrimeVars);

        // Rule: forall M, M'. head :- body
        BoolExpr rule = ctx.mkImplies(body, head);
        Quantifier qRule = ctx.mkForall(allSorts, allNames, rule, 1, null, null, null, null);

        fp.addRule(qRule, ctx.mkSymbol("t_" + ft.name()));
    }

    /**
     * Encodes one environment-injection rule (VER-006): the external world adds a
     * token to environment place {@code idx}. A {@code null} bound means unbounded
     * (AlwaysAvailable); an integer guards injection so the place never exceeds the
     * bound (Bounded). All other columns are copied unchanged. No P-invariant
     * strengthening (injection breaks conservation by design); non-negativity holds
     * because {@code M[idx] >= 0} implies {@code M'[idx] >= 1}.
     */
    private static void encodeInjectionRule(
            Context ctx, Fixedpoint fp,
            FuncDecl<BoolSort> reachable,
            int idx, Integer bound, int P
    ) {
        Symbol[] allNames = new Symbol[2 * P];
        Sort[] allSorts = new Sort[2 * P];
        Expr<IntSort>[] mVars = new Expr[P];
        Expr<IntSort>[] mPrimeVars = new Expr[P];

        for (int i = 0; i < P; i++) {
            allNames[i] = ctx.mkSymbol("m" + i);
            allSorts[i] = ctx.getIntSort();
            allNames[P + i] = ctx.mkSymbol("m'" + i);
            allSorts[P + i] = ctx.getIntSort();

            mVars[i] = (Expr<IntSort>) ctx.mkBound(2 * P - 1 - i, ctx.getIntSort());
            mPrimeVars[i] = (Expr<IntSort>) ctx.mkBound(P - 1 - i, ctx.getIntSort());
        }

        BoolExpr reachBody = (BoolExpr) reachable.apply(mVars);

        // fire: M'[idx] = M[idx] + 1; all other columns unchanged.
        BoolExpr fire = encodeInjectionFire(ctx, idx, mVars, mPrimeVars, P);

        // Bounded injection: only inject while still below the cap.
        BoolExpr guard = encodeInjectionGuard(ctx, idx, bound, mVars);

        BoolExpr body = ctx.mkAnd(reachBody, guard, fire);
        BoolExpr head = (BoolExpr) reachable.apply(mPrimeVars);
        BoolExpr rule = ctx.mkImplies(body, head);
        Quantifier qRule = ctx.mkForall(allSorts, allNames, rule, 1, null, null, null, null);

        fp.addRule(qRule, ctx.mkSymbol("env_inject_" + idx));
    }

    /** Non-negativity of a marking vector: {@code AND_i vars[i] >= 0} (same fold order as the CHC rules). */
    private static BoolExpr encodeNonNegativity(Context ctx, Expr<IntSort>[] vars, int P) {
        BoolExpr nonNeg = ctx.mkTrue();
        for (int i = 0; i < P; i++) {
            nonNeg = ctx.mkAnd(nonNeg, ctx.mkGe(vars[i], ctx.mkInt(0)));
        }
        return nonNeg;
    }

    /** Bounded-environment caps on a marking vector: {@code AND vars[idx] <= bound} per bounded env place. */
    private static BoolExpr encodeEnvBounds(Context ctx, FlatNet flatNet, Expr<IntSort>[] vars) {
        BoolExpr envBounds = ctx.mkTrue();
        for (var entry : flatNet.environmentBounds().entrySet()) {
            int idx = flatNet.indexOf(entry.getKey());
            if (idx >= 0) {
                envBounds = ctx.mkAnd(envBounds,
                    ctx.mkLe(vars[idx], ctx.mkInt(entry.getValue())));
            }
        }
        return envBounds;
    }

    /** Injection arithmetic: {@code M'[idx] = M[idx] + 1}, all other columns copied unchanged. */
    private static BoolExpr encodeInjectionFire(
            Context ctx, int idx,
            Expr<IntSort>[] mVars, Expr<IntSort>[] mPrimeVars, int P
    ) {
        BoolExpr fire = ctx.mkTrue();
        for (int i = 0; i < P; i++) {
            if (i == idx) {
                fire = ctx.mkAnd(fire, ctx.mkEq(mPrimeVars[i], ctx.mkAdd(mVars[i], ctx.mkInt(1))));
            } else {
                fire = ctx.mkAnd(fire, ctx.mkEq(mPrimeVars[i], mVars[i]));
            }
        }
        return fire;
    }

    /** Injection guard: {@code M[idx] < bound} for Bounded(k); {@code true} for AlwaysAvailable (null bound). */
    private static BoolExpr encodeInjectionGuard(Context ctx, int idx, Integer bound, Expr<IntSort>[] mVars) {
        return bound == null ? ctx.mkTrue() : ctx.mkLt(mVars[idx], ctx.mkInt(bound));
    }

    /**
     * One <em>unstrengthened</em> step of the encoded net as a single formula
     * {@code T(M, M')} over the given current/next marking expressions: the
     * disjunction of all transition steps (strict enablement AND firing
     * arithmetic AND non-negativity of M' AND environment bounds on M') and all
     * environment-injection steps (bound guard AND injection arithmetic, VER-006),
     * WITHOUT the P-invariant strengthening conjuncts that {@link #encode} adds
     * to the CHC transition-rule bodies.
     *
     * <p>This is the step relation {@link CertificateChecker} validates an IC3
     * certificate against. Dropping the invariant conjuncts keeps the check
     * independent of the P-invariant computation: a numerically wrong invariant
     * conjoined into the rules removes reachable successors, so re-checking
     * against the strengthened relation would inherit exactly the failure mode
     * the certificate check exists to catch. Every disjunct is built by the same
     * per-transition condition builders as the CHC rules, so the step semantics
     * match the encoding exactly.
     *
     * @param ctx        Z3 context
     * @param flatNet    the flattened net
     * @param mVars      current-marking expressions (length = placeCount)
     * @param mPrimeVars next-marking expressions (length = placeCount)
     * @return the step relation {@code T(M, M')}; {@code false} for a net with no steps
     */
    public static BoolExpr encodeStepRelation(
            Context ctx, FlatNet flatNet,
            Expr<IntSort>[] mVars, Expr<IntSort>[] mPrimeVars
    ) {
        int P = flatNet.placeCount();
        var steps = new java.util.ArrayList<BoolExpr>();

        for (var ft : flatNet.transitions()) {
            BoolExpr enabled = encodeEnabled(ctx, ft, flatNet, mVars, P);
            BoolExpr fire = encodeFire(ctx, ft, flatNet, mVars, mPrimeVars, P);
            BoolExpr nonNeg = encodeNonNegativity(ctx, mPrimeVars, P);
            BoolExpr envBounds = encodeEnvBounds(ctx, flatNet, mPrimeVars);
            steps.add(ctx.mkAnd(enabled, fire, nonNeg, envBounds));
        }

        for (var entry : flatNet.environmentInjection().entrySet()) {
            int idx = flatNet.indexOf(entry.getKey());
            if (idx >= 0) {
                BoolExpr guard = encodeInjectionGuard(ctx, idx, entry.getValue(), mVars);
                BoolExpr fire = encodeInjectionFire(ctx, idx, mVars, mPrimeVars, P);
                steps.add(ctx.mkAnd(guard, fire));
            }
        }

        if (steps.isEmpty()) {
            return ctx.mkFalse();
        }
        return ctx.mkOr(steps.toArray(new BoolExpr[0]));
    }

    private static BoolExpr encodeEnabled(
            Context ctx, FlatTransition ft, FlatNet flatNet,
            Expr<IntSort>[] mVars, int P
    ) {
        return encodeEnabled(ctx, ft, flatNet, mVars, P, false);
    }

    /**
     * Encodes the enablement predicate for a flat transition.
     *
     * <p>When {@code relaxEnv} is true (used only by the deadlock check),
     * input/read requirements on injectable environment places are treated as
     * satisfiable by external injection — AlwaysAvailable always satisfies them,
     * Bounded(k) satisfies them iff the required cardinality is &le; k (a check on
     * the arc weight, not the marking). This mirrors the state class graph's
     * always-available enablement (VER-006) so a reactive net merely waiting for
     * input is not reported as a deadlock. Transition firing always uses the strict
     * form because firing genuinely consumes tokens.
     */
    private static BoolExpr encodeEnabled(
            Context ctx, FlatTransition ft, FlatNet flatNet,
            Expr<IntSort>[] mVars, int P, boolean relaxEnv
    ) {
        BoolExpr result = ctx.mkTrue();
        java.util.Map<Integer, Integer> envInj = relaxEnv ? injectedEnvIndices(flatNet) : null;

        // Input requirements: M[p] >= pre[p] (relaxed for injectable env inputs).
        for (int p = 0; p < P; p++) {
            int pre = ft.preVector()[p];
            if (pre <= 0) continue;
            if (envInj != null && envInj.containsKey(p)) {
                Integer bound = envInj.get(p);
                if (bound != null && pre > bound) return ctx.mkFalse(); // never enableable
                continue; // satisfiable by injection
            }
            result = ctx.mkAnd(result, ctx.mkGe(mVars[p], ctx.mkInt(pre)));
        }

        // Read arcs: M[p] >= 1 (relaxed for injectable env inputs).
        for (int p : ft.readPlaces()) {
            if (envInj != null && envInj.containsKey(p)) {
                Integer bound = envInj.get(p);
                if (bound != null && bound < 1) return ctx.mkFalse();
                continue;
            }
            result = ctx.mkAnd(result, ctx.mkGe(mVars[p], ctx.mkInt(1)));
        }

        // Inhibitor arcs: M[p] == 0
        for (int p : ft.inhibitorPlaces()) {
            result = ctx.mkAnd(result, ctx.mkEq(mVars[p], ctx.mkInt(0)));
        }

        // Non-negativity of current marking
        for (int p = 0; p < P; p++) {
            result = ctx.mkAnd(result, ctx.mkGe(mVars[p], ctx.mkInt(0)));
        }

        return result;
    }

    /** Maps injected environment-place index -> injection bound (null = unbounded). */
    private static java.util.Map<Integer, Integer> injectedEnvIndices(FlatNet flatNet) {
        var out = new java.util.HashMap<Integer, Integer>();
        for (var entry : flatNet.environmentInjection().entrySet()) {
            int idx = flatNet.indexOf(entry.getKey());
            if (idx >= 0) out.put(idx, entry.getValue());
        }
        return out;
    }

    private static BoolExpr encodeFire(
            Context ctx, FlatTransition ft, FlatNet flatNet,
            Expr<IntSort>[] mVars, Expr<IntSort>[] mPrimeVars, int P
    ) {
        BoolExpr result = ctx.mkTrue();

        for (int p = 0; p < P; p++) {
            boolean isReset = false;
            for (int rp : ft.resetPlaces()) {
                if (rp == p) { isReset = true; break; }
            }

            if (isReset || ft.consumeAll()[p]) {
                // Reset/consumeAll: M'[p] = post[p]
                result = ctx.mkAnd(result,
                    ctx.mkEq(mPrimeVars[p], ctx.mkInt(ft.postVector()[p])));
            } else {
                // Standard: M'[p] = M[p] - pre[p] + post[p]
                int delta = ft.postVector()[p] - ft.preVector()[p];
                if (delta == 0) {
                    result = ctx.mkAnd(result,
                        ctx.mkEq(mPrimeVars[p], mVars[p]));
                } else {
                    result = ctx.mkAnd(result,
                        ctx.mkEq(mPrimeVars[p],
                            ctx.mkAdd(mVars[p], ctx.mkInt(delta))));
                }
            }
        }

        return result;
    }

    private static void encodeErrorRule(
            Context ctx, Fixedpoint fp,
            FuncDecl<BoolSort> reachable, FuncDecl<BoolSort> error,
            FlatNet flatNet, SmtProperty property,
            Set<Place<?>> sinkPlaces,
            int P, Sort[] sorts, Symbol[] names
    ) {
        // Create variables for the error rule
        Symbol[] varNames = new Symbol[P];
        Sort[] varSorts = new Sort[P];
        Expr<IntSort>[] mVars = new Expr[P];

        for (int i = 0; i < P; i++) {
            varNames[i] = ctx.mkSymbol("m" + i);
            varSorts[i] = ctx.getIntSort();
            mVars[i] = (Expr<IntSort>) ctx.mkBound(P - 1 - i, ctx.getIntSort());
        }

        BoolExpr reachBody = (BoolExpr) reachable.apply(mVars);
        BoolExpr violation = encodePropertyViolation(ctx, flatNet, property, sinkPlaces, mVars, P);

        BoolExpr head = (BoolExpr) error.apply();
        BoolExpr body = ctx.mkAnd(reachBody, violation);
        BoolExpr rule = ctx.mkImplies(body, head);

        Quantifier qRule = ctx.mkForall(varSorts, varNames, rule, 1, null, null, null, null);
        fp.addRule(qRule, ctx.mkSymbol("error_" + property.getClass().getSimpleName()));
    }

    /**
     * Encodes the property-violation predicate {@code Bad(M)} over the given
     * marking expressions — the same predicate the Error CHC rule conjoins with
     * {@code Reachable(M)}. Public so {@link CertificateChecker} can check the
     * safety verification condition {@code I(M) AND Bad(M)} against the identical
     * violation semantics used by the encoding.
     *
     * @throws IllegalArgumentException if the property references a place that is
     *     not in the flattened net (mirrors the Error-rule behavior)
     */
    public static BoolExpr encodePropertyViolation(
            Context ctx, FlatNet flatNet, SmtProperty property,
            Set<Place<?>> sinkPlaces,
            Expr<IntSort>[] mVars, int P
    ) {
        return switch (property) {
            case SmtProperty.DeadlockFree() -> {
                BoolExpr deadlock = encodeDeadlock(ctx, flatNet, mVars, P);
                if (!sinkPlaces.isEmpty()) {
                    // Deadlock is only a violation if NOT at any expected sink place
                    BoolExpr notAtSink = ctx.mkTrue();
                    for (var sink : sinkPlaces) {
                        int idx = flatNet.indexOf(sink);
                        if (idx >= 0) {
                            notAtSink = ctx.mkAnd(notAtSink,
                                ctx.mkEq(mVars[idx], ctx.mkInt(0)));
                        }
                    }
                    yield ctx.mkAnd(deadlock, notAtSink);
                }
                yield deadlock;
            }
            case SmtProperty.MutualExclusion me -> {
                int idx1 = flatNet.indexOf(me.p1());
                int idx2 = flatNet.indexOf(me.p2());
                if (idx1 < 0) throw new IllegalArgumentException(
                    "MutualExclusion property references unknown place: " + me.p1().name());
                if (idx2 < 0) throw new IllegalArgumentException(
                    "MutualExclusion property references unknown place: " + me.p2().name());
                // Violation: both places have tokens simultaneously
                yield ctx.mkAnd(
                    ctx.mkGe(mVars[idx1], ctx.mkInt(1)),
                    ctx.mkGe(mVars[idx2], ctx.mkInt(1))
                );
            }
            case SmtProperty.PlaceBound pb -> {
                int idx = flatNet.indexOf(pb.place());
                if (idx < 0) throw new IllegalArgumentException(
                    "PlaceBound property references unknown place: " + pb.place().name());
                // Violation: place exceeds bound
                yield ctx.mkGt(mVars[idx], ctx.mkInt(pb.bound()));
            }
            case SmtProperty.BranchPlaceBound bpb -> {
                // ν-net budget lever (NU-040): a count bound, encoded identically
                // to PlaceBound. Sound under the matched-transition
                // over-approximation — the real net fires fewer joins, so it
                // cannot exceed a bound the over-approximation respects.
                int idx = flatNet.indexOf(bpb.place());
                if (idx < 0) throw new IllegalArgumentException(
                    "BranchPlaceBound property references unknown place: " + bpb.place().name());
                yield ctx.mkGt(mVars[idx], ctx.mkInt(bpb.bound()));
            }
            case SmtProperty.JoinedOrDeadLettered jdl -> {
                // NU-040: a quiescent (deadlocked) marking that still holds a
                // `pending` token is a stranded correlation group. Reuse the
                // deadlock predicate and conjoin pending non-emptiness.
                int idx = flatNet.indexOf(jdl.pending());
                if (idx < 0) {
                    // Unknown pending place: no state can violate.
                    yield ctx.mkFalse();
                }
                BoolExpr deadlock = encodeDeadlock(ctx, flatNet, mVars, P);
                yield ctx.mkAnd(deadlock, ctx.mkGe(mVars[idx], ctx.mkInt(1)));
            }
            case SmtProperty.Unreachable ur -> {
                // Violation: all specified places have tokens (marking is reachable)
                BoolExpr allMarked = ctx.mkTrue();
                for (var place : ur.places()) {
                    int idx = flatNet.indexOf(place);
                    if (idx >= 0) {
                        allMarked = ctx.mkAnd(allMarked,
                            ctx.mkGe(mVars[idx], ctx.mkInt(1)));
                    }
                }
                yield allMarked;
            }
        };
    }

    /**
     * Encodes the deadlock condition: no transition is enabled. Environment inputs
     * are treated as injectable (relaxed enablement), so a marking that an external
     * injection could re-enable is NOT a deadlock — only a genuinely stuck marking
     * is (VER-006).
     */
    private static BoolExpr encodeDeadlock(
            Context ctx, FlatNet flatNet,
            Expr<IntSort>[] mVars, int P
    ) {
        BoolExpr deadlock = ctx.mkTrue();

        for (var ft : flatNet.transitions()) {
            // NOT enabled(M, t), with env inputs treated as injectable.
            BoolExpr enabled = encodeEnabled(ctx, ft, flatNet, mVars, P, /* relaxEnv */ true);
            deadlock = ctx.mkAnd(deadlock, ctx.mkNot(enabled));
        }

        return deadlock;
    }

    /**
     * Conjunction of P-invariant equalities {@code sum(y_i * M[i]) = constant}
     * over the given marking expressions. Package-private: {@link CertificateChecker}
     * folds the same equalities into its candidate invariant — where they are
     * re-proven from scratch (initiation and consecution), not trusted.
     */
    static BoolExpr encodeInvariantConstraints(
            Context ctx, List<PInvariant> invariants,
            Expr<IntSort>[] mVars, int P
    ) {
        BoolExpr result = ctx.mkTrue();
        for (var inv : invariants) {
            // sum(y_i * M[i]) == constant
            ArithExpr<IntSort> sum = ctx.mkInt(0);
            for (int idx : inv.support()) {
                if (idx < P) {
                    sum = ctx.mkAdd(sum,
                        ctx.mkMul(ctx.mkInt(inv.weights()[idx]), mVars[idx]));
                }
            }
            result = ctx.mkAnd(result, ctx.mkEq(sum, ctx.mkInt(inv.constant())));
        }
        return result;
    }
}
