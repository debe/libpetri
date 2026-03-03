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
        BoolExpr nonNeg = ctx.mkTrue();
        for (int i = 0; i < P; i++) {
            nonNeg = ctx.mkAnd(nonNeg, ctx.mkGe(mPrimeVars[i], ctx.mkInt(0)));
        }

        // 5. P-invariant constraints on M' (strengthening)
        BoolExpr invConstraints = encodeInvariantConstraints(ctx, invariants, mPrimeVars, P);

        // 6. Environment bounds on M'
        BoolExpr envBounds = ctx.mkTrue();
        for (var entry : flatNet.environmentBounds().entrySet()) {
            int idx = flatNet.indexOf(entry.getKey());
            if (idx >= 0) {
                envBounds = ctx.mkAnd(envBounds,
                    ctx.mkLe(mPrimeVars[idx], ctx.mkInt(entry.getValue())));
            }
        }

        // Body conjunction
        BoolExpr body = ctx.mkAnd(reachBody, enabled, fireRelation, nonNeg, invConstraints, envBounds);

        // Head: Reachable(M')
        BoolExpr head = (BoolExpr) reachable.apply(mPrimeVars);

        // Rule: forall M, M'. head :- body
        BoolExpr rule = ctx.mkImplies(body, head);
        Quantifier qRule = ctx.mkForall(allSorts, allNames, rule, 1, null, null, null, null);

        fp.addRule(qRule, ctx.mkSymbol("t_" + ft.name()));
    }

    private static BoolExpr encodeEnabled(
            Context ctx, FlatTransition ft, FlatNet flatNet,
            Expr<IntSort>[] mVars, int P
    ) {
        BoolExpr result = ctx.mkTrue();

        // Input requirements: M[p] >= pre[p]
        for (int p = 0; p < P; p++) {
            if (ft.preVector()[p] > 0) {
                result = ctx.mkAnd(result,
                    ctx.mkGe(mVars[p], ctx.mkInt(ft.preVector()[p])));
            }
        }

        // Read arcs: M[p] >= 1
        for (int p : ft.readPlaces()) {
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

    private static BoolExpr encodePropertyViolation(
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
     * Encodes the deadlock condition: no transition is enabled.
     */
    private static BoolExpr encodeDeadlock(
            Context ctx, FlatNet flatNet,
            Expr<IntSort>[] mVars, int P
    ) {
        BoolExpr deadlock = ctx.mkTrue();

        for (var ft : flatNet.transitions()) {
            // NOT enabled(M, t)
            BoolExpr enabled = encodeEnabled(ctx, ft, flatNet, mVars, P);
            deadlock = ctx.mkAnd(deadlock, ctx.mkNot(enabled));
        }

        return deadlock;
    }

    private static BoolExpr encodeInvariantConstraints(
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
