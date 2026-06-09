package org.libpetri.smt.z3;

import com.microsoft.z3.*;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.PetriNet;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.FlatTransition;
import org.libpetri.smt.invariant.PInvariant;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Bounded <b>name-coloured</b> CHC encoding for &nu;-net join correlation
 * (NU-050 #1, Route A — the EUF-style carve-out).
 *
 * <p>The flat {@link SmtEncoder} is a pure <em>counting</em> abstraction: a place
 * is one integer, and a matched (&nu;-join) transition is encoded name-blind — it
 * fires whenever the input <em>counts</em> allow, regardless of whether the
 * consumed tokens actually share a correlation name. That over-approximation is
 * sound for {@code Proven} on reachability-safety bounds but can report a
 * <b>spurious</b> {@code Violated} whose counterexample silently equates two
 * <em>distinct</em> names.
 *
 * <p>This encoder removes that imprecision for the bounded fragment. The
 * decidability lever (NU-040) is the budget: with a {@code Budget} place
 * pre-seeded with {@code k} tokens gating every mint, at most {@code k}
 * correlation names are live at once. So names are modelled as a <b>finite set of
 * {@code k} colours</b>. Each coloured place becomes {@code k} per-colour integer
 * counts; a mint introduces a <em>globally fresh</em> colour (one currently empty
 * everywhere); a matched join consumes the <b>same colour</b> from every
 * correlated input. Within the budget bound the encoding is <em>exact</em> — sound
 * and complete — so no different-name counterexample survives.
 *
 * <h3>Supported fragment (tracer bullet)</h3>
 *
 * <p>{@link #buildPlan} returns {@code null} (and the verifier falls back to the
 * sound over-approximation) unless the net is in the simple
 * <b>mint &rarr; matched-join</b> shape:
 * <ul>
 *   <li>coloured places = the correlated inputs of every matched transition;</li>
 *   <li>each coloured place is <em>produced only by</em> minting forks (count 1, no
 *       coloured input, costs &ge;1 budget token) and <em>consumed only by</em>
 *       matched joins (count 1, produces no coloured token);</li>
 *   <li>budget places are consumed only by mints and produced only by joins (so
 *       live colours &le; initial budget = {@code k});</li>
 *   <li>coloured places start empty; no inhibitor/read/reset/consume-all arc
 *       touches a coloured place; no XOR output anywhere.</li>
 * </ul>
 *
 * <p>Quiescence properties are never routed here (they are not reachability-safety
 * and the budget-bounded colouring does not yet model the absence of an enabled
 * join across colours — that is the SCG name-partition route, future work).
 *
 * <p>This mirrors the Rust reference {@code name_coloured_encoder.rs} exactly; the
 * only difference is that this encoder builds Z3 {@link BoolExpr} objects via the
 * native Java bindings rather than emitting SMT-LIB2 text.
 */
public final class NameColouredEncoder {

    private NameColouredEncoder() {}

    /** How a transition relates to the coloured (correlation-carrying) places. */
    private sealed interface Klass permits Mint, Join, Untouched {}

    /** Minting fork: produces a freshly-coloured token into each listed place. */
    private record Mint(int[] colouredOut) implements Klass {}

    /** Matched join: consumes one same-coloured token from each listed place. */
    private record Join(int[] colouredIn) implements Klass {}

    /** Touches no coloured place — a pure counting transition. */
    private record Untouched() implements Klass {}

    /**
     * A validated plan for the name-coloured encoding of a budget-bounded
     * &nu;-net. Opaque to the verifier except for {@link #k()} and
     * {@link #colouredCount()} (used only for the report line); the encoder reads
     * the remaining fields directly (same enclosing class).
     */
    public static final class ColouredPlan {
        /** Flat indices of the coloured places (sorted ascending). */
        final int[] coloured;
        /** Per flat place: whether it is coloured. */
        final boolean[] isColoured;
        /** Colour bound — the number of simultaneously-live names (= initial budget). */
        final int k;
        /** Classification per flat transition (1:1 — the fragment forbids XOR). */
        final List<Klass> classes;

        private ColouredPlan(int[] coloured, boolean[] isColoured, int k, List<Klass> classes) {
            this.coloured = coloured;
            this.isColoured = isColoured;
            this.k = k;
            this.classes = classes;
        }

        /** The colour bound (= total initial budget tokens). */
        public int k() {
            return k;
        }

        /** The number of coloured places. */
        public int colouredCount() {
            return coloured.length;
        }
    }

    /**
     * Detects whether {@code net} is in the supported budget-bounded
     * mint&rarr;matched-join fragment and, if so, returns the plan for
     * {@link #encode}. Returns {@code null} otherwise — the verifier then uses the
     * sound over-approximation.
     *
     * @param net              the source net (for match specs and XOR detection)
     * @param flat             the flattened net
     * @param initial          the initial marking
     * @param budgetPlaceNames the declared budget-place names (NU-040)
     */
    public static ColouredPlan buildPlan(
            PetriNet net, FlatNet flat, MarkingState initial, Set<String> budgetPlaceNames) {
        int p = flat.placeCount();

        // No XOR: every original transition maps 1:1 to a flat row, in order.
        if (flat.transitionCount() != net.transitions().size()) {
            return null;
        }

        // Place name -> flat index (Java FlatNet.placeIndex is keyed by Place, not
        // name; resolve matched + budget places by name to match the Rust contract).
        Map<String, Integer> nameIdx = new HashMap<>();
        for (int i = 0; i < p; i++) {
            nameIdx.put(flat.places().get(i).name(), i);
        }

        // 1. Coloured places = union of every matched transition's correlated
        //    inputs. Read the match spec off each flat row's source transition
        //    (net.transitions() is an unordered Set; the flat list is the ordered
        //    1:1 mapping guaranteed by the no-XOR check above).
        boolean[] isColoured = new boolean[p];
        for (var ft : flat.transitions()) {
            var ms = ft.source().matchSpec();
            if (ms != null) {
                for (var key : ms.keys()) {
                    Integer pid = nameIdx.get(key.place().name());
                    if (pid == null) {
                        return null;
                    }
                    isColoured[pid] = true;
                }
            }
        }
        int[] coloured = indicesOf(isColoured);
        if (coloured.length == 0) {
            return null;
        }

        // Coloured places must start empty — we do not model an initial colour
        // assignment for pre-seeded tokens.
        for (int pid : coloured) {
            if (initial.tokens(flat.places().get(pid)) != 0) {
                return null;
            }
        }

        // Colour bound k = total initial budget tokens (the live-name ceiling).
        Set<Integer> budgetIdx = new HashSet<>();
        for (String n : budgetPlaceNames) {
            Integer i = nameIdx.get(n);
            if (i != null) {
                budgetIdx.add(i);
            }
        }
        if (budgetIdx.isEmpty()) {
            return null;
        }
        int k = 0;
        for (int b : budgetIdx) {
            k += initial.tokens(flat.places().get(b));
        }
        if (k == 0) {
            return null;
        }

        // No inhibitor/read/reset/consume-all arc may touch a coloured place.
        for (var ft : flat.transitions()) {
            if (anyColoured(ft.inhibitorPlaces(), isColoured)
                    || anyColoured(ft.readPlaces(), isColoured)
                    || anyColoured(ft.resetPlaces(), isColoured)
                    || anyConsumeAllColoured(ft.consumeAll(), isColoured)) {
                return null;
            }
        }

        // 2. Classify each transition from its flat incidence.
        List<Klass> classes = new ArrayList<>(flat.transitionCount());
        for (int ti = 0; ti < flat.transitionCount(); ti++) {
            var ft = flat.transitions().get(ti);
            var t = ft.source();

            int[] colouredIn = colouredWithPositive(coloured, ft.preVector());
            int[] colouredOut = colouredWithPositive(coloured, ft.postVector());

            Klass klass;
            if (t.matchSpec() != null) {
                // Matched join: consumes coloured inputs (count 1), produces none.
                if (colouredOut.length != 0 || colouredIn.length == 0) {
                    return null;
                }
                for (int pid : colouredIn) {
                    if (ft.preVector()[pid] != 1) {
                        return null;
                    }
                }
                klass = new Join(colouredIn);
            } else if (colouredOut.length != 0) {
                // Minting fork: produces coloured (count 1), consumes none, costs budget.
                if (colouredIn.length != 0) {
                    return null;
                }
                for (int o : colouredOut) {
                    if (ft.postVector()[o] != 1) {
                        return null;
                    }
                }
                int budgetConsumed = 0;
                for (int b : budgetIdx) {
                    budgetConsumed += ft.preVector()[b];
                }
                if (budgetConsumed < 1) {
                    return null;
                }
                klass = new Mint(colouredOut);
            } else {
                // Touches no coloured place at all.
                if (colouredIn.length != 0) {
                    return null;
                }
                klass = new Untouched();
            }
            classes.add(klass);
        }

        // 3. Budget discipline: consumed only by mints, produced only by joins, AND
        //    conserved — a join may not refund MORE budget than the cheapest mint
        //    consumes, else repeated mint->join cycles inflate the pool above k, the
        //    real net can hold > k simultaneously-live names, and the k-colour
        //    encoding would UNDER-approximate and report a false `Proven`. With this
        //    bound live colours <= initial budget = k. Fail-closed (return null ->
        //    sound over-approximation) otherwise.
        Integer minMintCost = null;
        int maxJoinRefund = 0;
        for (int ti = 0; ti < classes.size(); ti++) {
            Klass cls = classes.get(ti);
            var ft = flat.transitions().get(ti);
            for (int b : budgetIdx) {
                if (ft.preVector()[b] > 0 && !(cls instanceof Mint)) {
                    return null;
                }
                if (ft.postVector()[b] > 0 && !(cls instanceof Join)) {
                    return null;
                }
            }
            if (cls instanceof Mint) {
                int cost = 0;
                for (int b : budgetIdx) {
                    cost += ft.preVector()[b];
                }
                minMintCost = (minMintCost == null) ? cost : Math.min(minMintCost, cost);
            } else if (cls instanceof Join) {
                int refund = 0;
                for (int b : budgetIdx) {
                    refund += ft.postVector()[b];
                }
                maxJoinRefund = Math.max(maxJoinRefund, refund);
            }
        }
        if (minMintCost == null || maxJoinRefund > minMintCost) {
            return null;
        }

        return new ColouredPlan(coloured, isColoured, k, classes);
    }

    // === Column layout over the coloured state vector ===
    // Uncoloured place -> one var; coloured place -> k per-colour vars.

    private static final class Layout {
        /** Column index of each uncoloured place ({@code -1} if coloured). */
        final int[] colUnc;
        /** Per coloured place: its {@code k} column indices ({@code null} if uncoloured). */
        final int[][] colCol;
        /** Total column count. */
        final int nCols;
        /** Current-marking bound vars, one per column (transition-rule scope: 2*nCols vars). */
        final Expr<IntSort>[] cur;
        /** Next-marking bound vars, one per column. */
        final Expr<IntSort>[] nxt;
        /** Quantified sorts for a transition rule (2*nCols Int). */
        final Sort[] allSorts;
        /** Quantified symbols for a transition rule. */
        final Symbol[] allNames;

        @SuppressWarnings("unchecked")
        private Layout(ColouredPlan plan, int p, Context ctx) {
            this.colUnc = new int[p];
            this.colCol = new int[p][];
            int cols = 0;
            for (int i = 0; i < p; i++) {
                colUnc[i] = -1;
                if (plan.isColoured[i]) {
                    int[] idxs = new int[plan.k];
                    for (int c = 0; c < plan.k; c++) {
                        idxs[c] = cols++;
                    }
                    colCol[i] = idxs;
                } else {
                    colUnc[i] = cols++;
                }
            }
            this.nCols = cols;

            IntSort intSort = ctx.getIntSort();
            this.cur = new Expr[nCols];
            this.nxt = new Expr[nCols];
            this.allSorts = new Sort[2 * nCols];
            this.allNames = new Symbol[2 * nCols];
            // forall(c0..c_{nCols-1}, cp0..cp_{nCols-1}): de Bruijn — cp_{nCols-1}
            // is innermost (index 0). cur[col] = mkBound(2*nCols-1-col),
            // nxt[col] = mkBound(nCols-1-col). Generalises SmtEncoder's P -> nCols.
            for (int col = 0; col < nCols; col++) {
                allNames[col] = ctx.mkSymbol("c" + col);
                allSorts[col] = intSort;
                allNames[nCols + col] = ctx.mkSymbol("cp" + col);
                allSorts[nCols + col] = intSort;
                cur[col] = (Expr<IntSort>) ctx.mkBound(2 * nCols - 1 - col, intSort);
                nxt[col] = (Expr<IntSort>) ctx.mkBound(nCols - 1 - col, intSort);
            }
        }
    }

    /** Contributes the enablement guards and the changed-column updates of a rule. */
    @FunctionalInterface
    private interface Fill {
        void apply(List<BoolExpr> enab, Map<Integer, Expr<IntSort>> upd);
    }

    /**
     * Encodes the supported &nu;-net as bounded name-coloured CHC for Z3 Spacer.
     * Reuses {@link SmtEncoder.EncodingResult}; with the query {@code (not Error)},
     * {@code sat} &rArr; PROVEN, {@code unsat} &rArr; VIOLATED (the Spacer
     * convention shared with {@link SmtEncoder}).
     */
    public static SmtEncoder.EncodingResult encode(
            Context ctx, Fixedpoint fp, ColouredPlan plan, FlatNet flat,
            MarkingState initial, SmtProperty property, List<PInvariant> invariants) {
        int p = flat.placeCount();
        int k = plan.k;
        Layout lay = new Layout(plan, p, ctx);

        Sort[] markingSorts = new Sort[lay.nCols];
        for (int i = 0; i < lay.nCols; i++) {
            markingSorts[i] = ctx.getIntSort();
        }
        FuncDecl<BoolSort> reachable = ctx.mkFuncDecl(
            ctx.mkSymbol("Reachable"), markingSorts, ctx.getBoolSort());
        fp.registerRelation(reachable);
        FuncDecl<BoolSort> error = ctx.mkFuncDecl(
            ctx.mkSymbol("Error"), new Sort[0], ctx.getBoolSort());
        fp.registerRelation(error);

        // Init: uncoloured places carry their initial count; coloured start empty.
        IntExpr[] init = new IntExpr[lay.nCols];
        for (int i = 0; i < p; i++) {
            if (plan.isColoured[i]) {
                for (int c = 0; c < k; c++) {
                    init[lay.colCol[i][c]] = ctx.mkInt(0);
                }
            } else {
                init[lay.colUnc[i]] = ctx.mkInt(initial.tokens(flat.places().get(i)));
            }
        }
        fp.addRule((BoolExpr) reachable.apply((Expr[]) init), ctx.mkSymbol("init"));

        // Transition rules.
        for (int ti = 0; ti < plan.classes.size(); ti++) {
            Klass cls = plan.classes.get(ti);
            FlatTransition ft = flat.transitions().get(ti);
            switch (cls) {
                case Untouched _ -> addRule(ctx, fp, reachable, lay, plan, invariants,
                    ft.name() + "_u",
                    (enab, upd) -> uncolouredIncidence(ctx, lay, plan, ft, enab, upd));
                case Mint m -> {
                    for (int c = 0; c < k; c++) {
                        final int cc = c;
                        addRule(ctx, fp, reachable, lay, plan, invariants,
                            ft.name() + "_mint_" + cc, (enab, upd) -> {
                                uncolouredIncidence(ctx, lay, plan, ft, enab, upd);
                                // Globally fresh colour: cc must be empty in every coloured place.
                                for (int q : plan.coloured) {
                                    enab.add(ctx.mkEq(lay.cur[lay.colCol[q][cc]], ctx.mkInt(0)));
                                }
                                for (int o : m.colouredOut()) {
                                    int col = lay.colCol[o][cc];
                                    upd.put(col, ctx.mkAdd(lay.cur[col], ctx.mkInt(1)));
                                }
                            });
                    }
                }
                case Join j -> {
                    for (int c = 0; c < k; c++) {
                        final int cc = c;
                        addRule(ctx, fp, reachable, lay, plan, invariants,
                            ft.name() + "_join_" + cc, (enab, upd) -> {
                                uncolouredIncidence(ctx, lay, plan, ft, enab, upd);
                                // Same colour cc present in every correlated input.
                                for (int ip : j.colouredIn()) {
                                    int col = lay.colCol[ip][cc];
                                    enab.add(ctx.mkGe(lay.cur[col], ctx.mkInt(1)));
                                    upd.put(col, ctx.mkSub(lay.cur[col], ctx.mkInt(1)));
                                }
                            });
                    }
                }
            }
        }

        // Error rule.
        addErrorRule(ctx, fp, reachable, error, lay, plan, flat, property);

        return new SmtEncoder.EncodingResult((BoolExpr) error.apply(), reachable);
    }

    /**
     * Builds one transition CHC rule. {@code fill} contributes the enablement
     * guards and the changed-column updates; every other column is copied
     * unchanged, changed columns get a non-negativity guard, and the (lifted)
     * P-invariants constrain the successor.
     */
    private static void addRule(
            Context ctx, Fixedpoint fp, FuncDecl<BoolSort> reachable, Layout lay,
            ColouredPlan plan, List<PInvariant> invariants, String ruleName, Fill fill) {
        List<BoolExpr> enab = new ArrayList<>();
        Map<Integer, Expr<IntSort>> upd = new HashMap<>();
        fill.apply(enab, upd);

        List<BoolExpr> conditions = new ArrayList<>();
        conditions.add((BoolExpr) reachable.apply(lay.cur));
        conditions.addAll(enab);

        // A changed column gets its update + a non-negativity guard; every other
        // column is copied unchanged.
        for (int col = 0; col < lay.nCols; col++) {
            Expr<IntSort> expr = upd.get(col);
            if (expr != null) {
                conditions.add(ctx.mkEq(lay.nxt[col], expr));
                conditions.add(ctx.mkGe(lay.nxt[col], ctx.mkInt(0)));
            } else {
                conditions.add(ctx.mkEq(lay.nxt[col], lay.cur[col]));
            }
        }

        for (PInvariant inv : invariants) {
            BoolExpr eq = liftedInvariant(ctx, inv, plan, lay, lay.nxt);
            if (eq != null) {
                conditions.add(eq);
            }
        }

        BoolExpr body = ctx.mkAnd(conditions.toArray(new BoolExpr[0]));
        BoolExpr head = (BoolExpr) reachable.apply(lay.nxt);
        BoolExpr rule = ctx.mkImplies(body, head);
        Quantifier qRule = ctx.mkForall(lay.allSorts, lay.allNames, rule, 1, null, null, null, null);
        fp.addRule(qRule, ctx.mkSymbol(ruleName));
    }

    /**
     * Pushes the enablement guards and column updates contributed by a
     * transition's <b>uncoloured</b> incidence (consume/produce on non-coloured
     * places). Coloured columns are handled by the caller (mint produces, join
     * consumes). Mirrors the Rust reference — no blanket current-marking
     * non-negativity guard (the Reachable invariant carries that).
     */
    private static void uncolouredIncidence(
            Context ctx, Layout lay, ColouredPlan plan, FlatTransition ft,
            List<BoolExpr> enab, Map<Integer, Expr<IntSort>> upd) {
        int p = ft.preVector().length;
        for (int i = 0; i < p; i++) {
            if (plan.isColoured[i]) {
                continue;
            }
            int col = lay.colUnc[i];
            int pre = ft.preVector()[i];
            if (pre > 0) {
                enab.add(ctx.mkGe(lay.cur[col], ctx.mkInt(pre)));
            }
            if (contains(ft.resetPlaces(), i) || ft.consumeAll()[i]) {
                upd.put(col, ctx.mkInt(ft.postVector()[i]));
            } else {
                int delta = ft.postVector()[i] - ft.preVector()[i];
                if (delta > 0) {
                    upd.put(col, ctx.mkAdd(lay.cur[col], ctx.mkInt(delta)));
                } else if (delta < 0) {
                    upd.put(col, ctx.mkSub(lay.cur[col], ctx.mkInt(-delta)));
                }
            }
        }
        // Inhibitor / read arcs (all on uncoloured places — checked in buildPlan).
        for (int pid : ft.inhibitorPlaces()) {
            enab.add(ctx.mkEq(lay.cur[lay.colUnc[pid]], ctx.mkInt(0)));
        }
        for (int pid : ft.readPlaces()) {
            enab.add(ctx.mkGe(lay.cur[lay.colUnc[pid]], ctx.mkInt(1)));
        }
    }

    /**
     * Lifts a flat P-invariant to the coloured layout: a coloured place's variable
     * becomes the sum of its colours (= its aggregate count), so the (true) flat
     * invariant constrains the coloured successor without excluding any reachable
     * state.
     */
    private static BoolExpr liftedInvariant(
            Context ctx, PInvariant inv, ColouredPlan plan, Layout lay, Expr<IntSort>[] vars) {
        if (inv.support().isEmpty()) {
            return null;
        }
        ArithExpr<IntSort> sum = ctx.mkInt(0);
        for (int i : inv.support()) {
            ArithExpr<IntSort> agg = aggregate(ctx, i, plan, lay, vars);
            int w = inv.weights()[i];
            sum = ctx.mkAdd(sum, w == 1 ? agg : ctx.mkMul(ctx.mkInt(w), agg));
        }
        return ctx.mkEq(sum, ctx.mkInt(inv.constant()));
    }

    /**
     * Aggregate token-count expression for a place over the given var-set: the
     * single uncoloured var, or the sum of its colours.
     */
    private static ArithExpr<IntSort> aggregate(
            Context ctx, int place, ColouredPlan plan, Layout lay, Expr<IntSort>[] vars) {
        if (plan.isColoured[place]) {
            int[] cols = lay.colCol[place];
            ArithExpr<IntSort> sum = (ArithExpr<IntSort>) vars[cols[0]];
            for (int c = 1; c < cols.length; c++) {
                sum = ctx.mkAdd(sum, vars[cols[c]]);
            }
            return sum;
        }
        return (ArithExpr<IntSort>) vars[lay.colUnc[place]];
    }

    /** Encodes the error rule: a reachable marking that violates the property. */
    @SuppressWarnings("unchecked")
    private static void addErrorRule(
            Context ctx, Fixedpoint fp, FuncDecl<BoolSort> reachable, FuncDecl<BoolSort> error,
            Layout lay, ColouredPlan plan, FlatNet flat, SmtProperty property) {
        int nCols = lay.nCols;
        IntSort intSort = ctx.getIntSort();
        Symbol[] names = new Symbol[nCols];
        Sort[] sorts = new Sort[nCols];
        Expr<IntSort>[] cur = new Expr[nCols];
        for (int col = 0; col < nCols; col++) {
            names[col] = ctx.mkSymbol("c" + col);
            sorts[col] = intSort;
            cur[col] = (Expr<IntSort>) ctx.mkBound(nCols - 1 - col, intSort);
        }

        BoolExpr reachBody = (BoolExpr) reachable.apply(cur);
        BoolExpr violation = encodeViolation(ctx, plan, lay, flat, property, cur);
        BoolExpr body = ctx.mkAnd(reachBody, violation);
        BoolExpr rule = ctx.mkImplies(body, (BoolExpr) error.apply());
        Quantifier qRule = ctx.mkForall(sorts, names, rule, 1, null, null, null, null);
        fp.addRule(qRule, ctx.mkSymbol("error"));
    }

    /**
     * Encodes the property-violation condition over the coloured current marking.
     * Only reachability-safety properties are routed here (the verifier guarantees
     * it); quiescence properties yield {@code false} (no violating state).
     */
    private static BoolExpr encodeViolation(
            Context ctx, ColouredPlan plan, Layout lay, FlatNet flat,
            SmtProperty property, Expr<IntSort>[] cur) {
        return switch (property) {
            case SmtProperty.PlaceBound pb -> boundViolation(ctx, plan, lay, flat, pb.place().name(), pb.bound(), cur);
            case SmtProperty.BranchPlaceBound bpb -> boundViolation(ctx, plan, lay, flat, bpb.place().name(), bpb.bound(), cur);
            case SmtProperty.MutualExclusion me -> {
                Integer i1 = flatIndex(flat, me.p1().name());
                Integer i2 = flatIndex(flat, me.p2().name());
                if (i1 == null || i2 == null) {
                    yield ctx.mkFalse();
                }
                yield ctx.mkAnd(
                    ctx.mkGe(aggregate(ctx, i1, plan, lay, cur), ctx.mkInt(1)),
                    ctx.mkGe(aggregate(ctx, i2, plan, lay, cur), ctx.mkInt(1)));
            }
            case SmtProperty.Unreachable ur -> {
                List<BoolExpr> conds = new ArrayList<>();
                for (var place : ur.places()) {
                    Integer pid = flatIndex(flat, place.name());
                    if (pid != null) {
                        conds.add(ctx.mkGe(aggregate(ctx, pid, plan, lay, cur), ctx.mkInt(1)));
                    }
                }
                yield conds.isEmpty() ? ctx.mkFalse() : ctx.mkAnd(conds.toArray(new BoolExpr[0]));
            }
            // Quiescence properties are never routed here.
            case SmtProperty.DeadlockFree _, SmtProperty.JoinedOrDeadLettered _ -> ctx.mkFalse();
        };
    }

    private static BoolExpr boundViolation(
            Context ctx, ColouredPlan plan, Layout lay, FlatNet flat,
            String placeName, int bound, Expr<IntSort>[] cur) {
        Integer pid = flatIndex(flat, placeName);
        if (pid == null) {
            return ctx.mkFalse();
        }
        return ctx.mkGt(aggregate(ctx, pid, plan, lay, cur), ctx.mkInt(bound));
    }

    // === small helpers ===

    private static Integer flatIndex(FlatNet flat, String name) {
        for (int i = 0; i < flat.placeCount(); i++) {
            if (flat.places().get(i).name().equals(name)) {
                return i;
            }
        }
        return null;
    }

    private static int[] indicesOf(boolean[] flags) {
        int n = 0;
        for (boolean f : flags) {
            if (f) {
                n++;
            }
        }
        int[] out = new int[n];
        int j = 0;
        for (int i = 0; i < flags.length; i++) {
            if (flags[i]) {
                out[j++] = i;
            }
        }
        return out;
    }

    private static int[] colouredWithPositive(int[] coloured, int[] vec) {
        int n = 0;
        for (int pid : coloured) {
            if (vec[pid] > 0) {
                n++;
            }
        }
        int[] out = new int[n];
        int j = 0;
        for (int pid : coloured) {
            if (vec[pid] > 0) {
                out[j++] = pid;
            }
        }
        return out;
    }

    private static boolean anyColoured(int[] indices, boolean[] isColoured) {
        for (int i : indices) {
            if (isColoured[i]) {
                return true;
            }
        }
        return false;
    }

    private static boolean anyConsumeAllColoured(boolean[] consumeAll, boolean[] isColoured) {
        for (int i = 0; i < consumeAll.length; i++) {
            if (consumeAll[i] && isColoured[i]) {
                return true;
            }
        }
        return false;
    }

    private static boolean contains(int[] arr, int v) {
        for (int x : arr) {
            if (x == v) {
                return true;
            }
        }
        return false;
    }
}
