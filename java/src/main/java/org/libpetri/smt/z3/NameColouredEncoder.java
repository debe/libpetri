package org.libpetri.smt.z3;

import com.microsoft.z3.*;
import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
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
 * <p>The flat {@link SmtEncoder} is a pure <em>counting</em> abstraction: a place is
 * one integer, and a matched (&nu;-join) transition is encoded name-blind — it fires
 * whenever the input <em>counts</em> allow, regardless of whether the consumed tokens
 * actually share a correlation name. That over-approximation is sound for
 * {@code Proven} on reachability-safety bounds but can report a <b>spurious</b>
 * {@code Violated} whose counterexample silently equates two <em>distinct</em> names.
 *
 * <p>This encoder removes that imprecision for the bounded fragment. The decidability
 * lever (NU-040) is a bounded live-name count: a budget place gates minting, and a
 * non-negative <b>P-semiflow</b> weighting every coloured place bounds the
 * simultaneously-live names to a finite {@code k} ({@code Σ_{coloured} M <= y·M0}; see
 * {@link #buildPlan} / {@link #colourSlotBound}). So names are modelled as a
 * <b>finite set of {@code k} colours</b>. Each coloured place becomes {@code k}
 * per-colour integer counts; a mint introduces a <em>globally-fresh</em> colour; a
 * matched join consumes the <b>same colour</b> from every correlated input. Within the
 * budget bound the encoding is <em>exact</em>.
 *
 * <p><b>Supported fragment.</b> {@link #buildPlan} returns {@code null} (and the
 * verifier falls back to the sound over-approximation) unless the net is in the
 * budget-bounded coloured fragment:
 * <ul>
 *   <li>coloured places = the correlated inputs of every matched transition, plus (in
 *       EXTENDED mode, NU-051) the declared carrier places;</li>
 *   <li>each coloured place is <em>produced only by</em> minting forks (count 1, no
 *       coloured input, costs &ge;1 budget token) or EXTENDED relays, and
 *       <em>consumed only by</em> matched joins or EXTENDED coloured consumers — a relay
 *       threads one colour on, a drain drops it, each consuming exactly one coloured
 *       input at count 1;</li>
 *   <li>the coloured place set is structurally token-bounded: some non-negative
 *       P-semiflow weights every coloured place, so the simultaneously-live colour count
 *       is bounded by that semiflow's initial value {@code k}
 *       ({@code Σ_{coloured} M <= y·M0}). A net with no covering non-negative semiflow
 *       (an unbounded colour leak) falls back;</li>
 *   <li>coloured places start empty; no inhibitor/read/reset/consume-all arc touches a
 *       coloured place.</li>
 * </ul>
 *
 * <p>XOR output branches are supported (NU-053, Part 3): each branch is a separate flat
 * row classified by its own incidence, with {@code matchSpec} read from its source.
 *
 * <p><b>Properties.</b> Reachability-safety properties compare aggregate coloured place
 * counts. Quiescence properties ({@code DeadlockFree}, {@code JoinedOrDeadLettered})
 * use a colour-aware deadlock predicate (NU-053, Part 2): every transition is disabled
 * for every colour (a mint has no globally-fresh colour, a join no shared colour, a
 * consumer no resident colour) and the marking is not a sink state — mirroring the flat
 * {@link SmtEncoder} deadlock with the same env-injection relaxation.
 *
 * <p>This mirrors the Rust reference {@code name_coloured_encoder.rs} exactly; the only
 * difference is that this encoder builds Z3 {@link BoolExpr} objects via the native Java
 * bindings rather than emitting SMT-LIB2 text.
 */
public final class NameColouredEncoder {

    private NameColouredEncoder() {}

    /** How a transition relates to the coloured (correlation-carrying) places. */
    private sealed interface Klass permits Mint, Join, Consume, Untouched {}

    /** Minting fork: produces a freshly-coloured token into each listed place. */
    private record Mint(int[] colouredOut) implements Klass {}

    /** Matched join: consumes one same-coloured token from each listed place. */
    private record Join(int[] colouredIn) implements Klass {}

    /**
     * EXTENDED coloured consumer (NU-051): a non-match transition that consumes one
     * same-coloured token from {@code inputCol} (count 1) and threads it into each
     * {@code colouredOut} (relay) or into none (drain — {@code colouredOut} empty).
     */
    private record Consume(int inputCol, int[] colouredOut) implements Klass {}

    /** Touches no coloured place — a pure counting transition. */
    private record Untouched() implements Klass {}

    /**
     * A validated plan for the name-coloured encoding of a budget-bounded &nu;-net.
     * Opaque to the verifier except for {@link #k()} and {@link #colouredCount()} (used
     * only for a report line); the encoder reads the remaining fields directly (same
     * enclosing class).
     */
    public static final class ColouredPlan {
        /** Flat indices of the coloured places (sorted ascending). */
        final int[] coloured;
        /** Per flat place: whether it is coloured. */
        final boolean[] isColoured;
        /** Colour bound — the number of simultaneously-live names (the colour-slot bound). */
        final int k;
        /** Classification, one entry per flat transition (XOR branches included). */
        final List<Klass> classes;

        private ColouredPlan(int[] coloured, boolean[] isColoured, int k, List<Klass> classes) {
            this.coloured = coloured;
            this.isColoured = isColoured;
            this.k = k;
            this.classes = classes;
        }

        /** The colour bound (the colour-slot bound from the covering P-semiflow). */
        public int k() {
            return k;
        }

        /** The number of coloured places. */
        public int colouredCount() {
            return coloured.length;
        }
    }

    /**
     * Detects whether {@code net} is in the supported budget-bounded coloured fragment
     * (mint&rarr;matched-join, plus the EXTENDED coloured consumers and carrier places of
     * NU-051, with XOR-expanded output branches) and, if so, returns the plan for
     * {@link #encode}. Returns {@code null} otherwise — the verifier then uses the sound
     * over-approximation.
     *
     * @param net              source net (for match specs)
     * @param flat             flattened net (each flat row carries its source transition)
     * @param initial          initial marking
     * @param budgetPlaceNames declared budget-place names (NU-040)
     * @param fragmentMode     BASE (mint&rarr;matched-join only) or EXTENDED (NU-051)
     * @param carrierPlaces    EXTENDED carrier-place names (ignored under BASE)
     * @param invariants       the net's non-negative P-semiflows (used to bound the
     *                         colour-slot count {@code k} via {@link #colourSlotBound})
     */
    public static ColouredPlan buildPlan(
            PetriNet net, FlatNet flat, MarkingState initial,
            Set<String> budgetPlaceNames, FragmentMode fragmentMode, Set<String> carrierPlaces,
            List<PInvariant> invariants) {
        int p = flat.placeCount();

        // Each flat row already carries its source transition (an XOR transition expands
        // to one flat row per output branch), so we read `matchSpec` from the source while
        // classifying by the flat row's own incidence — no 1:1 net↔flat assumption.

        // Place name -> flat index (Java FlatNet.placeIndex is keyed by Place, not name;
        // resolve matched + budget + carrier places by name to match the Rust contract).
        Map<String, Integer> nameIdx = new HashMap<>();
        for (int i = 0; i < p; i++) {
            nameIdx.put(flat.places().get(i).name(), i);
        }

        // 1. Coloured places = every matched transition's correlated inputs, plus (in
        //    EXTENDED mode) the declared carrier places that thread a fork-minted name
        //    through intermediate places to a ν-join input (NU-051).
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
        if (fragmentMode == FragmentMode.EXTENDED) {
            for (String c : carrierPlaces) {
                Integer pid = nameIdx.get(c);
                if (pid != null) {
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

        // Colour-slot bound k: a colour is live iff some coloured place holds it, so
        // #live colours ≤ Σ_{coloured} M(p) ≤ y·M0 for any non-negative P-semiflow y
        // weighting every coloured place ≥ 1. k is the tightest such y·M0 (each
        // PInvariant.constant is y·M0); any k ≥ #live is sound — a larger k only costs O(k)
        // columns, never under-approximates, since a mint may take any free slot behind the
        // freshness guard. If no covering non-negative semiflow exists the coloured set is
        // not structurally token-bounded (a genuine unbounded colour leak), so fall back to
        // the sound over-approximation. This replaces the old budget-count k and both
        // structural discipline checks (atomic-rejoin + budget-Φ) below.
        Integer kBound = colourSlotBound(coloured, invariants);
        if (kBound == null) {
            return null;
        }
        int k = kBound;
        // NU-053 AC6: k = 0 is an exact plan — no coloured token can ever exist, so every
        // mint / join / consumer is dead and the zero-slot encoding emits no rule for them
        // (Semiflow.lean, vacuous_colour_layer). The one shape it cannot encode is a net
        // with no uncoloured place at all (Reachable would be nullary and every rule's
        // quantifier empty); such a net holds no token at M0, so fall back to the flat
        // encoding.
        if (k == 0 && coloured.length == p) {
            return null;
        }

        // Budget places gate minting: a mint must consume ≥1 budget token — that is what
        // makes it a fresh-name fork rather than an arbitrary coloured producer.
        Set<Integer> budgetIdx = new HashSet<>();
        for (String n : budgetPlaceNames) {
            Integer i = nameIdx.get(n);
            if (i != null) {
                budgetIdx.add(i);
            }
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

        // 2. Classify each flat row from its own incidence (matchSpec from its source).
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
            } else if (colouredIn.length != 0) {
                // EXTENDED coloured consumer (relay/drain, NU-051): a non-match transition
                // consuming a coloured place. Admitted only in EXTENDED mode, and only when
                // it consumes EXACTLY ONE coloured input at count EXACTLY ONE (higher counts
                // would over-count the name layer against the base marking's single token per
                // place). It relays the name into its coloured outputs (each at count 1) or
                // drains it (no coloured output).
                if (fragmentMode != FragmentMode.EXTENDED) {
                    return null;
                }
                if (colouredIn.length != 1 || ft.preVector()[colouredIn[0]] != 1) {
                    return null;
                }
                for (int o : colouredOut) {
                    if (ft.postVector()[o] != 1) {
                        return null;
                    }
                }
                klass = new Consume(colouredIn[0], colouredOut);
            } else if (colouredOut.length != 0) {
                // Minting fork: produces coloured (count 1), consumes none, costs budget.
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
                klass = new Untouched();
            }
            classes.add(klass);
        }

        return new ColouredPlan(coloured, isColoured, k, classes);
    }

    /**
     * Sound colour-slot bound {@code k}: a colour is live iff some coloured place holds
     * it, so {@code #live colours <= Σ_{coloured} M(p) <= y·M0} for any non-negative
     * P-semiflow {@code y} ({@code y·C = 0}, {@code y >= 0}) that weights every coloured
     * place {@code >= 1}. Returns the tightest such {@code y·M0} (each
     * {@link PInvariant#constant()} is {@code y·M0}), or {@code null} when no covering
     * non-negative semiflow exists — the coloured set is then not structurally
     * token-bounded (a genuine unbounded colour leak) and the caller must fall back.
     *
     * <p>{@code 0} is a bound like any other (NU-053 AC6): with the covering law's initial
     * sum at zero no coloured token can ever exist, every mint / join / consumer is dead on
     * the reachable set, and the zero-slot plan is exact ({@code Semiflow.lean},
     * {@code vacuous_colour_layer}). A validated semi-positive law's {@code y·M0} is never
     * negative.
     */
    private static Integer colourSlotBound(int[] coloured, List<PInvariant> invariants) {
        // Tightest bound: a single non-negative P-semiflow weighting every coloured place.
        Integer single = null;
        for (PInvariant inv : invariants) {
            if (!isSemiflow(inv)) {
                continue;
            }
            boolean coversAll = true;
            for (int pid : coloured) {
                if (weightAt(inv, pid) < 1) {
                    coversAll = false;
                    break;
                }
            }
            if (coversAll) {
                single = (single == null) ? inv.constant() : Math.min(single, inv.constant());
            }
        }
        if (single != null) {
            return single;
        }

        // Otherwise sum non-negative semiflows that touch a coloured place — the sum is
        // itself a valid non-negative P-semiflow, so Σ y·M0 over any covering set is a
        // sound (looser) bound. Zero-constant semiflows cover their places for free, so
        // they go in first; a semiflow with a positive constant is added only if it
        // touches a coloured place the free ones left uncovered (decided against that
        // snapshot, so the result does not depend on enumeration order). If some
        // coloured place stays at weight 0 across all of them, no non-negative semiflow
        // covers it, so the coloured set is not structurally token-bounded → null
        // (sound over-approximation).
        boolean[] covered = new boolean[coloured.length];
        for (PInvariant inv : invariants) {
            if (!isSemiflow(inv) || inv.constant() != 0) {
                continue;
            }
            for (int i = 0; i < coloured.length; i++) {
                if (weightAt(inv, coloured[i]) >= 1) {
                    covered[i] = true;
                }
            }
        }
        boolean[] free = covered.clone();
        long sumConst = 0;
        for (PInvariant inv : invariants) {
            if (!isSemiflow(inv) || inv.constant() == 0) {
                continue;
            }
            boolean touchesUncovered = false;
            for (int i = 0; i < coloured.length; i++) {
                if (!free[i] && weightAt(inv, coloured[i]) >= 1) {
                    touchesUncovered = true;
                    break;
                }
            }
            if (!touchesUncovered) {
                continue;
            }
            for (int i = 0; i < coloured.length; i++) {
                if (weightAt(inv, coloured[i]) >= 1) {
                    covered[i] = true;
                }
            }
            sumConst += inv.constant();
        }
        boolean allCovered = true;
        for (boolean c : covered) {
            if (!c) {
                allCovered = false;
                break;
            }
        }
        return allCovered ? (int) sumConst : null;
    }

    /** Weight of place {@code pid} in {@code inv} (0 if out of range). */
    private static int weightAt(PInvariant inv, int pid) {
        int[] w = inv.weights();
        return (pid >= 0 && pid < w.length) ? w[pid] : 0;
    }

    /** Whether every weight is non-negative — i.e. a genuine non-negative P-semiflow. */
    private static boolean isSemiflow(PInvariant inv) {
        for (int x : inv.weights()) {
            if (x < 0) {
                return false;
            }
        }
        return true;
    }

    /** Column layout: uncoloured place -> one var; coloured place -> k per-colour vars. */
    @SuppressWarnings("unused")
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
            // forall(c0..c_{nCols-1}, cp0..cp_{nCols-1}): de Bruijn — cp_{nCols-1} is
            // innermost (index 0). cur[col] = mkBound(2*nCols-1-col), nxt[col] =
            // mkBound(nCols-1-col). Mirrors SmtEncoder's transition-rule indexing.
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

    /** Contributes a rule's enablement guards and changed-column updates. */
    @FunctionalInterface
    private interface Fill {
        void apply(List<BoolExpr> enab, Map<Integer, Expr<IntSort>> upd);
    }

    /**
     * Encodes the supported &nu;-net as bounded name-coloured CHC for Z3 Spacer. Reuses
     * {@link SmtEncoder.EncodingResult}; with the query {@code (not Error)}, {@code sat}
     * &rArr; PROVEN, {@code unsat} &rArr; VIOLATED (the Spacer convention shared with
     * {@link SmtEncoder}).
     *
     * @param sinkPlaces terminal places (a quiescent marking holding only sinks is not a
     *                   deadlock) — used by the colour-aware deadlock predicate
     */
    public static SmtEncoder.EncodingResult encode(
            Context ctx, Fixedpoint fp, ColouredPlan plan, FlatNet flat,
            MarkingState initial, SmtProperty property, List<PInvariant> invariants,
            Set<Place<?>> sinkPlaces) {
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
                        ft.name(), (enab, upd) -> uncolouredIncidence(ctx, lay, plan, ft, enab, upd));
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
                case Consume co -> {
                    // One rule per colour: consume colour cc from the single coloured input
                    // and thread it into each coloured output (relay), or into none (drain).
                    for (int c = 0; c < k; c++) {
                        final int cc = c;
                        addRule(ctx, fp, reachable, lay, plan, invariants,
                            ft.name() + "_consume_" + cc, (enab, upd) -> {
                                uncolouredIncidence(ctx, lay, plan, ft, enab, upd);
                                int icol = lay.colCol[co.inputCol()][cc];
                                enab.add(ctx.mkGe(lay.cur[icol], ctx.mkInt(1)));
                                upd.put(icol, ctx.mkSub(lay.cur[icol], ctx.mkInt(1)));
                                for (int o : co.colouredOut()) {
                                    int ocol = lay.colCol[o][cc];
                                    upd.put(ocol, ctx.mkAdd(lay.cur[ocol], ctx.mkInt(1)));
                                }
                            });
                    }
                }
            }
        }

        // Error rule. `false` ⇒ the property names an unresolved place; refuse to
        // build a vacuously-provable encoding and let the verifier report Unknown.
        if (!addErrorRule(ctx, fp, reachable, error, lay, plan, flat, property, sinkPlaces)) {
            return null;
        }

        return new SmtEncoder.EncodingResult((BoolExpr) error.apply(), reachable);
    }

    /**
     * Builds one transition CHC rule. {@code fill} contributes the enablement guards and
     * the changed-column updates; every other column is copied unchanged, changed columns
     * get a non-negativity guard, and the (lifted) P-invariants constrain the successor.
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

        // A changed column gets its update + non-negativity guard; every other column is
        // copied unchanged.
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
     * Pushes the enablement guards and column updates contributed by a transition's
     * <b>uncoloured</b> incidence (consume/produce on non-coloured places). Coloured
     * columns are handled by the caller (mint produces, join/consumer consume). Mirrors
     * the Rust reference — no blanket current-marking non-negativity guard (the Reachable
     * invariant carries that).
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
     * becomes the sum of its colours (= its aggregate count). Returns {@code null} when
     * the invariant support is empty.
     */
    @SuppressWarnings("unchecked")
    private static BoolExpr liftedInvariant(
            Context ctx, PInvariant inv, ColouredPlan plan, Layout lay, Expr<IntSort>[] vars) {
        if (inv.support().isEmpty()) {
            return null;
        }
        ArithExpr<IntSort> sum = ctx.mkInt(0);
        boolean any = false;
        for (int i : inv.support()) {
            ArithExpr<IntSort> agg = aggregate(ctx, i, plan, lay, vars);
            int w = inv.weights()[i];
            ArithExpr<IntSort> term = (w == 1) ? agg : ctx.mkMul(ctx.mkInt(w), agg);
            sum = ctx.mkAdd(sum, term);
            any = true;
        }
        if (!any) {
            return null;
        }
        return ctx.mkEq(sum, ctx.mkInt(inv.constant()));
    }

    /**
     * Aggregate token-count expression for a place over the given var-set: the single
     * uncoloured var, or the sum of its colours.
     */
    @SuppressWarnings("unchecked")
    private static ArithExpr<IntSort> aggregate(
            Context ctx, int place, ColouredPlan plan, Layout lay, Expr<IntSort>[] vars) {
        if (plan.isColoured[place]) {
            int[] cols = lay.colCol[place];
            if (cols.length == 0) {
                // k = 0: a coloured place has no slot and never holds a token.
                return ctx.mkInt(0);
            }
            ArithExpr<IntSort> sum = (ArithExpr<IntSort>) vars[cols[0]];
            for (int c = 1; c < cols.length; c++) {
                sum = ctx.mkAdd(sum, vars[cols[c]]);
            }
            return sum;
        }
        return (ArithExpr<IntSort>) vars[lay.colUnc[place]];
    }

    /** Encodes the error rule: a reachable marking that violates the property. */
    /**
     * Adds the error CHC rule, or returns {@code false} when the property names a
     * place that does not resolve in the net ({@link #encodeViolation} returned
     * {@code null}). In that case no rule is added and the caller reports Unknown
     * rather than certify a vacuous PROVEN.
     */
    @SuppressWarnings("unchecked")
    private static boolean addErrorRule(
            Context ctx, Fixedpoint fp, FuncDecl<BoolSort> reachable, FuncDecl<BoolSort> error,
            Layout lay, ColouredPlan plan, FlatNet flat, SmtProperty property, Set<Place<?>> sinkPlaces) {
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

        Map<Integer, Integer> envInj = injectedEnvIndices(flat);
        BoolExpr reachBody = (BoolExpr) reachable.apply(cur);
        BoolExpr violation = encodeViolation(ctx, plan, lay, flat, property, sinkPlaces, envInj, cur);
        if (violation == null) {
            return false; // unresolved property place → signal Unknown
        }
        BoolExpr body = ctx.mkAnd(reachBody, violation);
        BoolExpr rule = ctx.mkImplies(body, (BoolExpr) error.apply());
        Quantifier qRule = ctx.mkForall(sorts, names, rule, 1, null, null, null, null);
        fp.addRule(qRule, ctx.mkSymbol("error"));
        return true;
    }

    /**
     * Encodes the property-violation condition over the coloured current marking.
     * Reachability-safety properties compare aggregate place counts; quiescence
     * properties (NU-053) use the colour-aware deadlock predicate.
     *
     * <p>Returns {@code null} when the property names a place that does not resolve
     * in the net (e.g. a typo'd bound/pending place). A {@code false} violation term
     * there would make the Error rule unsatisfiable and yield a <b>vacuous</b>
     * PROVEN, silently certifying a mis-named place; {@code null} propagates up so
     * the verifier reports Unknown instead.
     */
    private static BoolExpr encodeViolation(
            Context ctx, ColouredPlan plan, Layout lay, FlatNet flat,
            SmtProperty property, Set<Place<?>> sinkPlaces, Map<Integer, Integer> envInj,
            Expr<IntSort>[] cur) {
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
            case SmtProperty.DeadlockFree _ ->
                encodeColouredDeadlock(ctx, plan, lay, flat, sinkPlaces, envInj, cur);
            case SmtProperty.JoinedOrDeadLettered jdl -> {
                Integer pid = flatIndex(flat, jdl.pending().name());
                if (pid == null) {
                    // Unresolved pending place: a false violation term would make the
                    // Error rule unsatisfiable → a vacuous PROVEN. Signal Unknown instead.
                    yield null;
                }
                BoolExpr deadlock = encodeColouredDeadlock(ctx, plan, lay, flat, sinkPlaces, envInj, cur);
                yield ctx.mkAnd(deadlock, ctx.mkGe(aggregate(ctx, pid, plan, lay, cur), ctx.mkInt(1)));
            }
        };
    }

    private static BoolExpr boundViolation(
            Context ctx, ColouredPlan plan, Layout lay, FlatNet flat,
            String placeName, int bound, Expr<IntSort>[] cur) {
        Integer pid = flatIndex(flat, placeName);
        if (pid == null) {
            // Unresolved bound place: a false violation term would vacuously PROVE the
            // bound. Return null so the verifier reports Unknown instead of certifying.
            return null;
        }
        return ctx.mkGt(aggregate(ctx, pid, plan, lay, cur), ctx.mkInt(bound));
    }

    /**
     * Colour-aware deadlock predicate (NU-053): every transition is disabled (no colour
     * enables it) and the marking is not a sink state. Mirrors {@link SmtEncoder}'s flat
     * {@code encodeDeadlock} with the same env-injection relaxation (VER-006), lifted to
     * the coloured layout.
     */
    private static BoolExpr encodeColouredDeadlock(
            Context ctx, ColouredPlan plan, Layout lay, FlatNet flat,
            Set<Place<?>> sinkPlaces, Map<Integer, Integer> envInj, Expr<IntSort>[] cur) {
        List<BoolExpr> disabledConditions = new ArrayList<>();
        for (int ti = 0; ti < plan.classes.size(); ti++) {
            Klass cls = plan.classes.get(ti);
            FlatTransition ft = flat.transitions().get(ti);
            List<BoolExpr> reasons = new ArrayList<>();
            boolean permanentlyDisabled = uncolouredDisable(ctx, ft, lay, plan, envInj, cur, reasons);
            if (permanentlyDisabled) {
                // The transition can never fire — it is always "disabled".
                disabledConditions.add(ctx.mkTrue());
                continue;
            }
            BoolExpr term = colouredDisabledTerm(ctx, cls, plan, lay, cur);
            if (term != null) {
                reasons.add(term);
            }
            if (reasons.isEmpty()) {
                // Always enabled (possibly via injection) — no marking is a deadlock.
                return ctx.mkFalse();
            }
            disabledConditions.add(reasons.size() == 1
                ? reasons.get(0)
                : ctx.mkOr(reasons.toArray(new BoolExpr[0])));
        }

        // Not a sink state: some non-sink place still holds a token (aggregate count).
        Set<Integer> sinkIndices = new HashSet<>();
        for (var sink : sinkPlaces) {
            int idx = flat.indexOf(sink);
            if (idx >= 0) {
                sinkIndices.add(idx);
            }
        }
        if (!sinkIndices.isEmpty()) {
            List<BoolExpr> nonSink = new ArrayList<>();
            for (int pid = 0; pid < flat.placeCount(); pid++) {
                if (!sinkIndices.contains(pid)) {
                    nonSink.add(ctx.mkGe(aggregate(ctx, pid, plan, lay, cur), ctx.mkInt(1)));
                }
            }
            if (!nonSink.isEmpty()) {
                disabledConditions.add(ctx.mkOr(nonSink.toArray(new BoolExpr[0])));
            }
        }

        if (disabledConditions.isEmpty()) {
            return ctx.mkTrue();
        }
        return ctx.mkAnd(disabledConditions.toArray(new BoolExpr[0]));
    }

    /**
     * The uncoloured disable reasons for a flat row: marking-dependent clauses (any one
     * true ⇒ the transition's uncoloured part is unmet), collected into {@code reasons};
     * returns {@code true} when the transition is permanently disabled (an env cap below
     * the demand means it can never fire). Coloured places are excluded — their
     * enablement is the per-class colour term. Mirrors {@link SmtEncoder}'s flat deadlock
     * with the same env relaxation.
     */
    private static boolean uncolouredDisable(
            Context ctx, FlatTransition ft, Layout lay, ColouredPlan plan,
            Map<Integer, Integer> envInj, Expr<IntSort>[] cur, List<BoolExpr> reasons) {
        boolean permanentlyDisabled = false;
        int p = ft.preVector().length;
        for (int i = 0; i < p; i++) {
            if (plan.isColoured[i] || ft.preVector()[i] == 0) {
                continue;
            }
            if (envInj.containsKey(i)) {
                Integer bound = envInj.get(i);
                if (bound != null && ft.preVector()[i] > bound) {
                    permanentlyDisabled = true;
                }
                continue;
            }
            reasons.add(ctx.mkLt(cur[lay.colUnc[i]], ctx.mkInt(ft.preVector()[i])));
        }
        for (int inh : ft.inhibitorPlaces()) {
            reasons.add(ctx.mkGt(cur[lay.colUnc[inh]], ctx.mkInt(0)));
        }
        for (int rd : ft.readPlaces()) {
            if (envInj.containsKey(rd)) {
                Integer bound = envInj.get(rd);
                if (bound != null && bound < 1) {
                    permanentlyDisabled = true;
                }
                continue;
            }
            reasons.add(ctx.mkLt(cur[lay.colUnc[rd]], ctx.mkInt(1)));
        }
        return permanentlyDisabled;
    }

    /**
     * The colour-specific "disabled for every colour" term for a class ({@code null} if
     * the class imposes no coloured enablement constraint). Combined by the caller with
     * the uncoloured disable reasons: the transition is disabled if EITHER holds.
     */
    private static BoolExpr colouredDisabledTerm(
            Context ctx, Klass cls, ColouredPlan plan, Layout lay, Expr<IntSort>[] cur) {
        int k = plan.k;
        if (k == 0) {
            // k = 0 (NU-053 AC6): no colour can ever be present, so every coloured class is
            // disabled outright rather than by an empty (nullary) conjunction.
            return cls instanceof Untouched ? null : ctx.mkTrue();
        }
        return switch (cls) {
            case Untouched _ -> null;
            case Mint _ -> {
                // No globally-fresh colour: for every colour c, some coloured place holds c.
                BoolExpr[] perColour = new BoolExpr[k];
                for (int c = 0; c < k; c++) {
                    BoolExpr[] present = new BoolExpr[plan.coloured.length];
                    for (int qi = 0; qi < plan.coloured.length; qi++) {
                        int q = plan.coloured[qi];
                        present[qi] = ctx.mkGe(cur[lay.colCol[q][c]], ctx.mkInt(1));
                    }
                    perColour[c] = ctx.mkOr(present);
                }
                yield ctx.mkAnd(perColour);
            }
            case Join j -> {
                // No colour is shared by all correlated inputs: for every colour c, some
                // input lacks c.
                BoolExpr[] perColour = new BoolExpr[k];
                for (int c = 0; c < k; c++) {
                    BoolExpr[] missing = new BoolExpr[j.colouredIn().length];
                    for (int ii = 0; ii < j.colouredIn().length; ii++) {
                        int inCol = j.colouredIn()[ii];
                        missing[ii] = ctx.mkEq(cur[lay.colCol[inCol][c]], ctx.mkInt(0));
                    }
                    perColour[c] = ctx.mkOr(missing);
                }
                yield ctx.mkAnd(perColour);
            }
            case Consume co -> {
                // No colour present at the single coloured input.
                BoolExpr[] perColour = new BoolExpr[k];
                for (int c = 0; c < k; c++) {
                    perColour[c] = ctx.mkEq(cur[lay.colCol[co.inputCol()][c]], ctx.mkInt(0));
                }
                yield ctx.mkAnd(perColour);
            }
        };
    }

    // === small helpers ===

    /** Maps injected environment-place index -> injection bound ({@code null} = unbounded). */
    private static Map<Integer, Integer> injectedEnvIndices(FlatNet flat) {
        Map<Integer, Integer> out = new HashMap<>();
        for (var entry : flat.environmentInjection().entrySet()) {
            int idx = flat.indexOf(entry.getKey());
            if (idx >= 0) {
                out.put(idx, entry.getValue());
            }
        }
        return out;
    }

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

    /** The subset of {@code coloured} indices whose vector entry is positive. */
    private static int[] colouredWithPositive(int[] coloured, int[] vector) {
        int n = 0;
        for (int pid : coloured) {
            if (vector[pid] > 0) {
                n++;
            }
        }
        int[] out = new int[n];
        int j = 0;
        for (int pid : coloured) {
            if (vector[pid] > 0) {
                out[j++] = pid;
            }
        }
        return out;
    }

    private static boolean anyColoured(int[] placeIndices, boolean[] isColoured) {
        for (int i : placeIndices) {
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
