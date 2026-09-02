package org.libpetri.smt.z3;

import org.libpetri.analysis.FragmentMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.FlatTransition;
import org.libpetri.smt.invariant.PInvariant;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

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
 * <p>This mirrors the Rust reference {@code name_coloured_encoder.rs} exactly and emits
 * the same SMT-LIB2 text byte for byte (VER-013).
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
    private static final class Layout {
        /** Column index of each uncoloured place ({@code -1} if coloured). */
        final int[] colUnc;
        /** Per coloured place: its {@code k} column indices (empty if uncoloured). */
        final int[][] colCol;
        /** Current-marking variable names, one per column. */
        final List<String> cur = new ArrayList<>();
        /** Next-marking variable names, one per column. */
        final List<String> nxt = new ArrayList<>();

        Layout(ColouredPlan plan, int p) {
            this.colUnc = new int[p];
            this.colCol = new int[p][];
            for (int i = 0; i < p; i++) {
                if (plan.isColoured[i]) {
                    int[] idxs = new int[plan.k];
                    for (int c = 0; c < plan.k; c++) {
                        idxs[c] = cur.size();
                        cur.add("m" + i + "_" + c);
                        nxt.add("m" + i + "_" + c + "p");
                    }
                    colCol[i] = idxs;
                    colUnc[i] = -1;
                } else {
                    colUnc[i] = cur.size();
                    colCol[i] = new int[0];
                    cur.add("m" + i);
                    nxt.add("m" + i + "p");
                }
            }
        }

        /**
         * Aggregate token-count expression for a place over the given var-set ({@code cur}
         * or {@code nxt}): the single uncoloured var, or the sum of its colours.
         */
        String aggregate(int place, ColouredPlan plan, List<String> vars) {
            if (plan.isColoured[place]) {
                int[] cols = colCol[place];
                return switch (cols.length) {
                    // k = 0: a coloured place has no slot and never holds a token.
                    case 0 -> "0";
                    case 1 -> vars.get(cols[0]);
                    default -> {
                        var parts = new ArrayList<String>(cols.length);
                        for (int c : cols) {
                            parts.add(vars.get(c));
                        }
                        yield "(+ " + String.join(" ", parts) + ")";
                    }
                };
            }
            return vars.get(colUnc[place]);
        }

        String quantified(List<String> vars) {
            var parts = new ArrayList<String>(vars.size());
            for (var v : vars) {
                parts.add("(" + v + " Int)");
            }
            return String.join(" ", parts);
        }
    }

    /** A changed column and its update expression. */
    private record Update(int col, String expr) {}

    /** Contributes a rule's enablement guards and changed-column updates. */
    @FunctionalInterface
    private interface Fill {
        void apply(List<String> enab, List<Update> upd);
    }

    /**
     * Encodes the supported &nu;-net as bounded name-coloured CHC for Z3 Spacer, as
     * SMT-LIB2 text byte-identical to the Rust reference ({@code encode_coloured}).
     * With the query {@code (not Error)}, {@code sat} &rArr; PROVEN, {@code unsat}
     * &rArr; VIOLATED (the Spacer convention shared with {@link SmtEncoder}).
     *
     * @param sinkPlaces terminal places (a quiescent marking holding a sink token is not a
     *                   deadlock, VER-002) — used by the colour-aware deadlock predicate
     * @return the encoding, or {@code null} when the property names a place that does not
     *         resolve in the net (the verifier reports Unknown rather than certify a
     *         vacuous PROVEN)
     */
    public static SmtEncoder.SmtEncoding encode(
            ColouredPlan plan, FlatNet flat, MarkingState initial, SmtProperty property,
            List<PInvariant> invariants, Collection<Place<?>> sinkPlaces) {
        int p = flat.placeCount();
        int k = plan.k;
        Layout lay = new Layout(plan, p);
        int nCols = lay.cur.size();

        var lines = new ArrayList<String>();
        lines.add("(set-logic HORN)");
        lines.add("");
        var ints = new ArrayList<String>(nCols);
        for (int i = 0; i < nCols; i++) {
            ints.add("Int");
        }
        lines.add("(declare-fun Reachable (" + String.join(" ", ints) + ") Bool)");
        lines.add("(declare-fun Error () Bool)");
        lines.add("");

        // Init: uncoloured places carry their initial count; coloured start empty.
        var init = new ArrayList<String>(nCols);
        for (int i = 0; i < p; i++) {
            if (plan.isColoured[i]) {
                for (int c = 0; c < k; c++) {
                    init.add("0");
                }
            } else {
                init.add(Integer.toString(initial.tokens(flat.places().get(i))));
            }
        }
        lines.add("(assert (Reachable " + String.join(" ", init) + "))");
        lines.add("");

        // Transition rules.
        for (int ti = 0; ti < plan.classes.size(); ti++) {
            Klass cls = plan.classes.get(ti);
            FlatTransition ft = flat.transitions().get(ti);
            switch (cls) {
                case Untouched _ -> lines.add(encodeRule(plan, lay, invariants,
                    (enab, upd) -> uncolouredIncidence(lay, plan, ft, enab, upd)));
                case Mint m -> {
                    for (int c = 0; c < k; c++) {
                        final int cc = c;
                        lines.add(encodeRule(plan, lay, invariants, (enab, upd) -> {
                            uncolouredIncidence(lay, plan, ft, enab, upd);
                            // Globally fresh colour: cc must be empty in every coloured place.
                            for (int q : plan.coloured) {
                                enab.add("(= " + lay.cur.get(lay.colCol[q][cc]) + " 0)");
                            }
                            for (int o : m.colouredOut()) {
                                int col = lay.colCol[o][cc];
                                upd.add(new Update(col, "(+ " + lay.cur.get(col) + " 1)"));
                            }
                        }));
                    }
                }
                case Join j -> {
                    for (int c = 0; c < k; c++) {
                        final int cc = c;
                        lines.add(encodeRule(plan, lay, invariants, (enab, upd) -> {
                            uncolouredIncidence(lay, plan, ft, enab, upd);
                            // Same colour cc present in every correlated input.
                            for (int ip : j.colouredIn()) {
                                int col = lay.colCol[ip][cc];
                                enab.add("(>= " + lay.cur.get(col) + " 1)");
                                upd.add(new Update(col, "(- " + lay.cur.get(col) + " 1)"));
                            }
                        }));
                    }
                }
                case Consume co -> {
                    // One rule per colour: consume colour cc from the single coloured input
                    // and thread it into each coloured output (relay), or into none (drain).
                    for (int c = 0; c < k; c++) {
                        final int cc = c;
                        lines.add(encodeRule(plan, lay, invariants, (enab, upd) -> {
                            uncolouredIncidence(lay, plan, ft, enab, upd);
                            int icol = lay.colCol[co.inputCol()][cc];
                            enab.add("(>= " + lay.cur.get(icol) + " 1)");
                            upd.add(new Update(icol, "(- " + lay.cur.get(icol) + " 1)"));
                            for (int o : co.colouredOut()) {
                                int ocol = lay.colCol[o][cc];
                                upd.add(new Update(ocol, "(+ " + lay.cur.get(ocol) + " 1)"));
                            }
                        }));
                    }
                }
            }
        }
        lines.add("");

        // Error rule. `null` ⇒ the property names an unresolved place; refuse to build a
        // vacuously-provable encoding and let the verifier report Unknown.
        String error = encodeError(plan, lay, flat, property, sinkPlaces, injectedEnvIndices(flat));
        if (error == null) {
            return null;
        }
        lines.add(error);
        lines.add("");
        lines.add("(assert (not Error))");
        lines.add("(check-sat)");

        return new SmtEncoder.SmtEncoding(String.join("\n", lines), p);
    }

    /**
     * Pushes the enablement guards and column updates contributed by a transition's
     * <b>uncoloured</b> incidence (consume/produce on non-coloured places). Coloured
     * columns are handled by the caller (mint produces, join/consumer consume).
     */
    private static void uncolouredIncidence(
            Layout lay, ColouredPlan plan, FlatTransition ft, List<String> enab, List<Update> upd) {
        int p = ft.preVector().length;
        for (int i = 0; i < p; i++) {
            if (plan.isColoured[i]) {
                continue;
            }
            int col = lay.colUnc[i];
            int pre = ft.preVector()[i];
            if (pre > 0) {
                enab.add("(>= " + lay.cur.get(col) + " " + pre + ")");
            }
            if (contains(ft.resetPlaces(), i) || ft.consumeAll()[i]) {
                upd.add(new Update(col, Integer.toString(ft.postVector()[i])));
            } else {
                int delta = ft.postVector()[i] - ft.preVector()[i];
                if (delta > 0) {
                    upd.add(new Update(col, "(+ " + lay.cur.get(col) + " " + delta + ")"));
                } else if (delta < 0) {
                    upd.add(new Update(col, "(- " + lay.cur.get(col) + " " + (-delta) + ")"));
                }
            }
        }
        // Inhibitor / read arcs (all on uncoloured places — checked in buildPlan).
        for (int pid : ft.inhibitorPlaces()) {
            enab.add("(= " + lay.cur.get(lay.colUnc[pid]) + " 0)");
        }
        for (int pid : ft.readPlaces()) {
            enab.add("(>= " + lay.cur.get(lay.colUnc[pid]) + " 1)");
        }
    }

    /**
     * Builds one transition CHC rule. {@code fill} contributes the enablement guards and
     * the changed-column updates; every other column is copied unchanged, changed columns
     * get a non-negativity guard, and the (lifted) P-invariants constrain the successor.
     */
    private static String encodeRule(
            ColouredPlan plan, Layout lay, List<PInvariant> invariants, Fill fill) {
        List<String> enab = new ArrayList<>();
        List<Update> upd = new ArrayList<>();
        fill.apply(enab, upd);

        var all = new ArrayList<>(lay.cur);
        all.addAll(lay.nxt);

        List<String> conditions = new ArrayList<>();
        conditions.add("(Reachable " + String.join(" ", lay.cur) + ")");
        conditions.addAll(enab);

        // A changed column gets its update + non-negativity guard; every other column is
        // copied unchanged. A later update of the same column wins.
        String[] changed = new String[lay.cur.size()];
        for (var u : upd) {
            changed[u.col()] = u.expr();
        }
        for (int col = 0; col < lay.cur.size(); col++) {
            if (changed[col] != null) {
                conditions.add("(= " + lay.nxt.get(col) + " " + changed[col] + ")");
                conditions.add("(>= " + lay.nxt.get(col) + " 0)");
            } else {
                conditions.add("(= " + lay.nxt.get(col) + " " + lay.cur.get(col) + ")");
            }
        }

        for (PInvariant inv : invariants) {
            String eq = liftedInvariant(inv, plan, lay, lay.nxt);
            if (eq != null) {
                conditions.add(eq);
            }
        }

        String body = "(and " + String.join("\n            ", conditions) + ")";
        return "(assert (forall (" + lay.quantified(all) + ")\n  (=> " + body
            + "\n      (Reachable " + String.join(" ", lay.nxt) + "))))";
    }

    /**
     * Lifts a flat P-invariant to the coloured layout: a coloured place's variable
     * becomes the sum of its colours (= its aggregate count). Returns {@code null} when
     * the invariant support is empty.
     */
    private static String liftedInvariant(
            PInvariant inv, ColouredPlan plan, Layout lay, List<String> vars) {
        var terms = new ArrayList<String>();
        for (int i : new TreeSet<>(inv.support())) {
            String agg = lay.aggregate(i, plan, vars);
            int w = inv.weights()[i];
            terms.add(w == 1 ? agg : "(* " + w + " " + agg + ")");
        }
        if (terms.isEmpty()) {
            return null;
        }
        String sum = terms.size() == 1 ? terms.getFirst() : "(+ " + String.join(" ", terms) + ")";
        return "(= " + sum + " " + inv.constant() + ")";
    }

    /**
     * Encodes the error rule: a reachable marking that violates the property, or
     * {@code null} when the property names an unresolved place ({@link #encodeViolation}).
     */
    private static String encodeError(
            ColouredPlan plan, Layout lay, FlatNet flat, SmtProperty property,
            Collection<Place<?>> sinkPlaces, Map<Integer, Integer> envInj) {
        String violation = encodeViolation(plan, lay, flat, property, sinkPlaces, envInj);
        if (violation == null) {
            return null;
        }
        return "(assert (forall (" + lay.quantified(lay.cur) + ")\n  (=> (and (Reachable "
            + String.join(" ", lay.cur) + ") " + violation + ")\n      Error)))";
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
    private static String encodeViolation(
            ColouredPlan plan, Layout lay, FlatNet flat, SmtProperty property,
            Collection<Place<?>> sinkPlaces, Map<Integer, Integer> envInj) {
        return switch (property) {
            case SmtProperty.PlaceBound pb -> boundViolation(plan, lay, flat, pb.place(), pb.bound());
            case SmtProperty.BranchPlaceBound bpb -> boundViolation(plan, lay, flat, bpb.place(), bpb.bound());
            case SmtProperty.MutualExclusion me ->
                anyPlacePresent(plan, lay, flat, List.of(me.p1(), me.p2()));
            case SmtProperty.Unreachable ur -> anyPlacePresent(plan, lay, flat, ur.places());
            case SmtProperty.DeadlockFree _ ->
                encodeColouredDeadlock(plan, lay, flat, sinkPlaces, envInj);
            case SmtProperty.JoinedOrDeadLettered jdl -> {
                int pid = flat.indexOf(jdl.pending());
                if (pid < 0) {
                    yield null;
                }
                String deadlock = encodeColouredDeadlock(plan, lay, flat, sinkPlaces, envInj);
                yield "(and " + deadlock + " (>= " + lay.aggregate(pid, plan, lay.cur) + " 1))";
            }
        };
    }

    /** All the given places (that resolve) hold a token; {@code false} when none resolves. */
    private static String anyPlacePresent(
            ColouredPlan plan, Layout lay, FlatNet flat, Collection<Place<?>> places) {
        var conds = new ArrayList<String>();
        for (int pid : SmtEncoder.indexOrdered(flat, places)) {
            conds.add("(>= " + lay.aggregate(pid, plan, lay.cur) + " 1)");
        }
        return conds.isEmpty() ? "false" : "(and " + String.join(" ", conds) + ")";
    }

    private static String boundViolation(
            ColouredPlan plan, Layout lay, FlatNet flat, Place<?> place, int bound) {
        int pid = flat.indexOf(place);
        if (pid < 0) {
            // Unresolved bound place: a false violation term would vacuously PROVE the
            // bound. Return null so the verifier reports Unknown instead of certifying.
            return null;
        }
        return "(> " + lay.aggregate(pid, plan, lay.cur) + " " + bound + ")";
    }

    /**
     * Colour-aware deadlock predicate (NU-053): every transition is disabled (no colour
     * enables it) and no declared sink place holds a token (VER-002). Mirrors
     * {@link SmtEncoder}'s flat deadlock with the same env-injection relaxation
     * (VER-006), lifted to the coloured layout.
     */
    private static String encodeColouredDeadlock(
            ColouredPlan plan, Layout lay, FlatNet flat, Collection<Place<?>> sinkPlaces,
            Map<Integer, Integer> envInj) {
        var disabledConditions = new ArrayList<String>();
        for (int ti = 0; ti < plan.classes.size(); ti++) {
            Klass cls = plan.classes.get(ti);
            FlatTransition ft = flat.transitions().get(ti);
            List<String> reasons = new ArrayList<>();
            boolean permanentlyDisabled = uncolouredDisable(ft, lay, plan, envInj, reasons);
            if (permanentlyDisabled) {
                // The transition can never fire — it is always "disabled".
                disabledConditions.add("true");
                continue;
            }
            String term = colouredDisabledTerm(cls, plan, lay);
            if (term != null) {
                reasons.add(term);
            }
            if (reasons.isEmpty()) {
                // Always enabled (possibly via injection) — no marking is a deadlock.
                return "false";
            }
            disabledConditions.add(reasons.size() == 1
                ? reasons.getFirst()
                : "(or " + String.join(" ", reasons) + ")");
        }

        // Declared sinks (VER-002): quiescence is a violation only when NO declared sink
        // holds a token, so each declared sink contributes `aggregate(sink) = 0` over its
        // colour slots. Same predicate as the flat deadlock.
        for (int pid : SmtEncoder.indexOrdered(flat, sinkPlaces)) {
            disabledConditions.add("(= " + lay.aggregate(pid, plan, lay.cur) + " 0)");
        }

        return disabledConditions.isEmpty()
            ? "true"
            : "(and " + String.join(" ", disabledConditions) + ")";
    }

    /**
     * The uncoloured disable reasons for a flat row: marking-dependent clauses (any one
     * true ⇒ the transition's uncoloured part is unmet), collected into {@code reasons};
     * returns {@code true} when the transition is permanently disabled (an env cap below
     * the demand means it can never fire). Coloured places are excluded — their
     * enablement is the per-class colour term.
     */
    private static boolean uncolouredDisable(
            FlatTransition ft, Layout lay, ColouredPlan plan, Map<Integer, Integer> envInj,
            List<String> reasons) {
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
            reasons.add("(< " + lay.cur.get(lay.colUnc[i]) + " " + ft.preVector()[i] + ")");
        }
        for (int inh : ft.inhibitorPlaces()) {
            reasons.add("(> " + lay.cur.get(lay.colUnc[inh]) + " 0)");
        }
        for (int rd : ft.readPlaces()) {
            if (envInj.containsKey(rd)) {
                Integer bound = envInj.get(rd);
                if (bound != null && bound < 1) {
                    permanentlyDisabled = true;
                }
                continue;
            }
            reasons.add("(< " + lay.cur.get(lay.colUnc[rd]) + " 1)");
        }
        return permanentlyDisabled;
    }

    /**
     * The colour-specific "disabled for every colour" term for a class ({@code null} if
     * the class imposes no coloured enablement constraint). Combined by the caller with
     * the uncoloured disable reasons: the transition is disabled if EITHER holds.
     */
    private static String colouredDisabledTerm(Klass cls, ColouredPlan plan, Layout lay) {
        int k = plan.k;
        if (k == 0) {
            // k = 0 (NU-053 AC6): no colour can ever be present, so every coloured class is
            // disabled outright; the empty conjunctions below would render as `(and )`.
            return cls instanceof Untouched ? null : "true";
        }
        return switch (cls) {
            case Untouched _ -> null;
            case Mint _ -> {
                // No globally-fresh colour: for every colour c, some coloured place holds c.
                var perColour = new ArrayList<String>(k);
                for (int c = 0; c < k; c++) {
                    var present = new ArrayList<String>(plan.coloured.length);
                    for (int q : plan.coloured) {
                        present.add("(>= " + lay.cur.get(lay.colCol[q][c]) + " 1)");
                    }
                    perColour.add("(or " + String.join(" ", present) + ")");
                }
                yield "(and " + String.join(" ", perColour) + ")";
            }
            case Join j -> {
                // No colour is shared by all correlated inputs: for every colour c, some
                // input lacks c.
                var perColour = new ArrayList<String>(k);
                for (int c = 0; c < k; c++) {
                    var missing = new ArrayList<String>(j.colouredIn().length);
                    for (int inCol : j.colouredIn()) {
                        missing.add("(= " + lay.cur.get(lay.colCol[inCol][c]) + " 0)");
                    }
                    perColour.add("(or " + String.join(" ", missing) + ")");
                }
                yield "(and " + String.join(" ", perColour) + ")";
            }
            case Consume co -> {
                // No colour present at the single coloured input.
                var perColour = new ArrayList<String>(k);
                for (int c = 0; c < k; c++) {
                    perColour.add("(= " + lay.cur.get(lay.colCol[co.inputCol()][c]) + " 0)");
                }
                yield "(and " + String.join(" ", perColour) + ")";
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
