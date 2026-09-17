package org.libpetri.smt.z3;

import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.FlatTransition;
import org.libpetri.smt.invariant.PInvariantComputer;
import org.libpetri.smt.z3.StateEquationQuery.MarkingInequality;
import org.libpetri.smt.z3.StateEquationQuery.Origin;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Pattern;

/**
 * Inductive-inequality refinement for the state-equation phase ([VER-018]).
 *
 * <p>The marking equation knows how often each transition fired, never in what order, and
 * it ignores the guards that impose the order. The typical spurious candidate on a workflow
 * net is a join that <em>skipped</em> — a transition inhibited by {@code hasdata} — after
 * the data token arrived: every count balances, and only the inhibitor rules the run out. A
 * trap cannot say that either. This refinement looks for one linear inequality
 * {@code a·M <= b} that
 * <ol>
 *   <li>holds at {@code M0},</li>
 *   <li>is kept by every step of the <b>exact</b> step relation — input weights, read and
 *       inhibitor guards, consume-all and reset clearing included, which is where it gets
 *       its power over the equation — and</li>
 *   <li>excludes the candidate: {@code a·M* >= b + 1}.</li>
 * </ol>
 *
 * <p>For the join above that is {@code hasdata <= ready_0 + ready_1}: arrivals raise both
 * sides together, {@code skip} fires only when {@code hasdata} is empty, and {@code start}
 * clears it.
 *
 * <p>Condition 2 is the Farkas form of consecution (Colón, Sankaranarayanan and Sipma,
 * "Linear invariant generation using non-linear constraint solving", CAV 2003) with the
 * invariant's own multiplier restricted to {@code λ_t ∈ {0, 1}} per transition, which keeps
 * the query linear. Write {@code l_p = max(pre_p, 1 if p is read)} for the guard's lower
 * bound; an inhibited place is exactly {@code 0} before the step.
 * <ul>
 *   <li>{@code λ_t = 1}, the step keeps the bound: {@code a·M' − a·M <= 0} for every enabled
 *       {@code M}. A place {@code t} does not clear contributes its column {@code C_p}; a place
 *       it clears contributes {@code post_p − M_p <= post_p − l_p}, provided {@code a_p >= 0}
 *       (on an inhibited cleared place {@code M_p = 0}, so {@code post_p} and no sign
 *       condition).</li>
 *   <li>{@code λ_t = 0}, the guard restores the bound on its own: {@code a_p <= 0} on every
 *       place {@code t} neither clears nor inhibits, so {@code a·M'} is largest at
 *       {@code M = l}, and that value is {@code <= b}.</li>
 * </ul>
 *
 * <p>An environment injection must keep the bound ({@code a_p <= 0} on an injected place).
 * The query is one {@code QF_LIA} script with integer weights in {@code [−bound, bound]}.
 *
 * <p>The weights {@link #encodeInductiveInequality} returns are re-checked in exact integer
 * arithmetic ({@link #checkInductiveExact}) before they are used, so the refinement rests
 * on the check, not on the solver. Those of {@link #encodeRelativeInequality} are not, and
 * cannot be: that bound holds only relative to the marking equation, so the exact re-check
 * would reject it. It rests on the certificate check, which re-proves the whole refinement
 * against the raw step relation before any verdict rests on it.
 *
 * <p>Both scripts build their own rows from the flat net, so they are byte-identical to the
 * TypeScript, Rust and Python ports for the same input ([VER-013] AC1).
 */
public final class InvariantSynthesis {

    private InvariantSynthesis() {}

    /** The default magnitude bound on the weights the query may choose. */
    public static final int DEFAULT_WEIGHT_BOUND = 8;

    /**
     * The two ways a transition can keep {@code a·M <= b}, as coefficient rows over the places.
     *
     * @param keepNonNegative {@code λ = 1}: {@code a_p >= 0} on these places, ascending, and
     * @param keep            {@code Σ keep[p]·a_p <= 0}
     * @param restoreFree     {@code λ = 0}: {@code a_p <= 0} on every place outside these, and
     * @param restore         {@code Σ restore[p]·a_p <= b}
     */
    private record StepShape(int[] keepNonNegative, long[] keep, int[] restoreFree, long[] restore) {}

    /** The shape of {@code ft}, or {@code null} when it can never fire (it inhibits a place it needs). */
    private static StepShape stepShape(FlatTransition ft, int placeCount) {
        Set<Integer> inhibited = asSet(ft.inhibitorPlaces());
        Set<Integer> read = asSet(ft.readPlaces());
        Set<Integer> resets = asSet(ft.resetPlaces());
        for (int p : ft.inhibitorPlaces()) {
            if (ft.preVector()[p] > 0 || read.contains(p)) {
                return null;
            }
        }
        long[] keep = new long[placeCount];
        long[] restore = new long[placeCount];
        var keepNonNegative = new ArrayList<Integer>();
        var restoreFree = new ArrayList<Integer>();
        for (int p = 0; p < placeCount; p++) {
            long pre = ft.preVector()[p];
            long post = ft.postVector()[p];
            long lower = Math.max(pre, read.contains(p) ? 1 : 0);
            if (resets.contains(p) || ft.consumeAll()[p]) {
                if (inhibited.contains(p)) {
                    keep[p] = post;
                } else {
                    keep[p] = post - lower;
                    keepNonNegative.add(p);
                }
                restore[p] = post;
                restoreFree.add(p);
            } else if (inhibited.contains(p)) {
                keep[p] = post - pre;
                restore[p] = post - pre;
                restoreFree.add(p);
            } else {
                keep[p] = post - pre;
                restore[p] = post - pre + lower;
            }
        }
        return new StepShape(toArray(keepNonNegative), keep, toArray(restoreFree), restore);
    }

    /** {@link #encodeInductiveInequality(FlatNet, int[], long[], long)} with {@link #DEFAULT_WEIGHT_BOUND}. */
    public static String encodeInductiveInequality(FlatNet flatNet, int[] initial, long[] candidate) {
        return encodeInductiveInequality(flatNet, initial, candidate, DEFAULT_WEIGHT_BOUND);
    }

    /**
     * The {@code QF_LIA} script asking for weights {@code a} and a bound {@code b} that
     * satisfy conditions 1–3 of the class description for the given candidate marking.
     * {@code u_p >= max(a_p, 0)} carries each weight's positive part, so the {@code λ = 0}
     * sign condition of a transition is one equation ({@code Σ_p u_p = Σ_{p free} u_p})
     * rather than one atom per place.
     *
     * @param initial     {@code M0}, one count per flat place
     * @param candidate   the marking to exclude
     * @param weightBound the magnitude bound on every weight
     */
    public static String encodeInductiveInequality(
            FlatNet flatNet, int[] initial, long[] candidate, long weightBound
    ) {
        int placeCount = flatNet.placeCount();
        var lines = new ArrayList<String>();
        lines.add("; Inductive-inequality refinement (VER-018): a.M <= b holding at M0, kept by every");
        lines.add("; step of the exact step relation (guards and clearing included), and excluding");
        lines.add("; the candidate marking.");
        lines.add("(set-logic QF_LIA)");
        declareWeights(lines, placeCount, weightBound, true);
        var positive = new ArrayList<String>(placeCount);
        for (int p = 0; p < placeCount; p++) {
            positive.add("u" + p);
        }
        lines.add("(assert (= upos " + sum(positive, "0") + "))");
        lines.add("(assert (<= " + linear(longs(initial), "a") + " b))");
        lines.add("(assert (>= " + linear(candidate, "a") + " (+ b 1)))");
        for (var ft : flatNet.transitions()) {
            var shape = stepShape(ft, placeCount);
            if (shape == null) {
                continue;
            }
            var keeps = new ArrayList<String>();
            for (int p : shape.keepNonNegative()) {
                keeps.add("(>= a" + p + " 0)");
            }
            keeps.add("(<= " + linear(shape.keep(), "a") + " 0)");
            var free = new ArrayList<String>();
            for (int p : shape.restoreFree()) {
                free.add("u" + p);
            }
            var restores = List.of(
                "(= upos " + sum(free, "0") + ")",
                "(<= " + linear(shape.restore(), "a") + " b)");
            lines.add("(assert (or " + SmtEncoder.conjoin(keeps) + " " + SmtEncoder.conjoin(restores) + "))");
        }
        for (var inj : SmtEncoder.resolveEnvInjection(flatNet)) {
            lines.add("(assert (<= a" + inj.pid() + " 0))");
        }
        // The sparsest inequality: it prints as the structural fact (`hasdata <= ready_0 +
        // ready_1`) rather than an arbitrary combination, and it excludes more candidates.
        lines.add("(minimize " + magnitudeObjective(placeCount) + ")");
        lines.add("(check-sat)");
        lines.add("(get-model)");
        return String.join("\n", lines);
    }

    /** {@link #encodeRelativeInequality(FlatNet, int[], long[], long)} with {@link #DEFAULT_WEIGHT_BOUND}. */
    public static String encodeRelativeInequality(FlatNet flatNet, int[] initial, long[] candidate) {
        return encodeRelativeInequality(flatNet, initial, candidate, DEFAULT_WEIGHT_BOUND);
    }

    /**
     * The query of {@link #encodeInductiveInequality} with the marking equation as a premise
     * of every step: the inequality need only be kept by steps from markings the equation
     * admits. A bound like {@code q + 3·out <= 3} on a queue that is bundled once a signal
     * arrives needs it — {@code produce} keeps the bound only because {@code q <= 2} whenever
     * {@code budget >= 1}, and that is the equation's {@code q + budget <= 3}.
     *
     * <p>By Farkas, the premise contributes to transition {@code t}'s consecution one linear
     * consequence of the equation: a weighting {@code η^t} with {@code η^t·C_j <= 0} on every
     * column {@code j}, non-negative on a place whose row is an upper bound and absent on an
     * injected place, so that {@code η^t·M <= η^t·M0} holds wherever the equation does. With
     * {@code κ_t = Σ_{p not cleared} a_p·C_p + Σ_{p cleared} a_p·post_p} the two cases read:
     * <ul>
     *   <li>{@code λ_t = 1}: {@code η^t_p >= 0} on a place {@code t} neither clears nor
     *       inhibits, {@code a_p + η^t_p >= 0} on a place it clears, and
     *       {@code κ_t <= −η^t·M0 + Σ_{p not inhibited} ν_p·l_p}, with {@code ν_p = η^t_p}
     *       ({@code a_p + η^t_p} on a cleared place).</li>
     *   <li>{@code λ_t = 0}: {@code a_p <= η^t_p} on a place {@code t} neither clears nor
     *       inhibits, {@code η^t_p >= 0} on a place it clears, and
     *       {@code κ_t − b <= −η^t·M0 + Σ ν_p·l_p}, with {@code ν_p = η^t_p − a_p}
     *       ({@code η^t_p} on a cleared place).</li>
     * </ul>
     *
     * <p>With {@code η^t = 0} these are the conditions of {@link #encodeInductiveInequality}.
     * The query carries one weighting per transition, so the phase asks it only when that one
     * found nothing. The weightings are real; the inequality's weights stay integers. The
     * certificate check re-proves the result as part of {@code SE ∧ refinements}.
     */
    public static String encodeRelativeInequality(
            FlatNet flatNet, int[] initial, long[] candidate, long weightBound
    ) {
        int placeCount = flatNet.placeCount();
        int transitionCount = flatNet.transitionCount();
        Set<Integer> upper = PInvariantComputer.nonlinearPlaces(flatNet);
        var injectedOrdered = new ArrayList<Integer>();
        for (var inj : SmtEncoder.resolveEnvInjection(flatNet)) {
            injectedOrdered.add(inj.pid());
        }
        Set<Integer> injected = new HashSet<>(injectedOrdered);
        var rows = new ArrayList<Integer>();
        for (int p = 0; p < placeCount; p++) {
            if (!injected.contains(p)) {
                rows.add(p);
            }
        }
        var lines = new ArrayList<String>();
        lines.add("; Inductive-inequality refinement relative to the marking equation (VER-018):");
        lines.add("; a.M <= b holding at M0, kept by every step from a marking the equation admits");
        lines.add("; (one Farkas weighting e<t>_<p> of the equation per transition), and excluding");
        lines.add("; the candidate marking.");
        lines.add("(set-logic QF_LIRA)");
        declareWeights(lines, placeCount, weightBound, false);
        lines.add("(assert (<= " + linear(longs(initial), "a") + " b))");
        lines.add("(assert (>= " + linear(candidate, "a") + " (+ b 1)))");
        for (int p : injectedOrdered) {
            lines.add("(assert (<= a" + p + " 0))");
        }
        for (int t = 0; t < transitionCount; t++) {
            var ft = flatNet.transitions().get(t);
            var shape = stepShape(ft, placeCount);
            if (shape == null) {
                continue;
            }
            String e = "e" + t + "_";
            for (int p : rows) {
                lines.add("(declare-const " + e + p + " Real)");
            }
            for (int p : rows) {
                if (upper.contains(p)) {
                    lines.add("(assert (>= " + e + p + " 0))");
                }
            }
            for (var col : flatNet.transitions()) {
                var terms = new ArrayList<String>();
                for (int p : rows) {
                    int c = col.postVector()[p] - col.preVector()[p];
                    if (c != 0) {
                        terms.add(scaled(c, e + p));
                    }
                }
                if (!terms.isEmpty()) {
                    lines.add("(assert (<= " + sum(terms, "0") + " 0.0))");
                }
            }
            Set<Integer> inhibited = asSet(ft.inhibitorPlaces());
            Set<Integer> read = asSet(ft.readPlaces());
            Set<Integer> resets = asSet(ft.resetPlaces());
            // κ_t over the weights, and −η·M0.
            var kappa = new ArrayList<String>();
            for (int p = 0; p < placeCount; p++) {
                boolean cleared = resets.contains(p) || ft.consumeAll()[p];
                long c = cleared ? ft.postVector()[p] : (long) ft.postVector()[p] - ft.preVector()[p];
                if (c != 0) {
                    kappa.add(scaled(c, realWeight(p)));
                }
            }
            var etaM0 = new ArrayList<String>();
            for (int p : rows) {
                long m0 = p < initial.length ? initial[p] : 0;
                if (m0 != 0) {
                    etaM0.add(scaled(-m0, e + p));
                }
            }
            var keep = new ArrayList<String>();
            var keepRhs = new ArrayList<>(etaM0);
            var restore = new ArrayList<String>();
            var restoreRhs = new ArrayList<>(etaM0);
            for (int p = 0; p < placeCount; p++) {
                if (inhibited.contains(p)) {
                    continue;
                }
                long lower = Math.max(ft.preVector()[p], read.contains(p) ? 1 : 0);
                String eta = injected.contains(p) ? "0.0" : e + p;
                String ra = realWeight(p);
                if (resets.contains(p) || ft.consumeAll()[p]) {
                    keep.add("(>= (+ " + ra + " " + eta + ") 0.0)");
                    restore.add("(>= " + eta + " 0.0)");
                    if (lower != 0) {
                        keepRhs.add(scaled(lower, "(+ " + ra + " " + eta + ")"));
                        restoreRhs.add(scaled(lower, eta));
                    }
                } else {
                    keep.add("(>= " + eta + " 0.0)");
                    restore.add("(<= " + ra + " " + eta + ")");
                    if (lower != 0) {
                        keepRhs.add(scaled(lower, eta));
                        restoreRhs.add(scaled(lower, "(- " + eta + " " + ra + ")"));
                    }
                }
            }
            keep.add("(<= " + sum(kappa, "0.0") + " " + sum(keepRhs, "0.0") + ")");
            restore.add("(<= (- " + sum(kappa, "0.0") + " (to_real b)) " + sum(restoreRhs, "0.0") + ")");
            lines.add("(assert (or " + SmtEncoder.conjoin(keep) + " " + SmtEncoder.conjoin(restore) + "))");
        }
        lines.add("(minimize " + magnitudeObjective(placeCount) + ")");
        lines.add("(check-sat)");
        lines.add("(get-model)");
        return String.join("\n", lines);
    }

    /**
     * The weight declarations both queries share: {@code a_p}, {@code u_p}, {@code w_p} and
     * {@code b} (then {@code upos} when {@code withPositivePart}), each weight within
     * {@code ±weightBound}, {@code u_p >= max(a_p, 0)} and {@code w_p >= max(−a_p, 0)}.
     */
    private static void declareWeights(List<String> lines, int placeCount, long weightBound, boolean withPositivePart) {
        for (int p = 0; p < placeCount; p++) {
            lines.add("(declare-const a" + p + " Int)");
        }
        for (int p = 0; p < placeCount; p++) {
            lines.add("(declare-const u" + p + " Int)");
        }
        for (int p = 0; p < placeCount; p++) {
            lines.add("(declare-const w" + p + " Int)");
        }
        lines.add("(declare-const b Int)");
        if (withPositivePart) {
            lines.add("(declare-const upos Int)");
        }
        for (int p = 0; p < placeCount; p++) {
            lines.add("(assert (and (>= a" + p + " (- " + weightBound + ")) (<= a" + p + " " + weightBound + ")))");
            lines.add("(assert (and (>= u" + p + " 0) (>= u" + p + " a" + p + ")))");
            lines.add("(assert (and (>= w" + p + " 0) (>= w" + p + " (- a" + p + "))))");
        }
    }

    /** {@code Σ_p u_p + w_p}, interleaved per place: the total magnitude of the weights. */
    private static String magnitudeObjective(int placeCount) {
        var terms = new ArrayList<String>(2 * placeCount);
        for (int p = 0; p < placeCount; p++) {
            terms.add("u" + p);
            terms.add("w" + p);
        }
        return sum(terms, "0");
    }

    private static final Pattern INEQUALITY_DEFINITION = Pattern.compile(
        "^\\(define-fun\\s+(a(\\d+)|b)\\s+\\(\\)\\s+Int\\s+(\\(-\\s*(\\d+)\\s*\\)|(\\d+))\\s*\\)$",
        Pattern.DOTALL);

    /**
     * The inequality in a {@code sat} reply's model; {@code null} when the model defines no
     * bound. A weight the model leaves out is zero, and a weight index past the net is
     * skipped. The origin is {@link Origin#INDUCTIVE} whichever query the reply answers: the
     * caller relabels a relative one ({@link MarkingInequality#withOrigin}).
     */
    public static MarkingInequality decodeInductiveInequality(String stdout, int placeCount) {
        var weights = new BigInteger[placeCount];
        Arrays.fill(weights, BigInteger.ZERO);
        BigInteger constant = null;
        for (var def : SmtText.extractDefineFuns(stdout)) {
            var m = INEQUALITY_DEFINITION.matcher(def.strip());
            if (!m.matches()) {
                continue;
            }
            BigInteger value = m.group(4) != null
                ? new BigInteger(m.group(4)).negate()
                : new BigInteger(m.group(5));
            if (m.group(1).equals("b")) {
                constant = value;
            } else {
                int index = StateEquationQuery.indexBelow(m.group(2), placeCount);
                if (index >= 0) {
                    weights[index] = value;
                }
            }
        }
        return constant == null ? null : new MarkingInequality(Arrays.asList(weights), constant, Origin.INDUCTIVE);
    }

    /**
     * Re-proves conditions 1 and 2 of the class description in exact integer arithmetic: the
     * inequality holds at {@code M0}, every injected place has a weight {@code <= 0}, and
     * every transition that can fire either keeps the bound ({@code λ = 1}) or restores it
     * from its guard ({@code λ = 0}). Condition 3 is not needed for soundness.
     *
     * <p>A relative inequality ({@link #encodeRelativeInequality}) is deliberately not
     * accepted here: it holds only where the marking equation does, so this check rejects
     * it, and the certificate check is what re-proves it.
     */
    public static boolean checkInductiveExact(FlatNet flatNet, int[] initial, MarkingInequality inequality) {
        var weights = inequality.weights();
        BigInteger constant = inequality.constant();
        int placeCount = flatNet.placeCount();
        if (weights.size() != placeCount) {
            return false;
        }
        if (dot(weights, longs(initial)).compareTo(constant) > 0) {
            return false;
        }
        for (var inj : SmtEncoder.resolveEnvInjection(flatNet)) {
            if (weights.get(inj.pid()).signum() > 0) {
                return false;
            }
        }
        for (var ft : flatNet.transitions()) {
            var shape = stepShape(ft, placeCount);
            if (shape == null) {
                continue;
            }
            boolean keepSigns = true;
            for (int p : shape.keepNonNegative()) {
                if (weights.get(p).signum() < 0) {
                    keepSigns = false;
                    break;
                }
            }
            if (keepSigns && dot(weights, shape.keep()).signum() <= 0) {
                continue;
            }
            Set<Integer> free = asSet(shape.restoreFree());
            boolean signs = true;
            for (int p = 0; p < placeCount; p++) {
                if (weights.get(p).signum() > 0 && !free.contains(p)) {
                    signs = false;
                    break;
                }
            }
            if (!signs || dot(weights, shape.restore()).compareTo(constant) > 0) {
                return false;
            }
        }
        return true;
    }

    /** {@code Σ_p weights[p]·values[p]}, a value past the end of {@code values} reading as 0. */
    private static BigInteger dot(List<BigInteger> weights, long[] values) {
        BigInteger s = BigInteger.ZERO;
        for (int p = 0; p < weights.size(); p++) {
            long v = p < values.length ? values[p] : 0;
            if (weights.get(p).signum() != 0 && v != 0) {
                s = s.add(weights.get(p).multiply(BigInteger.valueOf(v)));
            }
        }
        return s;
    }

    /** {@code Σ coeffs[p]·<prefix>p} over the non-zero coefficients, {@code 0} when there are none. */
    private static String linear(long[] coeffs, String prefix) {
        var terms = new ArrayList<String>();
        for (int p = 0; p < coeffs.length; p++) {
            long c = coeffs[p];
            if (c == 0) {
                continue;
            }
            String v = prefix + p;
            terms.add(c == 1 ? v
                : c == -1 ? "(- " + v + ")"
                : c > 0 ? "(* " + c + " " + v + ")"
                : "(* (- " + Math.negateExact(c) + ") " + v + ")");
        }
        return sum(terms, "0");
    }

    /** {@code c·x} for a real-valued {@code x}, {@code c} an integer. */
    private static String scaled(long c, String x) {
        if (c == 1) {
            return x;
        }
        if (c == -1) {
            return "(- " + x + ")";
        }
        return c > 0 ? "(* " + c + ".0 " + x + ")" : "(* (- " + Math.negateExact(c) + ".0) " + x + ")";
    }

    private static String realWeight(int p) {
        return "(to_real a" + p + ")";
    }

    /** A lone term unwrapped, otherwise {@code (+ t1 t2 …)}; {@code zero} when there are none. */
    private static String sum(List<String> terms, String zero) {
        return terms.isEmpty() ? zero
            : terms.size() == 1 ? terms.getFirst()
            : "(+ " + String.join(" ", terms) + ")";
    }

    private static long[] longs(int[] values) {
        long[] out = new long[values.length];
        for (int i = 0; i < values.length; i++) {
            out[i] = values[i];
        }
        return out;
    }

    private static Set<Integer> asSet(int[] places) {
        var out = new HashSet<Integer>();
        for (int p : places) {
            out.add(p);
        }
        return out;
    }

    private static int[] toArray(List<Integer> places) {
        return places.stream().mapToInt(Integer::intValue).toArray();
    }
}
