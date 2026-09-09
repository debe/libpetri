package org.libpetri.smt.z3;

import org.libpetri.analysis.MarkingState;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.invariant.PInvariantComputer;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Pattern;

/**
 * The linear state-equation bound ([VER-015]): a structural proof of a
 * reachability-safety property that needs no fixpoint search.
 *
 * <p>Every reachable marking of the abstract net satisfies {@code M = M0 + C·σ} for some
 * firing count vector {@code σ >= 0}, so for any weighting {@code y >= 0} with
 * {@code y·C <= 0} on every transition, {@code y·M <= y·M0} holds along every run — a
 * <b>decreasing</b> conservation law, where the P-invariants of [VER-005] are the
 * <em>equalities</em> {@code y·C = 0}. The violation of a reachability-safety property is
 * a lower demand on some places ({@code m_p >= 1} for each place of an {@code Unreachable},
 * {@code m_p >= k+1} for a {@code PlaceBound}); if some {@code y} makes that demand exceed
 * {@code y·M0}, no reachable marking meets it and the property is proven.
 *
 * <p>Finding {@code y} is one linear query in {@code QF_LIA}, answered by the same
 * {@code z3} transport as everything else ([VER-013]); the answer is then re-checked in
 * exact integer arithmetic ({@link BigInteger}: {@code y >= 0}, {@code y·C <= 0} per
 * transition, {@code y·d >= y·M0 + 1}), so the proof rests on the check, not on the
 * solver. It closes exactly the class of proofs IC3 misses on pipeline-shaped nets: an
 * ordering argument ("both join slots armed means every upstream stage has run, so no
 * halt is still possible") is a weighted count bound, which Spacer's lemma
 * generalisation does not invent over fifty variables but a linear solver finds in
 * milliseconds.
 *
 * <p>Soundness needs the same guards as the equality laws: zero weight on every
 * consume-all / reset place (H1 — the fire relation is not linear there) and on every
 * injected environment place (H3' — injection breaks conservation).
 */
public final class LinearBound {

    private LinearBound() {}

    /**
     * One linear bound {@code Σ weights[p]·m_p <= constant}, with the demand it separates.
     *
     * @param weights     {@code y}, one entry per flat place, all non-negative
     * @param constant    {@code y·M0}
     * @param demandValue {@code y·d}, what the violating markings need at least; strictly
     *                    above {@code constant}
     */
    public record Bound(List<BigInteger> weights, BigInteger constant, BigInteger demandValue) {
        public Bound {
            weights = List.copyOf(weights);
        }
    }

    /**
     * The violation's demand: flat place index → the least count a violating marking
     * holds there. {@code null} when the property is not a reachability-safety property,
     * or names no place the net resolves (the verifier refuses those before this runs).
     */
    public static Map<Integer, Integer> violationDemand(FlatNet flatNet, SmtProperty property) {
        var demand = new TreeMap<Integer, Integer>();
        switch (property) {
            case SmtProperty.Unreachable ur -> {
                for (var p : ur.places()) {
                    int pid = flatNet.indexOf(p);
                    if (pid >= 0) {
                        demand.put(pid, 1);
                    }
                }
            }
            case SmtProperty.MutualExclusion me -> {
                for (var p : List.of(me.p1(), me.p2())) {
                    int pid = flatNet.indexOf(p);
                    if (pid >= 0) {
                        demand.put(pid, 1);
                    }
                }
            }
            case SmtProperty.PlaceBound pb -> {
                int pid = flatNet.indexOf(pb.place());
                if (pid >= 0) {
                    demand.put(pid, pb.bound() + 1);
                }
            }
            case SmtProperty.BranchPlaceBound bpb -> {
                int pid = flatNet.indexOf(bpb.place());
                if (pid >= 0) {
                    demand.put(pid, bpb.bound() + 1);
                }
            }
            case SmtProperty.DeadlockFree _, SmtProperty.TerminatesAtSink _,
                 SmtProperty.JoinedOrDeadLettered _ -> {
                return null;
            }
        }
        return demand.isEmpty() ? null : demand;
    }

    /** The places whose weight is pinned to zero: H1 (consume-all / reset) and H3' (injected). */
    public static Set<Integer> zeroWeightPlaces(FlatNet flatNet) {
        var zero = new TreeSet<>(PInvariantComputer.nonlinearPlaces(flatNet));
        for (var inj : SmtEncoder.resolveEnvInjection(flatNet)) {
            zero.add(inj.pid());
        }
        return zero;
    }

    /**
     * The {@code QF_LIA} script asking for a separating {@code y}, or {@code null} when
     * the property has no linear demand. Byte-identical across the four implementations:
     * places in flat index order, one row per flat transition in net order, {@code (- k)}
     * for a negative literal, a lone term unwrapped.
     */
    public static String encode(FlatNet flatNet, MarkingState initialMarking, SmtProperty property) {
        var demand = violationDemand(flatNet, property);
        if (demand == null) {
            return null;
        }
        int p = flatNet.placeCount();
        var zero = zeroWeightPlaces(flatNet);
        var lines = new ArrayList<String>();
        lines.add("; Linear state-equation bound (VER-015): y >= 0 with y.C <= 0 on every");
        lines.add("; transition gives y.M <= y.M0 for every reachable M; sat = the violating");
        lines.add("; markings' demand exceeds that bound, so none is reachable.");
        lines.add("(set-logic QF_LIA)");
        for (int i = 0; i < p; i++) {
            lines.add("(declare-const y" + i + " Int)");
        }
        for (int i = 0; i < p; i++) {
            lines.add("(assert (>= y" + i + " 0))");
        }
        for (int i : zero) {
            lines.add("(assert (= y" + i + " 0))");
        }
        for (var ft : flatNet.transitions()) {
            var terms = new ArrayList<String>();
            for (int i = 0; i < p; i++) {
                int c = ft.postVector()[i] - ft.preVector()[i];
                if (c != 0) {
                    terms.add(term(c, "y" + i));
                }
            }
            if (!terms.isEmpty()) {
                lines.add("(assert (<= " + sum(terms) + " 0))");
            }
        }
        var demandTerms = new ArrayList<String>();
        for (var entry : demand.entrySet()) {
            demandTerms.add(term(entry.getValue(), "y" + entry.getKey()));
        }
        var initTerms = new ArrayList<String>();
        initTerms.add("1");
        for (int i = 0; i < p; i++) {
            int m0 = initialMarking.tokens(flatNet.places().get(i));
            if (m0 > 0) {
                initTerms.add(term(m0, "y" + i));
            }
        }
        lines.add("(assert (>= " + sum(demandTerms) + " " + sum(initTerms) + "))");
        lines.add("(check-sat)");
        lines.add("(get-model)");
        return String.join("\n", lines);
    }

    private static String term(int c, String v) {
        if (c == 1) {
            return v;
        }
        if (c == -1) {
            return "(- " + v + ")";
        }
        return c > 0 ? "(* " + c + " " + v + ")" : "(* (- " + (-c) + ") " + v + ")";
    }

    private static String sum(List<String> terms) {
        return terms.size() == 1 ? terms.getFirst() : "(+ " + String.join(" ", terms) + ")";
    }

    private static final Pattern Y_DEFINITION = Pattern.compile(
        "^\\(define-fun\\s+y(\\d+)\\s+\\(\\)\\s+Int\\s+(\\(-\\s*(\\d+)\\s*\\)|(\\d+))\\s*\\)$",
        Pattern.DOTALL);

    /**
     * The weighting in a {@code sat} reply's model: {@code y_p} per flat place, zero where
     * the model is silent. {@code null} when the reply defines no {@code y}.
     */
    public static BigInteger[] decode(String stdout, int placeCount) {
        var y = new BigInteger[placeCount];
        Arrays.fill(y, BigInteger.ZERO);
        boolean seen = false;
        for (var def : SmtText.extractDefineFuns(stdout)) {
            var m = Y_DEFINITION.matcher(def.strip());
            if (!m.matches()) {
                continue;
            }
            int pid = Integer.parseInt(m.group(1));
            if (pid >= placeCount) {
                continue;
            }
            y[pid] = m.group(3) != null
                ? new BigInteger(m.group(3)).negate()
                : new BigInteger(m.group(4));
            seen = true;
        }
        return seen ? y : null;
    }

    /**
     * Re-proves the bound in exact integer arithmetic: {@code y >= 0}, zero on every
     * H1/H3' place, {@code y·C <= 0} on every flat transition, and {@code y·d >= y·M0 + 1}.
     * Returns the bound when every check passes and {@code null} otherwise — the verifier
     * then continues to the fixpoint query rather than trust the solver's model.
     */
    public static Bound checkExact(
            FlatNet flatNet, MarkingState initialMarking, SmtProperty property, BigInteger[] y
    ) {
        var demand = violationDemand(flatNet, property);
        if (demand == null) {
            return null;
        }
        int p = flatNet.placeCount();
        if (y.length != p) {
            return null;
        }
        var zero = zeroWeightPlaces(flatNet);
        for (int i = 0; i < p; i++) {
            if (y[i].signum() < 0) {
                return null;
            }
            if (zero.contains(i) && y[i].signum() != 0) {
                return null;
            }
        }
        for (var ft : flatNet.transitions()) {
            BigInteger delta = BigInteger.ZERO;
            for (int i = 0; i < p; i++) {
                if (y[i].signum() == 0) {
                    continue;
                }
                delta = delta.add(y[i].multiply(BigInteger.valueOf(ft.postVector()[i] - ft.preVector()[i])));
            }
            if (delta.signum() > 0) {
                return null;
            }
        }
        BigInteger constant = BigInteger.ZERO;
        for (int i = 0; i < p; i++) {
            if (y[i].signum() != 0) {
                constant = constant.add(
                    y[i].multiply(BigInteger.valueOf(initialMarking.tokens(flatNet.places().get(i)))));
            }
        }
        BigInteger demandValue = BigInteger.ZERO;
        for (var entry : demand.entrySet()) {
            demandValue = demandValue.add(y[entry.getKey()].multiply(BigInteger.valueOf(entry.getValue())));
        }
        if (demandValue.compareTo(constant.add(BigInteger.ONE)) < 0) {
            return null;
        }
        return new Bound(Arrays.asList(y), constant, demandValue);
    }

    /** {@code 2*a + b <= 2} — the bound as the report prints it. */
    public static String formatBound(FlatNet flatNet, Bound bound) {
        var parts = new ArrayList<String>();
        for (int i = 0; i < bound.weights().size(); i++) {
            BigInteger w = bound.weights().get(i);
            if (w.signum() == 0) {
                continue;
            }
            String name = flatNet.places().get(i).name();
            parts.add(w.equals(BigInteger.ONE) ? name : w + "*" + name);
        }
        return (parts.isEmpty() ? "0" : String.join(" + ", parts)) + " <= " + bound.constant();
    }

    /** {@code ready_0 + ready_1 + _halt >= 3} — the violation's weighted demand as the report prints it. */
    public static String formatDemand(FlatNet flatNet, SmtProperty property, Bound bound) {
        var demand = violationDemand(flatNet, property);
        var parts = new ArrayList<String>();
        if (demand != null) {
            for (var entry : demand.entrySet()) {
                BigInteger w = bound.weights().get(entry.getKey()).multiply(BigInteger.valueOf(entry.getValue()));
                if (w.signum() == 0) {
                    continue;
                }
                String name = flatNet.places().get(entry.getKey()).name();
                parts.add(w.equals(BigInteger.ONE) ? name : w + "*" + name);
            }
        }
        return (parts.isEmpty() ? "0" : String.join(" + ", parts)) + " >= " + bound.demandValue();
    }
}
