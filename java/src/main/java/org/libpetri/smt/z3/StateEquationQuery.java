package org.libpetri.smt.z3;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;
import org.libpetri.smt.RestSet;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Objects;
import java.util.regex.Pattern;

/**
 * The query of the state-equation phase ([VER-018]): one {@code QF_LIA} script asking
 * whether a marking the <b>marking equation</b> admits can violate the property.
 *
 * <p>Every marking the untimed net reaches satisfies the rows of
 * {@link SmtEncoder#stateEquationConditions} for the firing counts {@code n >= 0} of the
 * run that reached it ([VER-016]): {@code m_p = M0_p + C_p·n} on a place whose column is
 * exact, and {@code m_p <= M0_p + C_p·n} on a place a consume-all or reset arc clears,
 * since every clearing firing removes at least its arc weight. {@code unsat} therefore
 * proves the property. A {@code sat} model is a <em>candidate</em>: a marking the
 * equation admits, which the net need not reach. The phase refines it away with
 * inequalities every reachable marking satisfies ({@link MarkingInequality}) and asks
 * again.
 *
 * <p>What the phase proves is {@code SE(M, n) ∧ ⋀ refinements(M)}, an inductive invariant
 * over the places and the firing counters. {@link #refinementCertificate} renders it as
 * the {@code Reachable} interpretation the [VER-016] certificate check takes, which
 * re-proves initiation, consecution and safety against the raw step relation.
 *
 * <p>The emitted script is byte-identical to the TypeScript, Rust and Python ports for the
 * same input ([VER-013] AC1): places in flat index order, then the firing counters,
 * {@code (- k)} for a negative literal, a lone term unwrapped. The equation rows are
 * {@link SmtEncoder#stateEquationConditions}'s, so the query can never disagree with the
 * fixpoint encoding about what the equation is.
 */
public final class StateEquationQuery {

    private StateEquationQuery() {}

    /** Which of the phase's three legs produced a refinement. The report names it. */
    public enum Origin {
        /** An initially marked trap the candidate leaves empty. */
        TRAP("trap"),
        /** An inequality kept by every step of the exact step relation. */
        INDUCTIVE("inductive"),
        /** One kept only by steps from markings the marking equation admits. */
        RELATIVE("relative");

        private final String label;

        Origin(String label) {
            this.label = label;
        }

        /** The word the report prints, e.g. {@code Refinement (inductive): …}. */
        public String label() {
            return label;
        }
    }

    /**
     * A linear inequality {@code Σ_p weights[p]·m_p <= constant} that every reachable marking
     * satisfies: an initially marked trap ({@code Σ_{q∈Q} m_q >= 1}, stored as weights
     * {@code -1} and constant {@code -1}), an inductive inequality, or one inductive relative
     * to the marking equation.
     *
     * <p>Weights and constant are {@link BigInteger} because every reading of them — the
     * exact re-check, {@link #holdsAt}, the certificate — must be exact: a wrapped product
     * would credit a refinement that was never evaluated.
     *
     * @param weights  one entry per flat place
     * @param constant the bound
     * @param origin   the leg that produced it
     */
    public record MarkingInequality(List<BigInteger> weights, BigInteger constant, Origin origin) {
        public MarkingInequality {
            weights = List.copyOf(weights);
            Objects.requireNonNull(constant);
            Objects.requireNonNull(origin);
        }

        /** The same inequality, attributed to another leg. */
        public MarkingInequality withOrigin(Origin other) {
            return new MarkingInequality(weights, constant, other);
        }
    }

    /**
     * A {@code sat} model of the query: a marking the equation admits and the firing counts
     * it takes.
     *
     * <p>{@code long} rather than {@code int}: a model value is whatever z3 chose, not a
     * token count the net ever held, and {@link #decodeCandidate} accepts every value the
     * TypeScript port does (up to {@code 2^53 - 1} in magnitude).
     *
     * @param marking one count per flat place
     * @param counts  one firing count per flat transition
     */
    public record Candidate(long[] marking, long[] counts) {
        public Candidate {
            marking = marking.clone();
            counts = counts.clone();
        }

        @Override
        public long[] marking() {
            return marking.clone();
        }

        @Override
        public long[] counts() {
            return counts.clone();
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof Candidate other
                && Arrays.equals(marking, other.marking)
                && Arrays.equals(counts, other.counts);
        }

        @Override
        public int hashCode() {
            return 31 * Arrays.hashCode(marking) + Arrays.hashCode(counts);
        }

        @Override
        public String toString() {
            return "Candidate[marking=" + Arrays.toString(marking)
                + ", counts=" + Arrays.toString(counts) + "]";
        }
    }

    /**
     * The query: {@code m, n >= 0}, the marking equation, the refinements, and the property's
     * violation exactly as the HORN error rule encodes it.
     *
     * @param sinkPlaces       places where a token may rest ([VER-002])
     * @param conditionalSinks places where a token may rest while a marker is marked ([VER-014])
     * @param refinements      the inequalities added so far, in the order they were found
     */
    public static String encode(
            FlatNet flatNet,
            MarkingState initialMarking,
            SmtProperty property,
            Collection<Place<?>> sinkPlaces,
            List<RestSet.ConditionalSinks> conditionalSinks,
            List<MarkingInequality> refinements
    ) {
        var mVars = new ArrayList<String>(flatNet.placeCount());
        for (int i = 0; i < flatNet.placeCount(); i++) {
            mVars.add("m" + i);
        }
        var nVars = new ArrayList<String>(flatNet.transitionCount());
        for (int k = 0; k < flatNet.transitionCount(); k++) {
            nVars.add("n" + k);
        }
        var lines = new ArrayList<String>();
        lines.add("; State-equation phase (VER-018): every reachable marking satisfies the marking");
        lines.add("; equation for the firing counts of its run (an upper bound on a place a");
        lines.add("; consume-all or reset arc clears); unsat = no such marking violates the property.");
        lines.add("(set-logic QF_LIA)");
        for (var v : mVars) {
            lines.add("(declare-const " + v + " Int)");
        }
        for (var v : nVars) {
            lines.add("(declare-const " + v + " Int)");
        }
        for (var v : mVars) {
            lines.add("(assert (>= " + v + " 0))");
        }
        for (var v : nVars) {
            lines.add("(assert (>= " + v + " 0))");
        }
        for (var c : SmtEncoder.stateEquationConditions(flatNet, initialMarking, nVars, mVars)) {
            lines.add("(assert " + c + ")");
        }
        for (var r : refinements) {
            lines.add("(assert " + inequalityTerm(r, mVars) + ")");
        }
        String bad = SmtEncoder.encodePropertyViolation(
            flatNet, property, mVars, sinkPlaces, SmtEncoder.resolveEnvInjection(flatNet), conditionalSinks);
        lines.add("(assert " + bad + ")");
        lines.add("(check-sat)");
        lines.add("(get-model)");
        return String.join("\n", lines);
    }

    private static final Pattern CANDIDATE_DEFINITION = Pattern.compile(
        "^\\(define-fun\\s+([mn])(\\d+)\\s+\\(\\)\\s+Int\\s+(\\(-\\s*(\\d+)\\s*\\)|(\\d+))\\s*\\)$",
        Pattern.DOTALL);

    /**
     * The largest magnitude the TypeScript port can hold exactly ({@code Number.MAX_SAFE_INTEGER}).
     * A model value beyond it fails the whole decode there, so it does here too: the same
     * reply must be decodable in every implementation, or the phase's verdict would depend
     * on the host.
     */
    private static final int SAFE_INTEGER_BITS = 53;

    /**
     * The candidate in a {@code sat} reply's model; {@code null} when the model defines no
     * marking or counter, or when a literal exceeds {@code 2^53 - 1} in magnitude — half a
     * candidate would be refined against as though it were whole.
     */
    public static Candidate decodeCandidate(String stdout, int placeCount, int transitionCount) {
        long[] marking = new long[placeCount];
        long[] counts = new long[transitionCount];
        boolean seen = false;
        for (var def : SmtText.extractDefineFuns(stdout)) {
            var m = CANDIDATE_DEFINITION.matcher(def.strip());
            if (!m.matches()) {
                continue;
            }
            BigInteger value = m.group(4) != null
                ? new BigInteger(m.group(4)).negate()
                : new BigInteger(m.group(5));
            if (value.abs().bitLength() > SAFE_INTEGER_BITS) {
                return null;
            }
            int index = indexBelow(m.group(2), m.group(1).equals("m") ? placeCount : transitionCount);
            if (index < 0) {
                continue;
            }
            if (m.group(1).equals("m")) {
                marking[index] = value.longValueExact();
            } else {
                counts[index] = value.longValueExact();
            }
            seen = true;
        }
        return seen ? new Candidate(marking, counts) : null;
    }

    /** The index {@code digits} names when it is below {@code limit}, else {@code -1}. */
    static int indexBelow(String digits, int limit) {
        var index = new BigInteger(digits);
        return index.compareTo(BigInteger.valueOf(limit)) < 0 ? index.intValueExact() : -1;
    }

    /**
     * Whether the inequality holds at a marking, in exact integer arithmetic. A place past
     * the end of {@code marking} counts as empty.
     */
    public static boolean holdsAt(MarkingInequality inequality, long[] marking) {
        BigInteger sum = BigInteger.ZERO;
        var weights = inequality.weights();
        for (int p = 0; p < weights.size(); p++) {
            BigInteger w = weights.get(p);
            if (w.signum() != 0) {
                long m = p < marking.length ? marking[p] : 0;
                sum = sum.add(w.multiply(BigInteger.valueOf(m)));
            }
        }
        return sum.compareTo(inequality.constant()) <= 0;
    }

    /**
     * The inequality as an SMT-LIB term over {@code vars}: {@code (<= Σ w·v c)}, or, when no
     * weight is positive, the same bound read the other way round — a trap is
     * {@code (>= (+ v3 v5) 1)}.
     */
    static String inequalityTerm(MarkingInequality inequality, List<String> vars) {
        var weights = inequality.weights();
        boolean flip = weights.stream().allMatch(w -> w.signum() <= 0);
        var terms = new ArrayList<String>();
        for (int p = 0; p < weights.size(); p++) {
            BigInteger w = flip ? weights.get(p).negate() : weights.get(p);
            if (w.signum() != 0) {
                terms.add(term(w, vars.get(p)));
            }
        }
        String lhs = terms.isEmpty() ? "0"
            : terms.size() == 1 ? terms.getFirst()
            : "(+ " + String.join(" ", terms) + ")";
        return flip
            ? "(>= " + lhs + " " + literal(inequality.constant().negate()) + ")"
            : "(<= " + lhs + " " + literal(inequality.constant()) + ")";
    }

    /**
     * The phase's proof as the {@code Reachable} interpretation the [VER-016] certificate
     * check takes: {@code (define-fun Reachable ((x!0 Int) …) Bool …)} over the places and one
     * firing counter per flat transition. The check conjoins the marking equation itself, so
     * the body carries only the refinements, and is {@code true} when none was needed.
     */
    public static String refinementCertificate(
            int placeCount, int transitionCount, List<MarkingInequality> refinements
    ) {
        var params = new ArrayList<String>(placeCount + transitionCount);
        for (int i = 0; i < placeCount + transitionCount; i++) {
            params.add("(x!" + i + " Int)");
        }
        var vars = new ArrayList<String>(placeCount);
        for (int i = 0; i < placeCount; i++) {
            vars.add("x!" + i);
        }
        var terms = new ArrayList<String>(refinements.size());
        for (var r : refinements) {
            terms.add(inequalityTerm(r, vars));
        }
        String body = terms.isEmpty() ? "true"
            : terms.size() == 1 ? terms.getFirst()
            : "(and " + String.join("\n         ", terms) + ")";
        return "(define-fun Reachable (" + String.join(" ", params) + ") Bool\n    " + body + ")";
    }

    /** {@code Merge/hasdata <= Merge/ready_0 + Merge/ready_1}; a trap reads {@code a + b >= 1}. */
    public static String formatInequality(FlatNet flatNet, MarkingInequality inequality) {
        var left = new ArrayList<String>();
        var right = new ArrayList<String>();
        var weights = inequality.weights();
        for (int p = 0; p < weights.size(); p++) {
            BigInteger w = weights.get(p);
            if (w.signum() > 0) {
                left.add(named(flatNet, p, w));
            } else if (w.signum() < 0) {
                right.add(named(flatNet, p, w.negate()));
            }
        }
        if (left.isEmpty()) {
            return (right.isEmpty() ? "0" : String.join(" + ", right))
                + " >= " + inequality.constant().negate();
        }
        // `a <= b` reads better than `a <= 0 + b`, so a zero constant is dropped once the
        // right-hand side has a term of its own.
        boolean dropZero = inequality.constant().signum() == 0 && !right.isEmpty();
        var rhs = new ArrayList<String>();
        if (!dropZero) {
            rhs.add(inequality.constant().toString());
        }
        rhs.addAll(right);
        return String.join(" + ", left) + " <= " + String.join(" + ", rhs);
    }

    private static String named(FlatNet flatNet, int p, BigInteger w) {
        String name = flatNet.places().get(p).name();
        return w.equals(BigInteger.ONE) ? name : w + "*" + name;
    }

    private static String term(BigInteger c, String v) {
        if (c.equals(BigInteger.ONE)) {
            return v;
        }
        if (c.equals(BigInteger.ONE.negate())) {
            return "(- " + v + ")";
        }
        return c.signum() > 0 ? "(* " + c + " " + v + ")" : "(* (- " + c.negate() + ") " + v + ")";
    }

    private static String literal(BigInteger c) {
        return c.signum() < 0 ? "(- " + c.negate() + ")" : c.toString();
    }
}
