package org.libpetri.smt.z3;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;
import org.libpetri.smt.RestSet;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.FlatTransition;
import org.libpetri.smt.invariant.PInvariant;
import org.libpetri.smt.invariant.PInvariantComputer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * Encodes a flattened Petri net as Constrained Horn Clauses (CHC) in SMT-LIB2 text for
 * Z3's Spacer engine (VER-013).
 *
 * <p>The encoding maps the Petri net to integer arithmetic over a state vector
 * {@code M = (m0, ..., m{P-1})} where {@code m_i} is the token count of place {@code i}:
 * <ul>
 *   <li>{@code (assert (Reachable M0))} — the initial marking is reachable</li>
 *   <li>one rule per flat transition: {@code Reachable(M') :- Reachable(M) AND enabled(M,t)
 *       AND fire(M,M',t) AND M' >= 0 AND invariants(M') AND env-bounds(M')}</li>
 *   <li>one env-injection rule per injected environment place (VER-006)</li>
 *   <li>{@code Error :- Reachable(M) AND violation(M)}</li>
 *   <li>{@code (assert (not Error))}: {@code sat} is PROVEN, {@code unsat} is VIOLATED</li>
 * </ul>
 *
 * <p>With the state equation ([VER-016], the {@code stateEquation} option of
 * {@link #encode(FlatNet, MarkingState, SmtProperty, List, Collection, boolean, List, boolean)})
 * the state is {@code (M, n)} — one firing counter per flat transition — and every
 * transition rule also conjoins {@code M' = M0 + C·n'}, which hands Spacer every linear
 * consequence of the marking equation (the inequality conservation laws it cannot invent)
 * at no enumeration cost.
 *
 * <p>The emitted script is byte-identical to the Rust reference
 * ({@code smt_encoder.rs}) and the TypeScript port for the same input: places are in
 * code-point order of their names, the property's places, sinks, env bounds and
 * injections in place-index order, invariants in the order the verifier canonicalised.
 */
public final class SmtEncoder {

    private SmtEncoder() {}

    /**
     * An encoded SMT-LIB2 script.
     *
     * @param smt2         the script text
     * @param placeCount   the number of flat places (the leading arguments of
     *                     {@code Reachable} in the flat encoding)
     * @param counterCount the number of firing counters that follow the places in
     *                     {@code Reachable} ([VER-016]): one per flat transition when the
     *                     state equation is encoded, else 0
     */
    public record SmtEncoding(String smt2, int placeCount, int counterCount) {
        /** An encoding without firing counters. */
        public SmtEncoding(String smt2, int placeCount) {
            this(smt2, placeCount, 0);
        }
    }

    /** An injected environment place: its flat index and its cap ({@code null} = unbounded). */
    record Injection(int pid, Integer bound) {}

    /**
     * Encodes the net and property as a HORN script, without conditional sinks or the
     * state equation.
     *
     * @param flatNet        the flattened net (carries the env bounds and injection map)
     * @param initialMarking the initial marking
     * @param property       the safety property to verify
     * @param invariants     P-invariants for strengthening (canonical order)
     * @param sinkPlaces     expected terminal places (deadlock permitted when any has a token)
     * @param produceProofs  emit {@code :produce-proofs} and {@code (get-proof)} so an
     *                       {@code unsat} reply carries the refutation the replay decodes
     */
    public static SmtEncoding encode(
            FlatNet flatNet,
            MarkingState initialMarking,
            SmtProperty property,
            List<PInvariant> invariants,
            Collection<Place<?>> sinkPlaces,
            boolean produceProofs
    ) {
        return encode(flatNet, initialMarking, property, invariants, sinkPlaces, produceProofs,
            List.of(), false);
    }

    /**
     * Encodes the net and property as a HORN script.
     *
     * <p>With {@code stateEquation} ([VER-016]) the state carries one firing counter per
     * flat transition after the places: {@code Reachable(M, n)}, the initial fact has
     * {@code n = 0}, transition {@code k}'s rule increments {@code n_k} and copies the
     * others, an injection rule copies them all, and every transition rule's body conjoins
     * {@code m'_p = M0_p + Σ_t C[p][t]·n'_t} for each place whose column is exact (no
     * consume-all / reset arc, not injected) together with {@code n' >= 0}. The error rule
     * quantifies the counters and constrains only the marking.
     *
     * @param conditionalSinks places where a token may rest while a marker is marked
     *                         ([VER-014]); read by {@code DeadlockFree} only
     * @param stateEquation    carry one firing counter per flat transition and conjoin the
     *                         marking equation into every rule body ([VER-016])
     */
    public static SmtEncoding encode(
            FlatNet flatNet,
            MarkingState initialMarking,
            SmtProperty property,
            List<PInvariant> invariants,
            Collection<Place<?>> sinkPlaces,
            boolean produceProofs,
            List<RestSet.ConditionalSinks> conditionalSinks,
            boolean stateEquation
    ) {
        int p = flatNet.placeCount();
        int t = stateEquation ? flatNet.transitionCount() : 0;
        var lines = new ArrayList<String>();
        List<Injection> envInject = resolveEnvInjection(flatNet);

        if (produceProofs) {
            lines.add("(set-option :produce-proofs true)");
        }
        lines.add("(set-logic HORN)");
        lines.add("");

        lines.add("(declare-fun Reachable (" + String.join(" ", ints(p + t)) + ") Bool)");
        lines.add("(declare-fun Error () Bool)");
        lines.add("");

        List<String> mVars = vars(p, "");
        List<String> mpVars = vars(p, "p");
        List<String> nVars = counterVars(t, "");
        List<String> npVars = counterVars(t, "p");

        var m0 = new ArrayList<String>(p + t);
        for (int i = 0; i < p; i++) {
            m0.add(Integer.toString(initialMarking.tokens(flatNet.places().get(i))));
        }
        for (int k = 0; k < t; k++) {
            m0.add("0");
        }
        lines.add("(assert (Reachable " + String.join(" ", m0) + "))");
        lines.add("");

        List<String> equation = t > 0
            ? stateEquationConditions(flatNet, initialMarking, npVars, mpVars)
            : List.of();
        for (int k = 0; k < flatNet.transitionCount(); k++) {
            var ft = flatNet.transitions().get(k);
            var strengthening = new ArrayList<>(invariantConditions(invariants, mpVars));
            if (t > 0) {
                strengthening.addAll(counterConditions(k, nVars, npVars));
                strengthening.addAll(equation);
            }
            lines.add(encodeTransitionRule(flatNet, ft, mVars, mpVars, nVars, npVars, strengthening));
        }
        // Environment-injection rules (VER-006): NOT flat transitions, so the deadlock
        // encoding never sees them; no P-invariant strengthening, injection breaks
        // conservation on purpose. The counters are carried unchanged (VER-016).
        for (var inj : envInject) {
            lines.add(encodeInjectionRule(p, inj.pid(), inj.bound(), mVars, mpVars, nVars, npVars));
        }
        lines.add("");

        lines.add(encodeErrorRule(flatNet, property, mVars, nVars, sinkPlaces, envInject, conditionalSinks));
        lines.add("");

        // Under HORN/Spacer this is SAT when an inductive invariant excludes every
        // violating state (PROVEN) and UNSAT when none exists (VIOLATED).
        lines.add("(assert (not Error))");
        lines.add("(check-sat)");
        if (produceProofs) {
            lines.add("(get-proof)");
        }
        lines.add("(get-model)");

        return new SmtEncoding(String.join("\n", lines), p, t);
    }

    /** The injected environment places in place-index order. */
    static List<Injection> resolveEnvInjection(FlatNet flatNet) {
        var out = new ArrayList<Injection>();
        for (var entry : flatNet.environmentInjection().entrySet()) {
            int idx = flatNet.indexOf(entry.getKey());
            if (idx >= 0) {
                out.add(new Injection(idx, entry.getValue()));
            }
        }
        out.sort(Comparator.comparingInt(Injection::pid));
        return out;
    }

    /** The bounded environment places (legacy post-cap) in place-index order. */
    private static List<int[]> envBounds(FlatNet flatNet) {
        var out = new ArrayList<int[]>();
        for (var entry : flatNet.environmentBounds().entrySet()) {
            int idx = flatNet.indexOf(entry.getKey());
            if (idx >= 0) {
                out.add(new int[] {idx, entry.getValue()});
            }
        }
        out.sort(Comparator.comparingInt(a -> a[0]));
        return out;
    }

    private static List<String> ints(int n) {
        var out = new ArrayList<String>(n);
        for (int i = 0; i < n; i++) {
            out.add("Int");
        }
        return out;
    }

    private static List<String> vars(int p, String suffix) {
        var out = new ArrayList<String>(p);
        for (int i = 0; i < p; i++) {
            out.add("m" + i + suffix);
        }
        return out;
    }

    /** {@code n0..n{T-1}} ({@code suffix} = {@code "p"} for the primed counters), empty when {@code T} is 0. */
    private static List<String> counterVars(int t, String suffix) {
        var out = new ArrayList<String>(t);
        for (int k = 0; k < t; k++) {
            out.add("n" + k + suffix);
        }
        return out;
    }

    private static String quantified(List<String> vars) {
        var parts = new ArrayList<String>(vars.size());
        for (var v : vars) {
            parts.add("(" + v + " Int)");
        }
        return String.join(" ", parts);
    }

    private static List<String> concat(List<String> a, List<String> b) {
        var out = new ArrayList<String>(a.size() + b.size());
        out.addAll(a);
        out.addAll(b);
        return out;
    }

    private static boolean contains(int[] arr, int v) {
        for (int x : arr) {
            if (x == v) {
                return true;
            }
        }
        return false;
    }

    // === State equation (VER-016) ===

    /**
     * The places whose column of the incidence matrix is exact in every step: no
     * consume-all / reset arc on them (H1) and not injected (H3'). Only these carry a
     * marking-equation row; the others are unconstrained by it.
     */
    public static List<Integer> equationPlaces(FlatNet flatNet) {
        var excluded = new java.util.HashSet<>(PInvariantComputer.nonlinearPlaces(flatNet));
        for (var inj : resolveEnvInjection(flatNet)) {
            excluded.add(inj.pid());
        }
        var out = new ArrayList<Integer>();
        for (int p = 0; p < flatNet.placeCount(); p++) {
            if (!excluded.contains(p)) {
                out.add(p);
            }
        }
        return out;
    }

    /**
     * The counter update of transition {@code fired} ({@code -1} for an injection step,
     * which fires no counted transition): {@code n'_k = n_k + 1} for the fired one,
     * {@code n'_j = n_j} for the rest, then {@code n' >= 0}.
     */
    static List<String> counterConditions(int fired, List<String> nVars, List<String> npVars) {
        var conditions = new ArrayList<String>();
        for (int k = 0; k < nVars.size(); k++) {
            conditions.add(k == fired
                ? "(= " + npVars.get(k) + " (+ " + nVars.get(k) + " 1))"
                : "(= " + npVars.get(k) + " " + nVars.get(k) + ")");
        }
        for (var np : npVars) {
            conditions.add("(>= " + np + " 0)");
        }
        return conditions;
    }

    /**
     * The marking equation over the given marking and counter variables: for every place
     * of {@link #equationPlaces}, {@code m_p = M0_p + Σ_t C[p][t]·n_t} over the flat
     * transitions with a non-zero effect on {@code p}, in transition order. A coefficient
     * of 1 is the bare counter, −1 is {@code (- n)}, any other {@code (* c n)} with a
     * negative {@code c} written {@code (- k)}.
     */
    public static List<String> stateEquationConditions(
            FlatNet flatNet, MarkingState initialMarking, List<String> nVars, List<String> mVars
    ) {
        var conditions = new ArrayList<String>();
        for (int p : equationPlaces(flatNet)) {
            var terms = new ArrayList<String>();
            for (int t = 0; t < flatNet.transitionCount(); t++) {
                var ft = flatNet.transitions().get(t);
                int c = ft.postVector()[p] - ft.preVector()[p];
                if (c == 0) {
                    continue;
                }
                String n = nVars.get(t);
                terms.add(c == 1 ? n
                    : c == -1 ? "(- " + n + ")"
                    : c > 0 ? "(* " + c + " " + n + ")"
                    : "(* (- " + (-c) + ") " + n + ")");
            }
            int m0 = initialMarking.tokens(flatNet.places().get(p));
            conditions.add(terms.isEmpty()
                ? "(= " + mVars.get(p) + " " + m0 + ")"
                : "(= " + mVars.get(p) + " (+ " + m0 + " " + String.join(" ", terms) + "))");
        }
        return conditions;
    }

    // === Shared condition emitters ===
    //
    // Emitted by BOTH the CHC rule encoding and the plain-SMT step relation
    // (encodeStepRelationSmt2) the certificate check uses, so the two cannot drift.

    /**
     * Enablement + firing + non-negativity conjuncts for one flat transition:
     * {@code enabled(M, t)}, {@code fire(M, M', t)}, {@code M' >= 0}. Excludes the
     * {@code Reachable} body atom, the P-invariant strengthening and the env bounds.
     */
    static List<String> firingConditions(
            FlatNet flatNet, FlatTransition ft, List<String> mVars, List<String> mpVars
    ) {
        int p = flatNet.placeCount();
        var conditions = new ArrayList<String>();
        for (int i = 0; i < p; i++) {
            if (ft.preVector()[i] > 0) {
                conditions.add("(>= " + mVars.get(i) + " " + ft.preVector()[i] + ")");
            }
        }
        for (int inh : ft.inhibitorPlaces()) {
            conditions.add("(= " + mVars.get(inh) + " 0)");
        }
        for (int rd : ft.readPlaces()) {
            conditions.add("(>= " + mVars.get(rd) + " 1)");
        }
        for (int i = 0; i < p; i++) {
            if (contains(ft.resetPlaces(), i) || ft.consumeAll()[i]) {
                // Reset / consume-all: clear then add post.
                conditions.add("(= " + mpVars.get(i) + " " + ft.postVector()[i] + ")");
            } else {
                int delta = ft.postVector()[i] - ft.preVector()[i];
                if (delta > 0) {
                    conditions.add("(= " + mpVars.get(i) + " (+ " + mVars.get(i) + " " + delta + "))");
                } else if (delta < 0) {
                    conditions.add("(= " + mpVars.get(i) + " (- " + mVars.get(i) + " " + (-delta) + "))");
                } else {
                    conditions.add("(= " + mpVars.get(i) + " " + mVars.get(i) + ")");
                }
            }
        }
        for (int i = 0; i < p; i++) {
            conditions.add("(>= " + mpVars.get(i) + " 0)");
        }
        return conditions;
    }

    /**
     * P-invariant conjuncts over the given marking variables. The step relation never
     * emits these: the certificate check keeps its relation UNSTRENGTHENED and conjoins
     * them into the candidate instead, where the VCs re-prove them.
     */
    static List<String> invariantConditions(List<PInvariant> invariants, List<String> vars) {
        var conditions = new ArrayList<String>();
        for (var inv : invariants) {
            var terms = new ArrayList<String>();
            for (int i : new TreeSet<>(inv.support())) {
                terms.add("(* " + inv.weights()[i] + " " + vars.get(i) + ")");
            }
            if (terms.isEmpty()) {
                continue;
            }
            String sum = terms.size() == 1 ? terms.getFirst() : "(+ " + String.join(" ", terms) + ")";
            conditions.add("(= " + sum + " " + inv.constant() + ")");
        }
        return conditions;
    }

    /** Environment post-cap conjuncts on the next marking (legacy Bounded mode). */
    private static List<String> envBoundConditions(FlatNet flatNet, List<String> mpVars) {
        var conditions = new ArrayList<String>();
        for (int[] bound : envBounds(flatNet)) {
            conditions.add("(<= " + mpVars.get(bound[0]) + " " + bound[1] + ")");
        }
        return conditions;
    }

    /**
     * Guard + column-update conjuncts for one env-injection step (VER-006):
     * {@code [m_pid < bound]}, {@code m'_pid = m_pid + 1}, all other columns copied.
     */
    private static List<String> injectionConditions(
            int p, int pid, Integer bound, List<String> mVars, List<String> mpVars
    ) {
        var conditions = new ArrayList<String>();
        if (bound != null) {
            conditions.add("(< " + mVars.get(pid) + " " + bound + ")");
        }
        for (int i = 0; i < p; i++) {
            if (i == pid) {
                conditions.add("(= " + mpVars.get(i) + " (+ " + mVars.get(i) + " 1))");
            } else {
                conditions.add("(= " + mpVars.get(i) + " " + mVars.get(i) + ")");
            }
        }
        return conditions;
    }

    private static String encodeTransitionRule(
            FlatNet flatNet, FlatTransition ft, List<String> mVars, List<String> mpVars,
            List<String> nVars, List<String> npVars, List<String> strengthening
    ) {
        var conditions = new ArrayList<String>();
        conditions.add("(Reachable " + String.join(" ", concat(mVars, nVars)) + ")");
        conditions.addAll(firingConditions(flatNet, ft, mVars, mpVars));
        conditions.addAll(strengthening);
        conditions.addAll(envBoundConditions(flatNet, mpVars));
        String body = "(and " + String.join("\n            ", conditions) + ")";
        var all = new ArrayList<>(mVars);
        all.addAll(mpVars);
        all.addAll(nVars);
        all.addAll(npVars);
        return "(assert (forall (" + quantified(all) + ")\n  (=> " + body
            + "\n      (Reachable " + String.join(" ", concat(mpVars, npVars)) + "))))";
    }

    private static String encodeInjectionRule(
            int p, int pid, Integer bound, List<String> mVars, List<String> mpVars,
            List<String> nVars, List<String> npVars
    ) {
        var conditions = new ArrayList<String>();
        conditions.add("(Reachable " + String.join(" ", concat(mVars, nVars)) + ")");
        conditions.addAll(injectionConditions(p, pid, bound, mVars, mpVars));
        if (!nVars.isEmpty()) {
            conditions.addAll(counterConditions(-1, nVars, npVars));
        }
        String body = "(and " + String.join("\n            ", conditions) + ")";
        var all = new ArrayList<>(mVars);
        all.addAll(mpVars);
        all.addAll(nVars);
        all.addAll(npVars);
        return "(assert (forall (" + quantified(all) + ")\n  (=> " + body
            + "\n      (Reachable " + String.join(" ", concat(mpVars, npVars)) + "))))";
    }

    /**
     * Joins conjuncts into one formula ({@code true} when empty, the bare conjunct when
     * singleton, since SMT-LIB {@code and} wants at least two arguments).
     */
    static String conjoin(List<String> conditions) {
        return switch (conditions.size()) {
            case 0 -> "true";
            case 1 -> conditions.getFirst();
            default -> "(and " + String.join(" ", conditions) + ")";
        };
    }

    /** {@link #encodeStepRelationSmt2(FlatNet, boolean)} without firing counters. */
    public static String encodeStepRelationSmt2(FlatNet flatNet) {
        return encodeStepRelationSmt2(flatNet, false);
    }

    /**
     * The net's one-step relation {@code T(M, M')} as one plain SMT-LIB2 formula over
     * the free variables {@code m0..} / {@code m0p..}: the disjunction of every flat
     * transition firing and every env-injection step (VER-006). This is the
     * UNSTRENGTHENED relation the certificate check validates against: it shares the
     * condition emitters with the CHC path but omits the P-invariant conjuncts, so a
     * certificate poisoned by a wrong invariant cannot re-certify itself.
     *
     * <p>With {@code stateEquation} the counters move with the step ([VER-016]); the
     * marking equation itself is strengthening and stays out — the candidate carries it
     * and the VCs re-prove it.
     */
    public static String encodeStepRelationSmt2(FlatNet flatNet, boolean stateEquation) {
        int p = flatNet.placeCount();
        int t = stateEquation ? flatNet.transitionCount() : 0;
        List<String> mVars = vars(p, "");
        List<String> mpVars = vars(p, "p");
        List<String> nVars = counterVars(t, "");
        List<String> npVars = counterVars(t, "p");
        var disjuncts = new ArrayList<String>();
        for (int k = 0; k < flatNet.transitionCount(); k++) {
            var ft = flatNet.transitions().get(k);
            var conditions = firingConditions(flatNet, ft, mVars, mpVars);
            if (t > 0) {
                conditions.addAll(counterConditions(k, nVars, npVars));
            }
            conditions.addAll(envBoundConditions(flatNet, mpVars));
            disjuncts.add(conjoin(conditions));
        }
        for (var inj : resolveEnvInjection(flatNet)) {
            var conditions = injectionConditions(p, inj.pid(), inj.bound(), mVars, mpVars);
            if (t > 0) {
                conditions.addAll(counterConditions(-1, nVars, npVars));
            }
            disjuncts.add(conjoin(conditions));
        }
        return switch (disjuncts.size()) {
            case 0 -> "false";
            case 1 -> disjuncts.getFirst();
            default -> "(or " + String.join("\n    ", disjuncts) + ")";
        };
    }

    private static String encodeErrorRule(
            FlatNet flatNet, SmtProperty property, List<String> mVars, List<String> nVars,
            Collection<Place<?>> sinkPlaces, List<Injection> envInject,
            List<RestSet.ConditionalSinks> conditionalSinks
    ) {
        String violation = encodePropertyViolation(
            flatNet, property, mVars, sinkPlaces, envInject, conditionalSinks);
        List<String> state = concat(mVars, nVars);
        return "(assert (forall (" + quantified(state) + ")\n  (=> (and (Reachable "
            + String.join(" ", state) + ") " + violation + ")\n      Error)))";
    }

    /** The flat indices of the given places that resolve, ascending. */
    static List<Integer> indexOrdered(FlatNet flatNet, Collection<Place<?>> places) {
        var idx = new TreeSet<Integer>();
        for (var place : places) {
            int i = flatNet.indexOf(place);
            if (i >= 0) {
                idx.add(i);
            }
        }
        return List.copyOf(idx);
    }

    private static int requireIndex(FlatNet flatNet, Place<?> place, String property) {
        int idx = flatNet.indexOf(place);
        if (idx < 0) {
            throw new IllegalArgumentException(
                property + " property references unknown place: " + place.name());
        }
        return idx;
    }

    /** {@link #encodePropertyViolation(FlatNet, SmtProperty, List, Collection, List, List)} without conditional sinks. */
    static String encodePropertyViolation(
            FlatNet flatNet, SmtProperty property, List<String> mVars,
            Collection<Place<?>> sinkPlaces, List<Injection> envInject
    ) {
        return encodePropertyViolation(flatNet, property, mVars, sinkPlaces, envInject, List.of());
    }

    /**
     * The property-violation condition {@code Bad(M)} over {@code mVars}. Also used by
     * the certificate check's safety VC, which must test against exactly the violation
     * the error rule encodes.
     */
    static String encodePropertyViolation(
            FlatNet flatNet, SmtProperty property, List<String> mVars,
            Collection<Place<?>> sinkPlaces, List<Injection> envInject,
            List<RestSet.ConditionalSinks> conditionalSinks
    ) {
        return switch (property) {
            // DeadlockFree (VER-002): a quiescent marking that STRANDS a token — holds
            // one in a place where resting is not permitted. The empty marking strands
            // nothing and is therefore not a violation (AC4). A conditional sink
            // (VER-014) is stranded only while every marker that would excuse it is
            // unmarked.
            case SmtProperty.DeadlockFree() -> {
                var conditions = encodeQuiescent(flatNet, mVars, envInject);
                if (conditions == null) {
                    yield "false";
                }
                var stranded = strandedConditions(
                    RestSet.strandingExcuses(flatNet, sinkPlaces, conditionalSinks), mVars);
                if (stranded.isEmpty()) {
                    // Every place is a declared sink: nothing can ever be stranded.
                    yield "false";
                }
                conditions.add("(or " + String.join(" ", stranded) + ")");
                yield joinConditions(conditions);
            }
            // TerminatesAtSink (VER-002): a quiescent marking that reached NO declared
            // sink. This is the predicate DeadlockFree carried before the VER-002 split,
            // unchanged.
            case SmtProperty.TerminatesAtSink() -> {
                var conditions = encodeQuiescent(flatNet, mVars, envInject);
                if (conditions == null) {
                    yield "false";
                }
                for (int pid : indexOrdered(flatNet, sinkPlaces)) {
                    conditions.add("(= " + mVars.get(pid) + " 0)");
                }
                yield joinConditions(conditions);
            }
            case SmtProperty.MutualExclusion me -> {
                int i1 = requireIndex(flatNet, me.p1(), "MutualExclusion");
                int i2 = requireIndex(flatNet, me.p2(), "MutualExclusion");
                var conditions = new ArrayList<String>();
                for (int i : new TreeSet<>(List.of(i1, i2))) {
                    conditions.add("(>= " + mVars.get(i) + " 1)");
                }
                yield "(and " + String.join(" ", conditions) + ")";
            }
            case SmtProperty.PlaceBound pb -> {
                int idx = requireIndex(flatNet, pb.place(), "PlaceBound");
                yield "(> " + mVars.get(idx) + " " + pb.bound() + ")";
            }
            case SmtProperty.BranchPlaceBound bpb -> {
                // ν-net budget lever (NU-040): a count bound, encoded like PlaceBound.
                int idx = requireIndex(flatNet, bpb.place(), "BranchPlaceBound");
                yield "(> " + mVars.get(idx) + " " + bpb.bound() + ")";
            }
            case SmtProperty.Unreachable ur -> {
                var conditions = new ArrayList<String>();
                for (int i : indexOrdered(flatNet, ur.places())) {
                    conditions.add("(>= " + mVars.get(i) + " 1)");
                }
                yield conditions.isEmpty() ? "false" : "(and " + String.join(" ", conditions) + ")";
            }
            // JoinedOrDeadLettered (NU-040 AC4): a quiescent state that still holds a
            // `pending` token is a stranded correlation group. Carries NO sink clause —
            // a declared sink must not excuse a stranded group.
            case SmtProperty.JoinedOrDeadLettered jdl -> {
                int idx = flatNet.indexOf(jdl.pending());
                if (idx < 0) {
                    // Unknown pending place name: no state can violate.
                    yield "false";
                }
                var conditions = encodeQuiescent(flatNet, mVars, envInject);
                if (conditions == null) {
                    yield "false";
                }
                conditions.add("(>= " + mVars.get(idx) + " 1)");
                yield joinConditions(conditions);
            }
        };
    }

    /**
     * One "a token is stranded here" disjunct per place where resting is not always
     * permitted: {@code (>= m 1)}, conjoined with {@code (= marker 0)} for every marker
     * whose presence would excuse it ([VER-014]), markers in place-index order. Shared
     * with the name-coloured encoder through {@code counts}, which renders a place's
     * count term.
     */
    static List<String> strandedConditions(int[][] excuses, List<String> counts) {
        var stranded = new ArrayList<String>();
        for (int pid = 0; pid < excuses.length; pid++) {
            int[] markers = excuses[pid];
            if (markers == null) {
                continue;
            }
            if (markers.length == 0) {
                stranded.add("(>= " + counts.get(pid) + " 1)");
            } else {
                var unmarked = new ArrayList<String>(markers.length);
                for (int k : markers) {
                    unmarked.add("(= " + counts.get(k) + " 0)");
                }
                stranded.add("(and (>= " + counts.get(pid) + " 1) " + String.join(" ", unmarked) + ")");
            }
        }
        return stranded;
    }

    /**
     * Joins violation conjuncts into the final {@code Bad(M)} term. An empty conjunction
     * is vacuously true — a net with no transitions is quiescent everywhere.
     */
    private static String joinConditions(List<String> conditions) {
        return conditions.isEmpty()
            ? "true"
            : "(and " + String.join("\n         ", conditions) + ")";
    }

    /**
     * Quiescence: every transition is disabled.
     *
     * <p>Shared core of the three quiescence-sensitive properties (VER-002
     * {@link SmtProperty.DeadlockFree} and {@link SmtProperty.TerminatesAtSink},
     * NU-040 {@link SmtProperty.JoinedOrDeadLettered}). Each conjoins its own clause on
     * top and none is encoded here, so a change to one predicate cannot silently move
     * the others — which is exactly how the sink clause leaked into
     * {@code JoinedOrDeadLettered} before NU-040 AC4.
     *
     * <p>Returns {@code null} when some transition is enabled in every marking: no
     * quiescent marking exists, so every property built on this is unviolatable.
     *
     * <p>Environment inputs are treated as injectable (VER-006): an input/read on an
     * injectable env place is NOT a reason the transition is disabled (AlwaysAvailable
     * always satisfies it, Bounded(k) iff the demand is at most k), so a reactive net
     * merely waiting for input is not reported as quiescent; only a genuinely stuck
     * marking is.
     */
    private static List<String> encodeQuiescent(
            FlatNet flatNet, List<String> mVars, List<Injection> envInject
    ) {
        var envBound = new java.util.HashMap<Integer, Integer>();
        for (var inj : envInject) {
            envBound.put(inj.pid(), inj.bound());
        }
        var disabledConditions = new ArrayList<String>();
        for (var ft : flatNet.transitions()) {
            var disableReasons = new ArrayList<String>();
            boolean permanentlyDisabled = false;
            for (int i = 0; i < flatNet.placeCount(); i++) {
                if (ft.preVector()[i] > 0) {
                    if (envBound.containsKey(i)) {
                        Integer k = envBound.get(i);
                        if (k != null && ft.preVector()[i] > k) {
                            permanentlyDisabled = true;
                        }
                        continue;
                    }
                    disableReasons.add("(< " + mVars.get(i) + " " + ft.preVector()[i] + ")");
                }
            }
            for (int inh : ft.inhibitorPlaces()) {
                disableReasons.add("(> " + mVars.get(inh) + " 0)");
            }
            for (int rd : ft.readPlaces()) {
                if (envBound.containsKey(rd)) {
                    Integer k = envBound.get(rd);
                    if (k != null && k < 1) {
                        permanentlyDisabled = true;
                    }
                    continue;
                }
                disableReasons.add("(< " + mVars.get(rd) + " 1)");
            }
            if (permanentlyDisabled) {
                disabledConditions.add("true");
                continue;
            }
            if (disableReasons.isEmpty()) {
                // Transition is always enabled (possibly via injection) — never quiescent.
                return null;
            }
            disabledConditions.add("(or " + String.join(" ", disableReasons) + ")");
        }
        return disabledConditions;
    }

    /**
     * Whether NO marking of this net can be quiescent, because some transition is enabled in
     * every marking — an environment-gated one whose input injection can always satisfy
     * ([VER-006]).
     *
     * <p>Every quiescence property is then unviolatable and comes back {@code Proven} for a
     * reason that has nothing to do with the net's own behaviour: an open net with an
     * always-available source never comes to rest, so "no reachable quiescent marking strands
     * a token" is vacuously true. The verdict is correct and says nothing, and a caller
     * reading it as "this workflow completes properly" is misreading it, so the verifier says
     * so in the report.
     */
    public static boolean quiescenceUnreachable(FlatNet flatNet) {
        return encodeQuiescent(flatNet, vars(flatNet.placeCount(), ""), resolveEnvInjection(flatNet))
            == null;
    }

    /** Env-injectable bound map, index to cap ({@code null} = unbounded), for the coloured encoder. */
    static Map<Integer, Integer> injectionMap(FlatNet flatNet) {
        var out = new java.util.HashMap<Integer, Integer>();
        for (var inj : resolveEnvInjection(flatNet)) {
            out.put(inj.pid(), inj.bound());
        }
        return out;
    }
}
