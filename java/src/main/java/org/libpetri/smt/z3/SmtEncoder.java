package org.libpetri.smt.z3;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.FlatTransition;
import org.libpetri.smt.invariant.PInvariant;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
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
     * @param smt2       the script text
     * @param placeCount the number of flat places (the arity of {@code Reachable} in the
     *                   flat encoding)
     */
    public record SmtEncoding(String smt2, int placeCount) {}

    /** An injected environment place: its flat index and its cap ({@code null} = unbounded). */
    record Injection(int pid, Integer bound) {}

    /**
     * Encodes the net and property as a HORN script.
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
        int p = flatNet.placeCount();
        var lines = new ArrayList<String>();
        List<Injection> envInject = resolveEnvInjection(flatNet);

        if (produceProofs) {
            lines.add("(set-option :produce-proofs true)");
        }
        lines.add("(set-logic HORN)");
        lines.add("");

        lines.add("(declare-fun Reachable (" + String.join(" ", ints(p)) + ") Bool)");
        lines.add("(declare-fun Error () Bool)");
        lines.add("");

        List<String> mVars = vars(p, "");
        List<String> mpVars = vars(p, "p");

        var m0 = new ArrayList<String>(p);
        for (int i = 0; i < p; i++) {
            m0.add(Integer.toString(initialMarking.tokens(flatNet.places().get(i))));
        }
        lines.add("(assert (Reachable " + String.join(" ", m0) + "))");
        lines.add("");

        for (var ft : flatNet.transitions()) {
            lines.add(encodeTransitionRule(flatNet, ft, mVars, mpVars, invariants));
        }
        // Environment-injection rules (VER-006): NOT flat transitions, so the deadlock
        // encoding never sees them; no P-invariant strengthening, injection breaks
        // conservation on purpose.
        for (var inj : envInject) {
            lines.add(encodeInjectionRule(p, inj.pid(), inj.bound(), mVars, mpVars));
        }
        lines.add("");

        lines.add(encodeErrorRule(flatNet, property, mVars, sinkPlaces, envInject));
        lines.add("");

        // Under HORN/Spacer this is SAT when an inductive invariant excludes every
        // violating state (PROVEN) and UNSAT when none exists (VIOLATED).
        lines.add("(assert (not Error))");
        lines.add("(check-sat)");
        if (produceProofs) {
            lines.add("(get-proof)");
        }
        lines.add("(get-model)");

        return new SmtEncoding(String.join("\n", lines), p);
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

    private static String quantified(List<String> vars) {
        var parts = new ArrayList<String>(vars.size());
        for (var v : vars) {
            parts.add("(" + v + " Int)");
        }
        return String.join(" ", parts);
    }

    private static boolean contains(int[] arr, int v) {
        for (int x : arr) {
            if (x == v) {
                return true;
            }
        }
        return false;
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
            List<PInvariant> invariants
    ) {
        var all = new ArrayList<>(mVars);
        all.addAll(mpVars);
        var conditions = new ArrayList<String>();
        conditions.add("(Reachable " + String.join(" ", mVars) + ")");
        conditions.addAll(firingConditions(flatNet, ft, mVars, mpVars));
        conditions.addAll(invariantConditions(invariants, mpVars));
        conditions.addAll(envBoundConditions(flatNet, mpVars));
        String body = "(and " + String.join("\n            ", conditions) + ")";
        return "(assert (forall (" + quantified(all) + ")\n  (=> " + body
            + "\n      (Reachable " + String.join(" ", mpVars) + "))))";
    }

    private static String encodeInjectionRule(
            int p, int pid, Integer bound, List<String> mVars, List<String> mpVars
    ) {
        var all = new ArrayList<>(mVars);
        all.addAll(mpVars);
        var conditions = new ArrayList<String>();
        conditions.add("(Reachable " + String.join(" ", mVars) + ")");
        conditions.addAll(injectionConditions(p, pid, bound, mVars, mpVars));
        String body = "(and " + String.join("\n            ", conditions) + ")";
        return "(assert (forall (" + quantified(all) + ")\n  (=> " + body
            + "\n      (Reachable " + String.join(" ", mpVars) + "))))";
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

    /**
     * The net's one-step relation {@code T(M, M')} as one plain SMT-LIB2 formula over
     * the free variables {@code m0..} / {@code m0p..}: the disjunction of every flat
     * transition firing and every env-injection step (VER-006). This is the
     * UNSTRENGTHENED relation the certificate check validates against: it shares the
     * condition emitters with the CHC path but omits the P-invariant conjuncts, so a
     * certificate poisoned by a wrong invariant cannot re-certify itself.
     */
    static String encodeStepRelationSmt2(FlatNet flatNet) {
        int p = flatNet.placeCount();
        List<String> mVars = vars(p, "");
        List<String> mpVars = vars(p, "p");
        var disjuncts = new ArrayList<String>();
        for (var ft : flatNet.transitions()) {
            var conditions = firingConditions(flatNet, ft, mVars, mpVars);
            conditions.addAll(envBoundConditions(flatNet, mpVars));
            disjuncts.add(conjoin(conditions));
        }
        for (var inj : resolveEnvInjection(flatNet)) {
            disjuncts.add(conjoin(injectionConditions(p, inj.pid(), inj.bound(), mVars, mpVars)));
        }
        return switch (disjuncts.size()) {
            case 0 -> "false";
            case 1 -> disjuncts.getFirst();
            default -> "(or " + String.join("\n    ", disjuncts) + ")";
        };
    }

    private static String encodeErrorRule(
            FlatNet flatNet, SmtProperty property, List<String> mVars,
            Collection<Place<?>> sinkPlaces, List<Injection> envInject
    ) {
        String violation = encodePropertyViolation(flatNet, property, mVars, sinkPlaces, envInject);
        return "(assert (forall (" + quantified(mVars) + ")\n  (=> (and (Reachable "
            + String.join(" ", mVars) + ") " + violation + ")\n      Error)))";
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

    /**
     * The property-violation condition {@code Bad(M)} over {@code mVars}. Also used by
     * the certificate check's safety VC, which must test against exactly the violation
     * the error rule encodes.
     */
    static String encodePropertyViolation(
            FlatNet flatNet, SmtProperty property, List<String> mVars,
            Collection<Place<?>> sinkPlaces, List<Injection> envInject
    ) {
        return switch (property) {
            case SmtProperty.DeadlockFree() -> encodeDeadlock(flatNet, mVars, sinkPlaces, envInject);
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
            case SmtProperty.JoinedOrDeadLettered jdl -> {
                // NU-040: a quiescent marking still holding a `pending` token.
                String deadlock = encodeDeadlock(flatNet, mVars, sinkPlaces, envInject);
                int idx = flatNet.indexOf(jdl.pending());
                yield idx < 0 ? "false" : "(and " + deadlock + " (>= " + mVars.get(idx) + " 1))";
            }
        };
    }

    /**
     * Deadlock: every transition is disabled. Environment inputs are treated as
     * injectable (VER-006): an input/read on an injectable env place is NOT a reason
     * the transition is disabled (AlwaysAvailable always satisfies it, Bounded(k) iff
     * the demand is at most k), so a reactive net merely waiting for input is not a
     * deadlock; only a genuinely stuck marking is. Declared sinks (VER-002) each
     * contribute {@code M[sink] = 0}.
     */
    private static String encodeDeadlock(
            FlatNet flatNet, List<String> mVars, Collection<Place<?>> sinkPlaces,
            List<Injection> envInject
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
                return "false";
            }
            disabledConditions.add("(or " + String.join(" ", disableReasons) + ")");
        }
        for (int pid : indexOrdered(flatNet, sinkPlaces)) {
            disabledConditions.add("(= " + mVars.get(pid) + " 0)");
        }
        return disabledConditions.isEmpty()
            ? "true"
            : "(and " + String.join("\n         ", disabledConditions) + ")";
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
