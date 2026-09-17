package org.libpetri.smt.z3;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;
import org.libpetri.smt.ProgrammingError;
import org.libpetri.smt.RestSet;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.encoding.FlatTransition;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The firing-bound phase ([VER-019]). When every firing strictly lowers a weighted token
 * count, every run is short, and a bounded model check to that length decides the property
 * exactly — consume-all and reset clearing, inhibitor and read guards included. A net whose
 * runs are not bounded this way is reported as such and left to the fixpoint query: a bound
 * is both the runtime cap and the width of the claim.
 *
 * <p><b>Ranking.</b> Weights {@code r >= 0} with {@code r·C_t <= −1} for every flat transition
 * {@code t} that can fire. A clearing arc removes at least its weight, so the column
 * {@code C_t = post − pre} bounds its effect from above. {@code r·M} then drops by at least one
 * per firing and never goes below zero, so a run from {@code M0} has at most {@code K = r·M0}
 * firings. One {@code QF_LIA} query minimising {@code r·M0} ({@link #encodeRankingQuery}),
 * re-checked in exact integer arithmetic ({@link #checkRankingExact}). When none exists, Farkas
 * gives {@code y >= 0, y != 0} with {@code C·y >= 0}: firing counts the marking equation lets
 * repeat forever ({@link #encodeRepeatableVectorQuery}), whose support the report names.
 *
 * <p><b>Bounded model check.</b> One {@code QF_LIA} script unrolls {@code d} steps of the exact
 * step relation from {@code M0} — step {@code i} fires the transition its selector {@code s_i}
 * names, or idles, and once idle stays idle — and asks for a violation at the last marking
 * ({@link #encodeBoundedRun}). Idling makes "at most {@code d} firings" one query. {@code sat}
 * is a run, decoded and replayed firing by firing before it is believed ({@link #replayRun});
 * {@code unsat} at {@code d = K} covers every run of the net.
 *
 * <p>Every emitted script is byte-identical to the TypeScript, Rust and Python ports for the
 * same input ([VER-013] AC1): places in flat index order, transitions in net order,
 * {@code (- k)} for a negative literal, a lone term unwrapped. Weights and bounds are
 * {@link BigInteger}, so no reading of a model, a ranking or a bound can wrap: a ranking the
 * re-check passes is a ranking, whatever its magnitude.
 */
public final class BoundedRun {

    private BoundedRun() {}

    /** The phase's wall-clock budget when the caller names none, in milliseconds. */
    public static final long DEFAULT_BUDGET_MS = 60_000;

    /** The deepest bounded run the phase asks for when the caller names no limit. */
    public static final int DEFAULT_MAX_DEPTH = 512;

    /**
     * The largest firing bound the phase model-checks to: JavaScript's
     * {@code Number.MAX_SAFE_INTEGER}, the largest bound the TypeScript port counts depths in
     * exactly. Refusing the same bounds keeps the ports' reasons identical; no depth limit
     * comes near it, so it never turns a decidable bound away in practice.
     */
    static final BigInteger LARGEST_BOUND = BigInteger.ONE.shiftLeft(53).subtract(BigInteger.ONE);

    /** Why the phase steps aside on a net the environment injects into. */
    static final String ENVIRONMENT_INJECTION_REASON = "environment injection has no firing bound";

    /**
     * A ranking and the firing bound it gives: {@code weights·C_t <= −1} on every transition
     * that can fire.
     *
     * @param weights {@code r}, one entry per flat place, all non-negative
     * @param bound   {@code K = r·M0}: no run from {@code M0} has more firings
     */
    public record FiringBound(List<BigInteger> weights, BigInteger bound) {
        public FiringBound {
            weights = List.copyOf(weights);
            Objects.requireNonNull(bound);
        }
    }

    /**
     * Whether {@code ft} can ever fire: it does not inhibit a place it needs. A transition that
     * cannot fire lengthens no run, so the ranking owes it no decrease.
     */
    private static boolean canFire(FlatTransition ft) {
        for (int p : ft.inhibitorPlaces()) {
            if (ft.preVector()[p] > 0 || contains(ft.readPlaces(), p)) {
                return false;
            }
        }
        return true;
    }

    /** The {@code QF_LIA} script asking for the ranking with the least {@code r·M0}. */
    public static String encodeRankingQuery(FlatNet flatNet, int[] initial) {
        int placeCount = flatNet.placeCount();
        var lines = new ArrayList<String>();
        lines.add("; Firing bound (VER-019): weights r >= 0 that every firing lowers by at least one");
        lines.add("; (r.C_t <= -1, a clearing arc counted at its weight); every run from M0 then has");
        lines.add("; at most r.M0 firings. sat with the least r.M0.");
        lines.add("(set-logic QF_LIA)");
        for (int p = 0; p < placeCount; p++) {
            lines.add("(declare-const r" + p + " Int)");
        }
        for (int p = 0; p < placeCount; p++) {
            lines.add("(assert (>= r" + p + " 0))");
        }
        for (var ft : flatNet.transitions()) {
            if (!canFire(ft)) {
                continue;
            }
            var terms = new ArrayList<String>();
            for (int p = 0; p < placeCount; p++) {
                int c = ft.postVector()[p] - ft.preVector()[p];
                if (c != 0) {
                    terms.add(term(c, "r" + p));
                }
            }
            lines.add("(assert (<= " + sum(terms) + " (- 1)))");
        }
        var objective = new ArrayList<String>();
        for (int p = 0; p < placeCount; p++) {
            if (initial[p] != 0) {
                objective.add(term(initial[p], "r" + p));
            }
        }
        lines.add("(minimize " + sum(objective) + ")");
        lines.add("(check-sat)");
        lines.add("(get-model)");
        return String.join("\n", lines);
    }

    /**
     * The ranking in a {@code sat} reply's model, zero where the model is silent; {@code null}
     * when it defines no weight. A negative weight is decoded as it stands: rejecting it is
     * {@link #checkRankingExact}'s job, so the solver's model is never quietly repaired.
     */
    public static List<BigInteger> decodeRanking(String stdout, int placeCount) {
        var weights = new BigInteger[placeCount];
        Arrays.fill(weights, BigInteger.ZERO);
        boolean seen = false;
        for (var def : SmtText.extractDefineFuns(stdout)) {
            var m = INT_DEFINITION.matcher(def.strip());
            if (!m.matches()) {
                continue;
            }
            int p = indexed(m.group(1), 'r', placeCount);
            if (p < 0) {
                continue;
            }
            weights[p] = literal(m);
            seen = true;
        }
        return seen ? Arrays.asList(weights) : null;
    }

    /**
     * Re-checks a ranking in exact integer arithmetic: {@code r >= 0} and {@code r·C_t <= −1} on
     * every flat transition that can fire. Returns the firing bound, or {@code null} when a
     * check fails — the phase then steps aside rather than bound runs by the solver's word.
     */
    public static FiringBound checkRankingExact(FlatNet flatNet, int[] initial, List<BigInteger> weights) {
        int placeCount = flatNet.placeCount();
        if (weights.size() != placeCount || weights.stream().anyMatch(w -> w.signum() < 0)) {
            return null;
        }
        for (var ft : flatNet.transitions()) {
            if (!canFire(ft)) {
                continue;
            }
            BigInteger delta = BigInteger.ZERO;
            for (int p = 0; p < placeCount; p++) {
                delta = delta.add(weights.get(p).multiply(
                    BigInteger.valueOf((long) ft.postVector()[p] - ft.preVector()[p])));
            }
            if (delta.compareTo(BigInteger.ONE.negate()) > 0) {
                return null;
            }
        }
        BigInteger bound = BigInteger.ZERO;
        for (int p = 0; p < placeCount; p++) {
            bound = bound.add(weights.get(p).multiply(BigInteger.valueOf(initial[p])));
        }
        return new FiringBound(weights, bound);
    }

    /**
     * The {@code QF_LIA} script asking for the Farkas alternative of a ranking: firing counts
     * {@code y >= 0}, not all zero, with {@code C·y >= 0} on every place — counts the marking
     * equation lets repeat forever. The fewest firings, so the support the report names is a
     * small one.
     */
    public static String encodeRepeatableVectorQuery(FlatNet flatNet) {
        int placeCount = flatNet.placeCount();
        var live = new ArrayList<Integer>();
        for (int t = 0; t < flatNet.transitionCount(); t++) {
            if (canFire(flatNet.transitions().get(t))) {
                live.add(t);
            }
        }
        var counts = new ArrayList<String>(live.size());
        for (int t : live) {
            counts.add("y" + t);
        }
        var lines = new ArrayList<String>();
        lines.add("; No firing bound (VER-019): firing counts y >= 0, not all zero, with C.y >= 0 on");
        lines.add("; every place, so the marking equation lets them repeat forever.");
        lines.add("(set-logic QF_LIA)");
        for (var y : counts) {
            lines.add("(declare-const " + y + " Int)");
        }
        for (var y : counts) {
            lines.add("(assert (>= " + y + " 0))");
        }
        lines.add("(assert (>= " + sum(counts) + " 1))");
        for (int p = 0; p < placeCount; p++) {
            var terms = new ArrayList<String>();
            for (int t : live) {
                var ft = flatNet.transitions().get(t);
                int c = ft.postVector()[p] - ft.preVector()[p];
                if (c != 0) {
                    terms.add(term(c, "y" + t));
                }
            }
            if (!terms.isEmpty()) {
                lines.add("(assert (>= " + sum(terms) + " 0))");
            }
        }
        lines.add("(minimize " + sum(counts) + ")");
        lines.add("(check-sat)");
        lines.add("(get-model)");
        return String.join("\n", lines);
    }

    /**
     * The transitions a repeatable vector fires, in net order; {@code null} when the model fires
     * none. Only the sign of a count matters, so a count of any magnitude is read exactly.
     */
    public static List<Integer> decodeRepeatableVector(String stdout, int transitionCount) {
        var support = new ArrayList<Integer>();
        for (var def : SmtText.extractDefineFuns(stdout)) {
            var m = INT_DEFINITION.matcher(def.strip());
            if (!m.matches()) {
                continue;
            }
            int t = indexed(m.group(1), 'y', transitionCount);
            if (t >= 0 && literal(m).signum() > 0) {
                support.add(t);
            }
        }
        Collections.sort(support);
        return support.isEmpty() ? null : support;
    }

    /**
     * The bounded model check: {@code depth} steps from {@code initial}, selector
     * {@code s_i ∈ [0, T]} per step ({@code T} idles), the exact guard and update of the
     * selected transition, the environment post-caps, and the property's violation at the last
     * marking, exactly as the HORN error rule encodes it.
     *
     * <p>Step 0 reads {@code M0} as literals rather than variables, so the first step's guards
     * and updates are ground terms the solver simplifies away.
     *
     * @param initial          {@code M0}, one count per flat place ({@link AbstractReplayer#toVector})
     * @param sinkPlaces       places where a token may rest ([VER-002])
     * @param conditionalSinks places where a token may rest while a marker is marked ([VER-014])
     * @param depth            the most firings a run may take
     */
    public static String encodeBoundedRun(
            FlatNet flatNet,
            int[] initial,
            SmtProperty property,
            Collection<Place<?>> sinkPlaces,
            List<RestSet.ConditionalSinks> conditionalSinks,
            int depth
    ) {
        int placeCount = flatNet.placeCount();
        int transitionCount = flatNet.transitionCount();
        // Vacuous as the phase stands: only the bounded environment mode fills
        // `environmentBounds`, and that mode fills `environmentInjection` for the same places,
        // which `runFiringBoundPhase` refuses outright. Kept because it is the encoder's
        // `envBounds(M')` conjunct — parity, and load-bearing the moment that guard is relaxed.
        List<int[]> caps = SmtEncoder.envBounds(flatNet);
        // Each place's touchers, reversed once, here: the `ite` chain below nests from the last
        // toucher inward, and the nesting must not change from one step to the next.
        var nesting = new ArrayList<List<Integer>>(placeCount);
        for (int p = 0; p < placeCount; p++) {
            var touching = new ArrayList<Integer>();
            for (int t = 0; t < transitionCount; t++) {
                var ft = flatNet.transitions().get(t);
                if (clears(ft, p) || ft.postVector()[p] != ft.preVector()[p]) {
                    touching.add(t);
                }
            }
            Collections.reverse(touching);
            nesting.add(touching);
        }
        var lines = new ArrayList<String>();
        lines.add("; Bounded run (VER-019): " + depth + " steps of the exact step relation from M0, idle");
        lines.add("; only at the end; sat = a run to a violating marking.");
        lines.add("(set-logic QF_LIA)");
        for (int i = 0; i < depth; i++) {
            lines.add("(declare-const s" + i + " Int)");
        }
        for (int i = 1; i <= depth; i++) {
            for (int p = 0; p < placeCount; p++) {
                lines.add("(declare-const " + marking(initial, i, p) + " Int)");
            }
        }
        for (int i = 0; i < depth; i++) {
            lines.add("(assert (and (>= s" + i + " 0) (<= s" + i + " " + transitionCount + ")))");
            if (i + 1 < depth) {
                lines.add("(assert (=> (= s" + i + " " + transitionCount + ") (= s" + (i + 1) + " "
                    + transitionCount + ")))");
            }
            for (int t = 0; t < transitionCount; t++) {
                var guard = guardConditions(flatNet.transitions().get(t), initial, i);
                lines.add("(assert (=> (= s" + i + " " + t + ") " + SmtEncoder.conjoin(guard) + "))");
            }
            for (int p = 0; p < placeCount; p++) {
                String current = marking(initial, i, p);
                String value = current;
                for (int t : nesting.get(p)) {
                    var ft = flatNet.transitions().get(t);
                    String next = clears(ft, p)
                        ? String.valueOf(ft.postVector()[p])
                        : shifted(current, ft.postVector()[p] - ft.preVector()[p]);
                    value = "(ite (= s" + i + " " + t + ") " + next + " " + value + ")";
                }
                lines.add("(assert (= " + marking(initial, i + 1, p) + " " + value + "))");
            }
            for (int[] cap : caps) {
                lines.add("(assert (<= " + marking(initial, i + 1, cap[0]) + " " + cap[1] + "))");
            }
        }
        var last = new ArrayList<String>(placeCount);
        for (int p = 0; p < placeCount; p++) {
            last.add(marking(initial, depth, p));
        }
        String bad = SmtEncoder.encodePropertyViolation(
            flatNet, property, last, sinkPlaces, SmtEncoder.resolveEnvInjection(flatNet), conditionalSinks);
        lines.add("(assert " + bad + ")");
        lines.add("(check-sat)");
        lines.add("(get-model)");
        return String.join("\n", lines);
    }

    /**
     * The transitions a {@code sat} bounded run fires, in order, up to the first idle step;
     * {@code null} when the model defines no selector at a positive depth.
     *
     * <p>A selector outside {@code [0, T)} is an idle step, however far outside, and a selector
     * the model is silent on idles too: the run is the prefix the solver committed to.
     */
    public static List<Integer> decodeBoundedRun(String stdout, int transitionCount, int depth) {
        int[] selectors = new int[depth];
        Arrays.fill(selectors, transitionCount);
        boolean seen = depth == 0;
        var limit = BigInteger.valueOf(transitionCount);
        for (var def : SmtText.extractDefineFuns(stdout)) {
            var m = INT_DEFINITION.matcher(def.strip());
            if (!m.matches()) {
                continue;
            }
            int i = indexed(m.group(1), 's', depth);
            if (i < 0) {
                continue;
            }
            BigInteger value = literal(m);
            selectors[i] = value.signum() >= 0 && value.compareTo(limit) < 0 ? value.intValueExact() : transitionCount;
            seen = true;
        }
        if (!seen) {
            return null;
        }
        var firings = new ArrayList<Integer>();
        for (int s : selectors) {
            if (s < 0 || s >= transitionCount) {
                break;
            }
            firings.add(s);
        }
        return firings;
    }

    /**
     * A firing sequence replayed under the exact abstract semantics.
     *
     * @param states the markings, {@code M0} first and the violating one last
     * @param steps  the flat transition names fired between consecutive states
     */
    public record ReplayedRun(List<int[]> states, List<String> steps) {
        public ReplayedRun {
            states = List.copyOf(states);
            steps = List.copyOf(steps);
        }
    }

    /**
     * Replays a firing sequence from {@code initial} under the exact abstract semantics
     * ({@link AbstractReplayer#enabledA} / {@link AbstractReplayer#fireA}) and returns its
     * markings and step names when every firing is enabled, respects the environment post-caps,
     * and the last marking violates the property; {@code null} otherwise.
     *
     * <p>This is what makes a {@code sat} bounded run a counterexample rather than a claim: the
     * run is believed because it replays, not because the solver produced it.
     *
     * @param firings flat transition indices; one the net does not have is a defect in the
     *                caller, and throws {@link IndexOutOfBoundsException}
     * @param isBad   the violation predicate, as {@link AbstractReplayer#violationPredicate} builds it
     */
    public static ReplayedRun replayRun(
            FlatNet flatNet, int[] initial, List<Integer> firings, Predicate<int[]> isBad
    ) {
        List<int[]> caps = SmtEncoder.envBounds(flatNet);
        var states = new ArrayList<int[]>();
        var steps = new ArrayList<String>();
        int[] state = initial.clone();
        states.add(state);
        for (int t : firings) {
            var ft = flatNet.transitions().get(t);
            if (!AbstractReplayer.enabledA(state, ft)) {
                return null;
            }
            state = AbstractReplayer.fireA(state, ft);
            for (int[] cap : caps) {
                if (state[cap[0]] > cap[1]) {
                    return null;
                }
            }
            states.add(state);
            steps.add(ft.name());
        }
        // The predicate gets a copy: the last marking is also the run's last state.
        return isBad.test(state.clone()) ? new ReplayedRun(states, steps) : null;
    }

    /** {@code budget + s + 2*src} — the ranking as the report prints it. */
    public static String formatRanking(FlatNet flatNet, FiringBound bound) {
        var parts = new ArrayList<String>();
        var weights = bound.weights();
        for (int p = 0; p < weights.size(); p++) {
            BigInteger w = weights.get(p);
            if (w.signum() == 0) {
                continue;
            }
            String name = flatNet.places().get(p).name();
            parts.add(w.equals(BigInteger.ONE) ? name : w + "*" + name);
        }
        return parts.isEmpty() ? "0" : String.join(" + ", parts);
    }

    /** What the bounded model check answered at one depth. */
    public enum DepthAnswer {
        /** A run of at most that many firings reaches a violation. */
        SAT("sat"),
        /** None does. */
        UNSAT("unsat");

        private final String label;

        DepthAnswer(String label) {
            this.label = label;
        }

        /** The solver's word: {@code sat} or {@code unsat}. */
        public String label() {
            return label;
        }
    }

    /**
     * One depth of the bounded model check and what it answered.
     *
     * @param depth  the most firings the run could take
     * @param answer what the solver answered
     */
    public record DepthStep(int depth, DepthAnswer answer) {
        public DepthStep {
            Objects.requireNonNull(answer);
        }
    }

    /** Outcome of {@link #runFiringBoundPhase}. */
    public sealed interface FiringBoundOutcome {

        /**
         * {@code unsat} at the firing bound: no run reaches a violation.
         *
         * @param depths every depth asked, in order, the bound last
         */
        record Proven(FiringBound bound, List<DepthStep> depths) implements FiringBoundOutcome {
            public Proven {
                Objects.requireNonNull(bound);
                depths = List.copyOf(depths);
            }
        }

        /**
         * A bounded run reaches a violation, replayed under the exact semantics.
         *
         * @param states the markings of the run, {@code M0} first
         * @param steps  the flat transitions fired, one per consecutive pair of {@code states}
         */
        record Violated(FiringBound bound, List<DepthStep> depths, List<int[]> states, List<String> steps)
                implements FiringBoundOutcome {
            public Violated {
                Objects.requireNonNull(bound);
                depths = List.copyOf(depths);
                states = List.copyOf(states);
                steps = List.copyOf(steps);
            }
        }

        /**
         * No ranking exists.
         *
         * @param repeatable the flat transitions a repeatable firing vector uses, in net order;
         *                   {@code null} when the second query named none
         */
        record Unbounded(List<Integer> repeatable) implements FiringBoundOutcome {
            public Unbounded {
                repeatable = repeatable == null ? null : List.copyOf(repeatable);
            }
        }

        /**
         * The phase stepped aside, and why. Every depth answered before it did is kept.
         *
         * @param reason report-ready
         * @param bound  the firing bound, when the ranking passed its re-check; else {@code null}
         */
        record Inconclusive(String reason, FiringBound bound, List<DepthStep> depths)
                implements FiringBoundOutcome {
            public Inconclusive {
                Objects.requireNonNull(reason);
                depths = List.copyOf(depths);
            }
        }
    }

    /** The solver phase a script belongs to: the {@code LIBPETRI_SMT_DUMP} file name ([VER-013]). */
    public enum Phase {
        /** The ranking query and, when there is none, the repeatable-vector query. */
        RANKING("ranking"),
        /** A bounded run. */
        BMC("bmc");

        private final String label;

        Phase(String label) {
            this.label = label;
        }

        /** The dump name: {@code ranking} or {@code bmc}. */
        public String label() {
            return label;
        }
    }

    /**
     * Runs one script through the solver within {@code timeoutMs} and returns its stdout.
     *
     * <p>Throws when the transport failed or the reply carries no verdict line, with the reason
     * as the message: the phase reports that message as its inconclusive reason. A programming
     * defect ({@link ProgrammingError}) is re-thrown, never reported as a reason.
     */
    @FunctionalInterface
    public interface FiringBoundSolver {
        String run(String script, Phase phase, long timeoutMs) throws Exception;
    }

    /**
     * Options of {@link #runFiringBoundPhase}.
     *
     * @param budgetMs wall-clock budget for the whole phase in milliseconds; each query gets
     *                 what is left
     * @param maxDepth the deepest bounded run the phase asks for; non-negative
     */
    public record Options(long budgetMs, int maxDepth) {
        /** {@link #DEFAULT_BUDGET_MS} and {@link #DEFAULT_MAX_DEPTH}. */
        public static final Options DEFAULT = new Options(DEFAULT_BUDGET_MS, DEFAULT_MAX_DEPTH);

        public Options {
            if (maxDepth < 0) {
                throw new IllegalArgumentException("maxDepth must be non-negative, got " + maxDepth);
            }
        }

        /** The same options with another budget. */
        public Options withBudgetMs(long other) {
            return new Options(other, maxDepth);
        }

        /** The same options with another depth limit. */
        public Options withMaxDepth(int other) {
            return new Options(budgetMs, other);
        }
    }

    /** {@link #runFiringBoundPhase(FlatNet, MarkingState, SmtProperty, Set, List, FiringBoundSolver, Options)} with {@link Options#DEFAULT}. */
    public static FiringBoundOutcome runFiringBoundPhase(
            FlatNet flatNet,
            MarkingState initialMarking,
            SmtProperty property,
            Set<Place<?>> sinkPlaces,
            List<RestSet.ConditionalSinks> conditionalSinks,
            FiringBoundSolver solver
    ) {
        return runFiringBoundPhase(flatNet, initialMarking, property, sinkPlaces, conditionalSinks, solver,
            Options.DEFAULT);
    }

    /**
     * Runs the phase: the ranking query (or, when there is none, the repeatable-vector query),
     * then the bounded model check at depths 8, 16, 32, … up to the firing bound. A violating run
     * is replayed before it is reported; {@code unsat} at the bound is a proof.
     *
     * <p>Takes the same arguments as the state-equation phase ([VER-018]) and builds the
     * violation predicate itself ({@link AbstractReplayer#violationPredicate}), so the two
     * phases cannot be handed inconsistent ones.
     *
     * <p>A net with environment places the analysis injects into is refused before any query:
     * an injection is not a firing, so no weighting bounds the runs it extends. The gate reads
     * every declared injection ({@link FlatNet#environmentInjection()}), resolved or not, as the
     * reference does.
     *
     * @param sinkPlaces       places where a token may rest ([VER-002])
     * @param conditionalSinks places where a token may rest while a marker is marked ([VER-014])
     * @param solver           runs one script; see {@link FiringBoundSolver}
     */
    public static FiringBoundOutcome runFiringBoundPhase(
            FlatNet flatNet,
            MarkingState initialMarking,
            SmtProperty property,
            Set<Place<?>> sinkPlaces,
            List<RestSet.ConditionalSinks> conditionalSinks,
            FiringBoundSolver solver,
            Options options
    ) {
        long budgetMs = options.budgetMs();
        int maxDepth = options.maxDepth();
        var clock = new Deadline(budgetMs);
        int[] initial = AbstractReplayer.toVector(flatNet, initialMarking);
        Predicate<int[]> isBad = AbstractReplayer.violationPredicate(flatNet, property, sinkPlaces, conditionalSinks);
        var depths = new ArrayList<DepthStep>();
        if (!flatNet.environmentInjection().isEmpty()) {
            return new FiringBoundOutcome.Inconclusive(ENVIRONMENT_INJECTION_REASON, null, depths);
        }

        Reply ranking = ask(solver, clock, encodeRankingQuery(flatNet, initial), Phase.RANKING);
        if (ranking.failure() != null) {
            return new FiringBoundOutcome.Inconclusive(ranking.failure(), null, depths);
        }
        String rankingAnswer = SmtText.classifyFirstLine(ranking.stdout());
        if ("unsat".equals(rankingAnswer)) {
            Reply vector = ask(solver, clock, encodeRepeatableVectorQuery(flatNet), Phase.RANKING);
            List<Integer> repeatable = vector.failure() != null || !"sat".equals(SmtText.classifyFirstLine(vector.stdout()))
                ? null
                : decodeRepeatableVector(vector.stdout(), flatNet.transitionCount());
            return new FiringBoundOutcome.Unbounded(repeatable);
        }
        if (!"sat".equals(rankingAnswer)) {
            return new FiringBoundOutcome.Inconclusive("the ranking query answered unknown", null, depths);
        }
        List<BigInteger> weights = decodeRanking(ranking.stdout(), flatNet.placeCount());
        FiringBound bound = weights == null ? null : checkRankingExact(flatNet, initial, weights);
        if (bound == null) {
            return new FiringBoundOutcome.Inconclusive("the ranking failed the exact re-check", null, depths);
        }
        if (bound.bound().compareTo(LARGEST_BOUND) > 0) {
            return new FiringBoundOutcome.Inconclusive(
                "firing bound " + bound.bound() + " is too large", bound, depths);
        }
        long k = bound.bound().longValueExact();
        int depth = (int) Math.min(Math.min(8, k), maxDepth);
        while (true) {
            Reply reply = ask(solver, clock,
                encodeBoundedRun(flatNet, initial, property, sinkPlaces, conditionalSinks, depth), Phase.BMC);
            if (reply.failure() != null) {
                return new FiringBoundOutcome.Inconclusive(reply.failure(), bound, depths);
            }
            // An answered depth is a depth we searched, whichever way it went; only a
            // verdict-less reply is not one.
            String answer = SmtText.classifyFirstLine(reply.stdout());
            if (!"sat".equals(answer) && !"unsat".equals(answer)) {
                return new FiringBoundOutcome.Inconclusive(
                    "the bounded run at depth " + depth + " answered unknown", bound, depths);
            }
            depths.add(new DepthStep(depth, "sat".equals(answer) ? DepthAnswer.SAT : DepthAnswer.UNSAT));
            if ("sat".equals(answer)) {
                List<Integer> firings = decodeBoundedRun(reply.stdout(), flatNet.transitionCount(), depth);
                ReplayedRun replayed = firings == null ? null : replayRun(flatNet, initial, firings, isBad);
                if (replayed == null) {
                    return new FiringBoundOutcome.Inconclusive(
                        "the bounded run did not replay under the exact semantics", bound, depths);
                }
                return new FiringBoundOutcome.Violated(bound, depths, replayed.states(), replayed.steps());
            }
            if (depth >= k) {
                return new FiringBoundOutcome.Proven(bound, depths);
            }
            if (depth >= maxDepth) {
                return new FiringBoundOutcome.Inconclusive(
                    "the firing bound " + k + " exceeds the depth limit " + maxDepth, bound, depths);
            }
            depth = (int) Math.min(Math.min(2L * depth, k), maxDepth);
        }
    }

    /** A solver's stdout, or the reason there is none. Exactly one is non-null. */
    private record Reply(String stdout, String failure) {}

    /**
     * A phase's wall clock: what is left of the budget, in whole milliseconds, rounded down,
     * as TypeScript's {@code Math.floor(deadline - performance.now())}. Shared with
     * {@link StateEquationPhase}, so the two phases cannot disagree about when a budget is spent.
     */
    static final class Deadline {
        private static final long NANOS_PER_MS = 1_000_000;
        private final long start = System.nanoTime();
        private final long budgetMs;
        private final long budgetNanos;

        Deadline(long budgetMs) {
            this.budgetMs = budgetMs;
            // Saturate: a budget past what nanoseconds hold never runs out, and a negative one
            // has run out already.
            this.budgetNanos = budgetMs > Long.MAX_VALUE / NANOS_PER_MS ? Long.MAX_VALUE
                : Math.max(budgetMs, -Long.MAX_VALUE / NANOS_PER_MS / 2) * NANOS_PER_MS;
        }

        long budgetMs() {
            return budgetMs;
        }

        long leftMs() {
            return Math.floorDiv(budgetNanos - (System.nanoTime() - start), NANOS_PER_MS);
        }
    }

    /**
     * One query within what is left of the budget. The budget is checked before the solver
     * runs, so a spent budget sends nothing.
     */
    private static Reply ask(FiringBoundSolver solver, Deadline clock, String script, Phase phase) {
        long left = clock.leftMs();
        if (left <= 0) {
            return new Reply(null, "time budget of " + clock.budgetMs() + " ms exhausted");
        }
        try {
            return new Reply(solver.run(script, phase, left), null);
        } catch (Exception e) {
            ProgrammingError.rethrowIfProgrammingError(e);
            if (e instanceof InterruptedException) {
                Thread.currentThread().interrupt();
            }
            return new Reply(null, e.getMessage() != null ? e.getMessage() : e.toString());
        }
    }

    /** A consume-all input or a reset arc empties the place. */
    private static boolean clears(FlatTransition ft, int p) {
        return ft.consumeAll()[p] || contains(ft.resetPlaces(), p);
    }

    /** The exact guard of {@code ft} at step {@code i}: inputs, then inhibitors, then reads. */
    private static List<String> guardConditions(FlatTransition ft, int[] initial, int i) {
        var out = new ArrayList<String>();
        for (int p = 0; p < ft.preVector().length; p++) {
            if (ft.preVector()[p] > 0) {
                out.add("(>= " + marking(initial, i, p) + " " + ft.preVector()[p] + ")");
            }
        }
        for (int p : ft.inhibitorPlaces()) {
            out.add("(= " + marking(initial, i, p) + " 0)");
        }
        for (int p : ft.readPlaces()) {
            out.add("(>= " + marking(initial, i, p) + " 1)");
        }
        return out;
    }

    /** Place {@code p} after {@code i} steps: {@code M0}'s literal at step 0, else {@code m<i>_<p>}. */
    private static String marking(int[] initial, int i, int p) {
        return i == 0 ? String.valueOf(initial[p]) : "m" + i + "_" + p;
    }

    /** {@code v + delta}, with the literal's sign spelled as the operator. */
    private static String shifted(String v, int delta) {
        if (delta == 0) {
            return v;
        }
        return delta > 0 ? "(+ " + v + " " + delta + ")" : "(- " + v + " " + (-(long) delta) + ")";
    }

    private static boolean contains(int[] values, int value) {
        for (int v : values) {
            if (v == value) {
                return true;
            }
        }
        return false;
    }

    /**
     * {@code (define-fun <name> () Int <lit>)}, {@code <lit>} a natural literal {@code k} or the
     * negation form {@code (- k)}, with whitespace wherever z3 may put it (it breaks the line
     * before the literal). The shape is exactly the one the TypeScript port matches; a
     * {@code Real} definition is not one.
     */
    private static final Pattern INT_DEFINITION = Pattern.compile(
        "^\\(define-fun\\s+(\\S+)\\s+\\(\\)\\s+Int\\s+(\\(-\\s*(\\d+)\\s*\\)|(\\d+))\\s*\\)$",
        Pattern.DOTALL);

    /** The literal a matched {@link #INT_DEFINITION} defines. */
    private static BigInteger literal(Matcher m) {
        return m.group(3) != null ? new BigInteger(m.group(3)).negate() : new BigInteger(m.group(4));
    }

    /**
     * The index {@code name} carries after {@code prefix} — {@code r3} is weight 3 — when the
     * rest is all ASCII digits and the index is below {@code limit}; {@code -1} otherwise.
     */
    private static int indexed(String name, char prefix, int limit) {
        if (name.length() < 2 || name.charAt(0) != prefix) {
            return -1;
        }
        for (int i = 1; i < name.length(); i++) {
            char c = name.charAt(i);
            if (c < '0' || c > '9') {
                return -1;
            }
        }
        return StateEquationQuery.indexBelow(name.substring(1), limit);
    }

    private static String term(int c, String v) {
        if (c == 1) {
            return v;
        }
        if (c == -1) {
            return "(- " + v + ")";
        }
        return c > 0 ? "(* " + c + " " + v + ")" : "(* (- " + (-(long) c) + ") " + v + ")";
    }

    private static String sum(List<String> terms) {
        return switch (terms.size()) {
            case 0 -> "0";
            case 1 -> terms.getFirst();
            default -> "(+ " + String.join(" ", terms) + ")";
        };
    }
}
