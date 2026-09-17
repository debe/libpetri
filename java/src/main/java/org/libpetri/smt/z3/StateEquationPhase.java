package org.libpetri.smt.z3;

import org.libpetri.analysis.MarkingState;
import org.libpetri.core.Place;
import org.libpetri.smt.ProgrammingError;
import org.libpetri.smt.RestSet;
import org.libpetri.smt.SmtProperty;
import org.libpetri.smt.encoding.FlatNet;
import org.libpetri.smt.z3.StateEquationQuery.Candidate;
import org.libpetri.smt.z3.StateEquationQuery.MarkingInequality;
import org.libpetri.smt.z3.StateEquationQuery.Origin;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.OptionalLong;
import java.util.Set;
import java.util.function.Predicate;

/**
 * The refinement loop of the state-equation phase ([VER-018]).
 *
 * <p>One {@code QF_LIA} query asks whether a marking the marking equation admits violates the
 * property ({@link StateEquationQuery#encode}). {@code unsat} proves it. A {@code sat} model is a
 * candidate, and each round settles it one of three ways, cheapest first:
 *
 * <ol>
 *   <li><b>Witness</b> — a real run from {@code M0} within the candidate's firing counts that
 *       reaches a violation ({@link ParikhSearch#searchWithinCounts}). The property is violated,
 *       and the run is the counterexample.</li>
 *   <li><b>Trap</b> — an initially marked trap the candidate leaves empty
 *       ({@link TrapRefinement#refutingTrap}); {@code Σ_{q∈Q} m_q >= 1} is added and the query
 *       asked again.</li>
 *   <li><b>Inductive inequality</b> — {@code a·M <= b}, kept by the exact step relation and
 *       excluding the candidate ({@link InvariantSynthesis#encodeInductiveInequality}), re-checked
 *       in exact integer arithmetic and added. When there is none, the same question is asked
 *       <em>relative to the marking equation</em>
 *       ({@link InvariantSynthesis#encodeRelativeInequality}), which is where the spec's
 *       {@code N·out + q <= N} shape comes from. A relative inequality is not inductive on its
 *       own, so it cannot be re-checked the same way: the certificate check over the equation
 *       and its refinements is what re-proves it.</li>
 * </ol>
 *
 * <p>Every refinement holds in every reachable marking, so an {@code unsat} after refinement is
 * still a proof, and the refinements it used are its certificate. When none of the three settles
 * a candidate, or the refinement budget or the deadline runs out, the phase is inconclusive and
 * the verifier falls through to the fixpoint query exactly as before; the phase can add verdicts,
 * never remove them.
 *
 * <p>Every reason string and {@link #describeCandidate} read exactly as the TypeScript port's,
 * because the verifier prints them in its report and the reports are diffed across ports.
 */
public final class StateEquationPhase {

    private StateEquationPhase() {}

    /** The most refinements the phase adds before it gives up, when the caller names no limit. */
    public static final int DEFAULT_MAX_REFINEMENTS = 32;

    /** The phase's wall-clock budget when the caller names none, in milliseconds. */
    public static final long DEFAULT_BUDGET_MS = 60_000;

    /** The solver phase a script belongs to: the {@code LIBPETRI_SMT_DUMP} file names ([VER-013]). */
    public enum Phase {
        /** The state-equation query, before and after each refinement. */
        STATE_EQUATION("state-equation"),
        /** An inductive- or relative-inequality synthesis query. */
        INVARIANT("invariant");

        private final String label;

        Phase(String label) {
            this.label = label;
        }

        /** The dump name: {@code state-equation} or {@code invariant}. */
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
    public interface StateEquationSolver {
        String run(String script, Phase phase, long timeoutMs) throws Exception;
    }

    /**
     * Options of {@link #runStateEquationPhase}.
     *
     * @param maxRefinements the most refinements the phase adds before it gives up; non-negative
     * @param weightBound    the magnitude bound on a synthesised inequality's weights; empty (the
     *                       default) is {@link InvariantSynthesis#DEFAULT_WEIGHT_BOUND} or the
     *                       tokens {@code M0} holds, whichever is larger
     * @param witnessNodes   the node budget of each witness search
     * @param budgetMs       wall-clock budget for the whole phase in milliseconds; each query gets
     *                       what is left
     */
    public record Options(int maxRefinements, OptionalLong weightBound, int witnessNodes, long budgetMs) {
        /** 32 refinements, the grown weight bound, {@link ParikhSearch#DEFAULT_NODE_BUDGET} nodes, 60 s. */
        public static final Options DEFAULT = new Options(
            DEFAULT_MAX_REFINEMENTS, OptionalLong.empty(), ParikhSearch.DEFAULT_NODE_BUDGET, DEFAULT_BUDGET_MS);

        public Options {
            if (maxRefinements < 0) {
                throw new IllegalArgumentException("maxRefinements must be non-negative, got " + maxRefinements);
            }
            Objects.requireNonNull(weightBound);
        }

        /** The same options with another refinement limit. */
        public Options withMaxRefinements(int other) {
            return new Options(other, weightBound, witnessNodes, budgetMs);
        }

        /** The same options with a fixed weight bound instead of the one grown from {@code M0}. */
        public Options withWeightBound(long other) {
            return new Options(maxRefinements, OptionalLong.of(other), witnessNodes, budgetMs);
        }

        /** The same options with another witness-search node budget. */
        public Options withWitnessNodes(int other) {
            return new Options(maxRefinements, weightBound, other, budgetMs);
        }

        /** The same options with another budget. */
        public Options withBudgetMs(long other) {
            return new Options(maxRefinements, weightBound, witnessNodes, other);
        }
    }

    /**
     * Outcome of {@link #runStateEquationPhase}. Every arm carries the refinements added so far,
     * in the order they were added, and the solver queries sent, both dump phases counted: the
     * report prints them whichever way the phase ended.
     */
    public sealed interface StateEquationOutcome {

        /** The refinements added, in order, however the phase ended. */
        List<MarkingInequality> refinements();

        /** The solver queries sent, however the phase ended. */
        int queries();

        /**
         * The query answered {@code unsat} over the equation and {@code refinements}. The caller
         * runs the certificate check ({@link StateEquationQuery#refinementCertificate}) before
         * reporting it.
         */
        record Proven(List<MarkingInequality> refinements, int queries) implements StateEquationOutcome {
            public Proven {
                refinements = List.copyOf(refinements);
            }
        }

        /**
         * A run within a candidate's firing counts reaches a violation.
         *
         * @param states the markings of the run, {@code M0} first and the violating one last
         * @param steps  the flat transitions fired, one per consecutive pair of {@code states}
         */
        record Violated(List<int[]> states, List<String> steps, List<MarkingInequality> refinements, int queries)
                implements StateEquationOutcome {
            public Violated {
                states = List.copyOf(states);
                steps = List.copyOf(steps);
                refinements = List.copyOf(refinements);
            }
        }

        /**
         * The phase stepped aside, and why.
         *
         * @param reason    report-ready
         * @param candidate the candidate the phase stopped on, or {@code null} when it stopped
         *                  holding none
         */
        record Inconclusive(String reason, List<MarkingInequality> refinements, int queries, Candidate candidate)
                implements StateEquationOutcome {
            public Inconclusive {
                Objects.requireNonNull(reason);
                refinements = List.copyOf(refinements);
            }
        }
    }

    /**
     * {@link #runStateEquationPhase(FlatNet, MarkingState, SmtProperty, Set, List, StateEquationSolver, Options)}
     * with {@link Options#DEFAULT}.
     */
    public static StateEquationOutcome runStateEquationPhase(
            FlatNet flatNet,
            MarkingState initialMarking,
            SmtProperty property,
            Set<Place<?>> sinkPlaces,
            List<RestSet.ConditionalSinks> conditionalSinks,
            StateEquationSolver solver
    ) {
        return runStateEquationPhase(flatNet, initialMarking, property, sinkPlaces, conditionalSinks, solver,
            Options.DEFAULT);
    }

    /**
     * Runs the phase on the flat path. The caller runs the certificate check on a
     * {@link StateEquationOutcome.Proven} before reporting it.
     *
     * <p>Takes the same arguments as the firing-bound phase ([VER-019]) and builds the violation
     * predicate itself ({@link AbstractReplayer#violationPredicate}), so the two phases cannot be
     * handed inconsistent ones. That predicate judges quiescence with relax-env enablement, which
     * is what keeps a witness found on a net the environment injects into a real violation.
     *
     * @param sinkPlaces       places where a token may rest ([VER-002])
     * @param conditionalSinks places where a token may rest while a marker is marked ([VER-014])
     * @param solver           runs one script; see {@link StateEquationSolver}
     */
    public static StateEquationOutcome runStateEquationPhase(
            FlatNet flatNet,
            MarkingState initialMarking,
            SmtProperty property,
            Set<Place<?>> sinkPlaces,
            List<RestSet.ConditionalSinks> conditionalSinks,
            StateEquationSolver solver,
            Options options
    ) {
        var run = new Run(flatNet, initialMarking, property, sinkPlaces, conditionalSinks, solver, options);
        return run.loop();
    }

    /** {@code a=1, b=1 after t0 x1, t2 x1} — a candidate as the report prints it. */
    public static String describeCandidate(FlatNet flatNet, Candidate candidate) {
        var marked = new ArrayList<String>();
        long[] marking = candidate.marking();
        for (int p = 0; p < marking.length; p++) {
            if (marking[p] != 0) {
                marked.add(flatNet.places().get(p).name() + "=" + marking[p]);
            }
        }
        var fired = new ArrayList<String>();
        long[] counts = candidate.counts();
        for (int t = 0; t < counts.length; t++) {
            if (counts[t] != 0) {
                fired.add(flatNet.transitions().get(t).name() + " x" + counts[t]);
            }
        }
        return (marked.isEmpty() ? "{}" : String.join(", ", marked))
            + " after " + (fired.isEmpty() ? "no firing" : String.join(", ", fired));
    }

    /** A solver's stdout, or the reason there is none. Exactly one is non-null. */
    private record Reply(String stdout, String failure) {}

    /**
     * What a synthesis query settled: the inequality it found, none ({@code inequality} and
     * {@code failure} both {@code null} — the solver proved there is none), or why it failed.
     */
    private record Synthesis(MarkingInequality inequality, String failure) {}

    /** A refinement that excludes the candidate, or the reason the phase cannot go on. */
    private record Refinement(MarkingInequality inequality, String failure) {}

    /** One run of the phase: the loop's state, so the three legs read as TypeScript's closures do. */
    private static final class Run {
        private final FlatNet flatNet;
        private final MarkingState initialMarking;
        private final SmtProperty property;
        private final Set<Place<?>> sinkPlaces;
        private final List<RestSet.ConditionalSinks> conditionalSinks;
        private final StateEquationSolver solver;
        private final Options options;
        private final BoundedRun.Deadline clock;
        private final int[] initial;
        private final long weightBound;
        private final Predicate<int[]> isBad;
        private final List<MarkingInequality> refinements = new ArrayList<>();
        private int queries;

        Run(FlatNet flatNet, MarkingState initialMarking, SmtProperty property, Set<Place<?>> sinkPlaces,
                List<RestSet.ConditionalSinks> conditionalSinks, StateEquationSolver solver, Options options) {
            this.flatNet = flatNet;
            this.initialMarking = initialMarking;
            this.property = property;
            this.sinkPlaces = sinkPlaces;
            this.conditionalSinks = conditionalSinks;
            this.solver = solver;
            this.options = options;
            this.clock = new BoundedRun.Deadline(options.budgetMs());
            this.initial = AbstractReplayer.toVector(flatNet, initialMarking);
            // A bound like `N·out + q <= N` weighs a flag by the capacity of the queue it guards,
            // so the default bound grows with the tokens the net starts with.
            long tokens = 0;
            for (int v : initial) {
                tokens += v;
            }
            this.weightBound = options.weightBound().orElse(Math.max(InvariantSynthesis.DEFAULT_WEIGHT_BOUND, tokens));
            this.isBad = AbstractReplayer.violationPredicate(flatNet, property, sinkPlaces, conditionalSinks);
        }

        StateEquationOutcome loop() {
            int placeCount = flatNet.placeCount();
            int transitionCount = flatNet.transitionCount();
            while (true) {
                String query = StateEquationQuery.encode(
                    flatNet, initialMarking, property, sinkPlaces, conditionalSinks, refinements);
                Reply reply = ask(query, Phase.STATE_EQUATION);
                if (reply.failure() != null) {
                    return inconclusive(reply.failure(), null);
                }
                String answer = SmtText.classifyFirstLine(reply.stdout());
                if ("unsat".equals(answer)) {
                    return new StateEquationOutcome.Proven(refinements, queries);
                }
                // A reply with no verdict line reads as unknown, never as a candidate; the
                // verifier's solver refuses such a reply before it gets here.
                if (!"sat".equals(answer)) {
                    return inconclusive("the state-equation query answered unknown", null);
                }
                Candidate candidate = StateEquationQuery.decodeCandidate(reply.stdout(), placeCount, transitionCount);
                if (candidate == null) {
                    return inconclusive("the state-equation model could not be decoded", null);
                }

                // `None` and `Exhausted` both leave the candidate to the refinements: neither is a
                // run, and only a run decides the property this way.
                var witness = ParikhSearch.searchWithinCounts(
                    flatNet, initial, candidate.counts(), isBad, options.witnessNodes());
                if (witness instanceof ParikhSearch.WitnessOutcome.Found found) {
                    return new StateEquationOutcome.Violated(found.states(), found.steps(), refinements, queries);
                }
                if (refinements.size() >= options.maxRefinements()) {
                    return inconclusive(
                        "refinement budget exhausted (" + options.maxRefinements() + " refinements)", candidate);
                }

                Refinement refinement = refine(candidate);
                if (refinement.failure() != null) {
                    return inconclusive(refinement.failure(), candidate);
                }
                refinements.add(refinement.inequality());
            }
        }

        private StateEquationOutcome inconclusive(String reason, Candidate candidate) {
            return new StateEquationOutcome.Inconclusive(reason, refinements, queries, candidate);
        }

        /**
         * One query within what is left of the budget. The budget is checked before the solver
         * runs, so a spent budget sends nothing and counts nothing; a query that goes out is
         * counted whether or not a reply comes back.
         */
        private Reply ask(String script, Phase phase) {
            long left = clock.leftMs();
            if (left <= 0) {
                return new Reply(null, "time budget of " + clock.budgetMs() + " ms exhausted");
            }
            queries++;
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

        /** The inequality a synthesis query found, none when it proved there is none, or why it failed. */
        private Synthesis synthesize(String script) {
            Reply reply = ask(script, Phase.INVARIANT);
            if (reply.failure() != null) {
                return new Synthesis(null, reply.failure());
            }
            String answer = SmtText.classifyFirstLine(reply.stdout());
            if ("sat".equals(answer)) {
                var inequality = InvariantSynthesis.decodeInductiveInequality(reply.stdout(), flatNet.placeCount());
                return inequality != null
                    ? new Synthesis(inequality, null)
                    : new Synthesis(null, "the inductive-inequality model could not be decoded");
            }
            if ("unsat".equals(answer)) {
                return new Synthesis(null, null);
            }
            return new Synthesis(null, "the inductive-inequality query answered unknown");
        }

        /**
         * The refinement that excludes {@code candidate}, cheapest first: a trap, then an
         * inequality inductive on its own, then one inductive only relative to the marking
         * equation. The failure is the reason the phase cannot go on, not a failure of the net.
         */
        private Refinement refine(Candidate candidate) {
            long[] marking = candidate.marking();
            var trap = TrapRefinement.refutingTrap(flatNet, initial, marking);
            if (trap != null) {
                return new Refinement(trap, null);
            }

            // An inequality inductive on its own is cheaper to find and re-checked exactly; one
            // inductive relative to the equation is asked for only when there is none.
            Synthesis inductive = synthesize(
                InvariantSynthesis.encodeInductiveInequality(flatNet, initial, marking, weightBound));
            if (inductive.failure() != null) {
                return new Refinement(null, inductive.failure());
            }
            if (inductive.inequality() != null) {
                if (!InvariantSynthesis.checkInductiveExact(flatNet, initial, inductive.inequality())
                        || StateEquationQuery.holdsAt(inductive.inequality(), marking)) {
                    return new Refinement(null, "an inductive inequality failed the exact re-check");
                }
                return new Refinement(inductive.inequality(), null);
            }

            Synthesis relative = synthesize(
                InvariantSynthesis.encodeRelativeInequality(flatNet, initial, marking, weightBound));
            if (relative.failure() != null) {
                return new Refinement(null, relative.failure());
            }
            if (relative.inequality() == null) {
                return new Refinement(null, "no trap and no inductive inequality with weights within ±"
                    + weightBound + " excludes the candidate");
            }
            // Deliberately not checkInductiveExact: the bound holds only relative to the marking
            // equation, so the exact re-check would reject it. The certificate check re-proves it
            // together with the equation before any verdict rests on it.
            if (StateEquationQuery.holdsAt(relative.inequality(), marking)) {
                return new Refinement(null, "an inductive inequality does not exclude its candidate");
            }
            // decodeInductiveInequality labels every model inductive; the report must tell this
            // one apart.
            return new Refinement(relative.inequality().withOrigin(Origin.RELATIVE), null);
        }
    }
}
