package org.libpetri.analysis;

import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;

import java.util.*;
import org.libpetri.core.internal.TerminalEncoding;

import static org.libpetri.analysis.AnalysisUtils.formatPlaces;
import static org.libpetri.analysis.AnalysisUtils.formatTransitions;

/**
 * Formal analyzer for Time Petri Nets using the State Class Graph method.
 * <p>
 * This implements the correct algorithm from:
 * <ul>
 *   <li>Berthomieu &amp; Diaz (1991): "Modeling and verification of time dependent
 *       systems using Time Petri Nets"</li>
 *   <li>Gardey, Roux &amp; Roux (2006): "State Space Computation and Analysis of
 *       Time Petri Nets"</li>
 * </ul>
 *
 * <h2>Correctness Guarantees</h2>
 * <p>
 * For a bounded Time Petri Net N:
 * <ul>
 *   <li><b>Theorem 1 (Reachability)</b>: A marking M is reachable in N ⟺
 *       there exists a state class (M, D) in the state class graph</li>
 *   <li><b>Theorem 2 (Liveness)</b>: N is live ⟺ every terminal SCC in the
 *       state class graph contains all transitions</li>
 *   <li><b>Theorem 3 (Goal Reachability)</b>: A goal marking is reachable from
 *       every state ⟺ every terminal SCC contains a goal state class</li>
 * </ul>
 *
 * <h2>Analysis Modes</h2>
 * <ul>
 *   <li><b>Classical Liveness (L4)</b>: Every transition can fire from every
 *       reachable marking</li>
 *   <li><b>Goal Liveness</b>: Every reachable marking can reach a goal marking
 *       (e.g., CloseSession place has token)</li>
 * </ul>
 *
 * @see StateClassGraph
 * @see SCCAnalyzer
 */
public final class TimePetriNetAnalyzer {

    private final PetriNet net;
    /** The net as the caller passed it: the L4 check expects its transitions ([VER-004]). */
    private final PetriNet callerNet;
    private final MarkingState initialMarking;
    private final Set<Place<?>> goalPlaces;
    private final int maxClasses;
    private final Set<EnvironmentPlace<?>> environmentPlaces;
    private final EnvironmentAnalysisMode environmentMode;
    /** The in-flight split line of the report ([VER-004]), or {@code null} when nothing was split. */
    private final String inFlightLine;

    private TimePetriNetAnalyzer(
            PetriNet net,
            MarkingState initialMarking,
            Set<Place<?>> goalPlaces,
            int maxClasses,
            Set<EnvironmentPlace<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        // VER-004: a transition whose output another tests non-monotonically fires in two steps,
        // as the executor fires it. Before the terminal rewrite, whose inhibitor counts as such a
        // test.
        this.callerNet = net;
        String line = null;
        switch (InFlight.split(net, Set.of(), Set.of())) {
            case InFlight.Outcome.Atomic _ -> {}
            case InFlight.Outcome.Split(var rewritten, var split) -> {
                net = rewritten;
                line = InFlight.splitNote(split);
            }
            case InFlight.Outcome.Refused(var reason) ->
                line = "WARNING: " + reason + "; the graph fires it in one step, so it can miss runs of the executor.";
        }
        this.inFlightLine = line;
        // EXEC-042: the net's terminal places inhibit every transition, as the runtime stops there.
        // The same instance for a net without terminals.
        this.net = TerminalEncoding.inhibited(net);
        this.initialMarking = initialMarking;
        // In the order given: the report lists them.
        this.goalPlaces = Collections.unmodifiableSet(new LinkedHashSet<>(goalPlaces));
        this.maxClasses = maxClasses;
        this.environmentPlaces = Set.copyOf(environmentPlaces);
        this.environmentMode = environmentMode;
    }

    /**
     * Creates a builder for the analyzer.
     */
    public static Builder forNet(PetriNet net) {
        return new Builder(net);
    }

    /**
     * Performs formal liveness analysis.
     *
     * @return the analysis result with formal guarantees
     */
    public LivenessResult analyze() {
        var report = new StringBuilder();
        report.append("=== TIME PETRI NET FORMAL ANALYSIS ===\n\n");
        report.append("Method: State Class Graph (Berthomieu-Diaz 1991)\n");
        report.append("Net: ").append(net.name()).append("\n");
        report.append("Places: ").append(net.places().size()).append("\n");
        report.append("Transitions: ").append(net.transitions().size()).append("\n");
        report.append("Goal places: ").append(formatPlaces(goalPlaces)).append("\n\n");
        if (inFlightLine != null) {
            report.append(inFlightLine).append("\n\n");
        }

        // Phase 1: Build State Class Graph
        report.append("Phase 1: Building State Class Graph...\n");
        if (!environmentPlaces.isEmpty()) {
            report.append("  Environment places: ").append(environmentPlaces.size()).append("\n");
            report.append("  Environment mode: ").append(environmentMode.getClass().getSimpleName()).append("\n");
        }
        var scg = StateClassGraph.build(net, initialMarking, maxClasses, environmentPlaces, environmentMode);
        report.append("  State classes: ").append(scg.size()).append("\n");
        report.append("  Edges: ").append(scg.edgeCount()).append("\n");
        report.append("  Complete: ").append(scg.isComplete() ? "YES" : "NO (truncated)").append("\n");

        if (!scg.isComplete()) {
            report.append("  WARNING: State class graph truncated at ").append(maxClasses)
                  .append(" classes. Analysis may be incomplete.\n");
        }
        report.append("\n");

        // Phase 2: Identify goal state classes
        report.append("Phase 2: Identifying goal state classes...\n");
        var goalClasses = new HashSet<StateClass>();
        for (var sc : scg.stateClasses()) {
            if (sc.marking().hasTokensInAny(goalPlaces)) {
                goalClasses.add(sc);
            }
        }
        report.append("  Goal state classes: ").append(goalClasses.size()).append("\n\n");

        // Phase 3: Compute SCCs
        report.append("Phase 3: Computing Strongly Connected Components...\n");
        var successorMap = new HashMap<StateClass, Set<StateClass>>();
        for (var sc : scg.stateClasses()) {
            successorMap.put(sc, scg.successors(sc));
        }

        var allSCCs = SCCAnalyzer.computeSCCs(scg.stateClasses(), successorMap);
        var terminalSCCs = SCCAnalyzer.findTerminalSCCs(scg.stateClasses(), successorMap);

        report.append("  Total SCCs: ").append(allSCCs.size()).append("\n");
        report.append("  Terminal SCCs: ").append(terminalSCCs.size()).append("\n\n");

        // Phase 4: Check goal liveness
        report.append("Phase 4: Verifying Goal Liveness...\n");
        report.append("  Property: From every reachable state, a goal state is reachable\n");
        report.append("  Formal: ∀C ∈ SCG: ∃C' reachable from C: C'.marking ∈ Goal\n\n");

        // For goal liveness: every terminal SCC must contain a goal state
        // AND every state class must be able to reach a terminal SCC with a goal
        var terminalSCCsWithGoal = new ArrayList<Set<StateClass>>();
        var terminalSCCsWithoutGoal = new ArrayList<Set<StateClass>>();

        for (var scc : terminalSCCs) {
            boolean hasGoal = false;
            for (var sc : scc) {
                if (goalClasses.contains(sc)) {
                    hasGoal = true;
                    break;
                }
            }
            if (hasGoal) {
                terminalSCCsWithGoal.add(scc);
            } else {
                terminalSCCsWithoutGoal.add(scc);
            }
        }

        report.append("  Terminal SCCs with goal: ").append(terminalSCCsWithGoal.size()).append("\n");
        report.append("  Terminal SCCs without goal: ").append(terminalSCCsWithoutGoal.size()).append("\n");

        // Check if all states can reach a goal
        var canReachGoal = computeBackwardReachability(scg, goalClasses);
        int statesNotReachingGoal = scg.size() - canReachGoal.size();

        report.append("  States that can reach goal: ").append(canReachGoal.size())
              .append("/").append(scg.size()).append("\n\n");

        // Determine liveness
        boolean isGoalLive = terminalSCCsWithoutGoal.isEmpty() && statesNotReachingGoal == 0;

        // Phase 5: Check classical liveness (L4)
        report.append("Phase 5: Verifying Classical Liveness (L4)...\n");
        report.append("  Property: Every transition can fire from every reachable marking\n");
        report.append("  Formal: ∀t ∈ T, ∀M reachable: ∃σ: M [σt⟩\n\n");

        // For L4 liveness: every terminal SCC must contain all transitions. The caller's, in its
        // net's order, which the report lists missing transitions in. A completion step
        // complete:<t> of the in-flight split counts as t firing ([VER-004]).
        var allTransitions = new LinkedHashSet<>(callerNet.transitions());
        var terminalSCCsMissingTransitions = new ArrayList<Set<StateClass>>();

        for (var scc : terminalSCCs) {
            var firedInSCC = new HashSet<String>();
            for (var sc : scc) {
                for (var entry : scg.outgoingTransitions(sc).entrySet()) {
                    if (scc.contains(entry.getValue())) {
                        firedInSCC.add(InFlight.sourceTransition(net, entry.getKey().name()));
                    }
                }
            }
            var missing = new LinkedHashSet<Transition>();
            for (var t : allTransitions) {
                if (!firedInSCC.contains(t.name())) {
                    missing.add(t);
                }
            }
            if (!missing.isEmpty()) {
                terminalSCCsMissingTransitions.add(scc);
                report.append("  Terminal SCC missing transitions: ")
                      .append(formatTransitions(missing)).append("\n");
            }
        }

        boolean isL4Live = terminalSCCsMissingTransitions.isEmpty() && scg.isComplete();

        // Summary
        report.append("\n=== ANALYSIS RESULT ===\n\n");

        if (isGoalLive && scg.isComplete()) {
            report.append("✓ GOAL LIVENESS VERIFIED\n");
            report.append("  From every reachable state class, a goal marking is reachable.\n");
            report.append("  This is a FORMAL PROOF based on state class graph theory.\n\n");
            report.append("  Theorem applied: Berthomieu-Diaz (1991)\n");
            report.append("  - State class graph is finite and complete\n");
            report.append("  - All terminal SCCs contain goal states\n");
            report.append("  - Backward reachability covers all state classes\n");
        } else if (isGoalLive && !scg.isComplete()) {
            report.append("⚠ GOAL LIVENESS LIKELY (incomplete proof)\n");
            report.append("  Analysis suggests goal is reachable from explored states,\n");
            report.append("  but state class graph was truncated.\n");
        } else {
            report.append("✗ GOAL LIVENESS VIOLATION\n");
            if (!terminalSCCsWithoutGoal.isEmpty()) {
                report.append("  ").append(terminalSCCsWithoutGoal.size())
                      .append(" terminal SCC(s) have no goal state.\n");
            }
            if (statesNotReachingGoal > 0) {
                report.append("  ").append(statesNotReachingGoal)
                      .append(" state class(es) cannot reach goal.\n");
            }
        }

        report.append("\n");

        if (isL4Live) {
            report.append("✓ CLASSICAL LIVENESS (L4) VERIFIED\n");
            report.append("  Every transition can fire from every reachable marking.\n");
        } else {
            report.append("✗ CLASSICAL LIVENESS (L4) NOT VERIFIED\n");
            if (!terminalSCCsMissingTransitions.isEmpty()) {
                report.append("  Some terminal SCCs don't contain all transitions.\n");
            }
            if (!scg.isComplete()) {
                report.append("  (State class graph incomplete - cannot prove L4)\n");
            }
        }

        return new LivenessResult(
                scg,
                allSCCs,
                terminalSCCs,
                goalClasses,
                canReachGoal,
                isGoalLive,
                isL4Live,
                scg.isComplete(),
                report.toString()
        );
    }

    /**
     * Computes backward reachability from goal states.
     */
    private Set<StateClass> computeBackwardReachability(StateClassGraph scg, Set<StateClass> goals) {
        var reachable = new HashSet<>(goals);
        var queue = new ArrayDeque<>(goals);

        while (!queue.isEmpty()) {
            var current = queue.poll();
            for (var pred : scg.predecessors(current)) {
                if (reachable.add(pred)) {
                    queue.add(pred);
                }
            }
        }

        return reachable;
    }

    // ==================== XOR Branch Analysis ====================

    /**
     * Analyzes XOR branch coverage for a built state class graph.
     *
     * <p>For each transition with XOR output semantics, identifies which branches
     * are actually reachable in the state class graph. Unreachable branches may
     * indicate dead code paths or modeling errors.
     *
     * <p>A graph from {@link #analyze()} is built on the analyzer's rewrite of the net: a
     * transition split for an in-flight action ([VER-004]) deposits through its completion step
     * {@code complete:<name>}, and the terminal rewrite ([EXEC-042]) rebuilds every transition.
     * A completion step's branches are reported under the transition it completes, and
     * {@link XorBranchAnalysis#branchInfo} finds a transition by name, so the caller's own
     * transition finds its entry.
     *
     * @param scg the state class graph to analyze
     * @return XOR branch analysis result
     */
    public static XorBranchAnalysis analyzeXorBranches(StateClassGraph scg) {
        // In the net's order, which the report follows.
        var result = new LinkedHashMap<Transition, XorBranchInfo>();
        var byName = new HashMap<String, Transition>();
        for (var t : scg.net().transitions()) {
            byName.put(t.name(), t);
        }

        for (var transition : scg.net().transitions()) {
            // The graph's virtual transitions: each XOR branch, and a timeout that deposits
            // differently (BranchOutcomes.outcomes).
            var allBranches = BranchOutcomes.outcomes(transition).stream()
                .map(BranchOutcomes.Outcome::places)
                .toList();
            if (allBranches.size() <= 1) {
                // Not a XOR transition (single branch or AND-only)
                continue;
            }

            // Find which branches are taken across all state classes
            var takenBranches = new HashSet<Integer>();
            for (var sc : scg.stateClasses()) {
                var edges = scg.branchEdges(sc, transition);
                for (var edge : edges) {
                    takenBranches.add(edge.branchIndex());
                }
            }

            // Identify untaken branches
            var untakenBranches = new HashSet<Integer>();
            for (int i = 0; i < allBranches.size(); i++) {
                if (!takenBranches.contains(i)) {
                    untakenBranches.add(i);
                }
            }

            // [VER-004]: complete:<t> deposits t's outputs, so its branches are t's.
            var completed = InFlight.completedTransition(transition);
            var owner = completed != null && byName.containsKey(completed) ? byName.get(completed) : transition;
            result.put(owner, new XorBranchInfo(
                    allBranches.size(),
                    takenBranches,
                    untakenBranches,
                    allBranches
            ));
        }

        return new XorBranchAnalysis(result);
    }

    /**
     * Information about XOR branch coverage for a single transition.
     */
    public record XorBranchInfo(
            int totalBranches,
            Set<Integer> takenBranches,
            Set<Integer> untakenBranches,
            List<Set<Place<?>>> branchOutputs
    ) {
        /**
         * Returns true if all XOR branches are reachable.
         */
        public boolean isComplete() {
            return untakenBranches.isEmpty();
        }

        /**
         * Returns the places for a specific branch.
         */
        public Set<Place<?>> branchPlaces(int branchIndex) {
            return branchOutputs.get(branchIndex);
        }
    }

    /**
     * Result of XOR branch analysis.
     */
    public record XorBranchAnalysis(
            Map<Transition, XorBranchInfo> transitionBranches
    ) {
        /**
         * Returns transitions where some XOR branches are never taken.
         */
        public Map<Transition, Set<Integer>> unreachableBranches() {
            var result = new LinkedHashMap<Transition, Set<Integer>>();
            for (var entry : transitionBranches.entrySet()) {
                if (!entry.getValue().untakenBranches().isEmpty()) {
                    result.put(entry.getKey(), entry.getValue().untakenBranches());
                }
            }
            return result;
        }

        /**
         * Returns true if all XOR branches of all transitions are reachable.
         */
        public boolean isXorComplete() {
            return unreachableBranches().isEmpty();
        }

        /**
         * Returns transitions that have XOR outputs.
         */
        public Set<Transition> xorTransitions() {
            return transitionBranches.keySet();
        }

        /**
         * Returns branch info for a specific transition, or empty if not a XOR transition.
         * Found by name when {@code t} is not the graph's own instance, as for a transition of
         * the net passed to {@link TimePetriNetAnalyzer#forNet}, whose graph is built on a
         * rewrite of it.
         */
        public Optional<XorBranchInfo> branchInfo(Transition t) {
            var info = transitionBranches.get(t);
            if (info != null) {
                return Optional.of(info);
            }
            for (var entry : transitionBranches.entrySet()) {
                if (entry.getKey().name().equals(t.name())) {
                    return Optional.of(entry.getValue());
                }
            }
            return Optional.empty();
        }

        /**
         * Generates a human-readable report of XOR branch coverage.
         */
        public String report() {
            if (transitionBranches.isEmpty()) {
                return "No XOR transitions in net.";
            }

            var sb = new StringBuilder();
            sb.append("XOR Branch Coverage Analysis\n");
            sb.append("============================\n\n");

            for (var entry : transitionBranches.entrySet()) {
                var t = entry.getKey();
                var info = entry.getValue();

                sb.append("Transition: ").append(t.name()).append("\n");
                sb.append("  Branches: ").append(info.totalBranches()).append("\n");
                sb.append("  Taken: ").append(info.takenBranches()).append("\n");

                if (!info.untakenBranches().isEmpty()) {
                    sb.append("  UNREACHABLE: ").append(info.untakenBranches()).append("\n");
                    for (var idx : info.untakenBranches()) {
                        sb.append("    Branch ").append(idx).append(" outputs: ")
                          .append(formatPlaces(info.branchPlaces(idx))).append("\n");
                    }
                } else {
                    sb.append("  All branches reachable\n");
                }
                sb.append("\n");
            }

            if (isXorComplete()) {
                sb.append("RESULT: All XOR branches are reachable.\n");
            } else {
                sb.append("RESULT: Some XOR branches are unreachable!\n");
            }

            return sb.toString();
        }
    }

    /**
     * Builder for TimePetriNetAnalyzer.
     */
    public static final class Builder {
        private final PetriNet net;
        private MarkingState initialMarking = MarkingState.empty();
        private final Set<Place<?>> goalPlaces = new LinkedHashSet<>();
        private int maxClasses = 100_000;
        private final Set<EnvironmentPlace<?>> environmentPlaces = new HashSet<>();
        private EnvironmentAnalysisMode environmentMode = EnvironmentAnalysisMode.ignore();

        private Builder(PetriNet net) {
            this.net = Objects.requireNonNull(net);
        }

        public Builder initialMarking(MarkingState marking) {
            this.initialMarking = marking;
            return this;
        }

        public Builder initialMarking(java.util.function.Consumer<MarkingState.Builder> configurator) {
            var builder = MarkingState.builder();
            configurator.accept(builder);
            this.initialMarking = builder.build();
            return this;
        }

        public Builder goalPlaces(Place<?>... places) {
            this.goalPlaces.addAll(Arrays.asList(places));
            return this;
        }

        public Builder goalPlaces(Set<Place<?>> places) {
            this.goalPlaces.addAll(places);
            return this;
        }

        public Builder maxClasses(int max) {
            this.maxClasses = max;
            return this;
        }

        /**
         * Declares places as environment places for reactive analysis.
         *
         * <p>Environment places model external inputs to the net. Their enablement
         * semantics are controlled by {@link #environmentMode(EnvironmentAnalysisMode)}.
         *
         * @param places environment places
         * @return this builder
         */
        @SafeVarargs
        public final Builder environmentPlaces(EnvironmentPlace<?>... places) {
            this.environmentPlaces.addAll(Arrays.asList(places));
            return this;
        }

        /**
         * Sets the analysis mode for environment places.
         *
         * <p>Controls how transitions depending on environment places are treated:
         * <ul>
         *   <li>{@link EnvironmentAnalysisMode#alwaysAvailable()}: Assume environment
         *       always provides tokens (useful for liveness under cooperative environment)</li>
         *   <li>{@link EnvironmentAnalysisMode#bounded(int)}: Analyze with bounded
         *       environment tokens (creates finite state space)</li>
         *   <li>{@link EnvironmentAnalysisMode#ignore()}: Standard semantics (default)</li>
         * </ul>
         *
         * @param mode the environment analysis mode
         * @return this builder
         */
        public Builder environmentMode(EnvironmentAnalysisMode mode) {
            this.environmentMode = Objects.requireNonNull(mode);
            return this;
        }

        public TimePetriNetAnalyzer build() {
            if (goalPlaces.isEmpty()) {
                throw new IllegalStateException("At least one goal place must be specified");
            }
            return new TimePetriNetAnalyzer(net, initialMarking, goalPlaces, maxClasses, environmentPlaces, environmentMode);
        }
    }

    /**
     * Result of liveness analysis.
     */
    public record LivenessResult(
            StateClassGraph stateClassGraph,
            List<Set<StateClass>> allSCCs,
            List<Set<StateClass>> terminalSCCs,
            Set<StateClass> goalClasses,
            Set<StateClass> canReachGoal,
            boolean isGoalLive,
            boolean isL4Live,
            boolean isComplete,
            String report
    ) {
        public String summary() {
            return String.format(
                    "StateClasses: %d, SCCs: %d, TerminalSCCs: %d, GoalLive: %s, L4Live: %s, Complete: %s",
                    stateClassGraph.size(),
                    allSCCs.size(),
                    terminalSCCs.size(),
                    isGoalLive ? "YES" : "NO",
                    isL4Live ? "YES" : "NO",
                    isComplete ? "YES" : "NO"
            );
        }
    }
}
