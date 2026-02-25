package org.libpetri.analysis;

import org.libpetri.core.Arc;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.In;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;

import java.util.*;
import java.util.stream.Collectors;

/**
 * State Class Graph for Time Petri Net analysis.
 * <p>
 * Implements the Berthomieu-Diaz (1991) algorithm for computing the state class
 * graph of a bounded Time Petri Net. This is a direct implementation of the
 * algorithm from the paper with no modifications or heuristics.
 *
 * <h2>Algorithm (Berthomieu-Diaz 1991)</h2>
 * <pre>
 * 1. Initialize: C₀ = (M₀, D₀) where D₀ has initial intervals for enabled transitions
 * 2. Repeat until no new classes:
 *    For each unexplored class C = (M, D):
 *      For each transition t enabled in M:
 *        Compute successor class C' = succ(C, t)
 *        If D' is non-empty (firing is temporally feasible):
 *          If C' is new, add to graph
 *          Add edge C --t--> C'
 * </pre>
 *
 * <h2>Successor Computation (Theorem 1 from paper)</h2>
 * <pre>
 * succ((M, D), t_f) = (M', D') where:
 *   1. Intersect D with {θ_f ≤ θᵢ for all i}  (t_f fires first)
 *   2. Substitute θᵢ' := θᵢ - θ_f              (shift time origin)
 *   3. Eliminate θ_f                           (Fourier-Motzkin)
 *   4. Add fresh intervals for newly enabled transitions
 *   5. Canonicalize via Floyd-Warshall
 * </pre>
 *
 * <h2>Theorem (Correctness)</h2>
 * <p>
 * For a bounded TPN N with initial marking M₀:
 * <ul>
 *   <li>The state class graph SCG(N, M₀) is finite</li>
 *   <li>M is reachable in N ⟺ ∃ class (M, D) in SCG</li>
 *   <li>Firing sequence σ is feasible in N ⟺ σ labels a path in SCG from C₀</li>
 * </ul>
 *
 * <h2>Reference</h2>
 * Berthomieu, Diaz: "Modeling and verification of time dependent systems
 * using Time Petri Nets", IEEE Transactions on Software Engineering, 1991.
 *
 * @see StateClass
 * @see DBM
 */
public final class StateClassGraph {

    // ==================== Internal Types for XOR Branch Analysis ====================

    /**
     * A virtual transition representing one branch of a XOR output.
     * For analysis-internal use only - the actual Transition object remains unchanged.
     *
     * <p>For non-XOR transitions, there's a single VirtualTransition with branchIndex=0.
     * For XOR transitions, each branch gets its own VirtualTransition.
     *
     * <p>This design maps XOR semantics to standard CPN conflict, keeping the
     * Berthomieu-Diaz algorithm unchanged while supporting formal XOR analysis.
     */
    private record VirtualTransition(
        Transition transition,      // The original transition
        int branchIndex,            // Which XOR branch (0 for non-XOR)
        Set<Place<?>> outputPlaces  // The specific outputs for this branch
    ) {
        String name() {
            return branchIndex == 0 && transition.outputSpec() == null
                ? transition.name()
                : transition.name() + "_branch" + branchIndex;
        }
    }

    /**
     * Edge that tracks which XOR branch was taken.
     * Enables XOR branch reachability analysis.
     */
    public record BranchEdge(int branchIndex, StateClass target) {}

    // ==================== Fields ====================

    private final PetriNet net;
    private final StateClass initialClass;
    private final Set<StateClass> stateClasses;
    private final Map<StateClass, Map<Transition, List<BranchEdge>>> transitions;
    private final Map<StateClass, Set<StateClass>> successors;
    private final Map<StateClass, Set<StateClass>> predecessors;
    private final boolean complete;
    private final int maxClasses;
    private final Set<Place<?>> environmentPlaces;
    private final EnvironmentAnalysisMode environmentMode;

    private StateClassGraph(
            PetriNet net,
            StateClass initialClass,
            Set<StateClass> stateClasses,
            Map<StateClass, Map<Transition, List<BranchEdge>>> transitions,
            boolean complete,
            int maxClasses,
            Set<Place<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        this.net = net;
        this.initialClass = initialClass;
        this.stateClasses = Set.copyOf(stateClasses);
        this.transitions = deepCopyTransitions(transitions);
        this.complete = complete;
        this.maxClasses = maxClasses;
        this.environmentPlaces = environmentPlaces;
        this.environmentMode = environmentMode;

        // Build successor/predecessor maps
        this.successors = new HashMap<>();
        this.predecessors = new HashMap<>();
        for (var sc : stateClasses) {
            successors.put(sc, new HashSet<>());
            predecessors.put(sc, new HashSet<>());
        }
        for (var entry : transitions.entrySet()) {
            var from = entry.getKey();
            for (var branchEdges : entry.getValue().values()) {
                for (var edge : branchEdges) {
                    successors.get(from).add(edge.target());
                    predecessors.get(edge.target()).add(from);
                }
            }
        }
    }

    private static Map<StateClass, Map<Transition, List<BranchEdge>>> deepCopyTransitions(
            Map<StateClass, Map<Transition, List<BranchEdge>>> original
    ) {
        var copy = new HashMap<StateClass, Map<Transition, List<BranchEdge>>>();
        for (var entry : original.entrySet()) {
            var innerCopy = new HashMap<Transition, List<BranchEdge>>();
            for (var inner : entry.getValue().entrySet()) {
                innerCopy.put(inner.getKey(), new ArrayList<>(inner.getValue()));
            }
            copy.put(entry.getKey(), innerCopy);
        }
        return copy;
    }

    /**
     * Builds the state class graph for a Time Petri Net.
     *
     * @param net the Time Petri Net
     * @param initialMarking the initial marking
     * @param maxClasses maximum number of state classes (for boundedness check)
     * @return the computed state class graph
     */
    public static StateClassGraph build(PetriNet net, MarkingState initialMarking, int maxClasses) {
        return build(net, initialMarking, maxClasses, Set.of(), EnvironmentAnalysisMode.ignore());
    }

    /**
     * Builds the state class graph for a Time Petri Net with environment place support.
     *
     * @param net the Time Petri Net
     * @param initialMarking the initial marking
     * @param maxClasses maximum number of state classes (for boundedness check)
     * @param environmentPlaces places that receive tokens from the environment
     * @param environmentMode how to treat environment places in enablement checks
     * @return the computed state class graph
     */
    public static StateClassGraph build(
            PetriNet net,
            MarkingState initialMarking,
            int maxClasses,
            Set<EnvironmentPlace<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        // Extract underlying places from EnvironmentPlace wrappers
        var envPlaces = new HashSet<Place<?>>();
        for (var ep : environmentPlaces) {
            envPlaces.add(ep.place());
        }

        // Compute initially enabled transitions
        var enabledTransitions = findEnabledTransitions(net, initialMarking, envPlaces, environmentMode);

        // Create initial firing domain
        var clockNames = enabledTransitions.stream().map(Transition::name).toList();
        var lowerBounds = new double[enabledTransitions.size()];
        var upperBounds = new double[enabledTransitions.size()];

        for (int i = 0; i < enabledTransitions.size(); i++) {
            var interval = enabledTransitions.get(i).interval();
            lowerBounds[i] = interval.earliest().toMillis() / 1000.0;
            upperBounds[i] = interval.latest().toMillis() / 1000.0;
        }

        var initialDBM = DBM.create(clockNames, lowerBounds, upperBounds);
        // Let time pass so transitions can fire
        initialDBM = initialDBM.letTimePass();
        var initialClass = new StateClass(initialMarking, initialDBM, enabledTransitions);

        // BFS exploration
        var stateClasses = new LinkedHashSet<StateClass>();
        var transitionMap = new HashMap<StateClass, Map<Transition, List<BranchEdge>>>();
        var queue = new ArrayDeque<StateClass>();

        stateClasses.add(initialClass);
        transitionMap.put(initialClass, new HashMap<>());
        queue.add(initialClass);

        boolean complete = true;

        while (!queue.isEmpty()) {
            if (stateClasses.size() >= maxClasses) {
                complete = false;
                break;
            }

            var current = queue.poll();

            // Pure Berthomieu-Diaz with XOR branch expansion:
            // Each enabled transition is expanded into virtual transitions (one per XOR branch).
            // This maps XOR semantics to standard CPN conflict while keeping the algorithm unchanged.
            for (var transition : current.enabledTransitions()) {
                // Expand transition into virtual transitions (one per XOR branch)
                var virtualTransitions = expandTransition(transition);

                for (var vt : virtualTransitions) {
                    var successor = computeSuccessor(net, current, vt, envPlaces, environmentMode);

                    // Empty DBM = temporally infeasible firing
                    if (successor == null || successor.isEmpty()) continue;

                    // Add edge with branch index
                    transitionMap.get(current)
                        .computeIfAbsent(transition, _ -> new ArrayList<>())
                        .add(new BranchEdge(vt.branchIndex(), successor));

                    // If new state class, add to frontier
                    if (stateClasses.add(successor)) {
                        transitionMap.put(successor, new HashMap<>());
                        queue.add(successor);
                    }
                }
            }
        }

        return new StateClassGraph(net, initialClass, stateClasses, transitionMap, complete, maxClasses, envPlaces, environmentMode);
    }

    /**
     * Expands a transition into virtual transitions (one per XOR branch).
     * For non-XOR transitions, returns a single-element list.
     *
     * <p>This is the key to supporting XOR semantics while staying compliant
     * with the Berthomieu-Diaz algorithm: each XOR branch becomes a separate
     * virtual transition in structural conflict with other branches.
     */
    private static List<VirtualTransition> expandTransition(Transition t) {
        List<Set<Place<?>>> branches;

        if (t.outputSpec() != null) {
            branches = t.outputSpec().enumerateBranches();
        } else if (!t.outputs().isEmpty()) {
            // Legacy: single branch with all outputs
            Set<Place<?>> places = t.outputs().stream()
                .map(Arc.Output::place)
                .collect(Collectors.toUnmodifiableSet());
            branches = List.of(places);
        } else {
            // No outputs (sink transition)
            branches = List.of(Set.of());
        }

        var result = new ArrayList<VirtualTransition>();
        for (int i = 0; i < branches.size(); i++) {
            result.add(new VirtualTransition(t, i, branches.get(i)));
        }
        return result;
    }

    /**
     * Computes the successor state class after firing a virtual transition.
     * <p>
     * This implements the Berthomieu-Diaz successor formula correctly,
     * with the extension that the output places come from the virtual transition
     * (which may be a specific XOR branch).
     */
    private static StateClass computeSuccessor(
            PetriNet net,
            StateClass current,
            VirtualTransition fired,
            Set<Place<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        var transition = fired.transition();

        // 1. Compute new marking (with environment place handling)
        // The VirtualTransition specifies which output places to use (for XOR branches)
        var newMarking = fireTransition(current.marking(), transition, fired.outputPlaces(), environmentPlaces, environmentMode);

        // 2. Determine persistent and newly enabled transitions
        var newEnabledAll = findEnabledTransitions(net, newMarking, environmentPlaces, environmentMode);

        // Persistent: enabled before AND after (excluding fired transition)
        var persistent = new ArrayList<Transition>();
        var persistentIndices = new ArrayList<Integer>();
        for (int i = 0; i < current.enabledTransitions().size(); i++) {
            var t = current.enabledTransitions().get(i);
            if (t != transition && newEnabledAll.contains(t)) {
                persistent.add(t);
                persistentIndices.add(i);
            }
        }

        // Newly enabled: enabled now but wasn't before, OR is the fired transition re-enabled
        // Per Berthomieu-Diaz: a transition is "newly enabled" if firing made it enabled
        // (it wasn't enabled before, or it's the same transition that just fired)
        var newlyEnabled = new ArrayList<Transition>();
        for (var t : newEnabledAll) {
            // Newly enabled if: not persistent
            // A transition t is newly enabled iff:
            //   - t was not enabled in the old marking, OR
            //   - t == fired (re-enabled after firing)
            if (!persistent.contains(t)) {
                newlyEnabled.add(t);
            }
        }

        // 3. Compute successor DBM using Berthomieu-Diaz algorithm
        int firedIdx = current.transitionIndex(transition);
        var newClockNames = newlyEnabled.stream().map(Transition::name).toList();
        var newLowerBounds = new double[newlyEnabled.size()];
        var newUpperBounds = new double[newlyEnabled.size()];

        for (int i = 0; i < newlyEnabled.size(); i++) {
            var interval = newlyEnabled.get(i).interval();
            newLowerBounds[i] = interval.earliest().toMillis() / 1000.0;
            newUpperBounds[i] = interval.latest().toMillis() / 1000.0;
        }

        int[] persistentArray = persistentIndices.stream().mapToInt(Integer::intValue).toArray();
        var newDBM = current.firingDomain().fireTransition(
                firedIdx,
                newClockNames,
                newLowerBounds,
                newUpperBounds,
                persistentArray
        );

        // Let time pass to reach canonical form where transitions can fire
        newDBM = newDBM.letTimePass();

        // 4. Build new enabled list (persistent + newly enabled)
        var allEnabled = new ArrayList<Transition>();
        allEnabled.addAll(persistent);
        allEnabled.addAll(newlyEnabled);

        return new StateClass(newMarking, newDBM, allEnabled);
    }

    /**
     * Finds all structurally enabled transitions for a marking.
     */
    private static List<Transition> findEnabledTransitions(PetriNet net, MarkingState marking) {
        return findEnabledTransitions(net, marking, Set.of(), EnvironmentAnalysisMode.ignore());
    }

    /**
     * Finds all structurally enabled transitions for a marking with environment place support.
     */
    private static List<Transition> findEnabledTransitions(
            PetriNet net,
            MarkingState marking,
            Set<Place<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        var enabled = new ArrayList<Transition>();
        for (var transition : net.transitions()) {
            if (isEnabled(transition, marking, environmentPlaces, environmentMode)) {
                enabled.add(transition);
            }
        }
        return enabled;
    }

    /**
     * Checks if a transition is structurally enabled (ignoring time).
     */
    private static boolean isEnabled(Transition transition, MarkingState marking) {
        return isEnabled(transition, marking, Set.of(), EnvironmentAnalysisMode.ignore());
    }

    /**
     * Checks if a transition is structurally enabled with environment place support.
     *
     * <p>Environment places are treated differently based on the analysis mode:
     * <ul>
     *   <li>{@link EnvironmentAnalysisMode.AlwaysAvailable}: Environment places are
     *       assumed to always have sufficient tokens</li>
     *   <li>{@link EnvironmentAnalysisMode.Bounded}: Environment places are checked
     *       up to the bounded token count</li>
     *   <li>{@link EnvironmentAnalysisMode.Ignore}: Standard Petri net semantics</li>
     * </ul>
     *
     * <p>Supports both new inputSpecs (with cardinality) and legacy inputs() for
     * backward compatibility.
     */
    private static boolean isEnabled(
            Transition transition,
            MarkingState marking,
            Set<Place<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        // Track which places have been checked via inputSpecs to avoid duplicate checks
        var checkedPlaces = new HashSet<Place<?>>();

        // ==================== Check inputSpecs (with cardinality) ====================
        for (var in : transition.inputSpecs()) {
            var place = in.place();
            checkedPlaces.add(place);

            int requiredCount = switch (in) {
                case In.One _ -> 1;
                case In.Exactly e -> e.count();
                case In.All _ -> 1;           // Need at least 1 token (consumes all at runtime)
                case In.AtLeast a -> a.minimum();
            };

            if (!checkPlaceEnabled(place, requiredCount, marking, environmentPlaces, environmentMode)) {
                return false;
            }
        }

        // ==================== Check legacy inputs() (backward compatibility) ====================
        for (var place : transition.inputs().keySet()) {
            // Skip if already checked via inputSpecs
            if (checkedPlaces.contains(place)) {
                continue;
            }

            int requiredCount = transition.inputs().get(place).size();
            if (!checkPlaceEnabled(place, requiredCount, marking, environmentPlaces, environmentMode)) {
                return false;
            }
        }

        // ==================== Check read arcs ====================
        for (var arc : transition.reads()) {
            var place = arc.place();
            if (!checkPlaceEnabled(place, 1, marking, environmentPlaces, environmentMode)) {
                return false;
            }
        }

        // ==================== Check inhibitor arcs ====================
        for (var arc : transition.inhibitors()) {
            if (marking.hasTokens(arc.place())) {
                return false;
            }
        }

        return true;
    }

    /**
     * Checks if a place has sufficient tokens for enablement.
     *
     * @param place the place to check
     * @param required required token count
     * @param marking current marking
     * @param environmentPlaces set of environment places
     * @param environmentMode how to handle environment places
     * @return true if place has sufficient tokens (or is an environment place handled by mode)
     */
    private static boolean checkPlaceEnabled(
            Place<?> place,
            int required,
            MarkingState marking,
            Set<Place<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        if (!environmentPlaces.contains(place)) {
            // Regular place - standard check
            return marking.tokens(place) >= required;
        }

        // Environment place - handle based on mode
        return switch (environmentMode) {
            case EnvironmentAnalysisMode.AlwaysAvailable() -> true; // Always sufficient
            case EnvironmentAnalysisMode.Bounded(int maxTokens) -> required <= maxTokens;
            case EnvironmentAnalysisMode.Ignore() -> marking.tokens(place) >= required;
        };
    }

    /**
     * Fires a transition, returning the new marking.
     */
    private static MarkingState fireTransition(MarkingState marking, Transition transition) {
        return fireTransition(marking, transition, Set.of(), EnvironmentAnalysisMode.ignore());
    }

    /**
     * Fires a transition with environment place support, returning the new marking.
     *
     * <p>For environment places in ALWAYS_AVAILABLE or BOUNDED mode, tokens are not
     * actually removed since they are assumed to be provided by the environment.
     */
    private static MarkingState fireTransition(
            MarkingState marking,
            Transition transition,
            Set<Place<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        // Delegate to the overload that uses the transition's own output places
        return fireTransition(marking, transition, null, environmentPlaces, environmentMode);
    }

    /**
     * Fires a transition with specific output places (for XOR branch analysis).
     *
     * <p>This overload allows specifying exactly which output places receive tokens,
     * supporting the virtual transition expansion for XOR branch analysis.
     *
     * @param marking the current marking
     * @param transition the transition to fire
     * @param outputPlaces specific output places to use (null = use transition's outputs)
     * @param environmentPlaces places treated as environment
     * @param environmentMode how to handle environment places
     * @return the new marking after firing
     */
    private static MarkingState fireTransition(
            MarkingState marking,
            Transition transition,
            Set<Place<?>> outputPlaces,
            Set<Place<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        var builder = MarkingState.builder().copyFrom(marking);

        // Track which places have been handled by inputSpecs
        var handledPlaces = new HashSet<Place<?>>();

        // ==================== Consume from inputs ====================
        // NEW: Check inputSpecs first (with cardinality), then legacy inputs

        // New style: inputSpecs with cardinality
        for (var in : transition.inputSpecs()) {
            var place = in.place();
            handledPlaces.add(place);

            int toConsume = switch (in) {
                case In.One _ -> 1;
                case In.Exactly e -> e.count();
                case In.All _ -> 1;       // Analysis: consume minimum (1 token)
                case In.AtLeast a -> a.minimum();
            };

            consumeFromPlace(builder, place, toConsume, environmentPlaces, environmentMode);
        }

        // Legacy style: inputs() multimap (for backward compatibility)
        for (var place : transition.inputs().keySet()) {
            // Skip if already handled by inputSpecs
            if (handledPlaces.contains(place)) {
                continue;
            }

            int count = transition.inputs().get(place).size();
            consumeFromPlace(builder, place, count, environmentPlaces, environmentMode);
        }

        // ==================== Reset places ====================
        // Remove all tokens from reset places
        for (var arc : transition.resets()) {
            int current = marking.tokens(arc.place());
            if (current > 0) {
                builder.removeTokens(arc.place(), current);
            }
        }

        // ==================== Produce to outputs ====================
        if (outputPlaces != null) {
            // Use specific output places (XOR branch)
            for (var place : outputPlaces) {
                builder.addTokens(place, 1);
            }
        } else if (transition.outputSpec() != null) {
            // Use all places from outputSpec (AND semantics for analysis)
            for (var place : transition.outputSpec().allPlaces()) {
                builder.addTokens(place, 1);
            }
        } else {
            // Legacy: use outputs() list
            for (var arc : transition.outputs()) {
                builder.addTokens(arc.place(), 1);
            }
        }

        return builder.build();
    }

    /**
     * Consumes tokens from a place, respecting environment place semantics.
     */
    private static void consumeFromPlace(
            MarkingState.Builder builder,
            Place<?> place,
            int count,
            Set<Place<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        if (!environmentPlaces.contains(place)) {
            // Regular place - always remove tokens
            builder.removeTokens(place, count);
            return;
        }

        // Environment place - only remove in Ignore mode
        if (environmentMode instanceof EnvironmentAnalysisMode.Ignore) {
            builder.removeTokens(place, count);
        }
        // AlwaysAvailable and Bounded modes don't remove tokens from environment
    }

    // ==================== Query Methods ====================

    public PetriNet net() {
        return net;
    }

    public StateClass initialClass() {
        return initialClass;
    }

    public Set<StateClass> stateClasses() {
        return stateClasses;
    }

    public int size() {
        return stateClasses.size();
    }

    public boolean isComplete() {
        return complete;
    }

    public Set<StateClass> successors(StateClass sc) {
        return successors.getOrDefault(sc, Set.of());
    }

    public Set<StateClass> predecessors(StateClass sc) {
        return predecessors.getOrDefault(sc, Set.of());
    }

    /**
     * Returns the outgoing transitions and their successors for a state class.
     *
     * <p>For backward compatibility, returns only the first branch target for
     * each transition. For full XOR branch support, use {@link #branchEdges(StateClass, Transition)}.
     *
     * @deprecated Use {@link #branchEdges(StateClass, Transition)} for XOR-aware analysis
     */
    @Deprecated
    public Map<Transition, StateClass> outgoingTransitions(StateClass sc) {
        var map = transitions.getOrDefault(sc, Map.of());
        var result = new HashMap<Transition, StateClass>();
        for (var entry : map.entrySet()) {
            var edges = entry.getValue();
            if (!edges.isEmpty()) {
                result.put(entry.getKey(), edges.get(0).target());
            }
        }
        return result;
    }

    /**
     * Returns all outgoing transitions with their branch edges.
     *
     * <p>This is the XOR-aware version of {@link #outgoingTransitions(StateClass)}.
     * Each transition maps to a list of branch edges, where each edge represents
     * one possible XOR branch outcome.
     *
     * @param sc the source state class
     * @return map of transitions to their branch edges
     */
    public Map<Transition, List<BranchEdge>> outgoingBranchEdges(StateClass sc) {
        return transitions.getOrDefault(sc, Map.of());
    }

    /**
     * Returns the branch edges for a specific transition from a state class.
     *
     * <p>For non-XOR transitions, returns a single-element list with branchIndex=0.
     * For XOR transitions, returns one edge per taken branch.
     *
     * @param sc the source state class
     * @param transition the transition
     * @return list of branch edges, empty if transition not enabled from this class
     */
    public List<BranchEdge> branchEdges(StateClass sc, Transition transition) {
        var map = transitions.getOrDefault(sc, Map.of());
        return map.getOrDefault(transition, List.of());
    }

    /**
     * Returns all transitions that are enabled from a state class.
     */
    public Set<Transition> enabledTransitions(StateClass sc) {
        return transitions.getOrDefault(sc, Map.of()).keySet();
    }

    /**
     * Finds all state classes with a given marking.
     */
    public Set<StateClass> classesWithMarking(MarkingState marking) {
        var result = new HashSet<StateClass>();
        for (var sc : stateClasses) {
            if (sc.marking().equals(marking)) {
                result.add(sc);
            }
        }
        return result;
    }

    /**
     * Checks if a marking is reachable.
     */
    public boolean isReachable(MarkingState marking) {
        for (var sc : stateClasses) {
            if (sc.marking().equals(marking)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Gets all reachable markings.
     */
    public Set<MarkingState> reachableMarkings() {
        var markings = new HashSet<MarkingState>();
        for (var sc : stateClasses) {
            markings.add(sc.marking());
        }
        return markings;
    }

    /**
     * Counts edges in the graph.
     *
     * <p>With XOR branch support, this counts all branch edges as separate edges.
     * For example, a transition with 2 XOR branches from one state class counts as 2 edges.
     */
    public int edgeCount() {
        int count = 0;
        for (var map : transitions.values()) {
            for (var edges : map.values()) {
                count += edges.size();
            }
        }
        return count;
    }

    /**
     * Counts the number of distinct transition firings in the graph.
     *
     * <p>Unlike {@link #edgeCount()}, this counts a transition with multiple XOR branches
     * as a single firing. Use this for metrics comparable to pre-XOR behavior.
     */
    public int transitionFiringCount() {
        int count = 0;
        for (var map : transitions.values()) {
            count += map.size();
        }
        return count;
    }

    @Override
    public String toString() {
        return String.format("StateClassGraph[classes=%d, edges=%d, complete=%s]",
                size(), edgeCount(), complete);
    }
}
