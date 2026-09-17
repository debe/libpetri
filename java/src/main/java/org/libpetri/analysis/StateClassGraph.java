package org.libpetri.analysis;

import org.libpetri.core.Arc;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;
import org.libpetri.core.internal.CodePointOrder;
import org.libpetri.core.internal.OutputActionCheck;

import java.util.*;

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
    record VirtualTransition(
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

    /**
     * Options for {@link StateClassGraph#build(PetriNet, MarkingState, int, Set,
     * EnvironmentAnalysisMode, Options)}.
     *
     * @param untimed explore the <b>untimed</b> reachable set: every clock gets the interval
     *                of {@link Timing#immediate()}, {@code [0, ∞)}, whatever its transition
     *                declares, so any enabled transition may fire next and the graph holds
     *                exactly the markings the untimed encoders reason about ([VER-004]). Its
     *                verdicts are then the stronger untimed claim, not the timed one — what a
     *                route standing in for the encoders on a net with timed transitions needs
     *                ([VER-022]). On a net whose transitions are all immediate this changes
     *                nothing.
     */
    public record Options(boolean untimed) {
        /** The timed graph every other {@code build} overload explores. */
        public static final Options TIMED = new Options(false);
        /** The untimed graph: every clock gets the {@code immediate()} interval. */
        public static final Options UNTIMED = new Options(true);
    }

    private static final Timing IMMEDIATE = Timing.immediate();

    /** The timing a clock is given: the transition's own, or {@code immediate()} when exploring untimed. */
    private static Timing clockTiming(Transition t, boolean untimed) {
        return untimed ? IMMEDIATE : t.timing();
    }

    // ==================== Fields ====================

    private final PetriNet net;
    private final StateClass initialClass;
    /** Every class with its edges, in the order the build discovered the classes. */
    private final LinkedHashMap<StateClass, Node> nodes;
    private final Set<StateClass> stateClasses;
    private final boolean complete;
    private final int maxClasses;
    private final Set<Place<?>> environmentPlaces;
    private final EnvironmentAnalysisMode environmentMode;

    private StateClassGraph(
            PetriNet net,
            StateClass initialClass,
            LinkedHashMap<StateClass, Node> nodes,
            boolean complete,
            int maxClasses,
            Set<Place<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        this.net = net;
        this.initialClass = initialClass;
        this.nodes = nodes;
        this.stateClasses = Collections.unmodifiableSequencedSet(nodes.sequencedKeySet());
        this.complete = complete;
        this.maxClasses = maxClasses;
        this.environmentPlaces = environmentPlaces;
        this.environmentMode = environmentMode;
    }

    // ==================== Adjacency ====================

    /**
     * Up to this many elements, a class's edge lists find an element by scanning them; above it,
     * they add an identity index.
     *
     * <p>A class's out-degree is the number of firings it enables, and in-degree is as small in
     * the nets this graph is built for. A scan of a few references costs less than hashing a
     * {@link StateClass}, whose hash reads its whole firing domain, and an exact-size array
     * costs 16 bytes plus 4 per element where a {@link HashSet} costs about 150 bytes before its
     * first element. The index keeps a class with a very large degree linear to build.
     */
    private static final int SCAN_LIMIT = 16;

    private static final Transition[] NO_TRANSITIONS = new Transition[0];
    private static final int[] NO_ENDS = new int[0];
    private static final BranchEdge[] NO_EDGES = new BranchEdge[0];

    /**
     * One class and its edges, every list in the order the build found it, as the reference's
     * {@code Map} and {@code Set} keep it. The order is part of a result: the first class to show
     * a violation is the witness, and the first edge to reach a class is the path to it
     * ([VER-017], [VER-022]), so a hash order here made the counterexample change from one JVM
     * run to the next.
     *
     * <p>Every edge target is the graph's own instance of its class, as in the reference, so the
     * graph holds each class once rather than once per edge that reaches it, and the lists
     * deduplicate by identity.
     */
    private static final class Node {
        final StateClass stateClass;
        /** The transitions with at least one edge, in enabled order. */
        Transition[] keys = NO_TRANSITIONS;
        /** {@code keyEnds[i]}: where the edges of {@code keys[i]} end in {@link #edges}. */
        int[] keyEnds = NO_ENDS;
        int keyCount;
        /** Above {@link #SCAN_LIMIT} keys: each key's position. */
        IdentityHashMap<Transition, Integer> keyIndex;
        /** The edges, grouped by key in key order, each group in branch order. */
        BranchEdge[] edges = NO_EDGES;
        int edgeCount;
        final ClassList successors = new ClassList();
        final ClassList predecessors = new ClassList();

        Node(StateClass stateClass) {
            this.stateClass = stateClass;
        }

        /** Records an edge; a transition's edges arrive together, before the next transition's. */
        void addEdge(Transition transition, int branchIndex, Node target) {
            if (keyCount == 0 || keys[keyCount - 1] != transition) {
                if (keyCount == keys.length) {
                    int capacity = Math.max(keyCount * 2, stateClass.enabledTransitions().size());
                    keys = Arrays.copyOf(keys, capacity);
                    keyEnds = Arrays.copyOf(keyEnds, capacity);
                }
                keys[keyCount++] = transition;
            }
            if (edgeCount == edges.length) {
                edges = Arrays.copyOf(edges, Math.max(edgeCount * 2, stateClass.enabledTransitions().size()));
            }
            edges[edgeCount++] = new BranchEdge(branchIndex, target.stateClass);
            keyEnds[keyCount - 1] = edgeCount;
            successors.add(target.stateClass);
            target.predecessors.add(stateClass);
        }

        /** Trims every array to its length once the build is done, and indexes many keys. */
        void freeze() {
            if (keys.length != keyCount) {
                keys = keyCount == 0 ? NO_TRANSITIONS : Arrays.copyOf(keys, keyCount);
                keyEnds = keyCount == 0 ? NO_ENDS : Arrays.copyOf(keyEnds, keyCount);
            }
            if (edges.length != edgeCount) {
                edges = edgeCount == 0 ? NO_EDGES : Arrays.copyOf(edges, edgeCount);
            }
            if (keyCount > SCAN_LIMIT) {
                keyIndex = new IdentityHashMap<>(keyCount);
                for (int i = 0; i < keyCount; i++) {
                    keyIndex.put(keys[i], i);
                }
            }
            successors.freeze();
            predecessors.freeze();
        }

        int keyPosition(Object transition) {
            if (keyIndex != null) {
                Integer at = keyIndex.get(transition);
                return at == null ? -1 : at;
            }
            for (int i = 0; i < keyCount; i++) {
                if (keys[i] == transition) {
                    return i;
                }
            }
            return -1;
        }

        List<BranchEdge> edgesOf(int key) {
            return new EdgeRange(edges, key == 0 ? 0 : keyEnds[key - 1], keyEnds[key]);
        }
    }

    /**
     * Distinct classes in the order first added: an array, plus an identity index above
     * {@link #SCAN_LIMIT}. Identity is equality here because every class the lists hold is the
     * graph's own instance.
     */
    private static final class ClassList {
        private static final StateClass[] NONE = new StateClass[0];

        StateClass[] items = NONE;
        int size;
        Set<StateClass> index;

        void add(StateClass sc) {
            if (index != null) {
                if (!index.add(sc)) {
                    return;
                }
            } else {
                for (int i = 0; i < size; i++) {
                    if (items[i] == sc) {
                        return;
                    }
                }
                if (size == SCAN_LIMIT) {
                    index = Collections.newSetFromMap(new IdentityHashMap<>());
                    for (int i = 0; i < size; i++) {
                        index.add(items[i]);
                    }
                    index.add(sc);
                }
            }
            if (size == items.length) {
                items = Arrays.copyOf(items, Math.max(4, size * 2));
            }
            items[size++] = sc;
        }

        boolean containsInstance(StateClass sc) {
            if (index != null) {
                return index.contains(sc);
            }
            for (int i = 0; i < size; i++) {
                if (items[i] == sc) {
                    return true;
                }
            }
            return false;
        }

        void freeze() {
            if (items.length != size) {
                items = size == 0 ? NONE : Arrays.copyOf(items, size);
            }
        }
    }

    /** A read-only view of one class's {@link ClassList}; membership by equality, as a set's. */
    private final class ClassSet extends AbstractSet<StateClass> {
        private final ClassList list;

        ClassSet(ClassList list) {
            this.list = list;
        }

        @Override
        public Iterator<StateClass> iterator() {
            return new ArrayIterator<>(list.items, 0, list.size);
        }

        @Override
        public int size() {
            return list.size;
        }

        @Override
        public boolean contains(Object o) {
            if (!(o instanceof StateClass sc)) {
                return false;
            }
            if (list.containsInstance(sc)) {
                return true;
            }
            var node = nodes.get(sc);
            return node != null && node.stateClass != sc && list.containsInstance(node.stateClass);
        }
    }

    /** A read-only view of one class's edges by transition, in key order. */
    private static final class EdgeMap extends AbstractMap<Transition, List<BranchEdge>> {
        private final Node node;

        EdgeMap(Node node) {
            this.node = node;
        }

        @Override
        public Set<Entry<Transition, List<BranchEdge>>> entrySet() {
            return new AbstractSet<>() {
                @Override
                public Iterator<Entry<Transition, List<BranchEdge>>> iterator() {
                    return new Iterator<>() {
                        private int next;

                        @Override
                        public boolean hasNext() {
                            return next < node.keyCount;
                        }

                        @Override
                        public Entry<Transition, List<BranchEdge>> next() {
                            if (next >= node.keyCount) {
                                throw new NoSuchElementException();
                            }
                            int key = next++;
                            return Map.entry(node.keys[key], node.edgesOf(key));
                        }
                    };
                }

                @Override
                public int size() {
                    return node.keyCount;
                }
            };
        }

        @Override
        public int size() {
            return node.keyCount;
        }

        @Override
        public boolean containsKey(Object key) {
            return node.keyPosition(key) >= 0;
        }

        @Override
        public List<BranchEdge> get(Object key) {
            int at = node.keyPosition(key);
            return at < 0 ? null : node.edgesOf(at);
        }
    }

    /** A read-only list over {@code edges[from, to)}. */
    private static final class EdgeRange extends AbstractList<BranchEdge> implements RandomAccess {
        private final BranchEdge[] edges;
        private final int from;
        private final int to;

        EdgeRange(BranchEdge[] edges, int from, int to) {
            this.edges = edges;
            this.from = from;
            this.to = to;
        }

        @Override
        public BranchEdge get(int index) {
            Objects.checkIndex(index, to - from);
            return edges[from + index];
        }

        @Override
        public int size() {
            return to - from;
        }
    }

    private static final class ArrayIterator<T> implements Iterator<T> {
        private final T[] items;
        private final int end;
        private int next;

        ArrayIterator(T[] items, int from, int to) {
            this.items = items;
            this.next = from;
            this.end = to;
        }

        @Override
        public boolean hasNext() {
            return next < end;
        }

        @Override
        public T next() {
            if (next >= end) {
                throw new NoSuchElementException();
            }
            return items[next++];
        }
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
        return build(net, initialMarking, maxClasses, environmentPlaces, environmentMode, Options.TIMED);
    }

    /**
     * Builds the state class graph with {@link Options}, e.g. the untimed exploration.
     *
     * @param net the Time Petri Net
     * @param initialMarking the initial marking
     * @param maxClasses maximum number of state classes (for boundedness check)
     * @param environmentPlaces places that receive tokens from the environment
     * @param environmentMode how to treat environment places in enablement checks
     * @param options how clocks are read; {@link Options#TIMED} is the graph the other
     *                overloads build
     * @return the computed state class graph
     */
    public static StateClassGraph build(
            PetriNet net,
            MarkingState initialMarking,
            int maxClasses,
            Set<EnvironmentPlace<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode,
            Options options
    ) {
        // Extract underlying places from EnvironmentPlace wrappers
        var envPlaces = new HashSet<Place<?>>();
        for (var ep : environmentPlaces) {
            envPlaces.add(ep.place());
        }
        boolean untimed = options.untimed();

        var initialClass = initialStateClass(net, initialMarking, envPlaces, environmentMode, untimed);

        // BFS exploration
        var nodes = new LinkedHashMap<StateClass, Node>();
        var queue = new ArrayDeque<Node>();
        var first = new Node(initialClass);
        nodes.put(initialClass, first);
        queue.add(first);

        boolean complete = true;

        while (!queue.isEmpty()) {
            if (nodes.size() >= maxClasses) {
                complete = false;
                break;
            }

            var node = queue.poll();
            var current = node.stateClass;

            // Pure Berthomieu-Diaz with XOR branch expansion:
            // Each enabled transition is expanded into virtual transitions (one per XOR branch).
            // This maps XOR semantics to standard CPN conflict while keeping the algorithm unchanged.
            for (var transition : current.enabledTransitions()) {
                // Expand transition into virtual transitions (one per XOR branch)
                var virtualTransitions = expandTransition(transition);

                for (var vt : virtualTransitions) {
                    var successor = computeSuccessor(net, current, vt, envPlaces, environmentMode, untimed);

                    // Empty DBM = temporally infeasible firing
                    if (successor == null || successor.isEmpty()) continue;

                    // A class found before keeps its first instance, which the edge then points
                    // at; a new one joins the frontier.
                    var target = nodes.computeIfAbsent(successor, Node::new);
                    if (target.stateClass == successor) {
                        queue.add(target);
                    }
                    node.addEdge(transition, vt.branchIndex(), target);
                }
            }
        }

        for (var node : nodes.values()) {
            node.freeze();
        }
        return new StateClassGraph(net, initialClass, nodes, complete, maxClasses, envPlaces, environmentMode);
    }

    /**
     * Builds the initial state class (enabled set + firing-domain DBM after
     * letting time pass). Shared by the plain SCG and the name-aware ν-partition
     * SCG ({@link NameStateClassGraph}), and so the single point every graph
     * construction passes through.
     *
     * @throws IllegalStateException per [CORE-043] — token production is read from the
     *     {@code Arc.Out} spec, never from the bound action, so a net that could not
     *     produce at run time would otherwise verify green
     */
    static StateClass initialStateClass(
            PetriNet net,
            MarkingState initialMarking,
            Set<Place<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        return initialStateClass(net, initialMarking, environmentPlaces, environmentMode, false);
    }

    /**
     * {@link #initialStateClass(PetriNet, MarkingState, Set, EnvironmentAnalysisMode)} with
     * every clock given the {@code immediate()} interval when {@code untimed}
     * ({@link Options#untimed()}).
     */
    static StateClass initialStateClass(
            PetriNet net,
            MarkingState initialMarking,
            Set<Place<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode,
            boolean untimed
    ) {
        OutputActionCheck.requireOutputProducingActions(net);
        var found = findEnabledTransitions(net, initialMarking, environmentPlaces, environmentMode);
        int[] order = canonicalOrder(found);
        var enabledTransitions = order == null ? found : permute(found, order);
        var clockNames = enabledTransitions.stream().map(Transition::name).toList();
        var lowerBounds = new double[enabledTransitions.size()];
        var upperBounds = new double[enabledTransitions.size()];
        for (int i = 0; i < enabledTransitions.size(); i++) {
            var timing = clockTiming(enabledTransitions.get(i), untimed);
            lowerBounds[i] = timing.earliest().toMillis() / 1000.0;
            upperBounds[i] = timing.latest().toMillis() / 1000.0;
        }
        var baseDBM = DBM.create(clockNames, lowerBounds, upperBounds);
        // Class-relative earliest-ready time of each enabled clock, captured BEFORE
        // letTimePass() zeroes the DBM lower bounds (NU-052 residual-earliest).
        var readyEarliest = new double[enabledTransitions.size()];
        for (int i = 0; i < enabledTransitions.size(); i++) {
            readyEarliest[i] = baseDBM.getLowerBound(i);
        }
        var initialDBM = baseDBM.letTimePass();
        return new StateClass(initialMarking, initialDBM, enabledTransitions, readyEarliest);
    }

    /**
     * The canonical clock order of an enabled set ([VER-010] AC1): ascending by
     * transition name in code-point order ({@link CodePointOrder}), as the other
     * implementations compare, ties keeping their incoming order. Returns the permutation as indices into
     * {@code transitions}, or {@code null} when the list is already in order — the
     * common case, which then costs no allocation.
     */
    static int[] canonicalOrder(List<Transition> transitions) {
        boolean sorted = true;
        for (int i = 1; i < transitions.size(); i++) {
            if (CodePointOrder.compare(transitions.get(i).name(), transitions.get(i - 1).name()) < 0) {
                sorted = false;
                break;
            }
        }
        if (sorted) return null;
        Integer[] order = new Integer[transitions.size()];
        for (int i = 0; i < order.length; i++) order[i] = i;
        // Arrays.sort on objects is stable, so equal names keep their incoming order.
        Arrays.sort(order, (a, b) -> CodePointOrder.compare(transitions.get(a).name(), transitions.get(b).name()));
        int[] out = new int[order.length];
        for (int i = 0; i < out.length; i++) out[i] = order[i];
        return out;
    }

    private static <T> List<T> permute(List<T> items, int[] order) {
        var out = new ArrayList<T>(items.size());
        for (int idx : order) out.add(items.get(idx));
        return out;
    }

    /**
     * Expands a transition into virtual transitions (one per XOR branch).
     * For non-XOR transitions, returns a single-element list.
     *
     * <p>This is the key to supporting XOR semantics while staying compliant
     * with the Berthomieu-Diaz algorithm: each XOR branch becomes a separate
     * virtual transition in structural conflict with other branches.
     */
    static List<VirtualTransition> expandTransition(Transition t) {
        List<Set<Place<?>>> branches;

        if (t.outputSpec() != null) {
            branches = t.outputSpec().enumerateBranches();
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
     * This implements the Berthomieu-Diaz successor formula with its intermediate-marking
     * persistence rule: a transition other than the fired one keeps its clock only when it
     * is enabled in the current marking, in the intermediate marking {@code M - Pre(t_f)}
     * (inputs consumed, resets drained) and in the new marking. Every other transition
     * enabled in the new marking is newly enabled, with a fresh interval ([TIME-012]); the
     * executors restart clocks by the same rule. The output places come from the virtual
     * transition (which may be a specific XOR branch).
     */
    static StateClass computeSuccessor(
            PetriNet net,
            StateClass current,
            VirtualTransition fired,
            Set<Place<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        return computeSuccessor(net, current, fired, environmentPlaces, environmentMode, false);
    }

    /**
     * {@link #computeSuccessor(PetriNet, StateClass, VirtualTransition, Set,
     * EnvironmentAnalysisMode)} with every newly enabled clock given the
     * {@code immediate()} interval when {@code untimed} ({@link Options#untimed()}).
     */
    static StateClass computeSuccessor(
            PetriNet net,
            StateClass current,
            VirtualTransition fired,
            Set<Place<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode,
            boolean untimed
    ) {
        var transition = fired.transition();

        // 1. Compute the intermediate marking (inputs consumed, resets drained) and the new
        // marking, with environment place handling. The VirtualTransition specifies which
        // output places to use (for XOR branches).
        var intermediate = consume(current.marking(), transition, environmentPlaces, environmentMode);
        var newMarking = produce(intermediate, fired.outputPlaces());

        // 2. Determine persistent and newly enabled transitions
        var newEnabledAll = findEnabledTransitions(net, newMarking, environmentPlaces, environmentMode);

        // Persistent (Berthomieu-Diaz intermediate semantics, [TIME-012]): enabled before,
        // enabled in the intermediate marking, and enabled after, excluding the fired
        // transition. A transition the firing's consumption disables is re-enabled by the
        // outputs, so its clock starts over even when they refill the very places it needs;
        // surplus tokens keep it enabled throughout, and its clock persists.
        var persistent = new ArrayList<Transition>();
        var persistentIndices = new ArrayList<Integer>();
        for (int i = 0; i < current.enabledTransitions().size(); i++) {
            var t = current.enabledTransitions().get(i);
            if (t != transition && newEnabledAll.contains(t)
                    && isEnabled(t, intermediate, environmentPlaces, environmentMode)) {
                persistent.add(t);
                persistentIndices.add(i);
            }
        }

        // Newly enabled: everything enabled now that is not persistent. That is a transition
        // disabled before, one disabled by the intermediate marking, or the fired transition
        // re-enabled.
        var newlyEnabled = new ArrayList<Transition>();
        for (var t : newEnabledAll) {
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
            var timing = clockTiming(newlyEnabled.get(i), untimed);
            newLowerBounds[i] = timing.earliest().toMillis() / 1000.0;
            newUpperBounds[i] = timing.latest().toMillis() / 1000.0;
        }

        int[] persistentArray = persistentIndices.stream().mapToInt(Integer::intValue).toArray();
        var firedDBM = current.firingDomain().fireTransition(
                firedIdx,
                newClockNames,
                newLowerBounds,
                newUpperBounds,
                persistentArray
        );

        // 4. Build new enabled list (persistent + newly enabled). Its order matches
        // firedDBM's clock order (persistent-then-newly-enabled), which is
        // path-dependent; put both in canonical order so the class identity is
        // ([VER-010] AC1). The earliest-ready times below are read from the permuted
        // DBM, so index k means the same clock in all three.
        List<Transition> allEnabled = new ArrayList<Transition>();
        allEnabled.addAll(persistent);
        allEnabled.addAll(newlyEnabled);
        int[] order = canonicalOrder(allEnabled);
        if (order != null) {
            allEnabled = permute(allEnabled, order);
            firedDBM = firedDBM.permuted(order);
        }

        // Capture the class-relative earliest-ready time of each clock BEFORE
        // letTimePass() zeroes the DBM lower bounds (NU-052 residual-earliest).
        var readyEarliest = new double[allEnabled.size()];
        for (int i = 0; i < allEnabled.size(); i++) {
            readyEarliest[i] = firedDBM.getLowerBound(i);
        }

        // Let time pass to reach canonical form where transitions can fire
        var newDBM = firedDBM.letTimePass();

        return new StateClass(newMarking, newDBM, allEnabled, readyEarliest);
    }

    /**
     * Finds all structurally enabled transitions for a marking with environment place support.
     */
    static List<Transition> findEnabledTransitions(
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
        // Check inputSpecs (with cardinality)
        for (var in : transition.inputSpecs()) {
            var place = in.place();

            int requiredCount = switch (in) {
                case Arc.In.One _ -> 1;
                case Arc.In.Exactly e -> e.count();
                case Arc.In.All _ -> 1;           // Need at least 1 token (consumes all at runtime)
                case Arc.In.AtLeast a -> a.minimum();
            };

            if (!checkPlaceEnabled(place, requiredCount, marking, environmentPlaces, environmentMode)) {
                return false;
            }
        }

        // Check read arcs
        for (var arc : transition.reads()) {
            var place = arc.place();
            if (!checkPlaceEnabled(place, 1, marking, environmentPlaces, environmentMode)) {
                return false;
            }
        }

        // Check inhibitor arcs
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
     * The first half of a firing: the intermediate marking, {@code marking} with the
     * transition's inputs consumed and its reset places drained, before any output is
     * produced ({@link #produce} is the second half). Persistence is judged against it
     * ([TIME-012]).
     *
     * <p>For environment places in ALWAYS_AVAILABLE or BOUNDED mode, tokens are not
     * actually removed since they are assumed to be provided by the environment.
     *
     * @param marking the current marking
     * @param transition the transition to fire
     * @param environmentPlaces places treated as environment
     * @param environmentMode how to handle environment places
     * @return the intermediate marking
     */
    private static MarkingState consume(
            MarkingState marking,
            Transition transition,
            Set<Place<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        var builder = MarkingState.builder().copyFrom(marking);

        // Consume from inputs with cardinality
        for (var in : transition.inputSpecs()) {
            var place = in.place();

            int toConsume = inputConsumeCount(in, marking.tokens(place));

            consumeFromPlace(builder, place, toConsume, environmentPlaces, environmentMode);
        }

        // Reset places: clear whatever is LEFT after the input loop, not what the
        // pre-firing marking held. Reading the original count overdraws whenever the reset
        // place is also an input — the inputs already took their share — and
        // {@code removeTokens} throws on the overdraw rather than mis-computing, so the
        // whole route died on a net both executors run happily. Setting the count states
        // the reset directly and cannot overdraw; it is also what the flat encoder emits
        // ({@code m'_p = postVector[p]} for a reset place), so the two agree by
        // construction. {@link #produce} adds the outputs afterwards, so a place that is both
        // reset and an output target ends at its post count ([EXEC-013] AC4: consume, then
        // read, then drain).
        for (var arc : transition.resets()) {
            builder.tokens(arc.place(), 0);
        }

        return builder.build();
    }

    /**
     * The second half of a firing: one token into each output place of the branch taken,
     * on top of the intermediate marking {@link #consume} returned.
     *
     * @param intermediate the firing's intermediate marking
     * @param outputPlaces the output places of the branch taken (one XOR branch, or the
     *     whole AND set)
     * @return the new marking after firing
     */
    private static MarkingState produce(MarkingState intermediate, Set<Place<?>> outputPlaces) {
        var builder = MarkingState.builder().copyFrom(intermediate);
        for (var place : outputPlaces) {
            builder.addTokens(place, 1);
        }
        return builder.build();
    }

    /**
     * Tokens removed from an input place by one firing, given how many are there.
     *
     * <p>Delegates to {@link Arc.In#consumptionCount(int)}, the canonical [IO-007]
     * definition the executor also follows — {@code In.All} and {@code In.AtLeast}
     * consume <strong>every</strong> available token, not a minimum. The executor
     * does not call this helper — it inlines the same rule in
     * {@code BitmapNetExecutor.fireTransition}, which computes
     * {@code marking.tokenCount(place)} for both variants — so the two encodings
     * must stay in agreement.
     *
     * <p>This used to be an independent copy that returned the <em>minimum</em>
     * (1 for {@code All}, {@code minimum()} for {@code AtLeast}). That left residual
     * tokens the real net never holds, which kept inhibitor-gated successors
     * suppressed and could report a reachable marking as unreachable — a false
     * {@code Verdict.Proven} on the {@code NuScgVerifier} safety path. Keep this
     * delegating; a second definition of consumption is exactly what caused that bug.
     *
     * <p>Note this is consumption only. Enablement uses {@code requiredCount}
     * semantics ({@code All} => 1, {@code AtLeast} => minimum), which is correct
     * and unchanged.
     *
     * @param in the input spec being fired
     * @param available tokens currently in the input place
     * @return the number of tokens to remove
     */
    private static int inputConsumeCount(Arc.In in, int available) {
        // consumptionCount throws when available < requiredCount. Successors are only
        // computed for transitions isEnabled accepted, so that normally holds — but an
        // environment place in AlwaysAvailable/Bounded mode is "enabled" while its
        // recorded marking is short. Clamp rather than let an analysis pass throw;
        // consumeFromPlace ignores the count for those modes anyway.
        if (available < in.requiredCount()) {
            return available;
        }
        return in.consumptionCount(available);
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

    /**
     * Returns every state class, in the order the breadth-first build discovered them: the
     * initial class first, then by depth.
     *
     * @return a read-only set in discovery order
     */
    public Set<StateClass> stateClasses() {
        return stateClasses;
    }

    public int size() {
        return nodes.size();
    }

    public boolean isComplete() {
        return complete;
    }

    /**
     * Returns the distinct classes one firing leads to from {@code sc}, in the order of the
     * edges that first reach them.
     *
     * @return a read-only set, empty for a class the graph does not hold
     */
    public Set<StateClass> successors(StateClass sc) {
        var node = nodes.get(sc);
        return node == null ? Set.of() : new ClassSet(node.successors);
    }

    /**
     * Returns the distinct classes with an edge to {@code sc}, in the order the build expanded
     * them.
     *
     * @return a read-only set, empty for a class the graph does not hold
     */
    public Set<StateClass> predecessors(StateClass sc) {
        var node = nodes.get(sc);
        return node == null ? Set.of() : new ClassSet(node.predecessors);
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
        var result = new LinkedHashMap<Transition, StateClass>();
        for (var entry : outgoingBranchEdges(sc).entrySet()) {
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
     * @return read-only map of transitions to their branch edges, the transitions in the class's
     *     enabled order and each list in branch order
     */
    public Map<Transition, List<BranchEdge>> outgoingBranchEdges(StateClass sc) {
        var node = nodes.get(sc);
        return node == null ? Map.of() : new EdgeMap(node);
    }

    /**
     * Returns the branch edges for a specific transition from a state class.
     *
     * <p>For non-XOR transitions, returns a single-element list with branchIndex=0.
     * For XOR transitions, returns one edge per taken branch.
     *
     * @param sc the source state class
     * @param transition the transition
     * @return read-only list of branch edges in branch order, empty if transition not enabled
     *     from this class
     */
    public List<BranchEdge> branchEdges(StateClass sc, Transition transition) {
        var node = nodes.get(sc);
        int at = node == null ? -1 : node.keyPosition(transition);
        return at < 0 ? List.of() : node.edgesOf(at);
    }

    /**
     * Returns all transitions that are enabled from a state class, in enabled order.
     */
    public Set<Transition> enabledTransitions(StateClass sc) {
        return outgoingBranchEdges(sc).keySet();
    }

    /**
     * Finds all state classes with a given marking, in discovery order.
     */
    public Set<StateClass> classesWithMarking(MarkingState marking) {
        var result = new LinkedHashSet<StateClass>();
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
     * Gets all reachable markings, in the order their first class was discovered.
     */
    public Set<MarkingState> reachableMarkings() {
        var markings = new LinkedHashSet<MarkingState>();
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
        for (var node : nodes.values()) {
            count += node.edgeCount;
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
        for (var node : nodes.values()) {
            count += node.keyCount;
        }
        return count;
    }

    @Override
    public String toString() {
        return String.format("StateClassGraph[classes=%d, edges=%d, complete=%s]",
                size(), edgeCount(), complete);
    }
}
