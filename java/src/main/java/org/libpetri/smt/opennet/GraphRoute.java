package org.libpetri.smt.opennet;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.StateClass;
import org.libpetri.analysis.StateClassGraph;
import org.libpetri.core.Place;
import org.libpetri.core.internal.CodePointOrder;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.OptionalInt;
import java.util.Set;

/**
 * The contract decided on the closed net's state-class graph ([VER-022]).
 *
 * <p>The graph is built <b>untimed</b> ([VER-004]): every clock gets the interval of
 * {@code immediate()}, so the graph holds exactly the markings the untimed encoders reason
 * about, and its verdict is the stronger untimed claim even for a subnet with delayed
 * transitions. Like every graph route it is priority-blind and value-blind.
 *
 * <p>When the graph closes, the verdict is exact. Every quiescent class is judged against the
 * contract, and a cycle anywhere in the graph is a run that never comes to rest. When it does
 * not close, what was found is still real. A class with no enabled transition is quiescent
 * whether or not the build got round to expanding it, and a cycle among explored classes is a
 * real cycle. Only the absence of findings needs the graph to have closed.
 */
final class GraphRoute {

    private GraphRoute() {}

    /**
     * What the graph route found.
     *
     * @param violations real violations: the shallowest witness per subject, then termination
     */
    record Outcome(boolean complete, int classCount, List<ContractViolation> violations) {
        Outcome {
            violations = List.copyOf(violations);
        }
    }

    /** Builds the closed net's untimed graph and judges it against {@code contract}. */
    static Outcome decideOnGraph(
            ClosedNet closed, OpenNetContract contract, int maxClasses, List<Place<?>> tracedPlaces
    ) {
        var graph = StateClassGraph.build(
            closed.net(), closed.initialMarking(), maxClasses, Set.of(), EnvironmentAnalysisMode.ignore(),
            StateClassGraph.Options.UNTIMED);
        var explored = Explored.of(graph);
        var rest = QuiescencePredicate.restDeclarationOf(contract, closed);

        // Classes come in BFS order, so the first class to show a subject is a shallowest one.
        var first = new LinkedHashMap<String, Hit>();
        for (int c = 0; c < explored.size(); c++) {
            // In an untimed exploration an enabled transition can always fire, so "nothing
            // enabled" is the graph's own quiescence, and it holds of a class the build never
            // expanded as well.
            if (!explored.classes.get(c).enabledTransitions().isEmpty()) {
                continue;
            }
            for (var finding : QuiescencePredicate.quiescenceFindings(
                    explored.marking(c), contract, closed, rest)) {
                first.putIfAbsent(finding.kind().label() + ":" + finding.subject(), new Hit(finding, c));
            }
        }

        var clauseOrder = new HashMap<String, Integer>();
        for (int i = 0; i < contract.clauses().size(); i++) {
            clauseOrder.put(contract.clauses().get(i).name(), i);
        }
        int strandedRank = contract.clauses().size();
        // Clauses in contract order, then stranded places by name in code-point order, as every
        // implementation lists them.
        var ordered = new ArrayList<>(first.values());
        ordered.sort(Comparator
            .comparingInt((Hit h) -> h.finding instanceof QuiescencePredicate.ClauseFinding cf
                ? clauseOrder.get(cf.clause().name()) : strandedRank)
            .thenComparing(h -> h.finding.subject(), CodePointOrder.COMPARATOR));

        var violations = new ArrayList<ContractViolation>();
        for (var hit : ordered) {
            var path = explored.pathTo(hit.target);
            violations.add(ContractViolation.of(closed, tracedPlaces, new ContractViolation.Witness(
                hit.finding.kind(),
                hit.finding.subject(),
                hit.finding.describe(),
                path.transitions,
                explored.markings(path.classes),
                OptionalInt.empty(),
                true)));
        }

        if (contract.requiresTermination()) {
            var cycle = explored.findCycle();
            if (cycle != null) {
                violations.add(ContractViolation.of(closed, tracedPlaces, cycle));
            }
        }
        return new Outcome(graph.isComplete(), explored.size(), violations);
    }

    /** A finding and the first class, in BFS order, that shows it. */
    private record Hit(QuiescencePredicate.Finding finding, int target) {}

    /** A firing sequence: the classes along it, target last, and the transitions between them. */
    private record Path(List<Integer> classes, List<String> transitions) {}

    /**
     * The explored graph by index, in the order the build discovered its classes.
     *
     * <p>The reference reads the graph in build order: the first class to show a subject is its
     * witness, and the first edge to reach a class is its path. Walking the graph breadth-first
     * the way the build expanded it, each class's edges as
     * {@link StateClassGraph#outgoingBranchEdges} lists them (transitions in their canonical
     * order, [VER-010] AC1, and branch edges in branch order), discovers the classes in
     * {@link StateClassGraph#stateClasses()} order, and the edge that discovered each one is the
     * reference's BFS-tree edge.
     */
    private static final class Explored {
        final List<StateClass> classes = new ArrayList<>();
        /** Per class, its outgoing edges in build order: transition names and target indices. */
        final List<String[]> vias = new ArrayList<>();
        final List<int[]> targets = new ArrayList<>();
        /** Per class, the BFS parent ({@code -1} for the initial class) and the transition from it. */
        int[] parent;
        String[] parentVia;

        static Explored of(StateClassGraph graph) {
            var e = new Explored();
            var index = new HashMap<StateClass, Integer>();
            var parents = new ArrayList<Integer>();
            var parentVias = new ArrayList<String>();
            e.classes.add(graph.initialClass());
            index.put(graph.initialClass(), 0);
            parents.add(-1);
            parentVias.add(null);
            for (int head = 0; head < e.classes.size(); head++) {
                var current = e.classes.get(head);
                var vias = new ArrayList<String>();
                var targets = new ArrayList<Integer>();
                for (var entry : graph.outgoingBranchEdges(current).entrySet()) {
                    String via = entry.getKey().name();
                    for (var edge : entry.getValue()) {
                        Integer at = index.get(edge.target());
                        if (at == null) {
                            at = e.classes.size();
                            e.classes.add(edge.target());
                            index.put(edge.target(), at);
                            parents.add(head);
                            parentVias.add(via);
                        }
                        vias.add(via);
                        targets.add(at);
                    }
                }
                e.vias.add(vias.toArray(new String[0]));
                e.targets.add(targets.stream().mapToInt(Integer::intValue).toArray());
            }
            if (e.classes.size() != graph.size()) {
                throw new IllegalStateException("VER-022: the walk found " + e.classes.size()
                    + " classes of a state-class graph that holds " + graph.size());
            }
            e.parent = parents.stream().mapToInt(Integer::intValue).toArray();
            e.parentVia = parentVias.toArray(new String[0]);
            return e;
        }

        int size() {
            return classes.size();
        }

        MarkingState marking(int c) {
            return classes.get(c).marking();
        }

        List<MarkingState> markings(List<Integer> path) {
            var out = new ArrayList<MarkingState>(path.size());
            for (int c : path) {
                out.add(marking(c));
            }
            return out;
        }

        /** The shortest firing sequence from the initial class to {@code target}. */
        Path pathTo(int target) {
            var path = new ArrayList<Integer>();
            var transitions = new ArrayList<String>();
            for (int c = target; ; c = parent[c]) {
                path.add(c);
                if (parent[c] < 0) {
                    break;
                }
                transitions.add(parentVia[c]);
            }
            Collections.reverse(path);
            Collections.reverse(transitions);
            return new Path(path, transitions);
        }

        /**
         * A reachable cycle as a lasso (the shortest stem to its entry class, then the loop), or
         * {@code null} when the explored graph has none. An iterative depth-first search: a
         * graph deep enough to matter would overflow a recursive one.
         */
        ContractViolation.Witness findCycle() {
            final int unseen = Integer.MIN_VALUE;
            final int finished = -1;
            // A class's position on the stack while it is open, `finished` once it is done.
            int[] position = new int[size()];
            Arrays.fill(position, unseen);
            position[0] = 0;
            // Frames: the class, the next edge to follow, and the transition that entered it.
            var nodes = new ArrayList<Integer>();
            var next = new ArrayList<Integer>();
            var entered = new ArrayList<String>();
            nodes.add(0);
            next.add(0);
            entered.add(null);
            while (!nodes.isEmpty()) {
                int top = nodes.size() - 1;
                int node = nodes.get(top);
                int edge = next.get(top);
                if (edge >= targets.get(node).length) {
                    position[node] = finished;
                    nodes.remove(top);
                    next.remove(top);
                    entered.remove(top);
                    continue;
                }
                next.set(top, edge + 1);
                String via = vias.get(node)[edge];
                int target = targets.get(node)[edge];
                int at = position[target];
                if (at == unseen) {
                    position[target] = nodes.size();
                    nodes.add(target);
                    next.add(0);
                    entered.add(via);
                } else if (at >= 0) {
                    // A back edge: the stack from `target` up to the top, closed by `via`, is a cycle.
                    var stem = pathTo(target);
                    var cycle = new ArrayList<String>(entered.subList(at + 1, nodes.size()));
                    cycle.add(via);
                    var transitions = new ArrayList<String>(stem.transitions);
                    transitions.addAll(cycle);
                    var markings = new ArrayList<MarkingState>(markings(stem.classes));
                    for (int i = at + 1; i < nodes.size(); i++) {
                        markings.add(marking(nodes.get(i)));
                    }
                    markings.add(marking(target));
                    return new ContractViolation.Witness(
                        ContractViolation.Kind.TERMINATION,
                        "termination",
                        "a run can repeat " + String.join(" → ", cycle) + " forever without coming to rest",
                        transitions,
                        markings,
                        OptionalInt.of(stem.transitions.size()),
                        true);
                }
            }
            return null;
        }
    }
}
