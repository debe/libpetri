package org.libpetri.analysis;

import java.util.*;

/**
 * Strongly Connected Component (SCC) analyzer using Tarjan's algorithm.
 * <p>
 * This is used for liveness analysis of Petri Nets. A bounded Petri Net is
 * live if and only if:
 * <ol>
 *   <li>All terminal SCCs contain all transitions, OR</li>
 *   <li>For goal-based liveness: from every SCC, a goal state is reachable</li>
 * </ol>
 *
 * <h2>Algorithm: Tarjan's SCC (1972)</h2>
 * <p>
 * Tarjan's algorithm finds all SCCs in O(V + E) time using a single DFS.
 * Each node is assigned:
 * <ul>
 *   <li>index: order of discovery</li>
 *   <li>lowlink: smallest index reachable from subtree</li>
 * </ul>
 * A node is a root of an SCC when index == lowlink after processing children.
 *
 * <h2>Terminal SCCs</h2>
 * <p>
 * A terminal (or bottom) SCC has no edges to nodes outside the SCC.
 * These represent the "final behaviors" of the system - once entered,
 * the system stays within the SCC forever.
 *
 * @param <T> the node type
 */
public final class SCCAnalyzer<T> {

    private final Set<T> nodes;
    private final Map<T, Set<T>> successors;

    // Tarjan's algorithm state
    private int index;
    private final Map<T, Integer> nodeIndex;
    private final Map<T, Integer> lowlink;
    private final Set<T> onStack;
    private final Deque<T> stack;
    private final List<Set<T>> sccs;

    private SCCAnalyzer(Set<T> nodes, Map<T, Set<T>> successors) {
        this.nodes = nodes;
        this.successors = successors;
        this.index = 0;
        this.nodeIndex = new HashMap<>();
        this.lowlink = new HashMap<>();
        this.onStack = new HashSet<>();
        this.stack = new ArrayDeque<>();
        this.sccs = new ArrayList<>();
    }

    /**
     * Computes all SCCs in the graph.
     *
     * @param nodes all nodes in the graph
     * @param successors function mapping each node to its successors
     * @param <T> node type
     * @return list of SCCs (each SCC is a set of nodes)
     */
    public static <T> List<Set<T>> computeSCCs(Set<T> nodes, Map<T, Set<T>> successors) {
        var analyzer = new SCCAnalyzer<>(nodes, successors);
        return analyzer.compute();
    }

    /**
     * Finds terminal (bottom) SCCs - SCCs with no outgoing edges to other SCCs.
     *
     * @param nodes all nodes
     * @param successors successor function
     * @param <T> node type
     * @return list of terminal SCCs
     */
    public static <T> List<Set<T>> findTerminalSCCs(Set<T> nodes, Map<T, Set<T>> successors) {
        var allSCCs = computeSCCs(nodes, successors);

        // Map each node to its SCC
        Map<T, Set<T>> nodeToSCC = new HashMap<>();
        for (var scc : allSCCs) {
            for (var node : scc) {
                nodeToSCC.put(node, scc);
            }
        }

        // Find terminal SCCs (no edges leaving the SCC)
        var terminal = new ArrayList<Set<T>>();
        for (var scc : allSCCs) {
            boolean isTerminal = true;
            outer:
            for (var node : scc) {
                for (var succ : successors.getOrDefault(node, Set.of())) {
                    if (!scc.contains(succ)) {
                        isTerminal = false;
                        break outer;
                    }
                }
            }
            if (isTerminal) {
                terminal.add(scc);
            }
        }

        return terminal;
    }

    private List<Set<T>> compute() {
        for (var node : nodes) {
            if (!nodeIndex.containsKey(node)) {
                strongConnect(node);
            }
        }
        return sccs;
    }

    private void strongConnect(T v) {
        nodeIndex.put(v, index);
        lowlink.put(v, index);
        index++;
        stack.push(v);
        onStack.add(v);

        for (var w : successors.getOrDefault(v, Set.of())) {
            if (!nodeIndex.containsKey(w)) {
                // Successor not yet visited
                strongConnect(w);
                lowlink.put(v, Math.min(lowlink.get(v), lowlink.get(w)));
            } else if (onStack.contains(w)) {
                // Successor is on stack, hence in current SCC
                lowlink.put(v, Math.min(lowlink.get(v), nodeIndex.get(w)));
            }
        }

        // If v is a root node, pop the stack and generate an SCC
        if (lowlink.get(v).equals(nodeIndex.get(v))) {
            var scc = new HashSet<T>();
            T w;
            do {
                w = stack.pop();
                onStack.remove(w);
                scc.add(w);
            } while (!w.equals(v));
            sccs.add(scc);
        }
    }
}
