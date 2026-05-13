package org.libpetri.export;

import org.libpetri.export.graph.GraphEdge;
import org.libpetri.export.graph.GraphNode;
import org.libpetri.export.graph.Subgraph;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Builds nested {@code subgraph cluster_*} blocks for DOT export per
 * {@code spec/11-modular-composition.md} <b>MOD-040</b> and
 * {@code spec/09-export.md} <b>EXP-016</b>.
 *
 * <p>Given a flat list of nodes and edges plus a {@code nodeId -> prefix}
 * map produced during mapping (see {@link PetriNetGraphMapper}), this
 * partitioner:
 *
 * <ol>
 *   <li>Walks every distinct prefix to produce the cluster tree (nested
 *       {@link Subgraph} records).</li>
 *   <li>Routes each node into the deepest cluster whose prefix equals the
 *       node's prefix; nodes without a prefix stay at the top level.</li>
 *   <li>Routes each edge into the deepest cluster that contains <b>both</b>
 *       endpoints; edges crossing cluster boundaries (or with at least one
 *       top-level endpoint) stay at the top level so Graphviz routes them
 *       correctly without truncating cluster boxes.</li>
 *   <li>Applies a default cluster style (rounded, dashed, light fill) when
 *       none is provided — readable defaults are sufficient until task #9
 *       layers the doclet styling on top.</li>
 * </ol>
 *
 * <p>This partitioner is structural-only: it does not consult any
 * {@link org.libpetri.core.SubnetDef} or {@link org.libpetri.core.Instance}
 * — it operates exclusively on the flattened post-composition node names
 * per <b>MOD-023</b>.
 */
final class ClusterBuilder {

    private ClusterBuilder() {}

    /**
     * Result of partitioning nodes/edges into a clustered hierarchy.
     */
    record Partition(
        List<GraphNode> topLevelNodes,
        List<GraphEdge> topLevelEdges,
        List<Subgraph> topLevelSubgraphs
    ) {}

    /**
     * Default cluster styling (per [EXP-016] visual contract — placeholder
     * defaults are sufficient until task #9 wires the {@code subnet-cluster}
     * style category from {@code petri-net-styles.json}).
     *
     * <p>Uses a {@link LinkedHashMap} (rather than {@link Map#of(Object...)
     * Map.of}) to preserve the {@code style → bgcolor → penwidth} insertion
     * order. Cross-language byte-parity with the TypeScript exporter
     * (V8 object literals iterate in insertion order) requires this; see
     * {@code scripts/cross-lang-dot-parity.sh}.
     */
    static final Map<String, String> DEFAULT_CLUSTER_ATTRS;
    static {
        var m = new LinkedHashMap<String, String>();
        m.put("style", "rounded,dashed");
        m.put("bgcolor", "#FAFAFA");
        m.put("penwidth", "1.5");
        DEFAULT_CLUSTER_ATTRS = Collections.unmodifiableMap(m);
    }

    /**
     * Partitions nodes and edges into a cluster hierarchy. Mutates neither
     * input list.
     *
     * @param nodes all nodes (places, transitions, junctions)
     * @param edges all edges
     * @param nodeIdToPrefix per-node instance prefix; absent entries stay
     *                      top-level
     * @return the partitioned cluster hierarchy
     */
    static Partition partition(
            List<GraphNode> nodes,
            List<GraphEdge> edges,
            Map<String, String> nodeIdToPrefix) {

        // Fast path: no prefixes => no clusters. Preserves byte-equal output
        // for flat (non-composed) nets.
        if (nodeIdToPrefix.isEmpty()) {
            return new Partition(
                List.copyOf(nodes),
                List.copyOf(edges),
                List.of());
        }

        // Step 1: walk every prefix to produce the cluster tree shape. We
        // need every internal prefix node, not just leaf prefixes — e.g. a
        // node "outer/inner/leaf" requires both "outer" and "outer/inner" to
        // exist as cluster blocks per [EXP-016] / [MOD-013].
        var prefixOrder = new LinkedHashMap<String, Object>();
        for (var prefix : nodeIdToPrefix.values()) {
            registerPrefixChain(prefix, prefixOrder);
        }

        // Maps prefix -> (mutable nodes, mutable edges, mutable child prefixes).
        // LinkedHashMap preserves the deterministic insertion order needed for
        // byte-equal exports per [EXP-014].
        var prefixState = new LinkedHashMap<String, MutableCluster>();
        for (var prefix : prefixOrder.keySet()) {
            prefixState.put(prefix, new MutableCluster(prefix));
        }
        // Wire parent -> child relationships.
        for (var entry : prefixState.entrySet()) {
            var parent = SubnetPrefixes.parentOf(entry.getKey());
            parent.ifPresent(p -> prefixState.get(p).childPrefixes.add(entry.getKey()));
        }

        // Step 2: route nodes into their deepest cluster.
        var topLevelNodes = new ArrayList<GraphNode>();
        for (var node : nodes) {
            var prefix = nodeIdToPrefix.get(node.id());
            if (prefix == null) {
                topLevelNodes.add(node);
            } else {
                prefixState.get(prefix).nodes.add(node);
            }
        }

        // Step 3: route edges into the deepest cluster containing both
        // endpoints. Cross-cluster edges stay at top-level so Graphviz draws
        // them between cluster boxes rather than inside one.
        var topLevelEdges = new ArrayList<GraphEdge>();
        for (var edge : edges) {
            var fromPrefix = nodeIdToPrefix.get(edge.from());
            var toPrefix = nodeIdToPrefix.get(edge.to());
            var commonPrefix = deepestCommonPrefix(fromPrefix, toPrefix);
            if (commonPrefix == null) {
                topLevelEdges.add(edge);
            } else {
                prefixState.get(commonPrefix).edges.add(edge);
            }
        }

        // Step 4: assemble Subgraph records bottom-up so children are built
        // before they're consumed by parents.
        var built = new HashMap<String, Subgraph>();
        var topLevel = new ArrayList<Subgraph>();
        var iterationOrder = new ArrayList<>(prefixState.keySet());
        // Bottom-up: reverse insertion order — parents were inserted before
        // children in registerPrefixChain so iterating reversed produces a
        // deepest-first order.
        Collections.reverse(iterationOrder);
        for (var prefix : iterationOrder) {
            var state = prefixState.get(prefix);
            var children = new ArrayList<Subgraph>(state.childPrefixes.size());
            for (var childPrefix : state.childPrefixes) {
                var child = built.get(childPrefix);
                if (child != null) {
                    children.add(child);
                }
            }
            // Children were built deepest-first, so they're reversed relative
            // to their original insertion order. Restore the original order.
            Collections.reverse(children);

            var subgraph = new Subgraph(
                DotExporter.sanitize(prefix),
                prefix,
                List.copyOf(state.nodes),
                List.copyOf(state.edges),
                List.copyOf(children),
                DEFAULT_CLUSTER_ATTRS
            );
            built.put(prefix, subgraph);
        }

        // Top-level subgraphs are those whose prefix has no parent.
        for (var prefix : prefixState.keySet()) {
            if (SubnetPrefixes.parentOf(prefix).isEmpty()) {
                topLevel.add(built.get(prefix));
            }
        }

        return new Partition(
            List.copyOf(topLevelNodes),
            List.copyOf(topLevelEdges),
            List.copyOf(topLevel));
    }

    /**
     * Walks a prefix root-to-leaf, registering every intermediate prefix in
     * {@code accumulator} (no-op when already present). Ensures parents are
     * inserted before children.
     */
    private static void registerPrefixChain(String prefix, Map<String, Object> accumulator) {
        if (prefix == null || prefix.isEmpty()) return;
        var segments = prefix.split("/");
        var built = new StringBuilder();
        for (var seg : segments) {
            if (built.length() > 0) built.append('/');
            built.append(seg);
            accumulator.putIfAbsent(built.toString(), Boolean.TRUE);
        }
    }

    /**
     * Returns the deepest prefix that is a (non-strict) ancestor of both
     * sides, or {@code null} when there is no shared cluster (top-level
     * routing).
     */
    private static String deepestCommonPrefix(String a, String b) {
        if (a == null || b == null) return null;
        if (a.equals(b)) return a;

        var aSegs = a.split("/");
        var bSegs = b.split("/");
        var built = new StringBuilder();
        var matched = 0;
        var min = Math.min(aSegs.length, bSegs.length);
        for (int i = 0; i < min; i++) {
            if (!aSegs[i].equals(bSegs[i])) break;
            if (matched > 0) built.append('/');
            built.append(aSegs[i]);
            matched++;
        }
        return matched == 0 ? null : built.toString();
    }

    /**
     * Mutable accumulator threaded through the partition pass.
     */
    private static final class MutableCluster {
        final String prefix;
        final List<GraphNode> nodes = new ArrayList<>();
        final List<GraphEdge> edges = new ArrayList<>();
        final List<String> childPrefixes = new ArrayList<>();

        MutableCluster(String prefix) {
            this.prefix = prefix;
        }
    }

    /**
     * Read-only view of the prefix relations exposed for callers that only
     * need topology (e.g. the debug protocol's
     * {@link org.libpetri.core.SubnetInstance} builder). Distinct from
     * {@link MutableCluster} which is the internal partitioning state.
     */
    static record PrefixNode(String prefix, Optional<String> parent) {}
}
