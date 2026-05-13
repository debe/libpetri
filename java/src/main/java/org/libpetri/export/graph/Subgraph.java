package org.libpetri.export.graph;

import java.util.List;
import java.util.Map;

/**
 * A subgraph (cluster) in the graph.
 *
 * <p>Subgraphs may nest arbitrarily via {@link #subgraphs()} to model nested
 * subnet instance prefixes per {@code spec/11-modular-composition.md}
 * <b>MOD-040</b> and {@code spec/09-export.md} <b>EXP-016</b>. Edges whose
 * endpoints both live inside the same cluster are placed inside that cluster
 * via {@link #edges()} so Graphviz routes them correctly. Top-level edges
 * (cross-cluster, or fully outside any cluster) live on the parent
 * {@link Graph#edges()} list.
 *
 * @param id subgraph identifier (used in {@code subgraph cluster_<id>} after
 *           sanitization per [EXP-014])
 * @param label optional display label (typically the un-sanitized prefix
 *              string for human readability per [EXP-016])
 * @param nodes nodes contained directly in this subgraph (excluding nodes in
 *              nested {@link #subgraphs()})
 * @param edges edges whose source and target both live inside this subgraph
 * @param subgraphs nested child subgraphs
 * @param attrs optional extra DOT attributes (style, bgcolor, penwidth, etc.)
 */
public record Subgraph(
    String id,
    String label,
    List<GraphNode> nodes,
    List<GraphEdge> edges,
    List<Subgraph> subgraphs,
    Map<String, String> attrs
) {
    public Subgraph {
        nodes = List.copyOf(nodes);
        edges = edges != null ? List.copyOf(edges) : List.of();
        subgraphs = subgraphs != null ? List.copyOf(subgraphs) : List.of();
        attrs = MapCopy.preservingOrder(attrs);
    }

    /**
     * Backwards-compatible constructor used by callers that produce a leaf
     * subgraph with no edges and no nested subgraphs (the only shape any
     * pre-existing caller in the tree built).
     *
     * @param id subgraph id
     * @param label display label
     * @param nodes contained nodes
     * @param attrs extra DOT attributes (may be null)
     */
    public Subgraph(String id, String label, List<GraphNode> nodes, Map<String, String> attrs) {
        this(id, label, nodes, List.of(), List.of(), attrs);
    }
}
