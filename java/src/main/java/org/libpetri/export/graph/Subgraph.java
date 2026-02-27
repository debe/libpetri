package org.libpetri.export.graph;

import java.util.List;
import java.util.Map;

/**
 * A subgraph (cluster) in the graph.
 *
 * @param id subgraph identifier
 * @param label optional display label
 * @param nodes nodes contained in this subgraph
 * @param attrs optional extra DOT attributes
 */
public record Subgraph(
    String id,
    String label,
    List<GraphNode> nodes,
    Map<String, String> attrs
) {
    public Subgraph {
        nodes = List.copyOf(nodes);
        attrs = attrs != null ? Map.copyOf(attrs) : Map.of();
    }
}
