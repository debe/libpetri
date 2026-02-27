package org.libpetri.export.graph;

import java.util.List;
import java.util.Map;

/**
 * Format-agnostic typed graph model.
 *
 * <p>Consumed by both the DOT renderer and the animation layer. Nodes carry a
 * {@code semanticId} that maps back to Place/Transition names.
 *
 * @param id graph identifier
 * @param rankdir layout direction
 * @param nodes all nodes
 * @param edges all edges
 * @param subgraphs subgraph clusters
 * @param graphAttrs global DOT graph attributes
 * @param nodeDefaults default DOT node attributes
 * @param edgeDefaults default DOT edge attributes
 */
public record Graph(
    String id,
    RankDir rankdir,
    List<GraphNode> nodes,
    List<GraphEdge> edges,
    List<Subgraph> subgraphs,
    Map<String, String> graphAttrs,
    Map<String, String> nodeDefaults,
    Map<String, String> edgeDefaults
) {
    public Graph {
        nodes = List.copyOf(nodes);
        edges = List.copyOf(edges);
        subgraphs = List.copyOf(subgraphs);
        graphAttrs = Map.copyOf(graphAttrs);
        nodeDefaults = Map.copyOf(nodeDefaults);
        edgeDefaults = Map.copyOf(edgeDefaults);
    }
}
