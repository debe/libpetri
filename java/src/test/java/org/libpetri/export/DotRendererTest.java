package org.libpetri.export;

import org.junit.jupiter.api.Test;
import org.libpetri.export.graph.*;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

class DotRendererTest {

    private Graph emptyGraph() {
        return new Graph("test", RankDir.TB, List.of(), List.of(), List.of(),
            Map.of(), Map.of(), Map.of());
    }

    private GraphNode placeNode(String id, String label) {
        return new GraphNode(id, label, NodeShape.CIRCLE, "#FFFFFF", "#333333",
            1.5, label, null, null, null, null);
    }

    private GraphEdge edge(String from, String to) {
        return new GraphEdge(from, to, null, "#333333", EdgeLineStyle.SOLID,
            ArrowHead.NORMAL, null, ArcType.INPUT, null);
    }

    @Test
    void rendersEmptyGraph() {
        var dot = DotRenderer.render(emptyGraph());
        assertTrue(dot.contains("digraph test {"));
        assertTrue(dot.contains("rankdir=TB;"));
        assertTrue(dot.contains("}"));
    }

    @Test
    void rendersGraphAttributes() {
        var graph = new Graph("test", RankDir.TB, List.of(), List.of(), List.of(),
            Map.of("nodesep", "0.5", "ranksep", "0.75"), Map.of(), Map.of());
        var dot = DotRenderer.render(graph);
        assertTrue(dot.contains("nodesep=0.5;"));
        assertTrue(dot.contains("ranksep=0.75;"));
    }

    @Test
    void rendersNodeDefaults() {
        var graph = new Graph("test", RankDir.TB, List.of(), List.of(), List.of(),
            Map.of(), Map.of("fontname", "Helvetica", "fontsize", "12"), Map.of());
        var dot = DotRenderer.render(graph);
        assertTrue(dot.contains("node ["));
        assertTrue(dot.contains("fontname=\"Helvetica\""));
    }

    @Test
    void rendersNodes() {
        var node = new GraphNode("p_Start", "Start", NodeShape.CIRCLE, "#d4edda", "#28a745",
            2.0, "Start", null, null, null, null);
        var graph = new Graph("test", RankDir.TB, List.of(node), List.of(), List.of(),
            Map.of(), Map.of(), Map.of());
        var dot = DotRenderer.render(graph);

        assertTrue(dot.contains("p_Start ["));
        assertTrue(dot.contains("label=\"Start\""));
        assertTrue(dot.contains("shape=\"circle\""));
        assertTrue(dot.contains("fillcolor=\"#d4edda\""));
        assertTrue(dot.contains("color=\"#28a745\""));
        assertTrue(dot.contains("penwidth=2"));
        assertTrue(dot.contains("style=\"filled\""));
    }

    @Test
    void rendersNodesWithDashedStyle() {
        var node = new GraphNode("p_env", "env", NodeShape.CIRCLE, "#f8d7da", "#721c24",
            2.0, "env", "dashed", null, null, null);
        var graph = new Graph("test", RankDir.TB, List.of(node), List.of(), List.of(),
            Map.of(), Map.of(), Map.of());
        var dot = DotRenderer.render(graph);
        assertTrue(dot.contains("style=\"filled,dashed\""));
    }

    @Test
    void rendersNodesWithHeightAndWidth() {
        var node = new GraphNode("t_fire", "fire", NodeShape.BOX, "#fff3cd", "#856404",
            1.0, "fire", null, 0.4, 0.8, null);
        var graph = new Graph("test", RankDir.TB, List.of(node), List.of(), List.of(),
            Map.of(), Map.of(), Map.of());
        var dot = DotRenderer.render(graph);
        assertTrue(dot.contains("height=0.4"));
        assertTrue(dot.contains("width=0.8"));
    }

    @Test
    void rendersEdges() {
        var graph = new Graph("test", RankDir.TB,
            List.of(placeNode("p_A", "A"), placeNode("p_B", "B")),
            List.of(edge("p_A", "p_B")),
            List.of(), Map.of(), Map.of(), Map.of());
        var dot = DotRenderer.render(graph);
        assertTrue(dot.contains("p_A -> p_B ["));
        assertTrue(dot.contains("color=\"#333333\""));
        assertTrue(dot.contains("style=\"solid\""));
    }

    @Test
    void rendersEdgesWithLabels() {
        var e = new GraphEdge("p_A", "t_T", "\u00d73", "#333333", EdgeLineStyle.SOLID,
            ArrowHead.NORMAL, null, ArcType.INPUT, null);
        var graph = new Graph("test", RankDir.TB, List.of(), List.of(e), List.of(),
            Map.of(), Map.of(), Map.of());
        var dot = DotRenderer.render(graph);
        assertTrue(dot.contains("label=\"\u00d73\""));
    }

    @Test
    void rendersInhibitorEdge() {
        var e = new GraphEdge("p_A", "t_T", null, "#dc3545", EdgeLineStyle.SOLID,
            ArrowHead.ODOT, null, ArcType.INHIBITOR, null);
        var graph = new Graph("test", RankDir.TB, List.of(), List.of(e), List.of(),
            Map.of(), Map.of(), Map.of());
        var dot = DotRenderer.render(graph);
        assertTrue(dot.contains("arrowhead=\"odot\""));
        assertTrue(dot.contains("color=\"#dc3545\""));
    }

    @Test
    void rendersDashedEdge() {
        var e = new GraphEdge("p_A", "t_T", "read", "#6c757d", EdgeLineStyle.DASHED,
            ArrowHead.NORMAL, null, ArcType.READ, null);
        var graph = new Graph("test", RankDir.TB, List.of(), List.of(e), List.of(),
            Map.of(), Map.of(), Map.of());
        var dot = DotRenderer.render(graph);
        assertTrue(dot.contains("style=\"dashed\""));
        assertTrue(dot.contains("label=\"read\""));
    }

    @Test
    void rendersSubgraphs() {
        var sg = new Subgraph("sg1", "Group 1", List.of(placeNode("p_inner", "inner")), null);
        var graph = new Graph("test", RankDir.TB, List.of(), List.of(), List.of(sg),
            Map.of(), Map.of(), Map.of());
        var dot = DotRenderer.render(graph);
        assertTrue(dot.contains("subgraph cluster_sg1 {"));
        assertTrue(dot.contains("label=\"Group 1\""));
        assertTrue(dot.contains("p_inner ["));
    }

    @Test
    void quotesDotKeywords() {
        var node = placeNode("node", "node");
        var graph = new Graph("test", RankDir.TB, List.of(node), List.of(), List.of(),
            Map.of(), Map.of(), Map.of());
        var dot = DotRenderer.render(graph);
        assertTrue(dot.contains("\"node\" ["));
    }

    @Test
    void escapesDoubleQuotesInLabels() {
        var node = new GraphNode("p_test", "label with \"quotes\"", NodeShape.CIRCLE,
            "#FFFFFF", "#333333", 1.5, "test", null, null, null, null);
        var graph = new Graph("test", RankDir.TB, List.of(node), List.of(), List.of(),
            Map.of(), Map.of(), Map.of());
        var dot = DotRenderer.render(graph);
        assertTrue(dot.contains("label=\"label with \\\"quotes\\\"\""));
    }

    @Test
    void rendersLRDirection() {
        var graph = new Graph("test", RankDir.LR, List.of(), List.of(), List.of(),
            Map.of(), Map.of(), Map.of());
        var dot = DotRenderer.render(graph);
        assertTrue(dot.contains("rankdir=LR;"));
    }
}
