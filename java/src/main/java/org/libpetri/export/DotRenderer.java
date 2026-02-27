package org.libpetri.export;

import org.libpetri.export.graph.Graph;
import org.libpetri.export.graph.GraphEdge;
import org.libpetri.export.graph.GraphNode;
import org.libpetri.export.graph.Subgraph;

import java.util.ArrayList;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Renders a Graph to DOT (Graphviz) format.
 *
 * <p>Pure function with zero Petri net knowledge. Operates solely on the
 * format-agnostic Graph model.
 */
public final class DotRenderer {

    private DotRenderer() {}

    private static final Set<String> DOT_KEYWORDS = Set.of(
        "graph", "digraph", "subgraph", "node", "edge", "strict"
    );

    /**
     * Renders a Graph to a DOT string suitable for Graphviz.
     *
     * @param graph the graph to render
     * @return DOT format string
     */
    public static String render(Graph graph) {
        var lines = new ArrayList<String>();

        lines.add("digraph %s {".formatted(quoteId(graph.id())));

        // Graph attributes
        lines.add("    rankdir=%s;".formatted(graph.rankdir()));
        for (var entry : graph.graphAttrs().entrySet()) {
            lines.add("    %s=%s;".formatted(entry.getKey(), quoteAttr(entry.getValue())));
        }

        // Node defaults
        if (!graph.nodeDefaults().isEmpty()) {
            lines.add("    node [%s];".formatted(formatAttrs(graph.nodeDefaults())));
        }

        // Edge defaults
        if (!graph.edgeDefaults().isEmpty()) {
            lines.add("    edge [%s];".formatted(formatAttrs(graph.edgeDefaults())));
        }

        lines.add("");

        // Subgraphs
        for (var sg : graph.subgraphs()) {
            renderSubgraph(sg, "    ", lines);
            lines.add("");
        }

        // Nodes
        for (var node : graph.nodes()) {
            lines.add("    " + renderNode(node));
        }

        if (!graph.nodes().isEmpty()) {
            lines.add("");
        }

        // Edges
        for (var edge : graph.edges()) {
            lines.add("    " + renderEdge(edge));
        }

        lines.add("}");

        return String.join("\n", lines);
    }

    // ======================== Internal Rendering ========================

    private static String renderNode(GraphNode node) {
        var attrs = new java.util.LinkedHashMap<String, String>();
        attrs.put("label", node.label());
        attrs.put("shape", node.shape().dotValue());
        attrs.put("style", node.style() != null ? "\"filled," + node.style() + "\"" : "filled");
        attrs.put("fillcolor", node.fill());
        attrs.put("color", node.stroke());
        attrs.put("penwidth", formatNumber(node.penwidth()));

        if (node.height() != null) {
            attrs.put("height", formatNumber(node.height()));
        }
        if (node.width() != null) {
            attrs.put("width", formatNumber(node.width()));
        }

        attrs.putAll(node.attrs());

        return "%s [%s];".formatted(quoteId(node.id()), formatNodeAttrs(attrs));
    }

    private static String renderEdge(GraphEdge edge) {
        var attrs = new java.util.LinkedHashMap<String, String>();
        attrs.put("color", edge.color());
        attrs.put("style", edge.style().dotValue());
        attrs.put("arrowhead", edge.arrowhead().dotValue());

        if (edge.label() != null) {
            attrs.put("label", edge.label());
        }
        if (edge.penwidth() != null) {
            attrs.put("penwidth", formatNumber(edge.penwidth()));
        }

        attrs.putAll(edge.attrs());

        return "%s -> %s [%s];".formatted(quoteId(edge.from()), quoteId(edge.to()), formatNodeAttrs(attrs));
    }

    private static void renderSubgraph(Subgraph sg, String indent, java.util.List<String> lines) {
        lines.add("%ssubgraph %s {".formatted(indent, quoteId("cluster_" + sg.id())));

        if (sg.label() != null) {
            lines.add("%s    label=%s;".formatted(indent, quoteAttr(sg.label())));
        }

        for (var entry : sg.attrs().entrySet()) {
            lines.add("%s    %s=%s;".formatted(indent, entry.getKey(), quoteAttr(entry.getValue())));
        }

        for (var node : sg.nodes()) {
            lines.add("%s    %s".formatted(indent, renderNode(node)));
        }

        lines.add("%s}".formatted(indent));
    }

    // ======================== DOT Quoting ========================

    static String quoteId(String id) {
        if (id.matches("[a-zA-Z_][a-zA-Z0-9_]*") && !DOT_KEYWORDS.contains(id.toLowerCase())) {
            return id;
        }
        return "\"" + escapeDot(id) + "\"";
    }

    static String quoteAttr(String value) {
        if (value.matches("-?\\d+(\\.\\d+)?")) {
            return value;
        }
        return "\"" + escapeDot(value) + "\"";
    }

    private static String escapeDot(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"");
    }

    private static String formatNumber(double value) {
        // Format without trailing zeros: 2.0 -> "2", 0.4 -> "0.4"
        if (value == (long) value) {
            return String.valueOf((long) value);
        }
        return String.valueOf(value);
    }

    private static String formatNodeAttrs(Map<String, String> attrs) {
        return attrs.entrySet().stream()
            .map(e -> {
                String value = e.getValue();
                // Pre-quoted values (style with commas)
                if (value.startsWith("\"") && value.endsWith("\"")) {
                    return e.getKey() + "=" + value;
                }
                return e.getKey() + "=" + quoteAttr(value);
            })
            .collect(Collectors.joining(", "));
    }

    private static String formatAttrs(Map<String, String> attrs) {
        return attrs.entrySet().stream()
            .map(e -> e.getKey() + "=" + quoteAttr(e.getValue()))
            .collect(Collectors.joining(", "));
    }
}
