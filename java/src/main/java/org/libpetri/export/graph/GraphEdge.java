package org.libpetri.export.graph;

import java.util.Map;

/**
 * An edge in the format-agnostic graph model.
 *
 * @param from source node id
 * @param to target node id
 * @param label optional edge label
 * @param color line color (hex)
 * @param style line style
 * @param arrowhead arrow shape
 * @param penwidth optional line width
 * @param arcType semantic arc type
 * @param attrs optional extra DOT attributes
 */
public record GraphEdge(
    String from,
    String to,
    String label,
    String color,
    EdgeLineStyle style,
    ArrowHead arrowhead,
    Double penwidth,
    ArcType arcType,
    Map<String, String> attrs
) {
    public GraphEdge {
        attrs = attrs != null ? Map.copyOf(attrs) : Map.of();
    }
}
