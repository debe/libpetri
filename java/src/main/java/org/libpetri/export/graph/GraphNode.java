package org.libpetri.export.graph;

import java.util.Map;

/**
 * A node in the format-agnostic graph model.
 *
 * @param id unique node identifier (p_ or t_ prefixed)
 * @param label display text
 * @param shape DOT shape
 * @param fill fill color (hex)
 * @param stroke border color (hex)
 * @param penwidth border width
 * @param semanticId maps back to Place.name or Transition.name for animation targeting
 * @param style optional DOT style (e.g., "dashed"), null for default
 * @param height optional fixed height
 * @param width optional fixed width
 * @param attrs optional extra DOT attributes
 */
public record GraphNode(
    String id,
    String label,
    NodeShape shape,
    String fill,
    String stroke,
    double penwidth,
    String semanticId,
    String style,
    Double height,
    Double width,
    Map<String, String> attrs
) {
    public GraphNode {
        attrs = attrs != null ? Map.copyOf(attrs) : Map.of();
    }
}
