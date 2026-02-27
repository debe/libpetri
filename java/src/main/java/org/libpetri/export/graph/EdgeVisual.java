package org.libpetri.export.graph;

/**
 * Visual properties for an edge/arc type.
 *
 * @param color line color (hex)
 * @param style line style
 * @param arrowhead arrow shape
 * @param penwidth optional line width, null for default
 */
public record EdgeVisual(
    String color,
    EdgeLineStyle style,
    ArrowHead arrowhead,
    Double penwidth
) {
    /** Convenience constructor without penwidth. */
    public EdgeVisual(String color, EdgeLineStyle style, ArrowHead arrowhead) {
        this(color, style, arrowhead, null);
    }
}
