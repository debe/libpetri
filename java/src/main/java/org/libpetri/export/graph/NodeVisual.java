package org.libpetri.export.graph;

/**
 * Visual properties for a node category.
 *
 * @param shape DOT shape
 * @param fill fill color (hex)
 * @param stroke border color (hex)
 * @param penwidth border width
 * @param style optional DOT style (e.g., "dashed"), null for default
 * @param height optional fixed height, null for auto
 * @param width optional fixed width, null for auto
 */
public record NodeVisual(
    NodeShape shape,
    String fill,
    String stroke,
    double penwidth,
    String style,
    Double height,
    Double width
) {
    /** Convenience constructor without optional fields. */
    public NodeVisual(NodeShape shape, String fill, String stroke, double penwidth) {
        this(shape, fill, stroke, penwidth, null, null, null);
    }
}
