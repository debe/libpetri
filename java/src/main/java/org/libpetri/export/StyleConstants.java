// GENERATED from spec/petri-net-styles.json — do not edit manually.
// Regenerate with: scripts/generate-styles.sh

package org.libpetri.export;

import org.libpetri.export.graph.*;

import java.util.Map;

/**
 * Hardcoded visual style constants from {@code spec/petri-net-styles.json}.
 *
 * <p>This avoids a runtime JSON dependency. Values must be kept in sync
 * with the shared spec file.
 */
public final class StyleConstants {

    private StyleConstants() {}

    // ======================== Node Styles ========================

    public static final NodeVisual PLACE         = new NodeVisual(NodeShape.CIRCLE,  "#FFFFFF", "#333333", 1.5, null, null, 0.35);
    public static final NodeVisual START         = new NodeVisual(NodeShape.CIRCLE,  "#d4edda", "#28a745", 2.0, null, null, 0.35);
    public static final NodeVisual END           = new NodeVisual(NodeShape.DOUBLECIRCLE,  "#cce5ff", "#004085", 2.0, null, null, 0.35);
    public static final NodeVisual ENVIRONMENT   = new NodeVisual(NodeShape.CIRCLE,  "#f8d7da", "#721c24", 2.0, "dashed", null, 0.35);
    public static final NodeVisual TRANSITION    = new NodeVisual(NodeShape.BOX,  "#fff3cd", "#856404", 1.0, null, 0.4, 0.8);

    private static final Map<String, NodeVisual> NODE_STYLES = Map.of(
        "place",       PLACE,
        "start",       START,
        "end",         END,
        "environment", ENVIRONMENT,
        "transition",  TRANSITION
    );

    // ======================== Edge Styles ========================

    public static final EdgeVisual INPUT_EDGE     = new EdgeVisual("#333333", EdgeLineStyle.SOLID,  ArrowHead.NORMAL);
    public static final EdgeVisual OUTPUT_EDGE    = new EdgeVisual("#333333", EdgeLineStyle.SOLID,  ArrowHead.NORMAL);
    public static final EdgeVisual INHIBITOR_EDGE = new EdgeVisual("#dc3545", EdgeLineStyle.SOLID,  ArrowHead.ODOT);
    public static final EdgeVisual READ_EDGE      = new EdgeVisual("#6c757d", EdgeLineStyle.DASHED,  ArrowHead.NORMAL);
    public static final EdgeVisual RESET_EDGE     = new EdgeVisual("#fd7e14", EdgeLineStyle.BOLD,  ArrowHead.NORMAL, 2.0);

    private static final Map<ArcType, EdgeVisual> EDGE_STYLES = Map.of(
        ArcType.INPUT,     INPUT_EDGE,
        ArcType.OUTPUT,    OUTPUT_EDGE,
        ArcType.INHIBITOR, INHIBITOR_EDGE,
        ArcType.READ,      READ_EDGE,
        ArcType.RESET,     RESET_EDGE
    );

    // ======================== Font & Graph ========================

    public static final String FONT_FAMILY = "Helvetica,Arial,sans-serif";
    public static final int NODE_FONT_SIZE = 12;
    public static final int EDGE_FONT_SIZE = 10;
    public static final double NODESEP = 0.5;
    public static final double RANKSEP = 0.75;
    public static final String FORCE_LABELS = "true";
    public static final String OVERLAP = "false";
    public static final String OUTPUT_ORDER = "edgesfirst";

    // ======================== Lookup ========================

    /** Returns the visual style for the given node category. */
    public static NodeVisual nodeStyle(String category) {
        var style = NODE_STYLES.get(category);
        if (style == null) throw new IllegalArgumentException("Unknown node category: " + category);
        return style;
    }

    /** Returns the visual style for the given arc type. */
    public static EdgeVisual edgeStyle(ArcType arcType) {
        return EDGE_STYLES.get(arcType);
    }
}
