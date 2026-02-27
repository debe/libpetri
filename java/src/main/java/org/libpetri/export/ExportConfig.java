package org.libpetri.export;

import org.libpetri.export.graph.RankDir;

import java.util.Set;

/**
 * Configuration for DOT export.
 *
 * @param direction graph layout direction
 * @param showTypes whether to show token types on places (used by {@link MermaidExporter} only; the DOT mapper always includes types)
 * @param showIntervals whether to show firing intervals on transitions
 * @param showPriority whether to show priority on transitions
 * @param environmentPlaces place names to render with dashed border + env color
 */
public record ExportConfig(
    RankDir direction,
    boolean showTypes,
    boolean showIntervals,
    boolean showPriority,
    Set<String> environmentPlaces
) {
    public ExportConfig {
        environmentPlaces = environmentPlaces != null ? Set.copyOf(environmentPlaces) : Set.of();
    }

    /** Default configuration: top-to-bottom, show all information. */
    public static final ExportConfig DEFAULT = new ExportConfig(
        RankDir.TB, true, true, true, Set.of()
    );

    /** Minimal configuration: no types, intervals, or priorities. */
    public static ExportConfig minimal() {
        return new ExportConfig(RankDir.TB, false, false, false, Set.of());
    }

    /** Left-to-right layout with all information. */
    public static ExportConfig leftToRight() {
        return new ExportConfig(RankDir.LR, true, true, true, Set.of());
    }
}
