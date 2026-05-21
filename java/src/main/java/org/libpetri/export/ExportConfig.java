package org.libpetri.export;

import org.libpetri.export.graph.RankDir;

import java.util.Set;

/**
 * Configuration for DOT export.
 *
 * @param direction graph layout direction
 * @param showTypes whether to show token types on places
 * @param showIntervals whether to show firing intervals on transitions
 * @param showPriority whether to show priority on transitions
 * @param environmentPlaces place names to render with dashed border + env color
 * @param clusterSource how to group nodes into subgraph clusters (per MOD-040 / EXP-016)
 */
public record ExportConfig(
    RankDir direction,
    boolean showTypes,
    boolean showIntervals,
    boolean showPriority,
    Set<String> environmentPlaces,
    ClusterSource clusterSource
) {
    /**
     * Selects how DOT export groups nodes into {@code subgraph cluster_*}
     * blocks (per <b>MOD-040</b> / <b>EXP-016</b>).
     */
    public enum ClusterSource {
        /**
         * Use subnet-membership metadata (per MOD-026) when the net carries
         * any; otherwise fall back to instance-prefix name detection. Default.
         */
        AUTO,
        /**
         * Strictly cluster from subnet-membership metadata (per MOD-026); a
         * node with no metadata entry — including a prefix-named instance
         * node — is not clustered. Use {@link #AUTO} to also cluster
         * prefix-named nodes.
         */
        METADATA,
        /** Always cluster from instance-prefix name segments; ignore metadata. */
        PREFIX,
        /** Emit no clusters — every node renders at the top level. */
        NONE
    }

    public ExportConfig {
        environmentPlaces = environmentPlaces != null ? Set.copyOf(environmentPlaces) : Set.of();
        clusterSource = clusterSource != null ? clusterSource : ClusterSource.AUTO;
    }

    /**
     * Backwards-compatible 5-argument constructor — defaults
     * {@code clusterSource} to {@link ClusterSource#AUTO}.
     */
    public ExportConfig(RankDir direction, boolean showTypes, boolean showIntervals,
                        boolean showPriority, Set<String> environmentPlaces) {
        this(direction, showTypes, showIntervals, showPriority, environmentPlaces,
            ClusterSource.AUTO);
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
