package org.libpetri.export;

import org.junit.jupiter.api.Test;
import org.libpetri.export.graph.*;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for ghost-edge synthesis in {@link ClusterBuilder#partition} per
 * spec EXP-017. Mirrors {@code typescript/tests/export/cluster-builder.test.ts}
 * and the {@code #[cfg(test)] mod} in {@code rust/libpetri-export/src/cluster_builder.rs}.
 */
class ClusterBuilderTest {

    private static GraphNode node(String id) {
        return new GraphNode(id, id, NodeShape.CIRCLE, "#FFFFFF", "#333333",
            1.5, id, null, null, null, null);
    }

    private static GraphEdge edge(String from, String to) {
        return new GraphEdge(from, to, null, "#333333", EdgeLineStyle.SOLID,
            ArrowHead.NORMAL, null, ArcType.INPUT, null);
    }

    private static long ghostCount(List<GraphEdge> edges) {
        return edges.stream().filter(e -> e.arcType() == ArcType.GHOST).count();
    }

    private static List<GraphEdge> ghosts(List<GraphEdge> edges) {
        return edges.stream().filter(e -> e.arcType() == ArcType.GHOST).toList();
    }

    @Test
    void emitsOneGhostForSingleOrphanBridgingTwoClusters() {
        var nodes = List.of(node("p_left_a"), node("t_orphan"), node("p_right_b"));
        var edges = List.of(edge("p_left_a", "t_orphan"), edge("t_orphan", "p_right_b"));
        var prefix = Map.of("p_left_a", "left", "p_right_b", "right");

        var result = ClusterBuilder.partition(nodes, edges, prefix);

        assertEquals(3, result.topLevelEdges().size(),
            "2 original cross-cluster edges + 1 ghost");
        var gs = ghosts(result.topLevelEdges());
        assertEquals(1, gs.size());
        var g = gs.get(0);
        assertEquals(EdgeLineStyle.INVIS, g.style());
        assertEquals(ArrowHead.NONE, g.arrowhead());
        assertEquals("cluster_left", g.attrs().get("ltail"));
        assertEquals("cluster_right", g.attrs().get("lhead"));
        assertEquals("p_left_a", g.from());
        assertEquals("p_right_b", g.to());
    }

    @Test
    void dedupsThreeOrphansBridgingSamePairToOneGhost() {
        var nodes = List.of(
            node("p_left_a"),
            node("t_o1"), node("t_o2"), node("t_o3"),
            node("p_right_b"));
        var edges = List.of(
            edge("p_left_a", "t_o1"), edge("t_o1", "p_right_b"),
            edge("p_left_a", "t_o2"), edge("t_o2", "p_right_b"),
            edge("p_left_a", "t_o3"), edge("t_o3", "p_right_b"));
        var prefix = Map.of("p_left_a", "left", "p_right_b", "right");

        var result = ClusterBuilder.partition(nodes, edges, prefix);

        var gs = ghosts(result.topLevelEdges());
        assertEquals(1, gs.size());
        assertEquals("cluster_left", gs.get(0).attrs().get("ltail"));
        assertEquals("cluster_right", gs.get(0).attrs().get("lhead"));
    }

    @Test
    void emitsGhostPerOrderedDirection() {
        var nodes = List.of(
            node("p_left_a"), node("t_fwd"),
            node("p_right_b"), node("t_back"));
        var edges = List.of(
            edge("p_left_a", "t_fwd"), edge("t_fwd", "p_right_b"),
            edge("p_right_b", "t_back"), edge("t_back", "p_left_a"));
        var prefix = Map.of("p_left_a", "left", "p_right_b", "right");

        var result = ClusterBuilder.partition(nodes, edges, prefix);

        var gs = ghosts(result.topLevelEdges());
        assertEquals(2, gs.size());
        var pairs = gs.stream()
            .map(g -> g.attrs().get("ltail") + "->" + g.attrs().get("lhead"))
            .sorted()
            .toList();
        assertEquals(List.of("cluster_left->cluster_right", "cluster_right->cluster_left"), pairs);
    }

    @Test
    void noGhostWhenOrphanTouchesOnlyOneCluster() {
        var nodes = List.of(node("p_a1"), node("t_orphan"), node("p_a2"));
        var edges = List.of(edge("p_a1", "t_orphan"), edge("t_orphan", "p_a2"));
        var prefix = Map.of("p_a1", "same", "p_a2", "same");

        var result = ClusterBuilder.partition(nodes, edges, prefix);

        assertEquals(0, ghostCount(result.topLevelEdges()));
    }

    @Test
    void noGhostWhenOrphanHasOnlyOneClusteredNeighbour() {
        var nodes = List.of(node("p_left_a"), node("t_orphan"), node("p_top"));
        var edges = List.of(edge("p_left_a", "t_orphan"), edge("t_orphan", "p_top"));
        var prefix = Map.of("p_left_a", "left");

        var result = ClusterBuilder.partition(nodes, edges, prefix);

        assertEquals(0, ghostCount(result.topLevelEdges()));
    }

    @Test
    void flatNetEmitsNoGhostEdges() {
        var nodes = List.of(node("p_a"), node("t_x"), node("p_b"));
        var edges = List.of(edge("p_a", "t_x"), edge("t_x", "p_b"));

        var result = ClusterBuilder.partition(nodes, edges, Map.of());

        assertEquals(2, result.topLevelEdges().size());
        assertEquals(0, ghostCount(result.topLevelEdges()));
    }

    @Test
    void sanitizesSlashedPrefixesInLheadLtail() {
        var nodes = List.of(node("p_outer_inner_a"), node("t_orphan"), node("p_far_b"));
        var edges = List.of(edge("p_outer_inner_a", "t_orphan"), edge("t_orphan", "p_far_b"));
        var prefix = Map.of("p_outer_inner_a", "outer/inner", "p_far_b", "far");

        var result = ClusterBuilder.partition(nodes, edges, prefix);

        var gs = ghosts(result.topLevelEdges());
        assertEquals(1, gs.size());
        assertEquals("cluster_outer_inner", gs.get(0).attrs().get("ltail"));
        assertEquals("cluster_far", gs.get(0).attrs().get("lhead"));
    }

    @Test
    void handlesMultipleOrphansBridgingMultipleClusterPairs() {
        var nodes = List.of(
            node("p_left_a"),
            node("p_mid_a"),
            node("p_right_a"),
            node("t_o1"), node("t_o2"), node("t_o3"));
        var edges = List.of(
            edge("p_left_a", "t_o1"), edge("t_o1", "p_right_a"),
            edge("p_left_a", "t_o2"), edge("t_o2", "p_mid_a"),
            edge("p_mid_a", "t_o3"), edge("t_o3", "p_right_a"));
        // Use a LinkedHashMap so iteration is deterministic across runs
        // (Map.of has unspecified iteration order).
        var prefix = new LinkedHashMap<String, String>();
        prefix.put("p_left_a", "left");
        prefix.put("p_mid_a", "mid");
        prefix.put("p_right_a", "right");

        var result = ClusterBuilder.partition(nodes, edges, prefix);

        var gs = ghosts(result.topLevelEdges());
        assertEquals(3, gs.size());
        var pairs = gs.stream()
            .map(g -> g.attrs().get("ltail") + "->" + g.attrs().get("lhead"))
            .sorted()
            .toList();
        assertEquals(List.of(
            "cluster_left->cluster_mid",
            "cluster_left->cluster_right",
            "cluster_mid->cluster_right"
        ), pairs);
    }
}
