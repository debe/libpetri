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

    /**
     * EXP-017 line 2 (RD-37): dedup is by ordered pair of cluster keys. A key may
     * hold NUL, so a NUL-joined string key would merge the distinct pairs
     * ({@code a\0b}, {@code c}) and ({@code a}, {@code b\0c}) into one ghost edge.
     * Fixture {@code exp017NulNet} of EXP_017.lean: the reference draws two.
     */
    @Test
    void ghostEdgesDedupByOrderedPair_nulInKeyDoesNotMerge_EXP017() {
        var nodes = List.of(
            node("p_ab"), node("t_o1"), node("p_c"),
            node("p_a"), node("t_o2"), node("p_bc"));
        var edges = List.of(
            edge("p_ab", "t_o1"), edge("t_o1", "p_c"),
            edge("p_a", "t_o2"), edge("t_o2", "p_bc"));
        var prefix = new LinkedHashMap<String, String>();
        prefix.put("p_ab", "a\0b");
        prefix.put("p_c", "c");
        prefix.put("p_a", "a");
        prefix.put("p_bc", "b\0c");

        var result = ClusterBuilder.partition(nodes, edges, prefix);

        var gs = ghosts(result.topLevelEdges());
        assertEquals(2, gs.size(), "one ghost edge per bridged ordered pair (EXP-017)");
        assertEquals("p_ab", gs.get(0).from());
        assertEquals("p_c", gs.get(0).to());
        assertEquals("p_a", gs.get(1).from());
        assertEquals("p_bc", gs.get(1).to());
    }

    /** Renders a cluster tree as {@code label[nodes|edges]{children}} for compact assertions. */
    private static String tree(List<Subgraph> subgraphs) {
        var sb = new StringBuilder();
        for (var sg : subgraphs) {
            if (sb.length() > 0) sb.append(' ');
            sb.append(sg.label()).append('[');
            sb.append(String.join(",", sg.nodes().stream().map(GraphNode::id).toList()));
            sb.append('|');
            sb.append(String.join(",", sg.edges().stream().map(e -> e.from() + ">" + e.to()).toList()));
            sb.append(']');
            if (!sg.subgraphs().isEmpty()) sb.append('{').append(tree(sg.subgraphs())).append('}');
        }
        return sb.toString();
    }

    /**
     * EXP-016 / MOD-040 (RD-12, ruling D46 (a)): the chain of a cluster key is
     * every non-empty {@code /}-prefix of it, then the key itself (the glossary's
     * {@code keyChain}), so a key with an empty segment ({@code a/}, {@code a//x},
     * {@code /a}, {@code http://host}) registers its own cluster and its parent's.
     * {@code String.split} dropped trailing empty segments and joined a leading
     * one without its slash, so such keys were never registered and the export
     * failed at the node's key.
     */
    @Test
    void partitionRegistersTheKeyChainOfAKeyWithAnEmptySegment_EXP016() {
        var nodes = List.of(node("n1"), node("n2"), node("n3"), node("n4"), node("n5"));
        var edges = List.of(edge("n1", "n2"), edge("n3", "n5"));
        var prefix = new LinkedHashMap<String, String>();
        prefix.put("n1", "a/");
        prefix.put("n2", "a//x");
        prefix.put("n3", "/a");
        prefix.put("n4", "http://host");
        prefix.put("n5", "/b");

        var result = ClusterBuilder.partition(nodes, edges, prefix);

        assertEquals(
            "a[|]{a/[n1|n1>n2]{a//x[n2|]}} /a[n3|] http:[|]{http:/[|]{http://host[n4|]}} /b[n5|]",
            tree(result.topLevelSubgraphs()),
            "every node sits in the cluster of its own key, under that key's chain; an edge "
                + "goes to the deepest cluster both endpoints' chains share");
        assertTrue(result.topLevelEdges().stream()
                .anyMatch(e -> e.from().equals("n3") && e.to().equals("n5")),
            "'/a' and '/b' share no cluster, so their edge stays at top level");
        assertTrue(result.topLevelNodes().isEmpty());
    }
}
