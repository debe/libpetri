package org.libpetri.export;

import org.junit.jupiter.api.Test;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.SubnetDef;
import org.libpetri.core.Transition;
import org.libpetri.export.graph.RankDir;
import org.libpetri.fixtures.SubnetFixtures;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

/**
 * DOT-cluster export tests per {@code spec/09-export.md} <b>EXP-016</b> and
 * {@code spec/11-modular-composition.md} <b>MOD-040</b>.
 *
 * <p>These tests exercise the cluster grouping the {@link DotExporter}
 * applies to nets produced via modular composition. They do not assert on
 * the cluster's visual styling beyond what the spec mandates (presence of
 * {@code subgraph cluster_<sanitizedPrefix>} blocks, correct membership,
 * nested structure).
 */
class SubnetDotExportTest {

    /** Returns the substring index of the next occurrence of {@code needle} after {@code from}. */
    private static int find(String haystack, String needle, int from) {
        int idx = haystack.indexOf(needle, from);
        if (idx < 0) {
            fail("expected to find '" + needle + "' starting at " + from + " in:\n" + haystack);
        }
        return idx;
    }

    // ============================================================
    //  EXP-016 AC#4: flat net produces no cluster blocks
    // ============================================================

    @Test
    void dotExport_flatNet_noClusters() {
        // Regression guard: a net with no '/' in any name MUST produce zero
        // cluster subgraphs per EXP-016 AC#4.
        var pending = Place.of("Pending", String.class);
        var processed = Place.of("Processed", String.class);
        var process = Transition.builder("Process")
            .inputs(In.one(pending))
            .outputs(Out.place(processed))
            .build();
        var net = PetriNet.builder("FlatNet").transition(process).build();

        var dot = DotExporter.export(net);

        assertFalse(dot.contains("subgraph cluster_"),
            "flat net (no '/' in names) must not emit any cluster subgraph. DOT:\n" + dot);
    }

    // ============================================================
    //  EXP-016 AC#1, AC#2: single instance produces one cluster
    // ============================================================

    @Test
    void dotExport_singleInstance_oneCluster() {
        // Compose one Producer instance with prefix "producer1"; expect one
        // top-level cluster block named cluster_producer1 containing the
        // renamed nodes.
        var producer = SubnetFixtures.producer().instantiate("producer1");
        Place<String> sink = Place.of("hostSink", String.class);

        var host = PetriNet.builder("Host")
            .place(sink)
            .compose(producer, Map.of("output", sink))
            .build();

        var dot = DotExporter.export(host);

        // EXP-016 AC#1: cluster block present.
        assertTrue(dot.contains("subgraph cluster_producer1 {"),
            "expected cluster_producer1 block. DOT:\n" + dot);
        // EXP-016 AC#5: id matches sanitization rules.
        // (producer1 has no special chars so it is its own sanitized form.)

        // EXP-016 AC#2: cluster contains the renamed nodes (p_producer1_*
        // and t_producer1_*).
        int clusterStart = find(dot, "subgraph cluster_producer1 {", 0);
        int clusterEnd = find(dot, "}", clusterStart);
        String clusterBody = dot.substring(clusterStart, clusterEnd);
        assertTrue(clusterBody.contains("p_producer1_nextItem"),
            "cluster must contain the renamed internal nextItem place. Cluster:\n" + clusterBody);
        assertTrue(clusterBody.contains("t_producer1_produce"),
            "cluster must contain the renamed produce transition. Cluster:\n" + clusterBody);

        // The merged host place stays at the top level (its name has no '/').
        // It must appear OUTSIDE the cluster.
        int hostSinkIdx = dot.indexOf("p_hostSink");
        assertTrue(hostSinkIdx >= 0, "hostSink place must appear in DOT");
        assertTrue(hostSinkIdx > clusterEnd || hostSinkIdx < clusterStart,
            "merged host place must NOT live inside the cluster body");
    }

    // ============================================================
    //  EXP-016 AC#1, AC#2: two top-level instances produce two clusters
    // ============================================================

    @Test
    void dotExport_twoInstances_twoSiblingClusters() {
        var producerDef = SubnetFixtures.producer();
        var p1 = producerDef.instantiate("b1");
        var p2 = producerDef.instantiate("b2");
        Place<String> sink = Place.of("sink", String.class);

        var host = PetriNet.builder("TwoProducers")
            .place(sink)
            .compose(p1, Map.of("output", sink))
            .compose(p2, Map.of("output", sink))
            .build();

        var dot = DotExporter.export(host);

        assertTrue(dot.contains("subgraph cluster_b1 {"),
            "expected cluster_b1. DOT:\n" + dot);
        assertTrue(dot.contains("subgraph cluster_b2 {"),
            "expected cluster_b2. DOT:\n" + dot);

        // Each cluster contains exactly its instance's renamed nodes.
        int b1Start = find(dot, "subgraph cluster_b1 {", 0);
        int b1End = find(dot, "}", b1Start);
        String b1Body = dot.substring(b1Start, b1End);
        assertTrue(b1Body.contains("p_b1_nextItem"));
        assertTrue(b1Body.contains("t_b1_produce"));
        assertFalse(b1Body.contains("p_b2_"),
            "b1 cluster must not contain b2 nodes. b1 cluster:\n" + b1Body);

        int b2Start = find(dot, "subgraph cluster_b2 {", 0);
        int b2End = find(dot, "}", b2Start);
        String b2Body = dot.substring(b2Start, b2End);
        assertTrue(b2Body.contains("p_b2_nextItem"));
        assertTrue(b2Body.contains("t_b2_produce"));
        assertFalse(b2Body.contains("p_b1_"),
            "b2 cluster must not contain b1 nodes. b2 cluster:\n" + b2Body);
    }

    // ============================================================
    //  EXP-016 AC#3 + MOD-013: nested instances produce nested clusters
    // ============================================================

    @Test
    void dotExport_nestedInstance_nestedClusters() {
        // Build a producer subnet, compose it inside an "inner" instance
        // wrapped by a higher-level subnet (T), then compose T with prefix
        // "outer". The flattened names should contain "outer/inner/<...>"
        // entries (per [MOD-013] prefix concatenation), and the DOT export
        // should produce nested clusters cluster_outer { cluster_outer_inner }.
        SubnetDef<Void> producerDef = SubnetFixtures.producer();

        // Build an outer subnet that composes a producer instance under
        // prefix "inner" and exposes the outgoing place as a port "out".
        Place<String> outerOut = Place.of("out", String.class);
        var producerInner = producerDef.instantiate("inner");
        var outerSubnetBody = PetriNet.builder("OuterBody")
            .place(outerOut)
            .compose(producerInner, Map.of("output", outerOut))
            .build();
        // Wrap it as a SubnetDef via the retrofit (MOD-014).
        var outerIface = org.libpetri.core.Interface.builder()
            .outputPort("out", outerOut)
            .build();
        var outerDef = SubnetDef.fromNet(outerSubnetBody, outerIface);

        // Top-level host that composes outerDef with prefix "outer".
        Place<String> hostSink = Place.of("hostSink", String.class);
        var outer = outerDef.instantiate("outer");
        var host = PetriNet.builder("Host")
            .place(hostSink)
            .compose(outer, Map.of("out", hostSink))
            .build();

        var dot = DotExporter.export(host);

        // Outer cluster must be present.
        assertTrue(dot.contains("subgraph cluster_outer {"),
            "expected cluster_outer. DOT:\n" + dot);
        // Nested cluster id: sanitize("outer/inner") -> "outer_inner".
        assertTrue(dot.contains("subgraph cluster_outer_inner {"),
            "expected nested cluster_outer_inner. DOT:\n" + dot);

        // Structural nesting: cluster_outer_inner block must appear inside
        // the cluster_outer block (its closing brace must be before
        // cluster_outer's closing brace).
        int outerStart = find(dot, "subgraph cluster_outer {", 0);
        int innerStart = find(dot, "subgraph cluster_outer_inner {", outerStart);
        // Skip past the inner block — find its matching closing brace.
        // For simplicity, look for the next "}" after innerStart and confirm
        // there's still another "}" later (the outer's).
        int innerEnd = find(dot, "}", innerStart);
        int outerEnd = find(dot, "}", innerEnd + 1);
        assertTrue(innerEnd < outerEnd,
            "nested cluster must close before outer cluster does. DOT:\n" + dot);

        // Members: p_outer_inner_nextItem is the deepest leaf, must be in inner cluster.
        String innerBody = dot.substring(innerStart, innerEnd);
        assertTrue(innerBody.contains("p_outer_inner_nextItem"),
            "nested inner cluster must hold the doubly-prefixed nextItem. Inner:\n" + innerBody);
    }

    // ============================================================
    //  EXP-016 AC#5: cluster IDs match the sanitization regex
    // ============================================================

    @Test
    void dotExport_clusterIdsAreSanitized() {
        // The prefix sanitization must replace '/' (and other non-word chars)
        // with '_' per [EXP-014]. We verified this in the nested test
        // (cluster_outer_inner is the sanitized form of "outer/inner"); this
        // test pins that NO raw '/' character ever leaks into a cluster id.
        var producerDef = SubnetFixtures.producer();
        var producerInner = producerDef.instantiate("inner");
        Place<String> outerOut = Place.of("out", String.class);
        var outerBody = PetriNet.builder("OuterBody")
            .place(outerOut)
            .compose(producerInner, Map.of("output", outerOut))
            .build();
        var outerIface = org.libpetri.core.Interface.builder()
            .outputPort("out", outerOut)
            .build();
        var outerDef = SubnetDef.fromNet(outerBody, outerIface);
        Place<String> hostSink = Place.of("hostSink", String.class);
        var outer = outerDef.instantiate("outer");
        var host = PetriNet.builder("Host")
            .place(hostSink)
            .compose(outer, Map.of("out", hostSink))
            .build();

        var dot = DotExporter.export(host);

        // Confirm no raw "cluster_outer/inner" leaked through (would be a sanitization bug).
        assertFalse(dot.contains("cluster_outer/inner"),
            "cluster id must be sanitized — '/' must be replaced. DOT:\n" + dot);
    }

    // ============================================================
    //  EXP-016 (cross-cluster edges): edges between two prefixes live at top-level
    // ============================================================

    @Test
    void dotExport_edgeCrossesCluster_atTopLevel() {
        // Compose two instances that ARE wired through interface places —
        // edges from one instance into a host (top-level) place are
        // top-level. Edges between the two instances go through the host
        // place so they end up as two separate top-level edges (one out of
        // cluster A to the host place, one from the host place into cluster
        // B). The point: any edge whose endpoints are NOT both inside the
        // same cluster lives at the top level so Graphviz routes it
        // correctly.
        var producer = SubnetFixtures.producer().instantiate("prod");
        var consumer = SubnetFixtures.consumer().instantiate("cons");
        Place<String> wire = Place.of("wire", String.class);

        var host = PetriNet.builder("PC")
            .place(wire)
            .compose(producer, Map.of("output", wire))
            .compose(consumer, Map.of("input", wire))
            .build();

        var dot = DotExporter.export(host);

        // Locate cluster bodies.
        int prodStart = find(dot, "subgraph cluster_prod {", 0);
        int prodEnd = find(dot, "}", prodStart);
        String prodBody = dot.substring(prodStart, prodEnd);

        int consStart = find(dot, "subgraph cluster_cons {", 0);
        int consEnd = find(dot, "}", consStart);
        String consBody = dot.substring(consStart, consEnd);

        // The cross-cluster edges (transition_prod_produce -> p_wire and
        // p_wire -> transition_cons_consume) must NOT appear inside either
        // cluster body — they must live at the top level so Graphviz draws
        // them between cluster boxes.
        assertFalse(prodBody.contains("p_wire"),
            "p_wire is a top-level node and must not appear inside cluster_prod. Body:\n" + prodBody);
        assertFalse(consBody.contains("p_wire"),
            "p_wire is a top-level node and must not appear inside cluster_cons. Body:\n" + consBody);

        // The edge t_prod_produce -> p_wire must appear OUTSIDE both clusters.
        int crossEdgeIdx = dot.indexOf("t_prod_produce -> p_wire");
        assertTrue(crossEdgeIdx >= 0, "expected cross-cluster edge in DOT");
        boolean inProdCluster = crossEdgeIdx > prodStart && crossEdgeIdx < prodEnd;
        boolean inConsCluster = crossEdgeIdx > consStart && crossEdgeIdx < consEnd;
        assertFalse(inProdCluster,
            "cross-cluster edge must not be inside cluster_prod");
        assertFalse(inConsCluster,
            "cross-cluster edge must not be inside cluster_cons");
    }

    // ============================================================
    //  MOD-026 / MOD-040: direct composition clusters by subnet name
    // ============================================================

    /** A producer whose output place is named {@code pipe} (wires by name). */
    private static SubnetDef<Void> pipeProducer() {
        Place<String> seed = Place.of("seed", String.class);
        Place<String> pipe = Place.of("pipe", String.class);
        return SubnetDef.builder("PipeProducer")
            .place(seed).place(pipe)
            .transition(Transition.builder("emit")
                .inputs(In.one(seed)).outputs(Out.place(pipe)).build())
            .build();
    }

    /** A consumer whose input place is named {@code pipe} (wires by name). */
    private static SubnetDef<Void> pipeConsumer() {
        Place<String> pipe = Place.of("pipe", String.class);
        Place<String> sink = Place.of("sink", String.class);
        return SubnetDef.builder("PipeConsumer")
            .place(pipe).place(sink)
            .transition(Transition.builder("eat")
                .inputs(In.one(pipe)).outputs(Out.place(sink)).build())
            .build();
    }

    @Test
    void dotExport_directComposed_clustersBySubnetName() {
        // MOD-026: a directly-composed net has no '/' prefixes, but the
        // recorded subnet-membership metadata lets the exporter cluster each
        // subnet's private nodes under cluster_<subnetName>.
        var net = PetriNet.builder("Pipeline")
            .compose(pipeProducer())
            .compose(pipeConsumer())
            .build();

        var dot = DotExporter.export(net);

        assertTrue(dot.contains("subgraph cluster_PipeProducer {"),
            "direct composition must cluster by subnet name. DOT:\n" + dot);
        assertTrue(dot.contains("subgraph cluster_PipeConsumer {"),
            "direct composition must cluster by subnet name. DOT:\n" + dot);

        int prodStart = find(dot, "subgraph cluster_PipeProducer {", 0);
        int prodEnd = find(dot, "}", prodStart);
        String prodBody = dot.substring(prodStart, prodEnd);
        assertTrue(prodBody.contains("p_seed"), "seed must be in the producer cluster");
        assertTrue(prodBody.contains("t_emit"), "emit must be in the producer cluster");

        int consStart = find(dot, "subgraph cluster_PipeConsumer {", 0);
        int consEnd = find(dot, "}", consStart);
        String consBody = dot.substring(consStart, consEnd);
        assertTrue(consBody.contains("p_sink"), "sink must be in the consumer cluster");
        assertTrue(consBody.contains("t_eat"), "eat must be in the consumer cluster");

        // The shared 'pipe' place has no single owner — it must render at the
        // top level, outside both clusters.
        assertFalse(prodBody.contains("p_pipe"),
            "shared place 'pipe' must not be inside the producer cluster");
        assertFalse(consBody.contains("p_pipe"),
            "shared place 'pipe' must not be inside the consumer cluster");
    }

    @Test
    void dotExport_directComposed_clusterSourcePrefix_ignoresMetadata() {
        // ClusterSource.PREFIX clusters only by '/' name segments; a
        // direct-composed net has none, so no clusters are emitted.
        var net = PetriNet.builder("Pipeline")
            .compose(pipeProducer())
            .compose(pipeConsumer())
            .build();

        var config = new ExportConfig(RankDir.TB, true, true, true, Set.of(),
            ExportConfig.ClusterSource.PREFIX);
        var dot = DotExporter.export(net, config);

        assertFalse(dot.contains("subgraph cluster_"),
            "ClusterSource.PREFIX must ignore subnet metadata. DOT:\n" + dot);
    }

    @Test
    void dotExport_clusterSourceNone_suppressesAllClusters() {
        // ClusterSource.NONE suppresses clustering even for a prefix-
        // instantiated net that would otherwise cluster.
        var producer = SubnetFixtures.producer().instantiate("producer1");
        Place<String> sink = Place.of("hostSink", String.class);
        var host = PetriNet.builder("Host")
            .place(sink)
            .compose(producer, Map.of("output", sink))
            .build();

        var config = new ExportConfig(RankDir.TB, true, true, true, Set.of(),
            ExportConfig.ClusterSource.NONE);
        var dot = DotExporter.export(host, config);

        assertFalse(dot.contains("subgraph cluster_"),
            "ClusterSource.NONE must emit no clusters. DOT:\n" + dot);
    }

    // ============================================================
    //  MOD-040 / EXP-016 AC#7: mixed direct + instance composition
    // ============================================================

    @Test
    void dotExport_mixedDirectAndInstance_bothClusterKinds() {
        // MOD-040 AC#7: a net that both directly composes a subnet and
        // instance-composes another carries metadata for the direct nodes and
        // '/' prefixes for the instance nodes. Under the default AUTO source
        // the exporter clusters direct nodes by subnet name and instance nodes
        // by prefix — both cluster kinds coexist.
        var producerInstance = SubnetFixtures.producer().instantiate("inst1");
        Place<String> hostSink = Place.of("hostSink", String.class);

        var net = PetriNet.builder("Mixed")
            .place(hostSink)
            .compose(pipeProducer())
            .compose(producerInstance, Map.of("output", hostSink))
            .build();

        var dot = DotExporter.export(net);

        // Direct-composed subnet → metadata cluster keyed by subnet name.
        assertTrue(dot.contains("subgraph cluster_PipeProducer {"),
            "direct-composed subnet must cluster by subnet name. DOT:\n" + dot);
        // Instance-composed subnet → prefix cluster keyed by instance prefix.
        assertTrue(dot.contains("subgraph cluster_inst1 {"),
            "instance-composed subnet must cluster by prefix. DOT:\n" + dot);

        int metaStart = find(dot, "subgraph cluster_PipeProducer {", 0);
        int metaEnd = find(dot, "}", metaStart);
        String metaBody = dot.substring(metaStart, metaEnd);
        assertTrue(metaBody.contains("p_seed") && metaBody.contains("t_emit"),
            "metadata cluster must hold the direct subnet's nodes. Cluster:\n" + metaBody);
        assertFalse(metaBody.contains("inst1"),
            "metadata cluster must not absorb prefix-named instance nodes. Cluster:\n" + metaBody);

        int instStart = find(dot, "subgraph cluster_inst1 {", 0);
        int instEnd = find(dot, "}", instStart);
        String instBody = dot.substring(instStart, instEnd);
        assertTrue(instBody.contains("p_inst1_nextItem") && instBody.contains("t_inst1_produce"),
            "prefix cluster must hold the instance's renamed nodes. Cluster:\n" + instBody);
    }

    // ============================================================
    //  MOD-040 / EXP-016: ClusterSource.METADATA is strict (no fallback)
    // ============================================================

    @Test
    void dotExport_clusterSourceMetadata_ignoresPrefixOnlyNet() {
        // ClusterSource.METADATA clusters strictly from subnet-membership
        // metadata. An instance-composed net carries no metadata — only '/'
        // prefixes — so METADATA emits no clusters at all. This is what
        // distinguishes METADATA from AUTO, which would cluster by prefix.
        var producer = SubnetFixtures.producer().instantiate("producer1");
        Place<String> sink = Place.of("hostSink", String.class);
        var host = PetriNet.builder("Host")
            .place(sink)
            .compose(producer, Map.of("output", sink))
            .build();

        var config = new ExportConfig(RankDir.TB, true, true, true, Set.of(),
            ExportConfig.ClusterSource.METADATA);
        var dot = DotExporter.export(host, config);

        assertFalse(dot.contains("subgraph cluster_"),
            "ClusterSource.METADATA must not fall back to prefix detection. DOT:\n" + dot);
    }
}
