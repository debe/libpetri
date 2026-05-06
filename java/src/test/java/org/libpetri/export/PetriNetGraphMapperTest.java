package org.libpetri.export;

import org.junit.jupiter.api.Test;
import org.libpetri.core.*;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.export.graph.*;

import java.time.Duration;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

class PetriNetGraphMapperTest {

    private static final Place<String> START = Place.of("Start", String.class);
    private static final Place<String> END = Place.of("End", String.class);

    private PetriNet simpleNet() {
        var t = Transition.builder("Process")
            .inputs(In.one(START))
            .outputs(Out.one(END))
            .build();
        return PetriNet.builder("Test").transition(t).build();
    }

    @Test
    void createsGraphWithIdAndRankdir() {
        var graph = PetriNetGraphMapper.map(simpleNet(), ExportConfig.DEFAULT);
        assertEquals("Test", graph.id());
        assertEquals(RankDir.TB, graph.rankdir());
    }

    @Test
    void createsPlaceNodesWithPrefix() {
        var graph = PetriNetGraphMapper.map(simpleNet(), ExportConfig.DEFAULT);
        var startNode = graph.nodes().stream().filter(n -> n.id().equals("p_Start")).findFirst();
        assertTrue(startNode.isPresent());
        assertEquals("", startNode.get().label());
        assertEquals(NodeShape.CIRCLE, startNode.get().shape());
        assertEquals("Start", startNode.get().semanticId());
        assertEquals("Start", startNode.get().attrs().get("xlabel"));
        assertEquals("true", startNode.get().attrs().get("fixedsize"));
        assertEquals(0.35, startNode.get().width());
    }

    @Test
    void createsTransitionNodesWithPrefix() {
        var graph = PetriNetGraphMapper.map(simpleNet(), ExportConfig.DEFAULT);
        var transNode = graph.nodes().stream().filter(n -> n.id().equals("t_Process")).findFirst();
        assertTrue(transNode.isPresent());
        assertTrue(transNode.get().label().contains("Process"));
        assertEquals(NodeShape.BOX, transNode.get().shape());
        assertEquals("Process", transNode.get().semanticId());
    }

    @Test
    void stylesStartPlaces() {
        var graph = PetriNetGraphMapper.map(simpleNet(), ExportConfig.DEFAULT);
        var startNode = graph.nodes().stream().filter(n -> n.id().equals("p_Start")).findFirst().orElseThrow();
        assertEquals("#d4edda", startNode.fill());
        assertEquals("#28a745", startNode.stroke());
    }

    @Test
    void stylesEndPlaces() {
        var graph = PetriNetGraphMapper.map(simpleNet(), ExportConfig.DEFAULT);
        var endNode = graph.nodes().stream().filter(n -> n.id().equals("p_End")).findFirst().orElseThrow();
        assertEquals("#cce5ff", endNode.fill());
        assertEquals("#004085", endNode.stroke());
    }

    @Test
    void stylesEnvironmentPlaces() {
        var envPlace = Place.of("Events", String.class);
        var t = Transition.builder("Process")
            .inputs(In.one(envPlace))
            .outputs(Out.one(END))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var config = new ExportConfig(RankDir.TB, true, true, true, Set.of("Events"));
        var graph = PetriNetGraphMapper.map(net, config);

        var envNode = graph.nodes().stream().filter(n -> n.id().equals("p_Events")).findFirst().orElseThrow();
        assertEquals("#f8d7da", envNode.fill());
        assertEquals("#721c24", envNode.stroke());
        assertEquals("dashed", envNode.style());
    }

    @Test
    void generatesInputEdges() {
        var graph = PetriNetGraphMapper.map(simpleNet(), ExportConfig.DEFAULT);
        var inputEdge = graph.edges().stream()
            .filter(e -> e.from().equals("p_Start") && e.to().equals("t_Process"))
            .findFirst();
        assertTrue(inputEdge.isPresent());
        assertEquals(ArcType.INPUT, inputEdge.get().arcType());
        assertNull(inputEdge.get().label());
    }

    @Test
    void generatesExactlyInputLabel() {
        var t = Transition.builder("Batch")
            .inputs(In.exactly(3, START))
            .outputs(Out.one(END))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var edge = graph.edges().stream().filter(e -> e.from().equals("p_Start")).findFirst().orElseThrow();
        assertEquals("\u00d73", edge.label());
    }

    @Test
    void generatesAllInputLabel() {
        var t = Transition.builder("Drain")
            .inputs(In.all(START))
            .outputs(Out.one(END))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var edge = graph.edges().stream().filter(e -> e.from().equals("p_Start")).findFirst().orElseThrow();
        assertEquals("*", edge.label());
    }

    @Test
    void generatesAtLeastInputLabel() {
        var t = Transition.builder("Accum")
            .inputs(In.atLeast(5, START))
            .outputs(Out.one(END))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var edge = graph.edges().stream().filter(e -> e.from().equals("p_Start")).findFirst().orElseThrow();
        assertEquals("\u22655", edge.label());
    }

    @Test
    void generatesOutputEdges() {
        var graph = PetriNetGraphMapper.map(simpleNet(), ExportConfig.DEFAULT);
        var outputEdge = graph.edges().stream()
            .filter(e -> e.from().equals("t_Process") && e.to().equals("p_End"))
            .findFirst();
        assertTrue(outputEdge.isPresent());
        assertEquals(ArcType.OUTPUT, outputEdge.get().arcType());
    }

    @Test
    void generatesXorJunctionWithBranchLabels() {
        var success = Place.of("Success", String.class);
        var error = Place.of("Error", String.class);
        var t = Transition.builder("Process")
            .inputs(In.one(START))
            .outputs(Out.xor(success, error))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var junction = graph.nodes().stream()
            .filter(n -> n.id().startsWith("j_Process__xor_"))
            .findFirst().orElseThrow();
        assertEquals(NodeShape.DIAMOND, junction.shape());
        assertEquals("✕", junction.label());
        assertEquals("#FFFFFF", junction.fill());
        assertEquals("#333333", junction.stroke());
        assertEquals("14", junction.attrs().get("fontsize"));

        var successEdge = graph.edges().stream().filter(e -> e.to().equals("p_Success")).findFirst().orElseThrow();
        var errorEdge = graph.edges().stream().filter(e -> e.to().equals("p_Error")).findFirst().orElseThrow();
        assertEquals(junction.id(), successEdge.from());
        assertEquals(junction.id(), errorEdge.from());
        assertEquals("Success", successEdge.label());
        assertEquals("Error", errorEdge.label());
    }

    @Test
    void generatesAndJunction() {
        var a = Place.of("A", String.class);
        var b = Place.of("B", String.class);
        var t = Transition.builder("Fork")
            .inputs(In.one(START))
            .outputs(Out.and(a, b))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var junction = graph.nodes().stream()
            .filter(n -> n.id().startsWith("j_Fork__and_"))
            .findFirst().orElseThrow();
        assertEquals(NodeShape.DIAMOND, junction.shape());
        assertEquals("✚", junction.label());
        assertEquals("#FFFFFF", junction.fill());
        assertEquals("#333333", junction.stroke());
        assertEquals("14", junction.attrs().get("fontsize"));
        assertEquals(0.3, junction.width());

        // Single T → junction edge
        var tToJ = graph.edges().stream()
            .filter(e -> e.from().equals("t_Fork") && e.to().equals(junction.id()))
            .toList();
        assertEquals(1, tToJ.size());

        // Two junction → child edges, no labels
        var jToChildren = graph.edges().stream()
            .filter(e -> e.from().equals(junction.id()) && e.arcType() == ArcType.OUTPUT)
            .toList();
        assertEquals(2, jToChildren.size());
        for (var e : jToChildren) {
            assertNull(e.label());
        }
    }

    @Test
    void singleChildAndCollapsesNoJunction() {
        var only = Place.of("Only", String.class);
        var t = Transition.builder("SingleAnd")
            .inputs(In.one(START))
            .outputs(Out.and(only))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var junctions = graph.nodes().stream().filter(n -> n.id().startsWith("j_")).toList();
        assertTrue(junctions.isEmpty(), "single-child AND should not emit a junction");

        var directEdge = graph.edges().stream()
            .filter(e -> e.from().equals("t_SingleAnd") && e.to().equals("p_Only"))
            .findFirst();
        assertTrue(directEdge.isPresent());
        assertEquals(ArcType.OUTPUT, directEdge.get().arcType());
    }

    @Test
    void combinesResetAndOutputIntoSingleEdge() {
        var cache = Place.of("Cache", String.class);
        var t = Transition.builder("Refresh")
            .inputs(In.one(START))
            .outputs(Out.one(cache))
            .reset(cache)
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var edgesToCache = graph.edges().stream().filter(e -> e.to().equals("p_Cache")).toList();
        assertEquals(1, edgesToCache.size());
        var combined = edgesToCache.get(0);
        assertEquals(ArcType.RESET_OUTPUT, combined.arcType());
        assertEquals("reset+out", combined.label());
        assertEquals("#fd7e14", combined.color());
        assertEquals(EdgeLineStyle.BOLD, combined.style());
        assertEquals(2.0, combined.penwidth());

        // No standalone reset edge for Cache
        var standalone = graph.edges().stream()
            .filter(e -> e.arcType() == ArcType.RESET && e.to().equals("p_Cache"))
            .findFirst();
        assertTrue(standalone.isEmpty());
    }

    @Test
    void combinesResetAndOutputThroughXorJunction() {
        var ok = Place.of("Ok", String.class);
        var cache = Place.of("Cache", String.class);
        var t = Transition.builder("Try")
            .inputs(In.one(START))
            .outputs(Out.xor(ok, cache))
            .reset(cache)
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var junction = graph.nodes().stream()
            .filter(n -> n.id().startsWith("j_Try__xor_"))
            .findFirst().orElseThrow();

        var toCache = graph.edges().stream().filter(e -> e.to().equals("p_Cache")).findFirst().orElseThrow();
        assertEquals(junction.id(), toCache.from());
        assertEquals(ArcType.RESET_OUTPUT, toCache.arcType());
        assertEquals("reset+out", toCache.label());

        var toOk = graph.edges().stream().filter(e -> e.to().equals("p_Ok")).findFirst().orElseThrow();
        assertEquals(ArcType.OUTPUT, toOk.arcType());
        assertEquals("Ok", toOk.label());
    }

    @Test
    void deterministicJunctionIdsInDepthFirstOrder() {
        var a = Place.of("A", String.class);
        var b = Place.of("B", String.class);
        var c = Place.of("C", String.class);
        var d = Place.of("D", String.class);
        // AND( XOR(a, b), XOR(c, d) )
        var t = Transition.builder("Nested")
            .inputs(In.one(START))
            .outputs(Out.and(Out.xor(a, b), Out.xor(c, d)))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var ids = graph.nodes().stream()
            .filter(n -> n.id().startsWith("j_Nested__"))
            .map(GraphNode::id)
            .toList();
        assertEquals(java.util.List.of(
            "j_Nested__and_0",
            "j_Nested__xor_1",
            "j_Nested__xor_2"
        ), ids);
    }

    /** EXP-014 AC#2: repeated exports of the same net produce byte-identical DOT. */
    @Test
    void roundTripExportIsByteIdentical() {
        var a = Place.of("A", String.class);
        var b = Place.of("B", String.class);
        var c = Place.of("C", String.class);
        var d = Place.of("D", String.class);
        var cache = Place.of("Cache", String.class);
        // Nested junctions + reset+output covers the full range of EXP-012/013/014 emission paths.
        var nested = Transition.builder("Nested")
            .inputs(In.one(START))
            .outputs(Out.and(Out.xor(a, b), Out.xor(c, d)))
            .build();
        var refresh = Transition.builder("RefreshCache")
            .inputs(In.one(a))
            .outputs(Out.one(cache))
            .reset(cache)
            .build();
        var net = PetriNet.builder("Stable").transition(nested).transition(refresh).build();

        String first = DotExporter.export(net, ExportConfig.DEFAULT);
        String second = DotExporter.export(net, ExportConfig.DEFAULT);
        assertEquals(first, second, "DOT output must be byte-identical across repeated exports");
    }

    @Test
    void generatesTimeoutLabel() {
        var timeoutP = Place.of("Timeout", String.class);
        var t = Transition.builder("Process")
            .inputs(In.one(START))
            .outputs(Out.timeout(Duration.ofSeconds(5), timeoutP))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var timeoutEdge = graph.edges().stream().filter(e -> e.to().equals("p_Timeout")).findFirst().orElseThrow();
        assertTrue(timeoutEdge.label().contains("5000ms"));
    }

    @Test
    void generatesInhibitorEdges() {
        var pause = Place.of("Pause", String.class);
        var t = Transition.builder("Process")
            .inputs(In.one(START))
            .outputs(Out.one(END))
            .inhibitor(pause)
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var inhEdge = graph.edges().stream().filter(e -> e.arcType() == ArcType.INHIBITOR).findFirst().orElseThrow();
        assertEquals("p_Pause", inhEdge.from());
        assertEquals("t_Process", inhEdge.to());
        assertEquals(ArrowHead.ODOT, inhEdge.arrowhead());
        assertEquals("#dc3545", inhEdge.color());
    }

    @Test
    void generatesReadEdges() {
        var config = Place.of("Config", String.class);
        var t = Transition.builder("Process")
            .inputs(In.one(START))
            .outputs(Out.one(END))
            .read(config)
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var readEdge = graph.edges().stream().filter(e -> e.arcType() == ArcType.READ).findFirst().orElseThrow();
        assertEquals(EdgeLineStyle.DASHED, readEdge.style());
        assertEquals("read", readEdge.label());
    }

    @Test
    void generatesResetEdges() {
        var cache = Place.of("Cache", String.class);
        var t = Transition.builder("Process")
            .inputs(In.one(START))
            .outputs(Out.one(END))
            .reset(cache)
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var resetEdge = graph.edges().stream().filter(e -> e.arcType() == ArcType.RESET).findFirst().orElseThrow();
        assertEquals("t_Process", resetEdge.from());
        assertEquals("p_Cache", resetEdge.to());
        assertEquals(EdgeLineStyle.BOLD, resetEdge.style());
        assertEquals("reset", resetEdge.label());
        assertEquals("#fd7e14", resetEdge.color());
        assertEquals(2.0, resetEdge.penwidth());
    }

    @Test
    void xorTransitionGetsBoxShape() {
        var success = Place.of("Success", String.class);
        var error = Place.of("Error", String.class);
        var t = Transition.builder("Process")
            .inputs(In.one(START))
            .outputs(Out.xor(success, error))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var transNode = graph.nodes().stream().filter(n -> n.id().equals("t_Process")).findFirst().orElseThrow();
        assertEquals(NodeShape.BOX, transNode.shape());
        assertEquals("#fff3cd", transNode.fill());
    }

    @Test
    void includesTimingInLabel() {
        var t = Transition.builder("Process")
            .inputs(In.one(START))
            .outputs(Out.one(END))
            .timing(Timing.delayed(Duration.ofMillis(500)))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var transNode = graph.nodes().stream().filter(n -> n.id().equals("t_Process")).findFirst().orElseThrow();
        assertTrue(transNode.label().contains("[500, \u221e]ms"));
    }

    @Test
    void includesPriorityInLabel() {
        var t = Transition.builder("Process")
            .inputs(In.one(START))
            .outputs(Out.one(END))
            .priority(10)
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.DEFAULT);

        var transNode = graph.nodes().stream().filter(n -> n.id().equals("t_Process")).findFirst().orElseThrow();
        assertTrue(transNode.label().contains("prio=10"));
    }

    @Test
    void minimalConfigHidesDetails() {
        var t = Transition.builder("Process")
            .inputs(In.one(START))
            .outputs(Out.one(END))
            .timing(Timing.delayed(Duration.ofMillis(500)))
            .priority(10)
            .build();
        var net = PetriNet.builder("Test").transition(t).build();
        var graph = PetriNetGraphMapper.map(net, ExportConfig.minimal());

        var transNode = graph.nodes().stream().filter(n -> n.id().equals("t_Process")).findFirst().orElseThrow();
        assertEquals("Process", transNode.label());
    }

    @Test
    void respectsDirectionConfig() {
        var graph = PetriNetGraphMapper.map(simpleNet(), ExportConfig.leftToRight());
        assertEquals(RankDir.LR, graph.rankdir());
    }

    @Test
    void graphAttrsIncludeOutputOrder() {
        var graph = PetriNetGraphMapper.map(simpleNet(), ExportConfig.DEFAULT);
        assertEquals("edgesfirst", graph.graphAttrs().get("outputorder"));
    }
}
