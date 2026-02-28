package org.libpetri.export;

import org.junit.jupiter.api.Test;
import org.libpetri.core.*;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.export.graph.RankDir;

import java.time.Duration;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

class DotExporterTest {

    private static final Place<String> START = Place.of("Start", String.class);
    private static final Place<String> END = Place.of("End", String.class);

    @Test
    void producesValidDotForSimpleNet() {
        var t = Transition.builder("Process")
            .inputs(In.one(START))
            .outputs(Out.place(END))
            .build();
        var net = PetriNet.builder("SimpleNet").transition(t).build();

        var dot = DotExporter.export(net);

        assertTrue(dot.contains("digraph SimpleNet {"));
        assertTrue(dot.contains("rankdir=TB;"));
        assertTrue(dot.contains("p_Start ["));
        assertTrue(dot.contains("p_End ["));
        assertTrue(dot.contains("t_Process ["));
        assertTrue(dot.contains("p_Start -> t_Process"));
        assertTrue(dot.contains("t_Process -> p_End"));
        assertTrue(dot.contains("}"));
    }

    @Test
    void containsCircleShapesForPlacesAndBoxForTransitions() {
        var t = Transition.builder("T")
            .inputs(In.one(START))
            .outputs(Out.place(END))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();

        var dot = DotExporter.export(net);

        assertTrue(dot.contains("shape=\"circle\""));
        assertTrue(dot.contains("shape=\"box\""));
    }

    @Test
    void handlesAllFiveArcTypes() {
        var input = Place.of("Input", String.class);
        var output = Place.of("Output", String.class);
        var blocker = Place.of("Blocker", String.class);
        var config = Place.of("Config", String.class);
        var cache = Place.of("Cache", String.class);

        var t = Transition.builder("Process")
            .inputs(In.one(input))
            .outputs(Out.place(output))
            .inhibitor(blocker)
            .read(config)
            .reset(cache)
            .build();
        var net = PetriNet.builder("AllArcs").transition(t).build();

        var dot = DotExporter.export(net);

        // Input arc
        assertTrue(dot.contains("p_Input -> t_Process"));
        // Output arc
        assertTrue(dot.contains("t_Process -> p_Output"));
        // Inhibitor arc (odot)
        assertTrue(dot.contains("p_Blocker -> t_Process"));
        assertTrue(dot.contains("arrowhead=\"odot\""));
        // Read arc (dashed)
        assertTrue(dot.contains("p_Config -> t_Process"));
        assertTrue(dot.contains("style=\"dashed\""));
        // Reset arc (bold)
        assertTrue(dot.contains("t_Process -> p_Cache"));
        assertTrue(dot.contains("style=\"bold\""));
    }

    @Test
    void handlesXorOutputsWithBranchLabels() {
        var success = Place.of("Success", String.class);
        var error = Place.of("Error", String.class);
        var t = Transition.builder("Process")
            .inputs(In.one(START))
            .outputs(Out.xor(success, error))
            .build();
        var net = PetriNet.builder("XorNet").transition(t).build();

        var dot = DotExporter.export(net);

        assertTrue(dot.contains("label=\"Success\""));
        assertTrue(dot.contains("label=\"Error\""));
        // XOR transitions use standard box shape
        assertTrue(dot.contains("shape=\"box\""));
    }

    @Test
    void handlesWeightedInputArcs() {
        var t = Transition.builder("Batch")
            .inputs(In.exactly(3, START))
            .outputs(Out.place(END))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();

        var dot = DotExporter.export(net);

        assertTrue(dot.contains("\u00d73"));
    }

    @Test
    void includesTimingInTransitionLabels() {
        var t = Transition.builder("Process")
            .inputs(In.one(START))
            .outputs(Out.place(END))
            .timing(Timing.delayed(Duration.ofMillis(500)))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();

        var dot = DotExporter.export(net);

        assertTrue(dot.contains("[500"));
    }

    @Test
    void respectsConfigDirection() {
        var t = Transition.builder("T")
            .inputs(In.one(START))
            .outputs(Out.place(END))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();

        var dot = DotExporter.export(net, ExportConfig.leftToRight());

        assertTrue(dot.contains("rankdir=LR;"));
    }

    @Test
    void rendersEnvironmentPlacesWithDashedStyle() {
        var envPlace = Place.of("Events", String.class);
        var t = Transition.builder("T")
            .inputs(In.one(envPlace))
            .outputs(Out.place(END))
            .build();
        var net = PetriNet.builder("Test").transition(t).build();

        var config = new ExportConfig(RankDir.TB, true, true, true, Set.of("Events"));
        var dot = DotExporter.export(net, config);

        assertTrue(dot.contains("style=\"filled,dashed\""));
        assertTrue(dot.contains("fillcolor=\"#f8d7da\""));
    }

    @Test
    void handlesMultiTransitionNet() {
        var pending = Place.of("Pending", String.class);
        var validated = Place.of("Validated", String.class);
        var processed = Place.of("Processed", String.class);

        var validate = Transition.builder("Validate")
            .inputs(In.one(pending))
            .outputs(Out.place(validated))
            .build();
        var process = Transition.builder("Process")
            .inputs(In.one(validated))
            .outputs(Out.place(processed))
            .build();

        var net = PetriNet.builder("Pipeline")
            .transitions(validate, process)
            .build();

        var dot = DotExporter.export(net);

        assertTrue(dot.contains("p_Pending"));
        assertTrue(dot.contains("p_Validated"));
        assertTrue(dot.contains("p_Processed"));
        assertTrue(dot.contains("t_Validate"));
        assertTrue(dot.contains("t_Process"));
    }

    @Test
    void sanitizesNames() {
        assertEquals("hello_world", DotExporter.sanitize("hello_world"));
        assertEquals("my_place_name", DotExporter.sanitize("my-place.name"));
        assertEquals("Place_Name", DotExporter.sanitize("Place Name"));
    }
}
