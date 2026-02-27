package org.libpetri.export;

import org.junit.jupiter.api.Test;

import org.libpetri.core.In;
import org.libpetri.core.Out;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.*;

class MermaidExporterTest {

    @Test
    void exportSimpleNet() {
        var start = Place.of("Start", String.class);
        var end = Place.of("End", String.class);

        var net = PetriNet.builder("Simple")
            .transition(Transition.builder("t1")
                .input(start)
                .output(end)
                .deadline(1000)
                .build())
            .build();

        var mermaid = MermaidExporter.export(net);

        assertTrue(mermaid.contains("layout: elk"), "Should use ELK layout");
        assertTrue(mermaid.contains("flowchart TB"));
        assertTrue(mermaid.contains("Start(["));
        assertTrue(mermaid.contains("End(["));
        assertTrue(mermaid.contains("t_t1["));
        assertTrue(mermaid.contains("[0, 1000]ms"));
        assertTrue(mermaid.contains("Start --> t_t1"));
        assertTrue(mermaid.contains("t_t1 --> End"));
        assertTrue(mermaid.contains("startPlace"));
        assertTrue(mermaid.contains("endPlace"));
    }

    @Test
    void exportWithGuard() {
        var input = Place.of("Input", String.class);
        var output = Place.of("Output", String.class);

        var net = PetriNet.builder("Guarded")
            .transition(Transition.builder("guarded")
                .inputWhen(input, s -> s.startsWith("valid"))
                .output(output)
                .build())
            .build();

        var mermaid = MermaidExporter.export(net);

        assertTrue(mermaid.contains("-.->|guard|"));
    }

    @Test
    void exportWithInhibitor() {
        var input = Place.of("Input", String.class);
        var blocker = Place.of("Blocker", String.class);
        var output = Place.of("Output", String.class);

        var net = PetriNet.builder("Inhibited")
            .transition(Transition.builder("t1")
                .input(input)
                .inhibitor(blocker)
                .output(output)
                .build())
            .build();

        var mermaid = MermaidExporter.export(net);

        assertTrue(mermaid.contains("--o"));
    }

    @Test
    void exportWithReadArc() {
        var input = Place.of("Input", String.class);
        var context = Place.of("Context", String.class);
        var output = Place.of("Output", String.class);

        var net = PetriNet.builder("WithRead")
            .transition(Transition.builder("t1")
                .input(input)
                .read(context)
                .output(output)
                .build())
            .build();

        var mermaid = MermaidExporter.export(net);

        assertTrue(mermaid.contains("-.->|read|"));
    }

    @Test
    void exportMinimalConfig() {
        var start = Place.of("Start", String.class);
        var end = Place.of("End", String.class);

        var net = PetriNet.builder("Minimal")
            .transition(Transition.builder("t1")
                .input(start)
                .output(end)
                .deadline(1000)
                .priority(5)
                .build())
            .build();

        var mermaid = MermaidExporter.export(net, MermaidExporter.Config.minimal());

        assertFalse(mermaid.contains("<String>"));
        assertFalse(mermaid.contains("[0, 1000]ms"));
        assertFalse(mermaid.contains("prio="));
    }

    @Test
    void exportLeftToRight() {
        var start = Place.of("Start", String.class);
        var end = Place.of("End", String.class);

        var net = PetriNet.builder("LR")
            .transition(Transition.builder("t1")
                .input(start)
                .output(end)
                .build())
            .build();

        var mermaid = MermaidExporter.export(net, MermaidExporter.Config.leftToRight());

        assertTrue(mermaid.contains("flowchart LR"));
    }

    @Test
    void exportChatWorkflow() {
        var pending = Place.of("Pending", String.class);
        var ready = Place.of("Ready", String.class);
        var validated = Place.of("Validated", String.class);
        var understood = Place.of("Understood", String.class);
        var answered = Place.of("Answered", String.class);

        var net = PetriNet.builder("ChatWorkflow")
            .transition(Transition.builder("ask")
                .input(pending)
                .output(ready)
                .output(ready)
                .deadline(100)
                .build())
            .transition(Transition.builder("Guard")
                .input(ready)
                .output(validated)
                .deadline(500)
                .priority(1)
                .build())
            .transition(Transition.builder("Intent")
                .input(ready)
                .output(understood)
                .deadline(2000)
                .build())
            .transition(Transition.builder("Compose")
                .input(validated)
                .input(understood)
                .output(answered)
                .deadline(6000)
                .build())
            .build();

        var mermaid = MermaidExporter.export(net);

        // Fork pattern: ask outputs twice to Ready
        assertEquals(2, mermaid.split("t_ask --> Ready").length - 1);

        // Join pattern: Compose takes from both Validated and Understood
        assertTrue(mermaid.contains("Validated --> t_Compose"));
        assertTrue(mermaid.contains("Understood --> t_Compose"));

        // Priority shown
        assertTrue(mermaid.contains("prio=1"));

        System.out.println("```mermaid");
        System.out.println(mermaid);
        System.out.println("```");
    }

    // ==================== EXP-005: XOR Branch Labels ====================

    @Test
    void exportXorBranches_labeledWithPlaceName() {
        // EXP-005: XOR branches should be labeled with inferred branch names
        var input = Place.of("Input", String.class);
        var success = Place.of("Success", String.class);
        var failure = Place.of("Failure", String.class);

        var t = Transition.builder("Decide")
            .inputs(In.one(input))
            .outputs(Out.xor(Out.place(success), Out.place(failure)))
            .build();

        var net = PetriNet.builder("XorBranch").transitions(t).build();
        var mermaid = MermaidExporter.export(net);

        // Each XOR branch should be labeled with the place name
        assertTrue(mermaid.contains("Success"), "Should contain Success branch label");
        assertTrue(mermaid.contains("Failure"), "Should contain Failure branch label");
    }

    @Test
    void exportXorBranches_timeoutBranchLabeled() {
        // EXP-005: Timeout branches in XOR should show timer notation
        var input = Place.of("Input", String.class);
        var success = Place.of("Success", String.class);
        var timeout = Place.of("Timeout", String.class);

        var t = Transition.builder("TimedDecision")
            .inputs(In.one(input))
            .outputs(Out.xor(
                Out.place(success),
                Out.timeout(Duration.ofMillis(500), timeout)
            ))
            .build();

        var net = PetriNet.builder("XorTimeout").transitions(t).build();
        var mermaid = MermaidExporter.export(net);

        assertTrue(mermaid.contains("Success"), "Should contain Success branch label");
        assertTrue(mermaid.contains("⏱500ms"), "Should contain timeout notation");
    }
}
