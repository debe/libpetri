package org.libpetri.core;

import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.concurrent.CompletableFuture;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for {@link Transition}.
 */
class TransitionTest {

    record TestValue(String data) {}
    record OtherValue(int count) {}

    @Test
    void builder_createsTransitionWithName() {
        var t = Transition.builder("MyTransition").build();

        assertEquals("MyTransition", t.name());
    }

    @Test
    void builder_emptyTransition_hasDefaultValues() {
        var t = Transition.builder("Empty").build();

        assertTrue(t.inputs().isEmpty());
        assertTrue(t.outputs().isEmpty());
        assertTrue(t.inhibitors().isEmpty());
        assertTrue(t.reads().isEmpty());
        assertTrue(t.resets().isEmpty());
        assertEquals(0, t.priority());
        assertFalse(t.interval().hasFiniteDeadline());
    }

    @Test
    void builder_withInput_addsInputArc() {
        var place = Place.of("Input", TestValue.class);
        var t = Transition.builder("t").input(place).build();

        assertEquals(1, t.inputs().size());
        assertEquals(place, t.inputs().get(place).get(0).place());
    }

    @Test
    void builder_withInputWhen_addsGuardedInputArc() {
        var place = Place.of("Input", Integer.class);
        var t = Transition.builder("t")
            .inputWhen(place, n -> n > 10)
            .build();

        assertEquals(1, t.inputs().size());
        assertTrue(t.inputs().get(place).get(0).hasGuard());
    }

    @Test
    void builder_withMultipleInputs_addsSamePlace() {
        var place = Place.of("Input", TestValue.class);
        var t = Transition.builder("t")
            .input(place)
            .input(place)
            .build();

        assertEquals(2, t.inputs().size());
        assertEquals(2, t.inputs().get(place).size());
    }

    @Test
    void builder_withOutput_addsOutputArc() {
        var place = Place.of("Output", TestValue.class);
        var t = Transition.builder("t").output(place).build();

        assertEquals(1, t.outputs().size());
        assertEquals(place, t.outputs().get(0).place());
    }

    @Test
    void builder_withInhibitor_addsInhibitorArc() {
        var place = Place.of("Blocker", TestValue.class);
        var t = Transition.builder("t").inhibitor(place).build();

        assertEquals(1, t.inhibitors().size());
        assertEquals(place, t.inhibitors().get(0).place());
    }

    @Test
    void builder_withRead_addsReadArc() {
        var place = Place.of("Context", TestValue.class);
        var t = Transition.builder("t").read(place).build();

        assertEquals(1, t.reads().size());
        assertEquals(place, t.reads().get(0).place());
    }

    @Test
    void builder_withReset_addsResetArc() {
        var place = Place.of("Buffer", TestValue.class);
        var t = Transition.builder("t").reset(place).build();

        assertEquals(1, t.resets().size());
        assertEquals(place, t.resets().get(0).place());
    }

    @Test
    void builder_withInterval_setsInterval() {
        var interval = new FiringInterval(Duration.ofMillis(100), Duration.ofMillis(500));
        var t = Transition.builder("t")
            .interval(interval)
            .build();

        assertEquals(interval, t.interval());
    }

    @Test
    void builder_withDeadlineDuration_createsImmediateInterval() {
        var t = Transition.builder("t")
            .deadline(Duration.ofMillis(500))
            .build();

        assertEquals(Duration.ZERO, t.interval().earliest());
        assertEquals(Duration.ofMillis(500), t.interval().deadline());
    }

    @Test
    void builder_withDeadlineMillis_createsImmediateInterval() {
        var t = Transition.builder("t")
            .deadline(500)
            .build();

        assertEquals(Duration.ZERO, t.interval().earliest());
        assertEquals(Duration.ofMillis(500), t.interval().deadline());
    }

    @Test
    void builder_withPriority_setsPriority() {
        var t = Transition.builder("t")
            .priority(10)
            .build();

        assertEquals(10, t.priority());
    }

    @Test
    void builder_withAction_setsAction() {
        var action = TransitionAction.passthrough();
        var t = Transition.builder("t")
            .action(action)
            .build();

        assertSame(action, t.action());
    }

    @Test
    void builder_varargMethods_addMultiple() {
        var p1 = Place.of("P1", TestValue.class);
        var p2 = Place.of("P2", TestValue.class);
        var p3 = Place.of("P3", TestValue.class);

        var t = Transition.builder("t")
            .inputs(p1, p2)
            .outputs(p2, p3)
            .inhibitors(p1)
            .reads(p3)
            .resets(p2)
            .build();

        assertEquals(2, t.inputs().size());
        assertEquals(2, t.outputs().size());
        assertEquals(1, t.inhibitors().size());
        assertEquals(1, t.reads().size());
        assertEquals(1, t.resets().size());
    }

    @Test
    void inputs_countsMultipleInputsFromSamePlace() {
        var p1 = Place.of("P1", TestValue.class);
        var p2 = Place.of("P2", TestValue.class);

        var t = Transition.builder("t")
            .input(p1)
            .input(p1)
            .input(p1)
            .input(p2)
            .build();

        assertEquals(3, t.inputs().get(p1).size());
        assertEquals(1, t.inputs().get(p2).size());
    }

    @Test
    void lists_areImmutable() {
        var place = Place.of("P", TestValue.class);
        var t = Transition.builder("t")
            .input(place)
            .output(place)
            .inhibitor(place)
            .read(place)
            .reset(place)
            .build();

        assertThrows(UnsupportedOperationException.class, () ->
            t.inputs().put(place, new Arc.Input<>(place)));
        assertThrows(UnsupportedOperationException.class, () ->
            t.outputs().add(new Arc.Output<>(place)));
        assertThrows(UnsupportedOperationException.class, () ->
            t.inhibitors().add(new Arc.Inhibitor<>(place)));
        assertThrows(UnsupportedOperationException.class, () ->
            t.reads().add(new Arc.Read<>(place)));
        assertThrows(UnsupportedOperationException.class, () ->
            t.resets().add(new Arc.Reset<>(place)));
    }

    @Test
    void equality_usesIdentity() {
        var t1 = Transition.builder("t").build();
        var t2 = Transition.builder("t").build();

        assertSame(t1, t1);
        assertNotSame(t1, t2);
        assertNotEquals(t1, t2);
    }

    @Test
    void toString_includesName() {
        var t = Transition.builder("MyTransition").build();

        assertTrue(t.toString().contains("MyTransition"));
    }

    @Test
    void fullTransition_withAllArcTypes() {
        var input = Place.of("Input", TestValue.class);
        var output = Place.of("Output", OtherValue.class);
        var inhibitor = Place.of("Inhibitor", String.class);
        var read = Place.of("Read", Integer.class);
        var reset = Place.of("Reset", Double.class);

        var t = Transition.builder("Full")
            .input(input)
            .inputWhen(input, v -> v.data().length() > 0)
            .output(output)
            .inhibitor(inhibitor)
            .read(read)
            .reset(reset)
            .interval(new FiringInterval(Duration.ofMillis(100), Duration.ofMillis(500)))
            .priority(5)
            .action(ctx -> {
                ctx.output(output, new OtherValue(42));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        assertEquals("Full", t.name());
        assertEquals(2, t.inputs().size());
        assertEquals(1, t.outputs().size());
        assertEquals(1, t.inhibitors().size());
        assertEquals(1, t.reads().size());
        assertEquals(1, t.resets().size());
        assertEquals(5, t.priority());
        assertEquals(Duration.ofMillis(100), t.interval().earliest());
        assertEquals(Duration.ofMillis(500), t.interval().deadline());
    }

    // ==================== NEW API TESTS: inputSpecs ====================

    @Test
    void inputs_withInOne_populatesInputSpecs() {
        var p1 = Place.of("P1", String.class);
        var p2 = Place.of("P2", Integer.class);

        var t = Transition.builder("test")
            .inputs(In.one(p1), In.one(p2))
            .build();

        assertEquals(2, t.inputSpecs().size(), "inputSpecs should have 2 elements");
        assertInstanceOf(In.One.class, t.inputSpecs().get(0));
        assertInstanceOf(In.One.class, t.inputSpecs().get(1));
        assertEquals(p1, t.inputSpecs().get(0).place());
        assertEquals(p2, t.inputSpecs().get(1).place());
    }

    @Test
    void inputs_withMixedCardinality_populatesInputSpecs() {
        var p1 = Place.of("P1", String.class);
        var p2 = Place.of("P2", Integer.class);
        var p3 = Place.of("P3", TestValue.class);

        var t = Transition.builder("test")
            .inputs(In.one(p1), In.exactly(3, p2), In.atLeast(2, p3))
            .build();

        assertEquals(3, t.inputSpecs().size());
        assertInstanceOf(In.One.class, t.inputSpecs().get(0));
        assertInstanceOf(In.Exactly.class, t.inputSpecs().get(1));
        assertInstanceOf(In.AtLeast.class, t.inputSpecs().get(2));
    }

    @Test
    void inputSpecs_isImmutable() {
        var p1 = Place.of("P1", String.class);
        var t = Transition.builder("test")
            .inputs(In.one(p1))
            .build();

        assertThrows(UnsupportedOperationException.class, () ->
            t.inputSpecs().add(In.one(p1)));
    }

    @Test
    void inputPlaces_includesBothNewAndLegacyInputs() {
        var p1 = Place.of("P1", String.class);
        var p2 = Place.of("P2", Integer.class);
        var p3 = Place.of("P3", TestValue.class);

        var t = Transition.builder("test")
            .inputs(In.one(p1))  // new API
            .input(p2)           // legacy API
            .inputs(p3)          // legacy vararg API
            .build();

        var inputPlaces = t.inputPlaces();
        assertEquals(3, inputPlaces.size());
        assertTrue(inputPlaces.contains(p1));
        assertTrue(inputPlaces.contains(p2));
        assertTrue(inputPlaces.contains(p3));
    }

    @Test
    void inputs_newApiDoesNotAffectLegacyInputsMap() {
        var p1 = Place.of("P1", String.class);
        var p2 = Place.of("P2", Integer.class);

        var t = Transition.builder("test")
            .inputs(In.one(p1), In.one(p2))
            .build();

        // Legacy inputs map should be empty when using new API
        assertTrue(t.inputs().isEmpty(), "Legacy inputs() should be empty when using new API");
        // New inputSpecs should be populated
        assertEquals(2, t.inputSpecs().size(), "New inputSpecs() should be populated");
    }
}
