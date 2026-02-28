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

        assertTrue(t.inputSpecs().isEmpty());
        assertNull(t.outputSpec());
        assertTrue(t.inhibitors().isEmpty());
        assertTrue(t.reads().isEmpty());
        assertTrue(t.resets().isEmpty());
        assertEquals(0, t.priority());
        assertFalse(t.timing().hasDeadline());
    }

    @Test
    void builder_withInput_addsInputSpec() {
        var place = Place.of("Input", TestValue.class);
        var t = Transition.builder("t").inputs(Arc.In.one(place)).build();

        assertEquals(1, t.inputSpecs().size());
        assertEquals(place, t.inputSpecs().get(0).place());
    }

    @Test
    void builder_withMultipleInputs_addsSamePlace() {
        var place = Place.of("Input", TestValue.class);
        var t = Transition.builder("t")
            .inputs(Arc.In.one(place), Arc.In.one(place))
            .build();

        assertEquals(2, t.inputSpecs().size());
        assertEquals(place, t.inputSpecs().get(0).place());
        assertEquals(place, t.inputSpecs().get(1).place());
    }

    @Test
    void builder_withOutput_addsOutputSpec() {
        var place = Place.of("Output", TestValue.class);
        var t = Transition.builder("t").outputs(Arc.Out.and(place)).build();

        assertNotNull(t.outputSpec());
        assertTrue(t.outputPlaces().contains(place));
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
    void builder_withTiming_setsTiming() {
        var t = Transition.builder("t")
            .timing(Timing.window(Duration.ofMillis(100), Duration.ofMillis(500)))
            .build();

        assertEquals(Duration.ofMillis(100), t.timing().earliest());
        assertEquals(Duration.ofMillis(500), t.timing().latest());
    }

    @Test
    void builder_withDeadlineTiming_createsDeadline() {
        var t = Transition.builder("t")
            .timing(Timing.deadline(Duration.ofMillis(500)))
            .build();

        assertEquals(Duration.ZERO, t.timing().earliest());
        assertEquals(Duration.ofMillis(500), t.timing().latest());
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
    void builder_multipleInputSpecs_addMultiple() {
        var p1 = Place.of("P1", TestValue.class);
        var p2 = Place.of("P2", TestValue.class);
        var p3 = Place.of("P3", TestValue.class);

        var t = Transition.builder("t")
            .inputs(Arc.In.one(p1), Arc.In.one(p2))
            .outputs(Arc.Out.and(p2, p3))
            .inhibitors(p1)
            .reads(p3)
            .resets(p2)
            .build();

        assertEquals(2, t.inputSpecs().size());
        assertTrue(t.outputPlaces().contains(p2));
        assertTrue(t.outputPlaces().contains(p3));
        assertEquals(1, t.inhibitors().size());
        assertEquals(1, t.reads().size());
        assertEquals(1, t.resets().size());
    }

    @Test
    void inputSpecs_countsMultipleInputsFromSamePlace() {
        var p1 = Place.of("P1", TestValue.class);
        var p2 = Place.of("P2", TestValue.class);

        var t = Transition.builder("t")
            .inputs(Arc.In.one(p1), Arc.In.one(p1), Arc.In.one(p1), Arc.In.one(p2))
            .build();

        assertEquals(4, t.inputSpecs().size());
        // 3 specs for p1, 1 for p2
        long p1Count = t.inputSpecs().stream().filter(s -> s.place().equals(p1)).count();
        long p2Count = t.inputSpecs().stream().filter(s -> s.place().equals(p2)).count();
        assertEquals(3, p1Count);
        assertEquals(1, p2Count);
    }

    @Test
    void lists_areImmutable() {
        var place = Place.of("P", TestValue.class);
        var t = Transition.builder("t")
            .inputs(Arc.In.one(place))
            .outputs(Arc.Out.and(place))
            .inhibitor(place)
            .read(place)
            .reset(place)
            .build();

        assertThrows(UnsupportedOperationException.class, () ->
            t.inputSpecs().add(Arc.In.one(place)));
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
            .inputs(Arc.In.one(input), Arc.In.one(input))
            .outputs(Arc.Out.and(output))
            .inhibitor(inhibitor)
            .read(read)
            .reset(reset)
            .timing(Timing.window(Duration.ofMillis(100), Duration.ofMillis(500)))
            .priority(5)
            .action(ctx -> {
                ctx.output(output, new OtherValue(42));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        assertEquals("Full", t.name());
        assertEquals(2, t.inputSpecs().size());
        assertNotNull(t.outputSpec());
        assertEquals(1, t.inhibitors().size());
        assertEquals(1, t.reads().size());
        assertEquals(1, t.resets().size());
        assertEquals(5, t.priority());
        assertEquals(Duration.ofMillis(100), t.timing().earliest());
        assertEquals(Duration.ofMillis(500), t.timing().latest());
    }

    // ==================== NEW API TESTS: inputSpecs ====================

    @Test
    void inputs_withInOne_populatesInputSpecs() {
        var p1 = Place.of("P1", String.class);
        var p2 = Place.of("P2", Integer.class);

        var t = Transition.builder("test")
            .inputs(Arc.In.one(p1), Arc.In.one(p2))
            .build();

        assertEquals(2, t.inputSpecs().size(), "inputSpecs should have 2 elements");
        assertInstanceOf(Arc.In.One.class, t.inputSpecs().get(0));
        assertInstanceOf(Arc.In.One.class, t.inputSpecs().get(1));
        assertEquals(p1, t.inputSpecs().get(0).place());
        assertEquals(p2, t.inputSpecs().get(1).place());
    }

    @Test
    void inputs_withMixedCardinality_populatesInputSpecs() {
        var p1 = Place.of("P1", String.class);
        var p2 = Place.of("P2", Integer.class);
        var p3 = Place.of("P3", TestValue.class);

        var t = Transition.builder("test")
            .inputs(Arc.In.one(p1), Arc.In.exactly(3, p2), Arc.In.atLeast(2, p3))
            .build();

        assertEquals(3, t.inputSpecs().size());
        assertInstanceOf(Arc.In.One.class, t.inputSpecs().get(0));
        assertInstanceOf(Arc.In.Exactly.class, t.inputSpecs().get(1));
        assertInstanceOf(Arc.In.AtLeast.class, t.inputSpecs().get(2));
    }

    @Test
    void inputSpecs_isImmutable() {
        var p1 = Place.of("P1", String.class);
        var t = Transition.builder("test")
            .inputs(Arc.In.one(p1))
            .build();

        assertThrows(UnsupportedOperationException.class, () ->
            t.inputSpecs().add(Arc.In.one(p1)));
    }

    @Test
    void inputPlaces_includesAllInputSpecs() {
        var p1 = Place.of("P1", String.class);
        var p2 = Place.of("P2", Integer.class);
        var p3 = Place.of("P3", TestValue.class);

        var t = Transition.builder("test")
            .inputs(Arc.In.one(p1), Arc.In.one(p2), Arc.In.one(p3))
            .build();

        var inputPlaces = t.inputPlaces();
        assertEquals(3, inputPlaces.size());
        assertTrue(inputPlaces.contains(p1));
        assertTrue(inputPlaces.contains(p2));
        assertTrue(inputPlaces.contains(p3));
    }

    @Test
    void inputs_populatesInputSpecs() {
        var p1 = Place.of("P1", String.class);
        var p2 = Place.of("P2", Integer.class);

        var t = Transition.builder("test")
            .inputs(Arc.In.one(p1), Arc.In.one(p2))
            .build();

        assertEquals(2, t.inputSpecs().size(), "inputSpecs() should be populated");
    }
}
