package org.libpetri.core;

import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.concurrent.CompletableFuture;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for {@link PetriNet}.
 */
class PetriNetTest {

    record TestValue(String data) {}

    @Test
    void builder_createsNetWithName() {
        var net = PetriNet.builder("MyNet").build();

        assertEquals("MyNet", net.name());
    }

    @Test
    void builder_emptyNet_hasNoPlacesOrTransitions() {
        var net = PetriNet.builder("Empty").build();

        assertTrue(net.places().isEmpty());
        assertTrue(net.transitions().isEmpty());
    }

    @Test
    void builder_withTransition_autoCollectsPlaces() {
        var input = Place.of("Input", TestValue.class);
        var output = Place.of("Output", TestValue.class);

        var t = Transition.builder("t")
            .input(input)
            .output(output)
            .build();

        var net = PetriNet.builder("Net").transition(t).build();

        assertEquals(1, net.transitions().size());
        assertEquals(2, net.places().size());
        assertTrue(net.places().contains(input));
        assertTrue(net.places().contains(output));
    }

    @Test
    void builder_withMultipleTransitions_collectsAllPlaces() {
        var p1 = Place.of("P1", TestValue.class);
        var p2 = Place.of("P2", TestValue.class);
        var p3 = Place.of("P3", TestValue.class);

        var t1 = Transition.builder("t1")
            .input(p1)
            .output(p2)
            .build();

        var t2 = Transition.builder("t2")
            .input(p2)
            .output(p3)
            .build();

        var net = PetriNet.builder("Chain")
            .transitions(t1, t2)
            .build();

        assertEquals(2, net.transitions().size());
        assertEquals(3, net.places().size());
    }

    @Test
    void builder_sharedPlaces_notDuplicated() {
        var shared = Place.of("Shared", TestValue.class);
        var p1 = Place.of("P1", TestValue.class);
        var p2 = Place.of("P2", TestValue.class);

        var t1 = Transition.builder("t1")
            .input(p1)
            .output(shared)
            .build();

        var t2 = Transition.builder("t2")
            .input(shared)
            .output(p2)
            .build();

        var net = PetriNet.builder("SharedPlace")
            .transitions(t1, t2)
            .build();

        assertEquals(3, net.places().size());
    }

    @Test
    void builder_collectsAllArcTypes() {
        var input = Place.of("Input", TestValue.class);
        var output = Place.of("Output", TestValue.class);
        var inhibitor = Place.of("Inhibitor", TestValue.class);
        var read = Place.of("Read", TestValue.class);

        var t = Transition.builder("t")
            .input(input)
            .output(output)
            .inhibitor(inhibitor)
            .read(read)
            .build();

        var net = PetriNet.builder("AllArcs").transition(t).build();

        assertEquals(4, net.places().size());
        assertTrue(net.places().contains(input));
        assertTrue(net.places().contains(output));
        assertTrue(net.places().contains(inhibitor));
        assertTrue(net.places().contains(read));
    }

    @Test
    void builder_explicitPlace_isIncluded() {
        var explicitPlace = Place.of("Explicit", TestValue.class);
        var transitionPlace = Place.of("FromTransition", TestValue.class);

        var t = Transition.builder("t")
            .input(transitionPlace)
            .build();

        var net = PetriNet.builder("Mixed")
            .place(explicitPlace)
            .transition(t)
            .build();

        assertEquals(2, net.places().size());
        assertTrue(net.places().contains(explicitPlace));
        assertTrue(net.places().contains(transitionPlace));
    }

    @Test
    void places_returnsImmutableSet() {
        var place = Place.of("Input", TestValue.class);
        var t = Transition.builder("t").input(place).build();
        var net = PetriNet.builder("Net").transition(t).build();

        assertThrows(UnsupportedOperationException.class, () ->
            net.places().add(Place.of("New", TestValue.class))
        );
    }

    @Test
    void transitions_returnsImmutableSet() {
        var place = Place.of("Input", TestValue.class);
        var t = Transition.builder("t").input(place).build();
        var net = PetriNet.builder("Net").transition(t).build();

        assertThrows(UnsupportedOperationException.class, () ->
            net.transitions().add(Transition.builder("t2").build())
        );
    }

    @Test
    void petriNet_isImmutable_builderDoesNotAffect() {
        var place = Place.of("P1", TestValue.class);
        var t = Transition.builder("t").input(place).build();

        var builder = PetriNet.builder("Net").transition(t);
        var net1 = builder.build();

        var extraPlace = Place.of("Extra", TestValue.class);
        var t2 = Transition.builder("t2").input(extraPlace).build();
        builder.transition(t2);

        var net2 = builder.build();

        assertEquals(1, net1.places().size());
        assertEquals(2, net2.places().size());
    }

    @Test
    void petriNet_canBeReusedWithDifferentMarkings() {
        var input = Place.of("Input", TestValue.class);
        var output = Place.of("Output", TestValue.class);

        var t = Transition.builder("t")
            .input(input)
            .output(output)
            .action(ctx -> {
                ctx.output(output, ctx.input(input));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var net = PetriNet.builder("Reusable").transition(t).build();

        // Same net definition, can be used multiple times
        assertNotNull(net);
        assertEquals("Reusable", net.name());
        assertEquals(2, net.places().size());
    }

    @Test
    void bindActions_preservesInputSpecs() {
        var p1 = Place.of("P1", Void.class);
        var p2 = Place.of("P2", Void.class);
        var output = Place.of("Output", Void.class);

        var t = Transition.builder("t")
            .inputs(In.one(p1), In.one(p2))
            .outputs(Out.place(output))
            .build();

        // Verify original has inputSpecs
        assertEquals(2, t.inputSpecs().size());

        var net = PetriNet.builder("Test").transitions(t).build();

        // Bind a new action
        var boundNet = net.bindActions(Map.of("t", ctx -> {
            ctx.output(output, (Void) null);
            return CompletableFuture.completedFuture(null);
        }));

        // Verify rebuilt transition STILL has inputSpecs
        var boundTransition = boundNet.transitions().iterator().next();
        assertEquals(2, boundTransition.inputSpecs().size(),
            "bindActions should preserve inputSpecs");
        assertNotNull(boundTransition.outputSpec(),
            "bindActions should preserve outputSpec");
    }
}
