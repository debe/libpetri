package org.libpetri.core;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for {@link Interface} — the port + channel declaration carrier.
 *
 * <p>Validates exhaustive sealed-type pattern matching over {@link Interface.Port}
 * variants, channel retrieval, and {@code portPlaceAs} type-safety on
 * {@link Interface#portPlaceAs(String, Class)} per MOD-003 / MOD-005 / MOD-011.
 */
class InterfaceTest {

    @Test
    void port_sealedHierarchy_isExhaustivelyPatternMatched() {
        Place<String> p = Place.of("p", String.class);
        Interface.Port input = new Interface.Port.Input<>("in", p);
        Interface.Port output = new Interface.Port.Output<>("out", p);
        Interface.Port inout = new Interface.Port.InOut<>("io", p);

        // Exhaustive pattern match — compile error if a Port subtype is added
        // without updating this switch.
        assertEquals("Input(in)", classifyPort(input));
        assertEquals("Output(out)", classifyPort(output));
        assertEquals("InOut(io)", classifyPort(inout));
    }

    private static String classifyPort(Interface.Port port) {
        return switch (port) {
            case Interface.Port.Input<?> i -> "Input(" + i.name() + ")";
            case Interface.Port.Output<?> o -> "Output(" + o.name() + ")";
            case Interface.Port.InOut<?> io -> "InOut(" + io.name() + ")";
        };
    }

    @Test
    void channel_syncChannel_retrievableByName() {
        Place<String> p = Place.of("p", String.class);
        Transition t = Transition.builder("attempt").read(p).build();
        var iface = Interface.builder()
            .syncChannel("attempt", t)
            .build();

        var resolved = iface.channel("attempt");
        assertTrue(resolved.isPresent());
        assertEquals(t, resolved.get().transition());
        assertInstanceOf(Interface.Channel.SyncChannel.class, resolved.get());
    }

    @Test
    void portPlaceAs_returnsEmpty_onMissingName() {
        var iface = Interface.builder().build();
        assertTrue(iface.portPlaceAs("nope", String.class).isEmpty());
    }

    @Test
    void portPlaceAs_returnsEmpty_onTypeMismatch() {
        Place<String> stringPlace = Place.of("s", String.class);
        var iface = Interface.builder()
            .inputPort("in", stringPlace)
            .build();

        assertTrue(iface.portPlaceAs("in", Integer.class).isEmpty(),
            "Mismatched token type must yield empty Optional");
    }

    @Test
    void portPlaceAs_returnsPlace_onTypeMatch() {
        Place<String> stringPlace = Place.of("s", String.class);
        var iface = Interface.builder()
            .inputPort("in", stringPlace)
            .build();

        var resolved = iface.portPlaceAs("in", String.class);
        assertTrue(resolved.isPresent());
        assertEquals(stringPlace, resolved.get());
    }

    @Test
    void builder_rejectsDuplicatePortName_withinPortNamespace() {
        Place<String> p1 = Place.of("p1", String.class);
        Place<String> p2 = Place.of("p2", String.class);

        var ex = assertThrows(IllegalArgumentException.class, () ->
            Interface.builder()
                .inputPort("dup", p1)
                .outputPort("dup", p2)
                .build());
        assertTrue(ex.getMessage().contains("dup"));
    }

    @Test
    void interface_equality_isStructural() {
        Place<String> p = Place.of("p", String.class);

        var a = Interface.builder().inputPort("in", p).build();
        var b = Interface.builder().inputPort("in", p).build();

        assertEquals(a, b, "Interfaces with equal port/channel sets must compare equal");
        assertEquals(a.hashCode(), b.hashCode());
    }
}
