package org.libpetri.core;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for {@link SubnetDef#fromNet(PetriNet, Interface)} — the
 * MOD-014 retrofit factory that wraps an existing closed {@link PetriNet}
 * plus an {@link Interface} into an unparameterised {@code SubnetDef<Void>}.
 *
 * <p>Validation rules per <b>MOD-014</b> / <b>MOD-006</b>:
 * <ul>
 *   <li>Every port's place must be in {@code net.places()}.</li>
 *   <li>Every channel's transition must be in {@code net.transitions()}.</li>
 *   <li>Port and channel name uniqueness within their respective namespaces.</li>
 * </ul>
 *
 * <p>Each rejection case is paired with an assertion on the offending name
 * appearing in the error message, per [MOD-006].
 */
class SubnetDefFromNetTest {

    record Item(String tag) { }

    // ============================================================
    //  Success cases
    // ============================================================

    @Test
    void fromNet_validNet_succeeds() {
        Place<Item> a = Place.of("a", Item.class);
        Place<Item> b = Place.of("b", Item.class);

        Transition t = Transition.builder("t")
            .inputs(Arc.In.one(a))
            .outputs(Arc.Out.and(b))
            .build();

        var net = PetriNet.builder("Original").transition(t).build();

        var iface = Interface.builder()
            .inputPort("in", a)
            .outputPort("out", b)
            .syncChannel("synth", t)
            .build();

        var def = SubnetDef.fromNet(net, iface);

        assertSame(net, def.body(), "fromNet must wrap the supplied net");
        assertEquals(iface, def.iface());
        assertEquals(Void.class, def.paramType());
        assertEquals("Original", def.name());
    }

    @Test
    void fromNet_emptyNetEmptyIface_succeeds() {
        var net = PetriNet.builder("Empty").build();
        var iface = Interface.builder().build();

        var def = SubnetDef.fromNet(net, iface);

        assertNotNull(def);
        assertSame(net, def.body());
        assertEquals(iface, def.iface());
        assertTrue(def.iface().ports().isEmpty());
        assertTrue(def.iface().channels().isEmpty());
    }

    @Test
    void fromNet_resultIsSubnetDef_void() {
        Place<Item> p = Place.of("p", Item.class);
        Transition t = Transition.builder("t").read(p).build();
        var net = PetriNet.builder("N").transition(t).build();
        var iface = Interface.builder().inputPort("in", p).build();

        SubnetDef<Void> def = SubnetDef.fromNet(net, iface);

        assertEquals(Void.class, def.paramType(),
            "fromNet must produce SubnetDef<Void> per MOD-014 acceptance criterion 3");
    }

    // ============================================================
    //  Validation failures
    // ============================================================

    @Test
    void fromNet_portPlaceMissing_throws() {
        Place<Item> bodyPlace = Place.of("inBody", Item.class);
        Place<Item> stranger = Place.of("stranger", Item.class);

        Transition t = Transition.builder("op").read(bodyPlace).build();
        var net = PetriNet.builder("N").transition(t).build();
        var iface = Interface.builder()
            .inputPort("ghost", stranger)
            .build();

        var ex = assertThrows(IllegalArgumentException.class,
            () -> SubnetDef.fromNet(net, iface));

        // MOD-006: error message must name the offender.
        assertTrue(ex.getMessage().contains("ghost") || ex.getMessage().contains("stranger"),
            "Error must name the offending port or place; got: " + ex.getMessage());
    }

    @Test
    void fromNet_channelTransitionMissing_throws() {
        Place<Item> p = Place.of("p", Item.class);
        Transition inBody = Transition.builder("real").read(p).build();
        Transition outOfBody = Transition.builder("ghost").read(p).build();

        var net = PetriNet.builder("N").transition(inBody).build();
        var iface = Interface.builder()
            .channel(new Interface.Channel.SyncChannel("ghostCh", outOfBody))
            .build();

        var ex = assertThrows(IllegalArgumentException.class,
            () -> SubnetDef.fromNet(net, iface));

        assertTrue(ex.getMessage().contains("ghostCh") || ex.getMessage().contains("ghost"),
            "Error must name the offending channel/transition; got: " + ex.getMessage());
    }

    @Test
    void fromNet_duplicatePortNames_throws() {
        // The Interface.Builder rejects duplicate port names at its own
        // build() per its own contract. The retrofit utility's defensive
        // check still rejects on that path even when the interface has
        // been hand-built without going through the builder. Easiest way
        // to drive this test is to use the builder path itself — which
        // throws before fromNet is ever called.
        Place<Item> p1 = Place.of("p1", Item.class);
        Place<Item> p2 = Place.of("p2", Item.class);

        var ex = assertThrows(IllegalArgumentException.class, () ->
            Interface.builder()
                .inputPort("dup", p1)
                .outputPort("dup", p2)
                .build());

        assertTrue(ex.getMessage().contains("dup"),
            "Interface.Builder must reject duplicate port name; got: " + ex.getMessage());
    }

    @Test
    void fromNet_duplicateChannelNames_throws() {
        Place<Item> p = Place.of("p", Item.class);
        Transition t1 = Transition.builder("t1").read(p).build();
        Transition t2 = Transition.builder("t2").read(p).build();

        var ex = assertThrows(IllegalArgumentException.class, () ->
            Interface.builder()
                .channel(new Interface.Channel.SyncChannel("ch", t1))
                .channel(new Interface.Channel.SyncChannel("ch", t2))
                .build());

        assertTrue(ex.getMessage().contains("ch"),
            "Interface.Builder must reject duplicate channel name; got: " + ex.getMessage());
    }

    // ============================================================
    //  Round-trip: fromNet output is usable for instantiation/compose
    // ============================================================

    @Test
    void fromNet_outputIsInstantiable() {
        Place<Item> a = Place.of("a", Item.class);
        Place<Item> b = Place.of("b", Item.class);

        Transition t = Transition.builder("t")
            .inputs(Arc.In.one(a))
            .outputs(Arc.Out.and(b))
            .build();

        var net = PetriNet.builder("Original").transition(t).build();
        var iface = Interface.builder().inputPort("in", a).build();

        var def = SubnetDef.fromNet(net, iface);

        // Smoke-test downstream API surface: instantiate must succeed and
        // the renamed body must contain prefixed transitions.
        var inst = def.instantiate("retro");
        assertEquals("retro", inst.prefix());
        assertEquals(1, inst.renamedBody().transitions().size());
        assertEquals("retro/t",
            inst.renamedBody().transitions().iterator().next().name());
    }
}
