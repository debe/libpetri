package org.libpetri.core;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for {@link SubnetDef} — open net fragment + interface declaration.
 *
 * <p>Covers MOD-001 (definition), MOD-003/MOD-005 (port/channel declaration via
 * builder), MOD-006 (validation), and MOD-014 ({@link SubnetDef#fromNet}
 * retrofit factory).
 *
 * <p>Tests covering instantiation, per-instance state isolation, nested
 * prefixes, and rich {@link Instance#bindActions} arrive in the next task
 * (the rename pass) — for now, {@link #instantiate_throwsUntilNextTask}
 * pins the current scaffolding behaviour.
 */
class SubnetDefTest {

    record Item(String tag) {}

    // ============================================================
    //  MOD-001: definition + accessors
    // ============================================================

    @Test
    void builder_producesSubnetDef_withName_body_iface() {
        Place<Item> input = Place.of("incoming", Item.class);
        Place<Item> output = Place.of("outgoing", Item.class);

        Transition t = Transition.builder("forward")
            .inputs(Arc.In.one(input))
            .outputs(Arc.Out.and(output))
            .build();

        var def = SubnetDef.builder("Forwarder")
            .transition(t)
            .inputPort("in", input)
            .outputPort("out", output)
            .build();

        assertEquals("Forwarder", def.name());
        assertNotNull(def.body());
        assertNotNull(def.iface());
        assertEquals(Void.class, def.paramType());
        assertTrue(def.body().places().contains(input));
        assertTrue(def.body().places().contains(output));
        assertEquals(1, def.body().transitions().size());
    }

    // ============================================================
    //  MOD-003: ports declared via builder end up on the Interface
    // ============================================================

    @Test
    void inputOutputInoutPort_appearOnInterface() {
        Place<Item> in = Place.of("in_p", Item.class);
        Place<Item> out = Place.of("out_p", Item.class);
        Place<Item> io = Place.of("io_p", Item.class);

        // A single transition that references all three places ensures they
        // are added to the body via auto-collect on the underlying
        // PetriNet.Builder; SubnetDef.Builder requires port places to be
        // present in the body per MOD-006.
        Transition wire = Transition.builder("wire")
            .inputs(Arc.In.one(in))
            .read(io)
            .outputs(Arc.Out.and(out))
            .build();

        var def = SubnetDef.builder("Triple")
            .transition(wire)
            .inputPort("in", in)
            .outputPort("out", out)
            .inoutPort("io", io)
            .build();

        var iface = def.iface();
        assertEquals(3, iface.ports().size());

        assertInstanceOf(Interface.Port.Input.class, iface.port("in").orElseThrow());
        assertInstanceOf(Interface.Port.Output.class, iface.port("out").orElseThrow());
        assertInstanceOf(Interface.Port.InOut.class, iface.port("io").orElseThrow());

        assertEquals(in, iface.port("in").orElseThrow().place());
        assertEquals(out, iface.port("out").orElseThrow().place());
        assertEquals(io, iface.port("io").orElseThrow().place());
    }

    // ============================================================
    //  MOD-005: channels declared via builder end up on the Interface
    // ============================================================

    @Test
    void channel_declared_appearsOnInterface() {
        Place<Item> p = Place.of("p", Item.class);
        Transition attempt = Transition.builder("attempt").read(p).build();

        var def = SubnetDef.builder("RetryPolicy")
            .transition(attempt)
            .channel("attempt", attempt)
            .build();

        var ch = def.iface().channel("attempt").orElseThrow();
        assertEquals(attempt, ch.transition());
        assertInstanceOf(Interface.Channel.SyncChannel.class, ch);
    }

    // ============================================================
    //  MOD-006: validation rejections
    // ============================================================

    @Test
    void build_rejectsPortPlace_notInBody() {
        Place<Item> bodyPlace = Place.of("inBody", Item.class);
        Place<Item> stranger = Place.of("stranger", Item.class);

        // Body references only bodyPlace via a read-arc transition.
        Transition t = Transition.builder("op").read(bodyPlace).build();

        var ex = assertThrows(IllegalArgumentException.class, () ->
            SubnetDef.builder("Bad")
                .transition(t)
                .inputPort("ghost", stranger) // stranger never appears in any arc
                .build());

        assertTrue(ex.getMessage().contains("ghost") || ex.getMessage().contains("stranger"),
            "Error must name the offending port or place: " + ex.getMessage());
    }

    @Test
    void build_rejectsChannelTransition_notInBody() {
        Place<Item> p = Place.of("p", Item.class);
        Transition inBody = Transition.builder("real").read(p).build();
        Transition outOfBody = Transition.builder("ghost").read(p).build();

        var ex = assertThrows(IllegalArgumentException.class, () ->
            SubnetDef.builder("Bad")
                .transition(inBody)
                .channel("ghost", outOfBody)
                .build());

        assertTrue(ex.getMessage().contains("ghost"),
            "Error must name offending channel: " + ex.getMessage());
    }

    @Test
    void build_rejectsDuplicatePortName_withinNamespace() {
        Place<Item> p1 = Place.of("p1", Item.class);
        Place<Item> p2 = Place.of("p2", Item.class);

        var ex = assertThrows(IllegalArgumentException.class, () ->
            SubnetDef.builder("Bad")
                .inputPort("dup", p1)
                .outputPort("dup", p2)
                .build());

        assertTrue(ex.getMessage().contains("dup"),
            "Error must name duplicate port: " + ex.getMessage());
    }

    @Test
    void build_rejectsDuplicateChannelName_withinNamespace() {
        Place<Item> p = Place.of("p", Item.class);
        Transition t1 = Transition.builder("t1").read(p).build();
        Transition t2 = Transition.builder("t2").read(p).build();

        var ex = assertThrows(IllegalArgumentException.class, () ->
            SubnetDef.builder("Bad")
                .transitions(t1, t2)
                .channel("ch", t1)
                .channel("ch", t2)
                .build());

        assertTrue(ex.getMessage().contains("ch"),
            "Error must name duplicate channel: " + ex.getMessage());
    }

    // ============================================================
    //  MOD-014: fromNet retrofit factory
    // ============================================================

    @Test
    void fromNet_producesSubnetDef_whoseBodyEqualsInputNet() {
        Place<Item> a = Place.of("a", Item.class);
        Place<Item> b = Place.of("b", Item.class);
        Transition t = Transition.builder("t")
            .inputs(Arc.In.one(a))
            .outputs(Arc.Out.and(b))
            .build();

        var net = PetriNet.builder("Original").transition(t).build();

        var iface = Interface.builder()
            .inputPort("in", a)
            .build();

        SubnetDef<Void> def = SubnetDef.fromNet(net, iface);

        assertSame(net, def.body(), "fromNet must wrap the supplied net by reference");
        assertEquals(iface, def.iface());
        assertEquals(Void.class, def.paramType());
        assertEquals("Original", def.name());
    }

    // ============================================================
    //  Smoke test: instantiate produces a real Instance now.
    //  (Rich coverage lives in InstanceTest.)
    // ============================================================

    @Test
    void instantiate_producesInstance_withRenamedBody() {
        Place<Item> p = Place.of("p", Item.class);
        Transition t = Transition.builder("t").read(p).build();

        var def = SubnetDef.builder("S").transition(t).build();
        var inst = def.instantiate("pre");

        assertEquals("pre", inst.prefix());
        assertSame(def, inst.def());
        assertNotNull(inst.renamedBody());
        // The renamed body should contain a single, prefixed transition.
        assertEquals(1, inst.renamedBody().transitions().size());
        assertEquals("pre/t", inst.renamedBody().transitions().iterator().next().name());
    }

    // ============================================================
    //  Subnet sealed sum-type membership (MOD-002)
    // ============================================================

    @Test
    void subnetDef_isSubnetOpen_andClosedWrapsPetriNet() {
        Place<Item> p = Place.of("p", Item.class);
        Transition t = Transition.builder("t").read(p).build();
        var def = SubnetDef.builder("S").transition(t).build();

        Subnet asSubnet = def;
        assertInstanceOf(Subnet.Open.class, asSubnet);

        Subnet closed = new Subnet.Closed(PetriNet.builder("X").build());
        assertInstanceOf(Subnet.Closed.class, closed);

        // Pattern-match exhaustiveness — compile error if Subnet gains a new variant.
        String tag = switch (asSubnet) {
            case Subnet.Closed c -> "closed:" + c.net().name();
            case Subnet.Open o -> "open";
        };
        assertEquals("open", tag);
    }
}
