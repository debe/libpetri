package org.libpetri.core;

import org.junit.jupiter.api.Test;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.fixtures.SubnetFixtures;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for subnet-membership metadata recorded by
 * {@link PetriNet.Builder#compose(SubnetDef)} — per <b>MOD-026</b>.
 *
 * <p>Direct composition records a {@code node-name → subnet-name} mapping on
 * the built net: a node contributed by exactly one subnet maps to that
 * subnet; a place contributed by two or more subnets is a shared rendezvous
 * place and is omitted. The mapping is what cluster-aware DOT export uses to
 * reconstruct {@code subgraph cluster_*} blocks without prefix names.
 */
class ComposeDirectMembershipTest {

    /** A producer whose output place is named {@code pipe} (wires by name). */
    private static SubnetDef<Void> pipeProducer() {
        Place<String> seed = Place.of("seed", String.class);
        Place<String> pipe = Place.of("pipe", String.class);
        return SubnetDef.builder("PipeProducer")
            .place(seed)
            .place(pipe)
            .transition(Transition.builder("emit")
                .inputs(In.one(seed))
                .outputs(Out.place(pipe))
                .build())
            .build();
    }

    /** A consumer whose input place is named {@code pipe} (wires by name). */
    private static SubnetDef<Void> pipeConsumer() {
        Place<String> pipe = Place.of("pipe", String.class);
        Place<String> sink = Place.of("sink", String.class);
        return SubnetDef.builder("PipeConsumer")
            .place(pipe)
            .place(sink)
            .transition(Transition.builder("eat")
                .inputs(In.one(pipe))
                .outputs(Out.place(sink))
                .build())
            .build();
    }

    @Test
    void directCompose_recordsMembershipPerSubnet() {
        var net = PetriNet.builder("Host")
            .compose(pipeProducer())
            .compose(pipeConsumer())
            .build();

        var membership = net.subnetMembership();
        assertEquals("PipeProducer", membership.get("seed"),
            "a single-owner place maps to its subnet");
        assertEquals("PipeProducer", membership.get("emit"),
            "a transition maps to its subnet");
        assertEquals("PipeConsumer", membership.get("sink"));
        assertEquals("PipeConsumer", membership.get("eat"));
    }

    @Test
    void directCompose_sharedPlace_hasNoMembershipEntry() {
        // 'pipe' is contributed by both subnets — a shared rendezvous place
        // with no single owner, so it carries no membership entry (it renders
        // top-level, outside any cluster).
        var net = PetriNet.builder("Host")
            .compose(pipeProducer())
            .compose(pipeConsumer())
            .build();

        assertFalse(net.subnetMembership().containsKey("pipe"),
            "a place contributed by 2+ subnets must have no membership entry");
    }

    @Test
    void directCompose_membershipIsOrderIndependent() {
        var ab = PetriNet.builder("Host")
            .compose(pipeProducer())
            .compose(pipeConsumer())
            .build();
        var ba = PetriNet.builder("Host")
            .compose(pipeConsumer())
            .compose(pipeProducer())
            .build();

        assertEquals(ab.subnetMembership(), ba.subnetMembership(),
            "membership must not depend on compose order");
    }

    @Test
    void flatNet_hasEmptyMembership() {
        Place<String> a = Place.of("a", String.class);
        Place<String> b = Place.of("b", String.class);
        var net = PetriNet.builder("Flat")
            .transition(Transition.builder("move")
                .inputs(In.one(a)).outputs(Out.place(b)).build())
            .build();

        assertTrue(net.subnetMembership().isEmpty(),
            "a hand-written flat net carries no subnet membership");
    }

    @Test
    void instanceCompose_hasEmptyMembership() {
        // compose(Instance) is the prefix-rename path — it records no
        // membership; the exporter clusters those nodes by name prefix.
        var net = PetriNet.builder("Host")
            .compose(SubnetFixtures.producer().instantiate("p1"))
            .build();

        assertTrue(net.subnetMembership().isEmpty(),
            "instance composition records no membership metadata");
    }

    @Test
    void directCompose_thenFuse_dropsNonCanonicalEntry() {
        // Fusion removes the non-canonical place 'b'; its membership entry
        // must be dropped so the map names only places that still exist.
        Place<String> a = Place.of("a", String.class);
        Place<String> b = Place.of("b", String.class);
        var subnet = SubnetDef.builder("AB")
            .transition(Transition.builder("move")
                .inputs(In.one(a))
                .outputs(Out.place(b))
                .build())
            .build();

        var net = PetriNet.builder("Host")
            .compose(subnet)
            .fuse(FusionSet.of("ab", a, b))
            .build();

        assertEquals("AB", net.subnetMembership().get("a"),
            "the canonical fused place keeps its membership entry");
        assertFalse(net.subnetMembership().containsKey("b"),
            "the non-canonical fused place must lose its membership entry");
        assertEquals("AB", net.subnetMembership().get("move"),
            "transitions are unaffected by fusion");
    }

    @Test
    void bindActions_preservesMembership() {
        var net = PetriNet.builder("Host")
            .compose(pipeProducer())
            .compose(pipeConsumer())
            .build();

        var bound = net.bindActions(Map.of("emit", TransitionAction.passthrough()));

        assertEquals(net.subnetMembership(), bound.subnetMembership(),
            "bindActions rebuilds transitions by name — membership must survive");
    }

    @Test
    void directCompose_subnetNameWithSlash_isSanitised() {
        // A subnet name containing '/' must be sanitised so it never triggers
        // spurious nested-cluster splitting in the exporter.
        Place<String> x = Place.of("x", String.class);
        Place<String> y = Place.of("y", String.class);
        var subnet = SubnetDef.builder("group/sub")
            .transition(Transition.builder("step")
                .inputs(In.one(x)).outputs(Out.place(y)).build())
            .build();

        var net = PetriNet.builder("Host").compose(subnet).build();

        assertEquals("group_sub", net.subnetMembership().get("step"),
            "'/' in a subnet name must be replaced with '_'");
    }
}
