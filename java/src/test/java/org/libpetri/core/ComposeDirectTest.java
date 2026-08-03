package org.libpetri.core;

import org.libpetri.fixtures.StructureOnly;
import org.junit.jupiter.api.Test;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.TimePetriNetAnalyzer;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.fixtures.SubnetFixtures;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for {@link PetriNet.Builder#compose(SubnetDef)} — direct composition
 * per <b>MOD-025</b>.
 *
 * <p>Rule: a {@link SubnetDef} composed directly is integrated <i>without</i>
 * instantiation/prefix-renaming. Body places and transitions keep their
 * original names; places merge into the host purely by {@link Place} equality.
 * Direct composition is order-independent.
 */
class ComposeDirectTest {

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
    void composeDirect_mergesBodyPlacesByName() {
        // producer()'s body place "output" must merge with the host's equal
        // place; the transition stays un-prefixed (MOD-025 AC1, AC2).
        Place<String> hostOutput = Place.of("output", String.class);

        var host = PetriNet.builder("Host")
            .place(hostOutput)
            .compose(SubnetFixtures.producer())
            .build();

        assertTrue(host.places().contains(hostOutput),
            "body place 'output' must merge with the host place");
        assertEquals(1, host.places().stream().filter(p -> p.name().equals("output")).count(),
            "exactly one 'output' place after the merge");
        assertTrue(host.places().stream().anyMatch(p -> p.name().equals("nextItem")),
            "internal body place 'nextItem' arrives un-prefixed");

        var produce = host.transitions().stream()
            .filter(t -> t.name().equals("produce"))
            .findFirst().orElseThrow();
        assertTrue(produce.outputPlaces().contains(hostOutput),
            "produce's output arc references the host place");
    }

    @Test
    void composeDirect_hostHasNoPreDeclaredPlace_arrivesUnPrefixed() {
        var host = PetriNet.builder("Host")
            .compose(SubnetFixtures.producer())
            .build();

        assertTrue(host.places().stream().anyMatch(p -> p.name().equals("output")),
            "'output' arrives via the produce arc, un-prefixed");
        assertTrue(host.places().stream().anyMatch(p -> p.name().equals("nextItem")),
            "'nextItem' arrives un-prefixed");
    }

    @Test
    void composeDirect_introducesNoPrefixSeparator() {
        // MOD-025 AC2: direct composition never introduces a "prefix/" name.
        var host = PetriNet.builder("Host")
            .compose(SubnetFixtures.producer())
            .compose(SubnetFixtures.consumer())
            .build();

        assertTrue(host.places().stream().noneMatch(p -> p.name().contains("/")),
            "no place name may contain the '/' instance separator");
        assertTrue(host.transitions().stream().noneMatch(t -> t.name().contains("/")),
            "no transition name may contain the '/' instance separator");
    }

    @Test
    void composeDirect_isOrderIndependent() {
        // MOD-025 AC3: the headline property — composing two subnets that
        // share place "pipe" in either order yields the same flat net.
        var prodThenCons = PetriNet.builder("Host")
            .compose(pipeProducer())
            .compose(pipeConsumer())
            .build();
        var consThenProd = PetriNet.builder("Host")
            .compose(pipeConsumer())
            .compose(pipeProducer())
            .build();

        assertEquals(prodThenCons.places(), consThenProd.places(),
            "place sets must be equal regardless of compose order");
        assertEquals(
            prodThenCons.transitions().stream().map(Transition::name).collect(java.util.stream.Collectors.toSet()),
            consThenProd.transitions().stream().map(Transition::name).collect(java.util.stream.Collectors.toSet()),
            "transition name sets must be equal regardless of compose order");

        // Per-transition arc topology must match (Transition equality is
        // identity-based, so compare arc-place projections by transition name).
        for (var name : Set.of("emit", "eat")) {
            var a = prodThenCons.transitions().stream()
                .filter(t -> t.name().equals(name)).findFirst().orElseThrow();
            var b = consThenProd.transitions().stream()
                .filter(t -> t.name().equals(name)).findFirst().orElseThrow();
            assertEquals(
                a.inputSpecs().stream().map(arc -> arc.place()).toList(),
                b.inputSpecs().stream().map(arc -> arc.place()).toList(),
                "input places must match for '" + name + "'");
            assertEquals(a.outputPlaces(), b.outputPlaces(),
                "output places must match for '" + name + "'");
        }
    }

    @Test
    void composeDirect_structurallyEqualToHandWrittenFlatNet() {
        // MOD-025 AC9: a direct-composed net is indistinguishable from a
        // hand-written flat net for the same wiring.
        var composed = PetriNet.builder("Net")
            .compose(pipeProducer())
            .compose(pipeConsumer())
            .build();

        Place<String> seed = Place.of("seed", String.class);
        Place<String> pipe = Place.of("pipe", String.class);
        Place<String> sink = Place.of("sink", String.class);
        var handWritten = PetriNet.builder("Net")
            .transition(Transition.builder("emit")
                .inputs(In.one(seed)).outputs(Out.place(pipe)).build())
            .transition(Transition.builder("eat")
                .inputs(In.one(pipe)).outputs(Out.place(sink)).build())
            .build();

        assertEquals(handWritten.places(), composed.places(),
            "place set must match the hand-written net");
        assertEquals(
            handWritten.transitions().stream().map(Transition::name).collect(java.util.stream.Collectors.toSet()),
            composed.transitions().stream().map(Transition::name).collect(java.util.stream.Collectors.toSet()),
            "transition names must match the hand-written net");
    }

    @Test
    void composeDirect_mixedWithInstanceCompose_coexist() {
        // MOD-025 AC8: direct (un-prefixed) and instance (prefixed) composition
        // coexist in one builder.
        var host = PetriNet.builder("Host")
            .compose(SubnetFixtures.producer())
            .compose(SubnetFixtures.consumer().instantiate("c1"))
            .build();

        var names = host.transitions().stream().map(Transition::name).toList();
        assertTrue(names.contains("produce"),
            "directly composed transition stays un-prefixed. Got: " + names);
        assertTrue(names.contains("c1/consume"),
            "instance-composed transition keeps its prefix. Got: " + names);
    }

    @Test
    void composeDirect_transitionNameCollision_throws() {
        // MOD-025 AC4: composing producer() twice collides on 'produce'.
        var hostBuilder = PetriNet.builder("Host")
            .compose(SubnetFixtures.producer());

        var ex = assertThrows(IllegalStateException.class,
            () -> hostBuilder.compose(SubnetFixtures.producer()));
        var msg = ex.getMessage();
        assertTrue(msg.contains("produce"),
            "error must name the colliding transition 'produce'. Got: " + msg);
        assertTrue(msg.contains("instantiate"),
            "error must point at the instantiate() path. Got: " + msg);
    }

    @Test
    void composeDirect_subnetWithChannel_throwsNamingChannel() {
        // MOD-025 AC5: retryPolicy() declares the channel 'attempt'.
        var hostBuilder = PetriNet.builder("Host");

        var ex = assertThrows(IllegalStateException.class,
            () -> hostBuilder.compose(SubnetFixtures.retryPolicy()));
        var msg = ex.getMessage();
        assertTrue(msg.contains("channel"),
            "error must mention channels. Got: " + msg);
        assertTrue(msg.contains("attempt"),
            "error must name the channel 'attempt'. Got: " + msg);
        assertTrue(msg.contains("instantiate"),
            "error must point at the instantiate() path. Got: " + msg);
    }

    @Test
    void composeDirect_placeTokenTypeConflict_throws() {
        // MOD-025 AC6: host has 'output':Integer, producer() has 'output':String.
        var hostBuilder = PetriNet.builder("Host")
            .place(Place.of("output", Integer.class));

        var ex = assertThrows(IllegalArgumentException.class,
            () -> hostBuilder.compose(SubnetFixtures.producer()));
        var msg = ex.getMessage();
        assertTrue(msg.contains("output"),
            "error must name the conflicting place 'output'. Got: " + msg);
        assertTrue(msg.contains("Integer") && msg.contains("String"),
            "error must name both token types. Got: " + msg);
    }

    @Test
    void composeDirect_emptySubnet_isNoOp() {
        // MOD-025 AC7.
        var empty = SubnetDef.builder("Empty").build();
        var host = PetriNet.builder("Host")
            .compose(empty)
            .build();

        assertTrue(host.places().isEmpty(), "no places from an empty subnet");
        assertTrue(host.transitions().isEmpty(), "no transitions from an empty subnet");
    }

    @Test
    void composeDirect_arclessStandalonePlace_flowsThrough() {
        // A body place referenced by no arc must still appear (places are
        // added explicitly, not only auto-collected from arcs).
        Place<String> standalone = Place.of("standalone", String.class);
        var subnet = SubnetDef.builder("Standalone")
            .place(standalone)
            .build();

        var host = PetriNet.builder("Host")
            .compose(subnet)
            .build();

        assertTrue(host.places().contains(standalone),
            "an arc-less standalone body place must survive direct composition");
    }

    @Test
    void composeDirect_inhibitorArcPlace_mergesByName() {
        // leakyBucket()'s 'reject' transition has an inhibitor on 'slots';
        // direct composition must merge 'slots' with the host's equal place.
        Place<String> hostSlots = Place.of("slots", String.class);
        var host = PetriNet.builder("Host")
            .place(hostSlots)
            .compose(SubnetFixtures.leakyBucket(2))
            .build();

        var reject = host.transitions().stream()
            .filter(t -> t.name().equals("reject"))
            .findFirst().orElseThrow();
        assertTrue(reject.inhibitors().stream().anyMatch(arc -> arc.place().equals(hostSlots)),
            "the inhibitor arc place must merge with the host 'slots' place");
    }

    @Test
    void composeDirect_thenFuse_fusionRunsAtBuild() {
        // Direct composition and fusion interoperate: fuse() runs at build()
        // over the un-prefixed transitions a direct compose contributed.
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

        assertTrue(net.places().contains(a), "canonical fused place 'a' survives");
        assertFalse(net.places().contains(b), "non-canonical fused place 'b' is substituted away");
    }

    @Test
    void composeDirect_producerToConsumer_isBoundedAndReachable() {
        // SCG-1: a direct-composed producer→pipe←consumer chain is bounded
        // (finite state class graph) and the sink is reachable — proves the
        // name-merge actually wired the two subnets through 'pipe'.
        var net = PetriNet.builder("DirectComposed")
            .compose(pipeProducer())
            .compose(pipeConsumer())
            .build();

        var seed = net.places().stream()
            .filter(p -> p.name().equals("seed")).findFirst().orElseThrow();
        var sink = net.places().stream()
            .filter(p -> p.name().equals("sink")).findFirst().orElseThrow();

        var result = TimePetriNetAnalyzer.forNet(StructureOnly.bind(net))
            .initialMarking(MarkingState.builder().tokens(seed, 1).build())
            .goalPlaces(sink)
            .maxClasses(100)
            .build()
            .analyze();

        assertTrue(result.isComplete(),
            "direct-composed net must be bounded. Report:\n" + result.report());
        assertTrue(result.isGoalLive(),
            "the sink token must become reachable. Report:\n" + result.report());
    }

    @Test
    void composeDirect_orderIndependentUnderStateClassAnalysis() {
        // SCG-2: formal backing for AC3 — the two compose orders produce nets
        // with identical reachability and identical state-class structure.
        var prodThenCons = PetriNet.builder("A")
            .compose(pipeProducer())
            .compose(pipeConsumer())
            .build();
        var consThenProd = PetriNet.builder("B")
            .compose(pipeConsumer())
            .compose(pipeProducer())
            .build();

        var a = analyzePipeChain(prodThenCons);
        var b = analyzePipeChain(consThenProd);

        assertEquals(a.isGoalLive(), b.isGoalLive(),
            "reachability must not depend on compose order");
        assertEquals(a.isComplete(), b.isComplete(),
            "boundedness must not depend on compose order");
        assertEquals(a.stateClassGraph().size(), b.stateClassGraph().size(),
            "state-class count must not depend on compose order");
    }

    private static TimePetriNetAnalyzer.LivenessResult analyzePipeChain(PetriNet net) {
        var seed = net.places().stream()
            .filter(p -> p.name().equals("seed")).findFirst().orElseThrow();
        var sink = net.places().stream()
            .filter(p -> p.name().equals("sink")).findFirst().orElseThrow();
        return TimePetriNetAnalyzer.forNet(StructureOnly.bind(net))
            .initialMarking(MarkingState.builder().tokens(seed, 1).build())
            .goalPlaces(sink)
            .maxClasses(100)
            .build()
            .analyze();
    }
}
