package org.libpetri.core;

import org.junit.jupiter.api.Test;
import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.TimePetriNetAnalyzer;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.fixtures.SubnetFixtures;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for {@link PetriNet.Builder#compose(Instance)} — identity-default
 * auto-composition per <b>MOD-024</b>.
 *
 * <p>Rule: every declared port whose underlying {@link Place} is equal (by
 * {@code (name, tokenType)}) to a host-builder place auto-binds to it. If
 * the subnet declares no interface ports at all, body places are matched
 * against host places directly.
 */
class AutoComposeTest {

    @Test
    void autoCompose_explicitInterface_matchesByPlaceEquality() {
        // Producer's "output" port carries Place.of("output", String.class).
        // The host declares an equal Place — auto-compose should bind them.
        var producer = SubnetFixtures.producer().instantiate("p1");
        Place<String> hostOutput = Place.of("output", String.class);

        var host = PetriNet.builder("Host")
            .place(hostOutput)
            .compose(producer)
            .build();

        // Host place survives; renamed interface place "p1/output" does not.
        assertTrue(host.places().contains(hostOutput),
            "host place must appear in the merged net");
        assertTrue(host.places().stream().noneMatch(p -> p.name().equals("p1/output")),
            "renamed interface place 'p1/output' must not survive auto-compose");

        // Internal renamed place flows through.
        assertTrue(host.places().stream().anyMatch(p -> p.name().equals("p1/nextItem")),
            "internal place 'p1/nextItem' must survive composition");

        // produce's output arc points at the host place.
        var produce = host.transitions().stream()
            .filter(t -> t.name().equals("p1/produce"))
            .findFirst().orElseThrow();
        assertTrue(produce.outputPlaces().contains(hostOutput),
            "produce.output must merge to host place");
    }

    @Test
    void autoCompose_structurallyEqualToExplicitBindPort() {
        // Same producer, two construction paths: auto vs explicit bindPort.
        // The resulting nets must be byte-equivalent.
        Place<String> hostOutput = Place.of("output", String.class);

        var autoHost = PetriNet.builder("Host")
            .place(hostOutput)
            .compose(SubnetFixtures.producer().instantiate("p1"))
            .build();

        var explicitHost = PetriNet.builder("Host")
            .place(hostOutput)
            .compose(SubnetFixtures.producer().instantiate("p1"),
                     b -> b.bindPort("output", hostOutput))
            .build();

        // Place sets equal (Place record equality on name+tokenType).
        assertEquals(autoHost.places(), explicitHost.places(),
            "auto-compose place set must match explicit-bindPort form");
        // Transition names equal in insertion order.
        var autoTrans = autoHost.transitions().stream().map(Transition::name).toList();
        var explicitTrans = explicitHost.transitions().stream().map(Transition::name).toList();
        assertEquals(autoTrans, explicitTrans,
            "transition names must match");
        // For each transition (by name), structural topology matches.
        // Transition uses identity equality, so compare arc-place projections.
        var autoByName = autoHost.transitions().stream()
            .collect(java.util.stream.Collectors.toMap(Transition::name, t -> t));
        var explicitByName = explicitHost.transitions().stream()
            .collect(java.util.stream.Collectors.toMap(Transition::name, t -> t));
        for (var name : autoTrans) {
            var a = autoByName.get(name);
            var e = explicitByName.get(name);
            assertEquals(
                a.inputSpecs().stream().map(arc -> arc.place()).toList(),
                e.inputSpecs().stream().map(arc -> arc.place()).toList(),
                "input places must match for transition '" + name + "'");
            assertEquals(a.outputPlaces(), e.outputPlaces(),
                "output places must match for transition '" + name + "'");
        }
    }

    @Test
    void autoCompose_hostHasNoPreDeclaredPlace_arrivesViaArcs() {
        // The host doesn't pre-declare any place; producer's "output" port
        // carries the host wiring (Place.of("output", String.class)) on its
        // interface. Auto-compose trusts the SubnetDef's declaration and
        // merges into that place, which arrives implicitly via the rewritten
        // produce.output arc.
        var producer = SubnetFixtures.producer().instantiate("p1");

        var host = PetriNet.builder("Host")
            .compose(producer)
            .build();

        // The interface place "output" is in the merged net (arrived via arcs).
        assertTrue(host.places().stream()
                .anyMatch(p -> p.name().equals("output") && p.tokenType().equals(String.class)),
            "the interface place arrives via rewritten arcs even without explicit host .place()");
        // Renamed interface place "p1/output" was merged away.
        assertTrue(host.places().stream().noneMatch(p -> p.name().equals("p1/output")),
            "the renamed interface place must not survive");
    }

    @Test
    void autoCompose_noInterfaceDeclared_infersFromBodyPlaces() {
        // Build a subnet with NO outputPort declaration. Its body uses a Place
        // that the host also declares. Auto-compose should infer the merge.
        Place<String> shared = Place.of("shared", String.class);
        Place<String> internal = Place.of("internal", String.class);

        var move = Transition.builder("move")
            .inputs(In.one(internal))
            .outputs(Out.place(shared))
            .build();

        var bareSubnet = SubnetDef.builder("Bare")
            .place(internal)
            .place(shared)
            .transition(move)
            .build();  // NO inputPort/outputPort declarations
        var inst = bareSubnet.instantiate("b1");

        var host = PetriNet.builder("Host")
            .place(shared)
            .compose(inst)
            .build();

        assertTrue(host.places().contains(shared),
            "shared place must remain in merged net");
        assertTrue(host.places().stream().noneMatch(p -> p.name().equals("b1/shared")),
            "renamed shared place 'b1/shared' must be merged away");
        assertTrue(host.places().stream().anyMatch(p -> p.name().equals("b1/internal")),
            "non-shared internal place 'b1/internal' must survive as private");

        // move's output points at host shared place.
        var renamedMove = host.transitions().stream()
            .filter(t -> t.name().equals("b1/move"))
            .findFirst().orElseThrow();
        assertTrue(renamedMove.outputPlaces().contains(shared),
            "renamed move.output must merge to host shared place");
    }

    @Test
    void autoCompose_subnetWithChannel_throwsNamingChannelsAndSuggestingOverload() {
        // SubnetFixtures.retryPolicy() declares a sync channel "attempt".
        // AC-4: auto-compose must fail fast, name the offending channel,
        // and direct the caller to the explicit-binding overload.
        var retry = SubnetFixtures.retryPolicy().instantiate("r1");
        var hostBuilder = PetriNet.builder("Host");

        var ex = assertThrows(IllegalStateException.class,
            () -> hostBuilder.compose(retry));
        var msg = ex.getMessage();
        assertTrue(msg.contains("channel"),
            "exception must mention channels. Got: " + msg);
        assertTrue(msg.contains("attempt"),
            "exception must name the channel 'attempt'. Got: " + msg);
        assertTrue(msg.contains("Consumer") && msg.contains("bindChannel"),
            "exception must suggest the Consumer overload + bindChannel. Got: " + msg);
    }

    @Test
    void autoCompose_multipleSubnets_endToEnd() {
        // Producer → host place ← Consumer, all wired by identity inference.
        Place<String> pipe = Place.of("pipe", String.class);

        // Both subnets reference pipe by value-equal Place; rename them
        // separately so each gets its own prefix.
        var producerDef = SubnetDef.builder("ProdLocal")
            .place(Place.of("seed", String.class))
            .place(pipe)
            .transition(Transition.builder("emit")
                .inputs(In.one(Place.of("seed", String.class)))
                .outputs(Out.place(pipe))
                .build())
            .outputPort("out", pipe)
            .build();

        var consumerDef = SubnetDef.builder("ConsLocal")
            .place(pipe)
            .place(Place.of("sink", String.class))
            .transition(Transition.builder("eat")
                .inputs(In.one(pipe))
                .outputs(Out.place(Place.of("sink", String.class)))
                .build())
            .inputPort("in", pipe)
            .build();

        var host = PetriNet.builder("Host")
            .place(pipe)
            .compose(producerDef.instantiate("p"))
            .compose(consumerDef.instantiate("c"))
            .build();

        // Both subnets share the host "pipe" place.
        assertTrue(host.places().contains(pipe));
        // Producer's emit writes to pipe; consumer's eat reads from pipe.
        var emit = host.transitions().stream()
            .filter(t -> t.name().equals("p/emit")).findFirst().orElseThrow();
        var eat = host.transitions().stream()
            .filter(t -> t.name().equals("c/eat")).findFirst().orElseThrow();
        assertTrue(emit.outputPlaces().contains(pipe));
        assertTrue(eat.inputSpecs().stream().anyMatch(a -> a.place().equals(pipe)));
    }

    @Test
    void autoCompose_inoutPort_alsoMatchesByEquality() {
        // An InOut port should also auto-bind by Place equality.
        Place<Integer> counter = Place.of("counter", Integer.class);

        var subnet = SubnetDef.builder("Counter")
            .place(counter)
            .transition(Transition.builder("tick")
                .inputs(In.one(counter))
                .outputs(Out.place(counter))
                .build())
            .inoutPort("counter", counter)
            .build();

        var host = PetriNet.builder("Host")
            .place(counter)
            .compose(subnet.instantiate("c1"))
            .build();

        assertTrue(host.places().contains(counter));
        assertTrue(host.places().stream().noneMatch(p -> p.name().equals("c1/counter")));
    }

    @Test
    void autoCompose_emptyBody_isHarmless() {
        // A SubnetDef with no body places and no ports composes as a no-op.
        var empty = SubnetDef.builder("Empty").build();
        var host = PetriNet.builder("Host")
            .compose(empty.instantiate("e1"))
            .build();
        assertTrue(host.places().isEmpty());
        assertTrue(host.transitions().isEmpty());
    }

    @Test
    void autoCompose_twoInstances_perInstanceStateIsolation() {
        // MOD-012: two auto-composed instances of the same SubnetDef must
        // keep their internal places under disjoint prefixed names so per-
        // instance runtime state can never alias.
        Place<String> shared = Place.of("output", String.class);

        var host = PetriNet.builder("Host")
            .place(shared)
            .compose(SubnetFixtures.producer().instantiate("p1"))
            .compose(SubnetFixtures.producer().instantiate("p2"))
            .build();

        assertTrue(host.places().stream().anyMatch(p -> p.name().equals("p1/nextItem")),
            "p1's internal place must survive under its prefix");
        assertTrue(host.places().stream().anyMatch(p -> p.name().equals("p2/nextItem")),
            "p2's internal place must survive under its prefix");
        // Crucially: there is no single "nextItem" place — both instances are isolated.
        assertTrue(host.places().stream().noneMatch(p -> p.name().equals("nextItem")),
            "no un-prefixed 'nextItem' should leak across instances");
        // Both produce transitions are present, each named for its instance.
        var transitionNames = host.transitions().stream().map(Transition::name).toList();
        assertTrue(transitionNames.contains("p1/produce") && transitionNames.contains("p2/produce"),
            "both produce transitions must be present, one per instance. Got: " + transitionNames);
    }

    @Test
    void autoCompose_nestedInstance_prefixesConcatenate() {
        // MOD-013: a SubnetDef whose body itself auto-composes another
        // instance must, when auto-composed at the top level, yield flat
        // names of the form outer/inner/<original>.
        Place<String> outerOut = Place.of("out", String.class);

        // Inner: wrap the producer subnet via auto-compose. The producer's
        // "output" port carries Place.of("output", String.class), which we
        // also pre-declare on the inner builder so identity inference merges.
        var producerInner = SubnetFixtures.producer().instantiate("inner");
        var outerBody = PetriNet.builder("OuterBody")
            .place(Place.of("output", String.class))
            .compose(producerInner)
            .build();

        // Wrap outerBody as a SubnetDef and expose the merged place as port "out".
        var outerIface = Interface.builder()
            .outputPort("out", Place.of("output", String.class))
            .build();
        var outerDef = SubnetDef.fromNet(outerBody, outerIface);

        // Top-level host: auto-compose outerDef with prefix "outer". The
        // host pre-declares "output" so identity inference can merge the
        // exposed port back into a single host place.
        var host = PetriNet.builder("Host")
            .place(Place.of("output", String.class))
            .compose(outerDef.instantiate("outer"))
            .build();

        // The nested instantiation per MOD-013 yields outer/inner/<original>.
        assertTrue(host.places().stream().anyMatch(p -> p.name().equals("outer/inner/nextItem")),
            "nested prefix concatenation must produce 'outer/inner/nextItem'. Got: "
                + host.places().stream().map(Place::name).toList());
        assertTrue(host.transitions().stream().anyMatch(t -> t.name().equals("outer/inner/produce")),
            "nested prefix concatenation must produce 'outer/inner/produce'. Got: "
                + host.transitions().stream().map(Transition::name).toList());
    }

    @Test
    void autoCompose_producerToConsumer_isBoundedAndReachable() {
        // SCG verification per the lang-expert reference: confirm the
        // auto-composed producer→pipe←consumer chain is structurally sound.
        // (1) Bounded — finite state class graph.
        // (2) The sink (c/sink) is reachable from a seed token.
        Place<String> pipe = Place.of("pipe", String.class);
        Place<String> seed = Place.of("seed", String.class);
        Place<String> sink = Place.of("sink", String.class);

        var producerDef = SubnetDef.builder("ProdLocal")
            .place(seed)
            .place(pipe)
            .transition(Transition.builder("emit")
                .inputs(In.one(seed))
                .outputs(Out.place(pipe))
                .build())
            .outputPort("out", pipe)
            .build();

        var consumerDef = SubnetDef.builder("ConsLocal")
            .place(pipe)
            .place(sink)
            .transition(Transition.builder("eat")
                .inputs(In.one(pipe))
                .outputs(Out.place(sink))
                .build())
            .inputPort("in", pipe)
            .build();

        var net = PetriNet.builder("AutoComposed")
            .place(pipe)
            .compose(producerDef.instantiate("p"))
            .compose(consumerDef.instantiate("c"))
            .build();

        // Goal: the c/sink in the auto-composed net (post-prefixing).
        var sinkInNet = net.places().stream()
            .filter(p -> p.name().equals("c/sink"))
            .findFirst().orElseThrow();
        var seedInNet = net.places().stream()
            .filter(p -> p.name().equals("p/seed"))
            .findFirst().orElseThrow();

        var result = TimePetriNetAnalyzer.forNet(net)
            .initialMarking(MarkingState.builder().tokens(seedInNet, 1).build())
            .goalPlaces(sinkInNet)
            .maxClasses(100)
            .build()
            .analyze();

        assertTrue(result.isGoalLive(),
            "auto-composed producer→consumer net must let the sink token become reachable. Report:\n"
                + result.report());
    }
}
