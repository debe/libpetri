package org.libpetri.debug;

import org.junit.jupiter.api.Test;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.core.Interface;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.SubnetDef;
import org.libpetri.core.Token;
import org.libpetri.core.Transition;
import org.libpetri.event.NetEvent;
import org.libpetri.fixtures.SubnetFixtures;

import java.time.Instant;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Wire-level tests for the debug protocol's subnet-instance support per
 * {@code spec/11-modular-composition.md} <b>MOD-041</b>.
 *
 * <p>Covers:
 * <ul>
 *   <li>{@link DebugResponse.Subscribed#subnetInstances()} populated for
 *       composed nets, empty for flat nets.</li>
 *   <li>{@link DebugResponse.PlaceInfo#instancePrefix()} and
 *       {@link DebugResponse.TransitionInfo#instancePrefix()} populated from
 *       the name's prefix portion.</li>
 *   <li>{@link NetEvent} variants exposing {@code instancePrefix()} as a
 *       derived helper.</li>
 *   <li>{@link NetEventConverter} surfacing {@code instancePrefix} in the
 *       wire-facing {@link DebugResponse.NetEventInfo} details map.</li>
 * </ul>
 */
class DebugProtocolSubnetTest {

    private static final Instant NOW = Instant.parse("2026-05-09T12:00:00Z");

    /** Builds a two-instance composed pipeline: producer1 -> wire -> consumer1. */
    private PetriNet composedTwoInstanceNet() {
        var producer = SubnetFixtures.producer().instantiate("producer1");
        var consumer = SubnetFixtures.consumer().instantiate("consumer1");
        Place<String> wire = Place.of("wire", String.class);
        return PetriNet.builder("Pipeline")
            .place(wire)
            .compose(producer, Map.of("output", wire))
            .compose(consumer, Map.of("input", wire))
            .build();
    }

    /** Builds a flat (non-composed) net with no '/' in any name. */
    private PetriNet flatNet() {
        var input = Place.of("Input", String.class);
        var output = Place.of("Output", String.class);
        var t = Transition.builder("Process")
            .inputs(In.one(input))
            .outputs(Out.place(output))
            .build();
        return PetriNet.builder("FlatNet").transition(t).build();
    }

    // ============================================================
    //  MOD-041 AC#5: flat net produces empty subnetInstances list
    // ============================================================

    @Test
    void subscribed_flatNet_emptySubnetInstances() {
        var registry = new DebugSessionRegistry();
        var session = registry.register("s1", flatNet());

        var subnetInstances = session.buildSubnetInstances();

        assertTrue(subnetInstances.isEmpty(),
            "flat net (no '/' in names) must produce no subnet-instance descriptors");
    }

    // ============================================================
    //  MOD-041 AC#1, AC#2: composed net produces populated descriptors
    // ============================================================

    @Test
    void subscribed_composedNet_populatedSubnetInstances() {
        var registry = new DebugSessionRegistry();
        var session = registry.register("s1", composedTwoInstanceNet());

        var subnetInstances = session.buildSubnetInstances();

        assertEquals(2, subnetInstances.size(),
            "expected one descriptor per composed instance. Got: " + subnetInstances);

        var byPrefix = subnetInstances.stream()
            .collect(java.util.stream.Collectors.toMap(
                DebugResponse.SubnetInstanceInfo::prefix,
                d -> d));
        assertTrue(byPrefix.containsKey("producer1"),
            "expected descriptor for producer1");
        assertTrue(byPrefix.containsKey("consumer1"),
            "expected descriptor for consumer1");

        // producer1 must enumerate its single transition.
        var producerDescriptor = byPrefix.get("producer1");
        assertEquals(Set.of("producer1/produce"), producerDescriptor.transitionNames(),
            "producer1 must enumerate the renamed produce transition");
        // The internal nextItem place is part of the producer instance;
        // the merged port place ("wire") is a host place and must NOT
        // appear under producer1's exposedPlaceNames.
        assertTrue(producerDescriptor.exposedPlaceNames().contains("producer1/nextItem"),
            "producer1 exposedPlaceNames must include the internal nextItem. Got: "
                + producerDescriptor.exposedPlaceNames());
        assertFalse(producerDescriptor.exposedPlaceNames().contains("wire"),
            "host-side wire place must NOT appear under producer1");

        // consumer1 must enumerate its single transition.
        var consumerDescriptor = byPrefix.get("consumer1");
        assertEquals(Set.of("consumer1/consume"), consumerDescriptor.transitionNames());
        assertTrue(consumerDescriptor.exposedPlaceNames().contains("consumer1/consumed"),
            "consumer1 exposedPlaceNames must include the internal consumed sink. Got: "
                + consumerDescriptor.exposedPlaceNames());

        // Top-level instances have no parentPrefix.
        assertEquals(Optional.empty(), producerDescriptor.parentPrefix());
        assertEquals(Optional.empty(), consumerDescriptor.parentPrefix());
    }

    // ============================================================
    //  MOD-041 AC#4: nested instance has parentPrefix set
    // ============================================================

    @Test
    void subscribed_nestedInstance_parentPrefixSet() {
        // Build a producer subnet, compose into an outer subnet (T), then
        // instantiate T with a top-level prefix. The nested instance prefix
        // is "outer/inner" and its parentPrefix MUST be "outer".
        var producerInner = SubnetFixtures.producer().instantiate("inner");
        Place<String> outerOut = Place.of("out", String.class);
        var outerBody = PetriNet.builder("OuterBody")
            .place(outerOut)
            .compose(producerInner, Map.of("output", outerOut))
            .build();
        var outerIface = Interface.builder()
            .outputPort("out", outerOut)
            .build();
        var outerDef = SubnetDef.fromNet(outerBody, outerIface);
        var outer = outerDef.instantiate("outer");
        Place<String> hostSink = Place.of("hostSink", String.class);
        var net = PetriNet.builder("Host")
            .place(hostSink)
            .compose(outer, Map.of("out", hostSink))
            .build();

        var registry = new DebugSessionRegistry();
        var session = registry.register("nested", net);

        var subnetInstances = session.buildSubnetInstances();

        // Find the nested instance (prefix "outer/inner") — its parentPrefix
        // must be "outer".
        var nested = subnetInstances.stream()
            .filter(d -> d.prefix().equals("outer/inner"))
            .findFirst()
            .orElseThrow(() -> new AssertionError(
                "expected nested 'outer/inner' descriptor. Got prefixes: "
                    + subnetInstances.stream()
                        .map(DebugResponse.SubnetInstanceInfo::prefix).toList()));
        assertEquals(Optional.of("outer"), nested.parentPrefix(),
            "nested instance must report 'outer' as its parentPrefix per MOD-041 AC#4");
    }

    // ============================================================
    //  MOD-041 AC#3: PlaceInfo / TransitionInfo carry instancePrefix
    // ============================================================

    @Test
    void placeInfo_instancePrefix_populated() {
        var registry = new DebugSessionRegistry();
        var session = registry.register("s1", composedTwoInstanceNet());

        var structure = session.buildNetStructure();

        // For a place named "producer1/nextItem", instancePrefix must be Optional.of("producer1").
        var p = structure.places().stream()
            .filter(pi -> pi.name().equals("producer1/nextItem"))
            .findFirst()
            .orElseThrow(() -> new AssertionError("expected place 'producer1/nextItem' in structure"));
        assertEquals(Optional.of("producer1"), p.instancePrefix());
    }

    @Test
    void placeInfo_flatPlace_emptyInstancePrefix() {
        var registry = new DebugSessionRegistry();
        var session = registry.register("s1", composedTwoInstanceNet());

        var structure = session.buildNetStructure();

        // The host wire place has no '/' so instancePrefix must be empty.
        var p = structure.places().stream()
            .filter(pi -> pi.name().equals("wire"))
            .findFirst()
            .orElseThrow(() -> new AssertionError("expected place 'wire' in structure"));
        assertEquals(Optional.empty(), p.instancePrefix());
    }

    @Test
    void transitionInfo_instancePrefix_populated() {
        var registry = new DebugSessionRegistry();
        var session = registry.register("s1", composedTwoInstanceNet());

        var structure = session.buildNetStructure();

        var t = structure.transitions().stream()
            .filter(ti -> ti.name().equals("producer1/produce"))
            .findFirst()
            .orElseThrow(() -> new AssertionError(
                "expected transition 'producer1/produce' in structure. Got: "
                    + structure.transitions().stream()
                        .map(DebugResponse.TransitionInfo::name).toList()));
        assertEquals(Optional.of("producer1"), t.instancePrefix());
    }

    @Test
    void transitionInfo_flatTransition_emptyInstancePrefix() {
        var registry = new DebugSessionRegistry();
        var session = registry.register("s1", flatNet());

        var structure = session.buildNetStructure();

        var t = structure.transitions().stream()
            .filter(ti -> ti.name().equals("Process"))
            .findFirst()
            .orElseThrow();
        assertEquals(Optional.empty(), t.instancePrefix());
    }

    // ============================================================
    //  MOD-041: NetEvent.instancePrefix() derived helper
    // ============================================================

    @Test
    void netEvent_transitionStarted_instancePrefix() {
        var prefixed = new NetEvent.TransitionStarted(NOW, "buf1/enqueue", java.util.List.of());
        assertEquals(Optional.of("buf1"), prefixed.instancePrefix());

        var flat = new NetEvent.TransitionStarted(NOW, "Process", java.util.List.of());
        assertEquals(Optional.empty(), flat.instancePrefix());
    }

    @Test
    void netEvent_tokenAdded_instancePrefix() {
        var prefixed = new NetEvent.TokenAdded(NOW, "buf1/items", Token.of("hi"));
        assertEquals(Optional.of("buf1"), prefixed.instancePrefix());

        var nested = new NetEvent.TokenAdded(NOW, "outer/inner/items", Token.of("hi"));
        assertEquals(Optional.of("outer/inner"), nested.instancePrefix());

        var flat = new NetEvent.TokenAdded(NOW, "Output", Token.of("hi"));
        assertEquals(Optional.empty(), flat.instancePrefix());
    }

    // ============================================================
    //  MOD-041: NetEventConverter surfaces instancePrefix on the wire
    // ============================================================

    @Test
    void netEventConverter_emitsInstancePrefixForPrefixedEvents() {
        var prefixedTransition = new NetEvent.TransitionEnabled(NOW, "buf1/enqueue");
        var info = NetEventConverter.toEventInfo(prefixedTransition);
        assertEquals("buf1", info.details().get("instancePrefix"),
            "NetEventInfo.details must carry the derived instancePrefix per MOD-041");

        var prefixedToken = new NetEvent.TokenAdded(NOW, "buf1/items", Token.of("v"));
        var tokenInfo = NetEventConverter.toEventInfo(prefixedToken);
        assertEquals("buf1", tokenInfo.details().get("instancePrefix"));
    }

    @Test
    void netEventConverter_omitsInstancePrefixForFlatEvents() {
        var flat = new NetEvent.TransitionEnabled(NOW, "Process");
        var info = NetEventConverter.toEventInfo(flat);
        assertFalse(info.details().containsKey("instancePrefix"),
            "flat-net events must NOT add an instancePrefix entry (would bloat the wire shape)");
    }
}
