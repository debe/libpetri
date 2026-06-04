package org.libpetri.core;

import org.junit.jupiter.api.Test;
import org.libpetri.fixtures.SubnetFixtures;
import org.libpetri.runtime.BitmapNetExecutor;

import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for {@link PetriNet.Builder#compose(Instance, Map)} and
 * {@link PetriNet.Builder#compose(Instance, java.util.function.Consumer)} —
 * the eager port-merging composition operator per <b>MOD-020</b> (composition
 * operation), <b>MOD-022</b> (type compatibility), and <b>MOD-023</b>
 * (composition produces a flat net).
 *
 * <p>Channel composition (MOD-021) is implemented by a future task; the
 * {@link #compose_channelBinding_throwsUnsupported} test pins the current
 * fail-fast behaviour.
 */
class ComposeTest {

    // ============================================================
    //  MOD-020: single-port merge
    // ============================================================

    @Test
    void compose_singlePort_mergesPlace() {
        // Producer subnet: produce -> output (port).
        var producerDef = SubnetFixtures.producer();
        var producer = producerDef.instantiate("p1");

        // Host place that the output port should merge into.
        Place<String> hostSink = Place.of("hostSink", String.class);

        var host = PetriNet.builder("Host")
            .place(hostSink)
            .compose(producer, Map.of("output", hostSink))
            .build();

        // The merged net should contain hostSink but NOT the renamed
        // interface place "p1/output" (it was rewritten away).
        assertTrue(host.places().contains(hostSink),
            "host place must appear in the merged net");
        for (var p : host.places()) {
            assertNotEquals("p1/output", p.name(),
                "renamed interface place 'p1/output' must NOT survive a port merge");
        }

        // Internal renamed places of the instance flow through.
        assertTrue(host.places().stream().anyMatch(p -> p.name().equals("p1/nextItem")),
            "internal place 'p1/nextItem' must survive composition");

        // Find the renamed produce transition; its output spec must point to
        // the host place, not the renamed interface place.
        Transition rewrittenProduce = host.transitions().stream()
            .filter(t -> t.name().equals("p1/produce"))
            .findFirst()
            .orElseThrow(() -> new AssertionError("expected transition 'p1/produce' in host"));
        assertTrue(rewrittenProduce.outputPlaces().contains(hostSink),
            "produce's output arc must point at the merged host place");
        assertFalse(rewrittenProduce.outputPlaces().stream()
                .anyMatch(p -> p.name().equals("p1/output")),
            "produce must no longer reference the renamed interface place");
    }

    // ============================================================
    //  MOD-022: type compatibility
    // ============================================================

    @Test
    void compose_typeMismatch_throwsIllegalArgumentException() {
        // Producer's "output" port has token type String.
        var producer = SubnetFixtures.producer().instantiate("p1");

        // Caller binds with an Integer-typed place — must reject per MOD-022.
        Place<Integer> wrongTypePlace = Place.of("wrong", Integer.class);

        var hostBuilder = PetriNet.builder("Host");
        var ex = assertThrows(IllegalArgumentException.class, () ->
            hostBuilder.compose(producer, Map.of("output", wrongTypePlace)));
        // Message should name both types so users can fix the binding.
        assertTrue(ex.getMessage().contains("String"),
            "exception message must name the interface type. Got: " + ex.getMessage());
        assertTrue(ex.getMessage().contains("Integer"),
            "exception message must name the caller type. Got: " + ex.getMessage());
    }

    @Test
    void compose_unknownPortName_throws() {
        var producer = SubnetFixtures.producer().instantiate("p1");
        Place<String> hostPlace = Place.of("h", String.class);

        var hostBuilder = PetriNet.builder("Host");
        var ex = assertThrows(IllegalArgumentException.class, () ->
            hostBuilder.compose(producer, Map.of("doesNotExist", hostPlace)));
        assertTrue(ex.getMessage().contains("doesNotExist"),
            "exception message must name the unknown port. Got: " + ex.getMessage());
    }

    // ============================================================
    //  MOD-012 + MOD-020: per-instance internal place isolation
    // ============================================================

    @Test
    void compose_internalPlacesGetTheirOwnSlot() {
        // Two instances of the same subnet, composed into the same host net.
        // Their internal (non-merged) renamed places must remain disjoint.
        var producerDef = SubnetFixtures.producer();
        var p1 = producerDef.instantiate("p1");
        var p2 = producerDef.instantiate("p2");

        Place<String> hostSink = Place.of("hostSink", String.class);

        var host = PetriNet.builder("Host")
            .place(hostSink)
            .compose(p1, Map.of("output", hostSink))
            .compose(p2, Map.of("output", hostSink))
            .build();

        // Both instances' internal "nextItem" place must appear, distinctly.
        assertTrue(host.places().stream().anyMatch(p -> p.name().equals("p1/nextItem")),
            "instance p1's internal nextItem must be present");
        assertTrue(host.places().stream().anyMatch(p -> p.name().equals("p2/nextItem")),
            "instance p2's internal nextItem must be present");

        // Two distinct produce transitions with different prefixed names.
        long produceCount = host.transitions().stream()
            .filter(t -> t.name().endsWith("/produce"))
            .count();
        assertEquals(2, produceCount, "expected one produce transition per instance");

        // The hostSink is shared: only one (post-merge) place with that name.
        long hostSinkCount = host.places().stream()
            .filter(p -> p.name().equals("hostSink"))
            .count();
        assertEquals(1, hostSinkCount, "the merged host place must be deduped");
    }

    // ============================================================
    //  MOD-021: channel binding produces a single merged transition
    // ============================================================

    @Test
    void compose_channelBinding_mergesIntoSingleTransition() {
        // Build a subnet that exposes a channel.
        Place<String> tick = Place.of("tick", String.class);
        Transition fire = Transition.builder("fire").read(tick).build();
        var def = SubnetDef.builder("WithChannel")
            .transition(fire)
            .channel("attempt", fire)
            .build();
        var inst = def.instantiate("i1");

        // Caller-side transition that we want to fuse with the channel.
        Place<String> hostTrigger = Place.of("hostTrigger", String.class);
        Transition callerSide = Transition.builder("callerSide")
            .read(hostTrigger)
            .build();

        var host = PetriNet.builder("Host")
            .compose(inst, b -> b.bindChannel("attempt", callerSide))
            .build();

        // The renamed instance-side channel transition "i1/fire" must be gone
        // (merged into "callerSide"); the caller-side transition is present
        // exactly once. The merged transition reads from both tick (renamed)
        // and hostTrigger.
        assertFalse(host.transitions().stream().anyMatch(t -> t.name().equals("i1/fire")),
            "renamed channel transition 'i1/fire' must NOT survive the merge");
        var merged = host.transitions().stream()
            .filter(t -> t.name().equals("callerSide"))
            .findFirst()
            .orElseThrow(() -> new AssertionError("expected merged 'callerSide' transition in host"));

        assertTrue(merged.readPlaces().contains(hostTrigger),
            "merged transition must read from caller-side place 'hostTrigger'");
        assertTrue(merged.readPlaces().stream().anyMatch(p -> p.name().equals("i1/tick")),
            "merged transition must read from instance-side renamed place 'i1/tick'");
    }

    // ============================================================
    //  Typed bindings — compile-time safety smoke test
    // ============================================================

    @Test
    void compose_typedBindings_compileTimeSafe() {
        // The Consumer<ComposeBindings> overload accepts Place<T> via the
        // typed bindPort method. The wrong-type case is verified by the Java
        // compiler — there is no test we can write that fails compilation
        // and still passes at runtime, so this test only exercises the
        // happy path of the typed API.
        var producer = SubnetFixtures.producer().instantiate("p1");
        Place<String> hostSink = Place.of("hostSink", String.class);

        var host = PetriNet.builder("Host")
            .place(hostSink)
            .compose(producer, b -> b.bindPort("output", hostSink))
            .build();

        // Same structural assertions as the Map overload.
        assertTrue(host.places().contains(hostSink));
        assertTrue(host.transitions().stream().anyMatch(t -> t.name().equals("p1/produce")));

        // Verify ComposeBindings correctly recorded the port binding.
        var bindings = new ComposeBindings();
        bindings.bindPort("output", hostSink);
        assertEquals(Map.of("output", hostSink), bindings.portBindings());
        assertTrue(bindings.channelBindings().isEmpty());
    }

    // ============================================================
    //  MOD-023: end-to-end token flow through composed net
    // ============================================================

    @Test
    void compose_producerBufferConsumer_endToEnd() {
        // Bind actions on each instance so tokens actually move.
        TransitionAction copyToOutput = ctx -> {
            // Copy the single input value to the single output place.
            var inputPlace = ctx.inputPlaces().iterator().next();
            @SuppressWarnings("unchecked")
            var v = ctx.input((Place<String>) inputPlace);
            for (var op : ctx.outputPlaces()) {
                @SuppressWarnings("unchecked")
                var p = (Place<String>) op;
                ctx.output(p, v);
            }
            return CompletableFuture.completedFuture(null);
        };

        // Buffer's enqueue/dequeue actions: enqueue must copy "put" -> "items"
        // (consume slot too); dequeue must copy "items" -> "get" (and emit a
        // slot back). We drive these via explicit outputs to avoid the
        // slot-place getting an unintended copy of the data token.
        var bufferDef = SubnetFixtures.boundedBuffer(2);
        var producerDef = SubnetFixtures.producer();
        var consumerDef = SubnetFixtures.consumer();

        // We build a producer instance that emits a single fixed string.
        TransitionAction produceAction = ctx -> {
            // The produce transition consumes nextItem and emits to output.
            var inputPlaces = ctx.inputPlaces();
            @SuppressWarnings("unchecked")
            var nextItemPlace = (Place<String>) inputPlaces.iterator().next();
            var item = ctx.input(nextItemPlace);
            for (var op : ctx.outputPlaces()) {
                @SuppressWarnings("unchecked")
                var p = (Place<String>) op;
                ctx.output(p, item);
            }
            return CompletableFuture.completedFuture(null);
        };

        TransitionAction enqueueAction = ctx -> {
            // Inputs: put + slots. Output: items. Forward "put" value to "items".
            String item = null;
            for (var ip : ctx.inputPlaces()) {
                @SuppressWarnings("unchecked")
                var p = (Place<String>) ip;
                if (p.name().endsWith("/put") || p.name().equals("hostSink-PB")) {
                    // matches the host-bound port: in the merged net the put
                    // port becomes the host place, so we read from whichever
                    // input place has the data token (slot tokens are tag values).
                }
                var v = ctx.input(p);
                if (v != null && !"slot".equals(v)) {
                    item = v;
                }
            }
            // Emit data token to the items place.
            for (var op : ctx.outputPlaces()) {
                @SuppressWarnings("unchecked")
                var p = (Place<String>) op;
                ctx.output(p, item);
            }
            return CompletableFuture.completedFuture(null);
        };

        TransitionAction dequeueAction = ctx -> {
            // Input: items. Outputs: get + slots. Send data to get; "slot"
            // marker back to slots.
            var inputPlace = ctx.inputPlaces().iterator().next();
            @SuppressWarnings("unchecked")
            var ip = (Place<String>) inputPlace;
            var item = ctx.input(ip);
            for (var op : ctx.outputPlaces()) {
                @SuppressWarnings("unchecked")
                var p = (Place<String>) op;
                if (p.name().endsWith("/slots")) {
                    ctx.output(p, "slot");
                } else {
                    ctx.output(p, item);
                }
            }
            return CompletableFuture.completedFuture(null);
        };

        TransitionAction consumeAction = ctx -> {
            var inputPlace = ctx.inputPlaces().iterator().next();
            @SuppressWarnings("unchecked")
            var ip = (Place<String>) inputPlace;
            var v = ctx.input(ip);
            for (var op : ctx.outputPlaces()) {
                @SuppressWarnings("unchecked")
                var p = (Place<String>) op;
                ctx.output(p, v);
            }
            return CompletableFuture.completedFuture(null);
        };

        var producer = producerDef.instantiate("prod")
            .bindActions(Map.of("produce", produceAction));
        var buffer = bufferDef.instantiate("buf")
            .bindActions(Map.of("enqueue", enqueueAction, "dequeue", dequeueAction));
        var consumer = consumerDef.instantiate("cons")
            .bindActions(Map.of("consume", consumeAction));

        // Wire: producer.output -> buffer.put; buffer.get -> consumer.input.
        Place<String> producerToBuffer = Place.of("producerToBuffer", String.class);
        Place<String> bufferToConsumer = Place.of("bufferToConsumer", String.class);

        var host = PetriNet.builder("PBC")
            .compose(producer, b -> b.bindPort("output", producerToBuffer))
            .compose(buffer,   b -> b.bindPort("put", producerToBuffer)
                                     .bindPort("get", bufferToConsumer))
            .compose(consumer, b -> b.bindPort("input", bufferToConsumer))
            .build();

        // Resolve the renamed internal places we need to seed.
        Place<String> nextItem = (Place<String>) findPlace(host, "prod/nextItem");
        Place<String> slots = (Place<String>) findPlace(host, "buf/slots");
        Place<String> consumed = (Place<String>) findPlace(host, "cons/consumed");

        try (var executor = BitmapNetExecutor.create(host, Map.of(
            nextItem, List.of(Token.of("hello")),
            slots, List.of(Token.of("slot"), Token.of("slot"))
        ))) {
            var marking = executor.run();
            // After producer -> buffer -> consumer, the consumed sink should
            // hold the originating token.
            assertTrue(marking.hasTokens(consumed),
                "expected token to land in consumer's 'consumed' sink. Marking: " + marking);
            assertEquals("hello", marking.peekFirst(consumed).value());
        }
    }

    // ============================================================
    //  MOD-012: per-instance state isolation across compose calls
    // ============================================================

    @Test
    void compose_twoProducerInstances_perInstanceState() {
        var producerDef = SubnetFixtures.producer();
        var p1 = producerDef.instantiate("p1");
        var p2 = producerDef.instantiate("p2");

        Place<String> sink = Place.of("sink", String.class);

        var host = PetriNet.builder("TwoProducers")
            .place(sink)
            .compose(p1, Map.of("output", sink))
            .compose(p2, Map.of("output", sink))
            .build();

        // Two independent nextItem places (state isolation per MOD-012).
        Place<?> p1NextItem = findPlace(host, "p1/nextItem");
        Place<?> p2NextItem = findPlace(host, "p2/nextItem");
        assertNotEquals(p1NextItem, p2NextItem,
            "MOD-012: each instance must have its own internal place");

        // Two produce transitions (one per instance) — verifies that adding
        // both instances did not collapse into a single transition.
        Transition p1Produce = findTransition(host, "p1/produce");
        Transition p2Produce = findTransition(host, "p2/produce");
        assertNotSame(p1Produce, p2Produce);

        // p1's produce must consume from p1's nextItem (not p2's).
        assertTrue(p1Produce.inputPlaces().contains(p1NextItem));
        assertFalse(p1Produce.inputPlaces().contains(p2NextItem));
        assertTrue(p2Produce.inputPlaces().contains(p2NextItem));
        assertFalse(p2Produce.inputPlaces().contains(p1NextItem));

        // Both produce transitions must emit to the merged host sink.
        assertTrue(p1Produce.outputPlaces().contains(sink));
        assertTrue(p2Produce.outputPlaces().contains(sink));
    }

    // ============================================================
    //  MOD-031: action place resolution under composition
    //  (actions that hardcode DECLARED place constants)
    // ============================================================

    @Test
    void compose_hardcodedAction_underBindPort_fires_MOD031() {
        // Declared place constants the action closes over (author-time identity).
        Place<String> reqDecl  = Place.of("reqDecl",  String.class);
        Place<String> respDecl = Place.of("respDecl", String.class);

        // Action hardcodes the DECLARED places — NOT port-agnostic discovery.
        TransitionAction call = ctx -> {
            ctx.output(respDecl, ctx.input(reqDecl) + "!");
            return CompletableFuture.completedFuture(null);
        };
        Transition step = Transition.builder("call")
            .inputs(Arc.In.one(reqDecl))
            .outputs(Arc.Out.place(respDecl))
            .action(call)
            .build();
        SubnetDef<Void> def = SubnetDef.builder("Step")
            .transition(step)
            .inputPort("in", reqDecl)
            .outputPort("out", respDecl)
            .build();

        Place<String> REQ  = Place.of("REQ",  String.class);
        Place<String> RESP = Place.of("RESP", String.class);

        var net = PetriNet.builder("h")
            .place(REQ).place(RESP)
            .compose(def.instantiate("probe"),
                     b -> b.bindPort("in", REQ).bindPort("out", RESP))
            .build();

        // MOD-031 AC#5: place-set discovery returns the ACTUAL composed places,
        // never the declared constants — port-agnostic actions stay valid.
        Transition composed = findTransition(net, "probe/call");
        assertTrue(composed.inputPlaces().contains(REQ));
        assertTrue(composed.outputPlaces().contains(RESP));
        assertFalse(composed.inputPlaces().contains(reqDecl));
        assertFalse(composed.outputPlaces().contains(respDecl));

        try (var executor = BitmapNetExecutor.create(net, Map.of(REQ, List.of(Token.of("x"))))) {
            var marking = executor.run();
            assertTrue(marking.hasTokens(RESP),
                "hardcoded-declared-place action must fire and produce on the bound RESP place (MOD-031). Marking: " + marking);
            assertEquals("x!", marking.peekFirst(RESP).value());
        }
    }

    @Test
    void compose_xorBranchSelection_hardcoded_MOD031() {
        Place<String> inDecl = Place.of("inDecl", String.class);
        Place<String> aDecl  = Place.of("aDecl",  String.class);
        Place<String> bDecl  = Place.of("bDecl",  String.class);

        // XOR action selects the 'a' branch by its DECLARED constant.
        TransitionAction branch = ctx -> {
            ctx.output(aDecl, "via-a:" + ctx.input(inDecl));
            return CompletableFuture.completedFuture(null);
        };
        Transition route = Transition.builder("route")
            .inputs(Arc.In.one(inDecl))
            .outputs(Arc.Out.xor(aDecl, bDecl))
            .action(branch)
            .build();
        SubnetDef<Void> def = SubnetDef.builder("Router")
            .transition(route)
            .inputPort("in", inDecl)
            .outputPort("a", aDecl)
            .outputPort("b", bDecl)
            .build();

        Place<String> REQ = Place.of("REQ", String.class);
        Place<String> A   = Place.of("A",   String.class);
        Place<String> B   = Place.of("B",   String.class);

        var net = PetriNet.builder("h")
            .place(REQ).place(A).place(B)
            .compose(def.instantiate("r"),
                     b -> b.bindPort("in", REQ).bindPort("a", A).bindPort("b", B))
            .build();

        try (var executor = BitmapNetExecutor.create(net, Map.of(REQ, List.of(Token.of("go"))))) {
            var marking = executor.run();
            assertEquals(1, marking.tokenCount(A),
                "MOD-031: ctx.output(aDecl) on Out.xor(a,b) must produce exactly one token on the actual 'A'");
            assertEquals(0, marking.tokenCount(B),
                "the unselected XOR branch 'B' must stay empty (validator satisfied)");
            assertEquals("via-a:go", marking.peekFirst(A).value());
        }
    }

    @Test
    void compose_nestedInstance_resolvesDoublyPrefixed_MOD013_MOD031() {
        // Inner subnet: action hardcodes declared reqDecl (input) and the
        // internal xDecl sink (output).
        Place<String> reqDecl = Place.of("reqDecl", String.class);
        Place<String> xDecl   = Place.of("xDecl",   String.class);

        TransitionAction emit = ctx -> {
            ctx.output(xDecl, ctx.input(reqDecl));
            return CompletableFuture.completedFuture(null);
        };
        Transition tEmit = Transition.builder("emit")
            .inputs(Arc.In.one(reqDecl))
            .outputs(Arc.Out.place(xDecl))
            .action(emit)
            .build();
        SubnetDef<Void> innerDef = SubnetDef.builder("Inner")
            .place(xDecl)
            .transition(tEmit)
            .inputPort("in", reqDecl)
            .build();

        // Compose inner (prefix "inner") into a body net, exposing sIn as the bound input.
        Place<String> sIn = Place.of("sIn", String.class);
        PetriNet sBody = PetriNet.builder("Sbody")
            .place(sIn)
            .compose(innerDef.instantiate("inner"), b -> b.bindPort("in", sIn))
            .build();

        // Retrofit the composed body as a subnet S, re-exposing sIn as port "sin".
        SubnetDef<Void> sDef = SubnetDef.fromNet(sBody,
            Interface.builder().inputPort("sin", sIn).build());

        // Instantiate S as "outer" and compose into the host, binding sin -> hostReq.
        Place<String> hostReq = Place.of("hostReq", String.class);
        PetriNet host = PetriNet.builder("host")
            .place(hostReq)
            .compose(sDef.instantiate("outer"), b -> b.bindPort("sin", hostReq))
            .build();

        @SuppressWarnings("unchecked")
        Place<String> doublyPrefixed = (Place<String>) findPlace(host, "outer/inner/xDecl");

        try (var executor = BitmapNetExecutor.create(host, Map.of(hostReq, List.of(Token.of("deep"))))) {
            var marking = executor.run();
            assertTrue(marking.hasTokens(doublyPrefixed),
                "MOD-013: nested hardcoded action must resolve declared xDecl to 'outer/inner/xDecl'. Marking: " + marking);
            assertEquals("deep", marking.peekFirst(doublyPrefixed).value());
        }
    }

    @Test
    void handWritten_and_flatNet_haveIdentityAlias_MOD031_MOD025() {
        Place<String> a = Place.of("a", String.class);
        Place<String> b = Place.of("b", String.class);
        Transition t = Transition.builder("t")
            .inputs(Arc.In.one(a))
            .outputs(Arc.Out.place(b))
            .build();
        assertTrue(t.placeAlias().isEmpty(),
            "MOD-031: a hand-written transition's correspondence is the identity (empty)");

        var net = PetriNet.builder("flat").transition(t).build();
        for (var tr : net.transitions()) {
            assertTrue(tr.placeAlias().isEmpty(),
                "MOD-031: a non-composed flat-net transition carries an empty (identity) alias");
        }
    }

    @Test
    void compose_structurallyEqualToHandWritten_aliasIsOffStructure_MOD031_MOD023() {
        // AC#6: a composed net whose action hardcodes DECLARED places is
        // structurally indistinguishable from the equivalent hand-written flat
        // net (place index, transition names, arc topology). The declared→actual
        // correspondence sits on the action/binding side of [MOD-023] — it is
        // present on the composed transition yet absent from the structure.
        Place<String> reqDecl  = Place.of("reqDecl",  String.class);
        Place<String> respDecl = Place.of("respDecl", String.class);

        TransitionAction call = ctx -> {
            ctx.output(respDecl, ctx.input(reqDecl) + "!");
            return CompletableFuture.completedFuture(null);
        };
        Transition step = Transition.builder("call")
            .inputs(Arc.In.one(reqDecl))
            .outputs(Arc.Out.place(respDecl))
            .action(call)
            .build();
        SubnetDef<Void> def = SubnetDef.builder("Step")
            .transition(step)
            .inputPort("in", reqDecl)
            .outputPort("out", respDecl)
            .build();

        Place<String> REQ  = Place.of("REQ",  String.class);
        Place<String> RESP = Place.of("RESP", String.class);

        var composed = PetriNet.builder("h")
            .place(REQ).place(RESP)
            .compose(def.instantiate("probe"),
                     b -> b.bindPort("in", REQ).bindPort("out", RESP))
            .build();

        // The equivalent hand-written flat net: same final place set, same
        // transition name "probe/call", same REQ → RESP arc topology, no action.
        var handWritten = PetriNet.builder("h")
            .place(REQ).place(RESP)
            .transition(Transition.builder("probe/call")
                .inputs(Arc.In.one(REQ))
                .outputs(Arc.Out.place(RESP))
                .build())
            .build();

        // Structural equivalence per [MOD-023]: place index, transition names,
        // and per-transition arc topology match the hand-written net.
        assertEquals(handWritten.places(), composed.places(),
            "place set must match the hand-written net");
        assertEquals(
            handWritten.transitions().stream().map(Transition::name).collect(java.util.stream.Collectors.toSet()),
            composed.transitions().stream().map(Transition::name).collect(java.util.stream.Collectors.toSet()),
            "transition names must match the hand-written net");

        Transition composedT = findTransition(composed,   "probe/call");
        Transition handT     = findTransition(handWritten, "probe/call");
        assertEquals(handT.inputPlaces(),  composedT.inputPlaces(),
            "input arc topology must match the hand-written net");
        assertEquals(handT.outputPlaces(), composedT.outputPlaces(),
            "output arc topology must match the hand-written net");

        // ...yet the correspondence is OFF-structure: the composed transition
        // carries exactly the declared→actual alias, the hand-written one is empty.
        assertEquals(Map.of(reqDecl, REQ, respDecl, RESP), composedT.placeAlias(),
            "MOD-031: composed transition carries the declared→actual correspondence");
        assertTrue(handT.placeAlias().isEmpty(),
            "MOD-031: the hand-written equivalent carries the identity (empty) correspondence");
    }

    // ============================================================
    //  Helpers
    // ============================================================

    private static Place<?> findPlace(PetriNet net, String name) {
        for (var p : net.places()) {
            if (p.name().equals(name)) return p;
        }
        throw new AssertionError("no place named '" + name + "' in net '" + net.name()
            + "'. Places: " + net.places());
    }

    private static Transition findTransition(PetriNet net, String name) {
        for (var t : net.transitions()) {
            if (t.name().equals(name)) return t;
        }
        throw new AssertionError("no transition named '" + name + "' in net '" + net.name()
            + "'. Transitions: " + net.transitions());
    }
}
