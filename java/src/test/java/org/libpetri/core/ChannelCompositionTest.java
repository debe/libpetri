package org.libpetri.core;

import org.junit.jupiter.api.Test;
import org.libpetri.core.internal.SubnetRewriter;
import org.libpetri.fixtures.SubnetFixtures;
import org.libpetri.runtime.BitmapNetExecutor;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for synchronous-channel composition per <b>MOD-021</b>: the
 * caller-side transition and the instance-side renamed channel transition
 * fuse into a single merged transition in the composed flat net.
 *
 * <p>Coverage:
 * <ul>
 *   <li>Arc-union semantics across all arc kinds (input, read, output,
 *       inhibitor, reset).</li>
 *   <li>Dedup via record equality on shared places.</li>
 *   <li>Caller-wins identity, name, priority.</li>
 *   <li>Timing resolution: caller-wins on Immediate, instance-wins on
 *       caller-Immediate, equal collapse, conflict throws.</li>
 *   <li>Action composition: sequential caller-then-instance, null-safety,
 *       both-null falls back to passthrough.</li>
 *   <li>End-to-end retry-policy fixture: composing into a host net wires
 *       the retry-policy logic into the host's call site, observable via
 *       the executor.</li>
 * </ul>
 */
class ChannelCompositionTest {

    // ============================================================
    //  Arc-union semantics
    // ============================================================

    @Test
    void channelMerge_unionsArcsFromBothSides() {
        Place<String> a = Place.of("a", String.class);
        Place<String> b = Place.of("b", String.class);

        Transition caller = Transition.builder("merged")
            .read(a)
            .build();
        Transition instance = Transition.builder("instanceSide")
            .read(b)
            .build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");

        assertEquals("merged", merged.name(), "caller-wins identity");
        assertTrue(merged.readPlaces().contains(a),
            "merged transition must read caller-side place 'a'");
        assertTrue(merged.readPlaces().contains(b),
            "merged transition must read instance-side place 'b'");
        assertEquals(2, merged.reads().size(), "no extra arcs introduced");
    }

    @Test
    void channelMerge_unionsInputArcs() {
        Place<String> a = Place.of("a", String.class);
        Place<String> b = Place.of("b", String.class);

        Transition caller = Transition.builder("merged")
            .inputs(Arc.In.one(a))
            .build();
        Transition instance = Transition.builder("instanceSide")
            .inputs(Arc.In.one(b))
            .build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");

        assertEquals(2, merged.inputSpecs().size(), "input arcs from both sides survive");
        assertTrue(merged.inputPlaces().contains(a));
        assertTrue(merged.inputPlaces().contains(b));
    }

    @Test
    void channelMerge_unionsInhibitorReadResetArcs() {
        Place<String> inh1 = Place.of("inh1", String.class);
        Place<String> inh2 = Place.of("inh2", String.class);
        Place<String> rd1  = Place.of("rd1",  String.class);
        Place<String> rd2  = Place.of("rd2",  String.class);
        Place<String> rs1  = Place.of("rs1",  String.class);
        Place<String> rs2  = Place.of("rs2",  String.class);

        Transition caller = Transition.builder("merged")
            .inhibitor(inh1)
            .read(rd1)
            .reset(rs1)
            .build();
        Transition instance = Transition.builder("instanceSide")
            .inhibitor(inh2)
            .read(rd2)
            .reset(rs2)
            .build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");

        assertEquals(2, merged.inhibitors().size());
        assertEquals(2, merged.reads().size());
        assertEquals(2, merged.resets().size());
    }

    @Test
    void channelMerge_dedupesIdenticalArcs() {
        // Both sides reference the same shared place via the same arc kind.
        Place<String> shared = Place.of("shared", String.class);

        Transition caller = Transition.builder("merged")
            .read(shared)
            .build();
        Transition instance = Transition.builder("instanceSide")
            .read(shared)
            .build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");

        // Arc.Read<T> is a record, so the two read arcs are equal -> deduped.
        assertEquals(1, merged.reads().size(),
            "identical arcs to the same place are deduped by record equality");
        assertTrue(merged.readPlaces().contains(shared));
    }

    @Test
    void channelMerge_samePlaceInputArcs_mergeAdditively() {
        // MOD-021 AC6: Input(One) from both sides on one place sums, it does
        // not dedupe — the merged transition consumes one token per side.
        Place<String> shared = Place.of("shared", String.class);

        Transition caller = Transition.builder("merged")
            .inputs(Arc.In.one(shared))
            .build();
        Transition instance = Transition.builder("instanceSide")
            .inputs(Arc.In.one(shared))
            .build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");

        assertEquals(List.of(new Arc.In.Exactly(shared, 2)), merged.inputSpecs(),
            "one() + one() on a shared place must merge to exactly(2) (MOD-021 AC6)");
    }

    @Test
    void channelMerge_unsummableInputCardinalities_rejected() {
        // MOD-021 AC8: One + All on one place has no additive merge.
        Place<String> shared = Place.of("shared", String.class);

        Transition caller = Transition.builder("merged")
            .inputs(Arc.In.one(shared))
            .build();
        Transition instance = Transition.builder("instanceSide")
            .inputs(Arc.In.all(shared))
            .build();

        var ex = assertThrows(IllegalArgumentException.class,
            () -> SubnetRewriter.mergeTransitions(caller, instance, "merged"));
        assertTrue(ex.getMessage().contains("'merged'"),
            "exception must name the merge seam. Got: " + ex.getMessage());
        assertTrue(ex.getMessage().contains("'shared'"),
            "exception must name the place. Got: " + ex.getMessage());
        assertTrue(ex.getMessage().contains("one()") && ex.getMessage().contains("all()"),
            "exception must name both arc cardinalities. Got: " + ex.getMessage());
    }

    @Test
    void channelMerge_conflictingArcKindsOnOnePlace_rejected() {
        // MOD-021 AC7: Input on one side, Reset on the other — no coherent merge.
        Place<String> shared = Place.of("shared", String.class);

        Transition caller = Transition.builder("merged")
            .inputs(Arc.In.one(shared))
            .build();
        Transition instance = Transition.builder("instanceSide")
            .reset(shared)
            .build();

        var ex = assertThrows(IllegalArgumentException.class,
            () -> SubnetRewriter.mergeTransitions(caller, instance, "merged"));
        assertTrue(ex.getMessage().contains("'shared'"),
            "exception must name the place. Got: " + ex.getMessage());
        assertTrue(ex.getMessage().contains("input") && ex.getMessage().contains("reset"),
            "exception must name both arc kinds. Got: " + ex.getMessage());
    }

    @Test
    void channelMerge_unionsOutputSpecs_intoAnd() {
        Place<String> qCaller = Place.of("qCaller", String.class);
        Place<String> qInstance = Place.of("qInstance", String.class);

        Transition caller = Transition.builder("merged")
            .outputs(Arc.Out.place(qCaller))
            .build();
        Transition instance = Transition.builder("instanceSide")
            .outputs(Arc.Out.place(qInstance))
            .build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");

        // Both output places should be present in the merged transition's
        // declared output set (the underlying spec is And(caller, instance)).
        assertTrue(merged.outputPlaces().contains(qCaller),
            "caller-side output place must survive");
        assertTrue(merged.outputPlaces().contains(qInstance),
            "instance-side output place must survive");
    }

    @Test
    void channelMerge_outputSpecsOnlyOneSide_thatSideWins() {
        Place<String> qCaller = Place.of("qCaller", String.class);

        Transition caller = Transition.builder("merged")
            .outputs(Arc.Out.place(qCaller))
            .build();
        Transition instance = Transition.builder("instanceSide")
            .build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");

        assertNotNull(merged.outputSpec(), "caller-only output spec must survive");
        assertTrue(merged.outputPlaces().contains(qCaller));
    }

    // ============================================================
    //  Identity, priority, timing
    // ============================================================

    @Test
    void channelMerge_callerSidePriorityWins() {
        Transition caller = Transition.builder("merged").priority(5).build();
        Transition instance = Transition.builder("instanceSide").priority(10).build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");

        assertEquals(5, merged.priority(), "MOD-021: caller-side priority wins");
    }

    @Test
    void channelMerge_callerSideTimingWins_whenInstanceImmediate() {
        Transition caller = Transition.builder("merged")
            .timing(Timing.delayed(Duration.ofMillis(50)))
            .build();
        Transition instance = Transition.builder("instanceSide")
            .timing(Timing.immediate())
            .build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");

        assertEquals(Timing.delayed(Duration.ofMillis(50)), merged.timing(),
            "non-Immediate caller wins over Immediate instance");
    }

    @Test
    void channelMerge_instanceSideTimingWins_whenCallerImmediate() {
        Transition caller = Transition.builder("merged")
            .timing(Timing.immediate())
            .build();
        Transition instance = Transition.builder("instanceSide")
            .timing(Timing.delayed(Duration.ofMillis(75)))
            .build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");

        assertEquals(Timing.delayed(Duration.ofMillis(75)), merged.timing(),
            "non-Immediate instance wins over Immediate caller");
    }

    @Test
    void channelMerge_bothImmediate_resultImmediate() {
        Transition caller = Transition.builder("merged")
            .timing(Timing.immediate())
            .build();
        Transition instance = Transition.builder("instanceSide")
            .timing(Timing.immediate())
            .build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");

        assertInstanceOf(Timing.Immediate.class, merged.timing(),
            "both Immediate -> Immediate per MOD-021");
    }

    @Test
    void channelMerge_equalNonImmediateTimings_collapse() {
        Transition caller = Transition.builder("merged")
            .timing(Timing.delayed(Duration.ofMillis(50)))
            .build();
        Transition instance = Transition.builder("instanceSide")
            .timing(Timing.delayed(Duration.ofMillis(50)))
            .build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");

        assertEquals(Timing.delayed(Duration.ofMillis(50)), merged.timing(),
            "equal non-Immediate timings collapse to a single value");
    }

    @Test
    void channelMerge_conflictingTimings_throws() {
        Transition caller = Transition.builder("merged")
            .timing(Timing.delayed(Duration.ofMillis(50)))
            .build();
        Transition instance = Transition.builder("instanceSide")
            .timing(Timing.delayed(Duration.ofMillis(100)))
            .build();

        var ex = assertThrows(IllegalArgumentException.class, () ->
            SubnetRewriter.mergeTransitions(caller, instance, "attempt"));

        // The message must name the channel and both timings so users can
        // resolve the conflict explicitly per MOD-021.
        assertTrue(ex.getMessage().contains("attempt"),
            "exception must name the channel/merged-name. Got: " + ex.getMessage());
        assertTrue(ex.getMessage().contains("PT0.05S")
                || ex.getMessage().contains("Delayed"),
            "exception must describe the caller timing. Got: " + ex.getMessage());
        assertTrue(ex.getMessage().contains("PT0.1S")
                || ex.getMessage().contains("Delayed"),
            "exception must describe the instance timing. Got: " + ex.getMessage());
    }

    // ============================================================
    //  Action composition
    // ============================================================

    @Test
    void channelMerge_actionsRunSequentially() throws Exception {
        var calls = new ArrayList<String>();

        TransitionAction callerAction = ctx -> {
            calls.add("caller");
            return CompletableFuture.completedFuture(null);
        };
        TransitionAction instanceAction = ctx -> {
            calls.add("instance");
            return CompletableFuture.completedFuture(null);
        };

        Transition caller = Transition.builder("merged").action(callerAction).build();
        Transition instance = Transition.builder("instanceSide").action(instanceAction).build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");

        // Drive the merged action with a stub TransitionContext built from
        // the merged transition's own structure (no inputs/outputs declared,
        // so the context simply provides empty input/output containers).
        var ctx = new TransitionContext(merged, new TokenInput(), new TokenOutput());
        var stage = merged.action().execute(ctx);
        stage.toCompletableFuture().get();

        assertEquals(List.of("caller", "instance"), calls,
            "MOD-021: caller-side action runs first, then instance-side");
    }

    @Test
    void channelMerge_singleNullAction_noThrow() throws Exception {
        var instanceCalls = new AtomicInteger();
        TransitionAction instanceAction = ctx -> {
            instanceCalls.incrementAndGet();
            return CompletableFuture.completedFuture(null);
        };

        // Use SubnetRewriter.composeActions directly to exercise the null branch
        // — Transition.Builder always defaults action to passthrough(), so there
        // is no way to construct a Transition with null action at the builder level.
        var composed = SubnetRewriter.composeActions(null, instanceAction);
        assertSame(instanceAction, composed,
            "single non-null side returned by reference (no extra wrapping)");

        var ctx = new TransitionContext(
            Transition.builder("t").build(), new TokenInput(), new TokenOutput());
        composed.execute(ctx).toCompletableFuture().get();
        assertEquals(1, instanceCalls.get());
    }

    @Test
    void channelMerge_bothNullAction_returnsNull() {
        var composed = SubnetRewriter.composeActions(null, null);
        assertNull(composed,
            "both null -> null, so the caller (mergeTransitions) leaves the builder default in place");
    }

    @Test
    void channelMerge_singlePassthroughAction_returnsOtherSideByReference() throws Exception {
        var calls = new AtomicInteger();
        TransitionAction instanceAction = ctx -> {
            calls.incrementAndGet();
            return CompletableFuture.completedFuture(null);
        };

        assertSame(instanceAction,
            SubnetRewriter.composeActions(TransitionAction.passthrough(), instanceAction),
            "passthrough on the caller side collapses away (CORE-043 needs the survivor unwrapped)");
        assertSame(instanceAction,
            SubnetRewriter.composeActions(instanceAction, TransitionAction.passthrough()),
            "and on the instance side too");

        var ctx = new TransitionContext(
            Transition.builder("t").build(), new TokenInput(), new TokenOutput());
        SubnetRewriter.composeActions(TransitionAction.passthrough(), instanceAction)
            .execute(ctx).toCompletableFuture().get();
        assertEquals(1, calls.get(), "the surviving side still runs exactly once");
    }

    @Test
    void channelMerge_bothPassthroughAction_compositionStillRuns() throws Exception {
        // Both sides' actions are the default passthrough; the merge must yield the singleton
        // itself, not a lambda wrapping it — otherwise CORE-043 stops seeing merged transitions.
        Transition caller = Transition.builder("merged").build();
        Transition instance = Transition.builder("instanceSide").build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");
        assertTrue(TransitionAction.isPassthrough(merged.action()),
            "both-passthrough must collapse to the singleton");

        var ctx = new TransitionContext(merged, new TokenInput(), new TokenOutput());
        // Should complete without throwing.
        merged.action().execute(ctx).toCompletableFuture().get();
    }

    /**
     * The collapse is load-bearing: a merged transition that gains an output spec from one side
     * and passthrough from the other must still be rejected at compile time.
     */
    @Test
    void channelMerge_mergedPassthroughWithOutputSpec_isRejectedAtCompileTime() {
        Place<String> in = Place.of("in", String.class);
        Place<String> out = Place.of("out", String.class);

        Transition caller = Transition.builder("merged").inputs(Arc.In.one(in)).build();
        Transition instance = Transition.builder("instanceSide").outputs(Arc.Out.place(out)).build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");
        var net = PetriNet.builder("Merged").transitions(merged).build();

        var ex = assertThrows(IllegalStateException.class,
            () -> org.libpetri.runtime.CompiledNet.compile(net));
        assertTrue(ex.getMessage().contains("'merged'"), ex.getMessage());
    }

    // ============================================================
    //  ν-net match + declared→actual alias carry (NU-060 / MOD-031)
    // ============================================================

    @Test
    void channelMerge_carriesOneSidedMatchSpec() {
        Place<String> a = Place.of("branchA", String.class);
        Place<String> b = Place.of("branchB", String.class);

        Transition caller = Transition.builder("join")
            .inputs(Arc.In.one(a), Arc.In.one(b))
            .match(MatchSpec.builder()
                .key(a, (String s) -> NameId.of(s))
                .key(b, (String s) -> NameId.of(s))
                .build())
            .build();
        Transition instance = Transition.builder("instanceSide").build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "join");

        assertNotNull(merged.matchSpec(),
            "NU-060: the merge must not silently drop the caller-side ν-net match");
        assertTrue(merged.matchSpec().correlates(a), "match still correlates branchA");
        assertTrue(merged.matchSpec().correlates(b), "match still correlates branchB");
    }

    @Test
    void channelMerge_carriesInstanceSideMatchSpec() {
        Place<String> a = Place.of("branchA", String.class);
        Place<String> b = Place.of("branchB", String.class);

        Transition caller = Transition.builder("join").build();
        Transition instance = Transition.builder("instanceSide")
            .inputs(Arc.In.one(a), Arc.In.one(b))
            .match(MatchSpec.builder()
                .key(a, (String s) -> NameId.of(s))
                .key(b, (String s) -> NameId.of(s))
                .build())
            .build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "join");

        assertNotNull(merged.matchSpec(),
            "NU-060: a match on the instance side must also survive the merge");
        assertTrue(merged.matchSpec().correlates(a));
        assertTrue(merged.matchSpec().correlates(b));
    }

    @Test
    void channelMerge_bothSidesCarryMatch_throws() {
        Place<String> a = Place.of("branchA", String.class);
        Place<String> b = Place.of("branchB", String.class);
        Place<String> c = Place.of("branchC", String.class);
        Place<String> d = Place.of("branchD", String.class);

        Transition caller = Transition.builder("join")
            .inputs(Arc.In.one(a), Arc.In.one(b))
            .match(MatchSpec.builder()
                .key(a, (String s) -> NameId.of(s))
                .key(b, (String s) -> NameId.of(s))
                .build())
            .build();
        Transition instance = Transition.builder("instanceSide")
            .inputs(Arc.In.one(c), Arc.In.one(d))
            .match(MatchSpec.builder()
                .key(c, (String s) -> NameId.of(s))
                .key(d, (String s) -> NameId.of(s))
                .build())
            .build();

        // NU-060: two independent correlations cannot be silently fused — reject.
        var ex = assertThrows(IllegalArgumentException.class, () ->
            SubnetRewriter.mergeTransitions(caller, instance, "attempt"));
        assertTrue(ex.getMessage().contains("attempt"),
            "exception must name the channel. Got: " + ex.getMessage());
        assertTrue(ex.getMessage().contains("NU-060"),
            "exception should cite NU-060. Got: " + ex.getMessage());
    }

    @Test
    void channelMerge_carriesPlaceAliasFromBothSides() {
        Place<String> declaredA = Place.of("declaredA", String.class);
        Place<String> actualA   = Place.of("host/actualA", String.class);
        Place<String> declaredB = Place.of("declaredB", String.class);
        Place<String> actualB   = Place.of("host/actualB", String.class);

        Transition caller = Transition.builder("merged")
            .placeAlias(Map.of(declaredA, actualA))
            .build();
        Transition instance = Transition.builder("instanceSide")
            .placeAlias(Map.of(declaredB, actualB))
            .build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "merged");

        assertEquals(actualA, merged.placeAlias().get(declaredA),
            "MOD-031: caller-side declared→actual alias survives the merge");
        assertEquals(actualB, merged.placeAlias().get(declaredB),
            "MOD-031: instance-side declared→actual alias survives the merge");
    }

    @Test
    void channelMerge_conflictingPlaceAlias_throws() {
        Place<String> declared = Place.of("declaredX", String.class);
        Place<String> actualA  = Place.of("host/a", String.class);
        Place<String> actualB  = Place.of("host/b", String.class);

        // Same declared place bound to two different actual places across the
        // two fused sides — an ambiguous MOD-031 correspondence, rejected.
        Transition caller = Transition.builder("merged")
            .placeAlias(Map.of(declared, actualA))
            .build();
        Transition instance = Transition.builder("instanceSide")
            .placeAlias(Map.of(declared, actualB))
            .build();

        var ex = assertThrows(IllegalArgumentException.class, () ->
            SubnetRewriter.mergeTransitions(caller, instance, "attempt"));
        assertTrue(ex.getMessage().contains("attempt"),
            "exception must name the channel. Got: " + ex.getMessage());
        assertTrue(ex.getMessage().contains("MOD-031"),
            "exception should cite MOD-031. Got: " + ex.getMessage());
    }

    @Test
    void channelMerge_mergedMatchJoin_correlatesByName_notFifo() {
        // Behavioral regression for the reported production symptom: a matched
        // join fused through the channel-merge path must still pair tokens by
        // name — not by FIFO arrival order (which would serve a stale answer).
        Place<String> a = Place.of("branchA", String.class);
        Place<String> b = Place.of("branchB", String.class);
        Place<String> out = Place.of("merged", String.class);

        Transition caller = Transition.builder("join")
            .inputs(Arc.In.one(a), Arc.In.one(b))
            .match(MatchSpec.builder()
                .key(a, (String s) -> NameId.of(s))
                .key(b, (String s) -> NameId.of(s))
                .build())
            .outputs(Arc.Out.place(out))
            .action(ctx -> {
                ctx.output(out, ctx.input(a) + "+" + ctx.input(b));
                return CompletableFuture.completedFuture(null);
            })
            .build();
        Transition instance = Transition.builder("instanceSide").build();

        var merged = SubnetRewriter.mergeTransitions(caller, instance, "join");
        var net = PetriNet.builder("mergedNuJoin").transitions(merged).build();

        // Interleaved timestamps: FIFO would cross-pair (X+Y / Y+X); a live
        // match yields the correlated X+X / Y+Y.
        var initial = Map.<Place<?>, List<Token<?>>>of(
            a, List.of(new Token<>("X", Instant.ofEpochMilli(0)),
                       new Token<>("Y", Instant.ofEpochMilli(1))),
            b, List.of(new Token<>("Y", Instant.ofEpochMilli(0)),
                       new Token<>("X", Instant.ofEpochMilli(1)))
        );

        try (var executor = BitmapNetExecutor.create(net, initial)) {
            var marking = executor.run();
            var vals = new ArrayList<String>();
            for (var tk : marking.peekTokens(out)) vals.add(tk.value());
            java.util.Collections.sort(vals);
            assertEquals(List.of("X+X", "Y+Y"), vals,
                "merged join must correlate by name (regression: dropped match FIFO-pairs to X+Y/Y+X)");
        }
    }

    // ============================================================
    //  End-to-end with the retryPolicy fixture (MOD-021 + EXEC-001)
    // ============================================================

    @Test
    void channelMerge_endToEnd_retryPolicy() {
        // The retry-policy subnet exposes one channel "attempt"; binding it
        // to the host's "attemptHttp" transition fuses both sides — firing
        // the host transition also runs the retry-policy logic atomically.
        var retryDef = SubnetFixtures.retryPolicy();

        // Bind an instance-side action that increments a counter when the
        // channel fires — i.e., the per-attempt retry-policy hook.
        var attemptCounter = new AtomicInteger();
        TransitionAction attemptAction = ctx -> {
            attemptCounter.incrementAndGet();
            // The instance-side transition's output spec emits to attemptCount;
            // produce a synthetic value so the merged firing is well-formed.
            for (var op : ctx.outputPlaces()) {
                if (op.name().endsWith("/attemptCount")) {
                    @SuppressWarnings("unchecked")
                    var p = (Place<String>) op;
                    ctx.output(p, "tick");
                }
            }
            return CompletableFuture.completedFuture(null);
        };
        var retryInst = retryDef.instantiate("rp")
            .bindActions(Map.of("attempt", attemptAction));

        // Host net: a "trigger" place enables an "attemptHttp" transition.
        Place<String> trigger = Place.of("trigger", String.class);
        Place<String> hostResult = Place.of("hostResult", String.class);

        var hostCalls = new AtomicInteger();
        TransitionAction hostAction = ctx -> {
            hostCalls.incrementAndGet();
            // Host action also writes a result so the test can observe its firing.
            for (var op : ctx.outputPlaces()) {
                if (op.name().equals("hostResult")) {
                    @SuppressWarnings("unchecked")
                    var p = (Place<String>) op;
                    ctx.output(p, "ok");
                }
            }
            return CompletableFuture.completedFuture(null);
        };
        Transition attemptHttp = Transition.builder("attemptHttp")
            .inputs(Arc.In.one(trigger))
            .outputs(Arc.Out.place(hostResult))
            .action(hostAction)
            .build();

        var host = PetriNet.builder("HostWithRetry")
            .compose(retryInst, b -> b.bindChannel("attempt", attemptHttp))
            .build();

        // After compose, the host net contains the merged "attemptHttp"
        // transition (caller-wins identity) and NOT the renamed "rp/attempt".
        assertFalse(host.transitions().stream().anyMatch(t -> t.name().equals("rp/attempt")),
            "renamed channel transition 'rp/attempt' must merge away");
        assertTrue(host.transitions().stream().anyMatch(t -> t.name().equals("attemptHttp")),
            "merged 'attemptHttp' transition must remain");

        // Resolve the renamed instance-side internal place so we can observe
        // the increment via the executor's marking.
        Place<String> attemptCountPlace = (Place<String>) findPlace(host, "rp/attemptCount");

        try (var executor = BitmapNetExecutor.create(host, Map.of(
            trigger, List.of(Token.of("go"))
        ))) {
            var marking = executor.run();

            // The merged transition fires once for the single trigger token —
            // both the host action and the instance-side action increment.
            assertEquals(1, hostCalls.get(), "host action runs exactly once per merged firing");
            assertEquals(1, attemptCounter.get(), "instance-side retry-policy action runs exactly once");

            // Tokens land in both the host's result place and the
            // retry-policy's attemptCount sink.
            assertTrue(marking.hasTokens(hostResult),
                "host result token must be present after firing");
            assertTrue(marking.hasTokens(attemptCountPlace),
                "retry-policy attemptCount token must be present after firing");
        }
    }

    // ============================================================
    //  Channel-handle invariant (compose-time defensive check)
    // ============================================================

    /**
     * Positive round-trip: {@link Instance#bindActions} followed by
     * {@link PetriNet.Builder#compose(Instance, java.util.function.Consumer)}
     * must work end-to-end. This exercises the invariant from the happy-path
     * side: today's {@code bindActions} preserves transition names, so the
     * channel-handle map remains valid in the rebound instance.
     */
    @Test
    void bindActionsThenCompose_roundTrips_whenChannelIdentityPreserved() {
        var retryDef = SubnetFixtures.retryPolicy();

        TransitionAction attemptAction = ctx -> {
            for (var op : ctx.outputPlaces()) {
                if (op.name().endsWith("/attemptCount")) {
                    @SuppressWarnings("unchecked")
                    var p = (Place<String>) op;
                    ctx.output(p, "tick");
                }
            }
            return CompletableFuture.completedFuture(null);
        };
        var retryInst = retryDef.instantiate("rp")
            .bindActions(Map.of("attempt", attemptAction));

        Place<String> trigger = Place.of("trigger", String.class);
        Transition attemptHttp = Transition.builder("attemptHttp")
            .inputs(Arc.In.one(trigger))
            .build();

        // Must not throw — bindActions preserved channel-transition identity.
        var host = PetriNet.builder("HostWithRetry")
            .compose(retryInst, b -> b.bindChannel("attempt", attemptHttp))
            .build();

        assertTrue(host.transitions().stream().anyMatch(t -> t.name().equals("attemptHttp")),
            "merged 'attemptHttp' must be present after bindActions + compose");
    }

    /**
     * Negative: if an instance's channel-handle map points at a transition
     * whose name is not present in {@link Instance#renamedBody()}, the
     * defensive compose-time check must fire with a clear message. We
     * fabricate the corrupted instance via the package-private
     * {@link Instance} constructor — no production code path produces this
     * shape; the test guards against future refactors regressing the
     * invariant.
     */
    @Test
    void compose_failsLoudly_whenChannelHandleStaleVsRenamedBody() {
        // Build a normal retry-policy instance so we have a valid renamed
        // body + port-handle map to reuse.
        var retryDef = SubnetFixtures.retryPolicy();
        var goodInst = retryDef.instantiate("rp");

        // Fabricate a stale channel-handle map: it points at a transition
        // whose name does NOT match any transition in goodInst.renamedBody().
        Transition phantom = Transition.builder("rp/ghostChannel").build();
        // retryPolicy has no ports, so the port-handle map can be empty.
        var stalePortHandles = new java.util.LinkedHashMap<String, Place<?>>();
        var staleChannelHandles = new java.util.LinkedHashMap<String, Transition>();
        staleChannelHandles.put("attempt", phantom);

        var corruptInst = new Instance<>(
            goodInst.prefix(),
            goodInst.def(),
            goodInst.renamedBody(),
            stalePortHandles,
            staleChannelHandles,
            goodInst.params()
        );

        Place<String> trigger = Place.of("trigger", String.class);
        Transition attemptHttp = Transition.builder("attemptHttp")
            .inputs(Arc.In.one(trigger))
            .build();

        var ex = assertThrows(IllegalStateException.class, () ->
            PetriNet.builder("Host")
                .compose(corruptInst, b -> b.bindChannel("attempt", attemptHttp))
                .build());

        var msg = ex.getMessage();
        assertNotNull(msg, "exception message must not be null");
        assertTrue(msg.contains("attempt"),
            "message must name the channel 'attempt'. Got: " + msg);
        assertTrue(msg.contains("rp"),
            "message must name the instance prefix 'rp'. Got: " + msg);
        assertTrue(msg.contains("rp/ghostChannel"),
            "message must name the missing transition 'rp/ghostChannel'. Got: " + msg);
        assertTrue(msg.contains("bindActions"),
            "message must reference the bindActions contract. Got: " + msg);
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
}
