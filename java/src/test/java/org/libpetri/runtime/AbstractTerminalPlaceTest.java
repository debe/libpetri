package org.libpetri.runtime;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.libpetri.core.*;
import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;

import java.time.Instant;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.BooleanSupplier;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.core.Arc.In.one;
import static org.libpetri.core.Arc.Out.and;
import static org.libpetri.core.Arc.Out.place;

/**
 * <b>EXEC-042</b> terminal places, against both executors: the run ends as soon as a deposit
 * marks a terminal place, strictly — no transition fires afterwards, not even one already
 * enabled later in the same firing pass — with the reason {@code TERMINAL}.
 *
 * <p>The two executors share no deposit path (rings and opcodes against a {@link Marking}), so
 * every case runs on both.
 */
@Timeout(60)
abstract class AbstractTerminalPlaceTest {

    /** {@code store} and {@code environment} may be null, leaving that knob at its default. */
    protected abstract PetriNetExecutor create(
        PetriNet net, Map<Place<?>, List<Token<?>>> initial, Set<EnvironmentPlace<?>> environmentPlaces,
        EventStore store, ExecutionEnvironment environment);

    private PetriNetExecutor create(PetriNet net, Map<Place<?>, List<Token<?>>> initial) {
        return create(net, initial, Set.of(), null, null);
    }

    private static final Place<String> IN = Place.of("in", String.class);
    private static final Place<String> A = Place.of("a", String.class);
    private static final Place<String> B = Place.of("b", String.class);
    private static final Place<String> OUT = Place.of("out", String.class);
    private static final Place<String> OTHER = Place.of("other", String.class);
    private static final Place<String> DONE = Place.of("done", String.class);
    private static final Place<String> LATE = Place.of("late", String.class);

    private static Token<String> tok(String v) {
        return Token.of(v);
    }

    /** A sync transition {@code from -> to}, forwarding its token. */
    private static Transition forward(String name, Place<String> from, Place<String> to, int priority) {
        return Transition.builder(name).inputs(one(from)).outputs(place(to)).priority(priority)
            .action(ctx -> { ctx.output(to, ctx.input(from)); return CompletableFuture.completedFuture(null); })
            .build();
    }

    // ============================================================
    //  AC1 — the initial marking
    // ============================================================

    @Test
    void initialMarkingOnATerminalPlaceFiresNothing_EXEC042_AC1() {
        var net = PetriNet.builder("pre-terminated")
            .transition(forward("t", IN, OUT, 0))
            .terminal(DONE)
            .build();
        try (var executor = create(net, Map.of(IN, List.of(tok("x")), DONE, List.of(tok("d"))))) {
            var marking = executor.run();
            assertEquals(TerminationReason.TERMINAL, executor.terminationReason(),
                "EXEC-042 AC1: the initial marking is a check point");
            assertTrue(executor.terminationReason().isComplete(), "TERMINAL is a completed reason");
            assertTrue(marking.hasTokens(IN) && !marking.hasTokens(OUT),
                "EXEC-042 AC1: nothing fires when the run starts terminal. Got: " + marking);
        }
    }

    @Test
    void aNetWhoseTerminalIsNeverMarkedStillQuiesces_EXEC042() {
        var net = PetriNet.builder("never-terminal")
            .transition(forward("t", IN, OUT, 0))
            .terminal(DONE)
            .build();
        try (var executor = create(net, Map.of(IN, List.of(tok("x"))))) {
            var marking = executor.run();
            assertEquals(TerminationReason.QUIESCENT, executor.terminationReason());
            assertTrue(marking.hasTokens(OUT));
        }
    }

    // ============================================================
    //  AC2 — an asynchronous completion, with other work in flight
    // ============================================================

    @Test
    void asyncCompletionOnATerminalPlaceAbandonsTheOtherInFlightAction_EXEC042_AC2() throws Exception {
        var slow = new CompletableFuture<Void>();
        var slowContext = new AtomicReference<TransitionContext>();
        var net = PetriNet.builder("fork")
            .transition(Transition.builder("fork").inputs(one(IN)).outputs(and(A, B))
                .action(ctx -> {
                    ctx.output(A, "a");
                    ctx.output(B, "b");
                    return CompletableFuture.completedFuture(null);
                }).build())
            .transition(Transition.builder("finish").inputs(one(A)).outputs(place(DONE))
                .action(ctx -> CompletableFuture.runAsync(
                    () -> ctx.output(DONE, ctx.input(A)),
                    CompletableFuture.delayedExecutor(30, TimeUnit.MILLISECONDS)))
                .build())
            .transition(Transition.builder("straggler").inputs(one(B)).outputs(place(LATE))
                .action(ctx -> { slowContext.set(ctx); return slow; })
                .build())
            .terminal(DONE)
            .build();

        var store = EventStore.inMemory();
        try (var executor = create(net, Map.of(IN, List.of(tok("x"))), Set.of(), store, null)) {
            var marking = executor.run();

            assertEquals(TerminationReason.TERMINAL, executor.terminationReason(),
                "EXEC-042 AC2: the completion that marked the terminal place ended the run");
            assertTrue(marking.hasTokens(DONE), "Got: " + marking);
            assertFalse(slow.isDone(), "the premise: the other action was still in flight");

            // The abandoned action finishes after the run: its result is discarded.
            slowContext.get().output(LATE, "late");
            slow.complete(null);
            Thread.sleep(50);
            assertFalse(executor.marking().hasTokens(LATE),
                "EXEC-042 AC2: an abandoned action's result never appears in the marking");
            assertTrue(executor.snapshot().actionInFlight(),
                "EXEC-042: a snapshot taken afterwards still reports abandoned work as work in flight");

            assertTrue(store.events().stream().noneMatch(e -> e instanceof NetEvent.LogMessage lm
                    && "WARN".equals(lm.level())),
                "EVT-013 AC5: a designed terminal stop emits no diagnostic. Events: " + store.events());
        }
    }

    // ============================================================
    //  AC3 — an injection
    // ============================================================

    @Test
    void injectionIntoATerminalEnvironmentPlaceRefusesTheEventQueuedBehindIt_EXEC042_AC3() {
        var stop = EnvironmentPlace.of(Place.of("stop", String.class));
        var events = EnvironmentPlace.of(Place.of("events", String.class));
        var net = PetriNet.builder("session")
            .transition(forward("absorb", events.place(), OUT, 0))
            .terminal(stop.place())
            .build();

        var stopAccepted = new AtomicReference<CompletableFuture<Boolean>>();
        var behind = new AtomicReference<CompletableFuture<Boolean>>();
        var executorRef = new AtomicReference<PetriNetExecutor>();
        // A host that, at its first wait, injects the terminal event and then another behind
        // it — both only enqueue — and returns. The next external-events phase admits the
        // first; the second must be refused.
        var host = new ExecutionEnvironment() {
            boolean injected;
            @Override public long nanoTime() { return 0; }
            @Override public Instant now() { return Instant.EPOCH; }
            @Override public void awaitWork(BooleanSupplier ready, long delayNanos) {
                if (injected) throw new AssertionError("the run should have ended at the terminal event");
                injected = true;
                stopAccepted.set(executorRef.get().inject(stop, "halt"));
                behind.set(executorRef.get().inject(events, "e"));
            }
        };
        try (var executor = create(net, Map.of(), Set.of(stop, events), null, host)) {
            executorRef.set(executor);
            var marking = executor.run();

            assertEquals(TerminationReason.TERMINAL, executor.terminationReason(),
                "EXEC-042 AC3: an injection is a check point");
            assertTrue(stopAccepted.get().join(), "the terminal event itself was admitted");
            assertFalse(behind.get().join(),
                "EXEC-042 AC3: an external event queued behind the terminal one is refused (ENV-004)");
            assertTrue(marking.hasTokens(stop.place()) && !marking.hasTokens(OUT)
                    && !marking.hasTokens(events.place()),
                "Got: " + marking);
            assertFalse(executor.inject(events, "after").join(),
                "an inject after the run ended is refused");
        }
    }

    @Test
    void injectionIntoATerminalEnvironmentPlaceUnderTheBuiltInWait_EXEC042_AC3() throws Exception {
        var stop = EnvironmentPlace.of(Place.of("stop", String.class));
        var events = EnvironmentPlace.of(Place.of("events", String.class));
        var net = PetriNet.builder("session")
            .transition(forward("absorb", events.place(), OUT, 0))
            .terminal(stop.place())
            .build();
        try (var executor = create(net, Map.of(), Set.of(stop, events), null, null)) {
            var run = CompletableFuture.supplyAsync(executor::run);
            assertTrue(executor.inject(events, "e").get(10, TimeUnit.SECONDS));
            assertTrue(executor.inject(stop, "halt").get(10, TimeUnit.SECONDS));
            var marking = run.get(10, TimeUnit.SECONDS);
            assertEquals(TerminationReason.TERMINAL, executor.terminationReason(),
                "a net with environment places never quiesces; the terminal event ends it");
            assertTrue(marking.hasTokens(OUT) && marking.hasTokens(stop.place()), "Got: " + marking);
            assertFalse(executor.inject(events, "after").get(10, TimeUnit.SECONDS),
                "an inject after the run ended is refused");
        }
    }

    // ============================================================
    //  AC4 — a synchronous output, strictly within the pass
    // ============================================================

    @Test
    void syncOutputOnATerminalPlaceStopsTheFiringPass_ByPriority_EXEC042_AC4() {
        // Both enabled before the pass began; priority orders 'finish' first. It is synchronous
        // and marks the terminal place, so 'other', later in the same pass, must never fire.
        var net = PetriNet.builder("same-pass")
            .transition(forward("finish", A, DONE, 10))
            .transition(forward("other", B, OTHER, 1))
            .terminal(DONE)
            .build();
        try (var executor = create(net, Map.of(A, List.of(tok("a")), B, List.of(tok("b"))))) {
            var marking = executor.run();
            assertEquals(TerminationReason.TERMINAL, executor.terminationReason());
            assertTrue(marking.hasTokens(DONE), "Got: " + marking);
            assertFalse(marking.hasTokens(OTHER),
                "EXEC-042 AC4: no transition fires after the deposit that marked a terminal "
                    + "place — not even one enabled before the pass began. Got: " + marking);
            assertTrue(marking.hasTokens(B), "'other' never consumed its input. Got: " + marking);
        }
    }

    @Test
    void syncOutputOnATerminalPlaceStopsTheFiringPass_SamePriority_EXEC042_AC4() {
        // All immediate and one priority: the executors' fast firing path, in declaration order.
        var net = PetriNet.builder("same-pass-fast")
            .transition(forward("finish", A, DONE, 0))
            .transition(forward("other", B, OTHER, 0))
            .terminal(DONE)
            .build();
        try (var executor = create(net, Map.of(A, List.of(tok("a")), B, List.of(tok("b"))))) {
            var marking = executor.run();
            assertEquals(TerminationReason.TERMINAL, executor.terminationReason());
            assertFalse(marking.hasTokens(OTHER),
                "EXEC-042 AC4 on the fast path: 'other' must not fire. Got: " + marking);
        }
    }

    @Test
    void theFiringThatMarksTheTerminalDepositsAllItsOutputs_EXEC042() {
        var net = PetriNet.builder("atomic")
            .transition(Transition.builder("finish").inputs(one(A)).outputs(and(DONE, OUT))
                .action(ctx -> {
                    ctx.output(DONE, "d");
                    ctx.output(OUT, "o");
                    return CompletableFuture.completedFuture(null);
                }).build())
            .terminal(DONE)
            .build();
        try (var executor = create(net, Map.of(A, List.of(tok("a"))))) {
            var marking = executor.run();
            assertTrue(marking.hasTokens(DONE) && marking.hasTokens(OUT),
                "the firing that made the deposit completes atomically. Got: " + marking);
        }
    }

    // ============================================================
    //  AC5 / AC6 — well-formedness and composition
    // ============================================================

    @Test
    void aTransitionConsumingATerminalPlaceIsRejectedAtBuild_EXEC042_AC5() {
        var ex = assertThrows(IllegalArgumentException.class, () -> PetriNet.builder("bad")
            .transition(forward("consumer", DONE, OUT, 0))
            .terminal(DONE)
            .build());
        assertTrue(ex.getMessage().contains("'done'") && ex.getMessage().contains("'consumer'"),
            "names the place and the transition. Got: " + ex.getMessage());
    }

    @Test
    void aTransitionReadingATerminalPlaceIsRejectedAtBuild_EXEC042_AC5() {
        var ex = assertThrows(IllegalArgumentException.class, () -> PetriNet.builder("bad")
            .transition(Transition.builder("reader").inputs(one(A)).read(DONE).outputs(place(OUT))
                .action(ctx -> { ctx.output(OUT, ctx.input(A)); return CompletableFuture.completedFuture(null); })
                .build())
            .terminal(DONE)
            .build());
        assertTrue(ex.getMessage().contains("'done'") && ex.getMessage().contains("'reader'"),
            "names the place and the transition. Got: " + ex.getMessage());
    }

    @Test
    void anInhibitorOnATerminalPlaceIsAllowed_EXEC042_AC5() {
        assertDoesNotThrow(() -> PetriNet.builder("ok")
            .transition(Transition.builder("guarded").inputs(one(A)).inhibitor(DONE).outputs(place(OUT))
                .action(ctx -> { ctx.output(OUT, ctx.input(A)); return CompletableFuture.completedFuture(null); })
                .build())
            .terminal(DONE)
            .build());
    }

    @Test
    void aSubnetBodyDeclaringATerminalIsRejectedByComposeAndInstantiate_EXEC042_AC6() {
        var body = PetriNet.builder("body")
            .transition(forward("finish", A, DONE, 0))
            .terminal(DONE)
            .build();
        var def = SubnetDef.fromNet(body, Interface.builder().build());

        var direct = assertThrows(IllegalArgumentException.class,
            () -> PetriNet.builder("host").compose(def));
        assertTrue(direct.getMessage().contains("'done'"),
            "compose names the place. Got: " + direct.getMessage());

        var instantiated = assertThrows(IllegalArgumentException.class, () -> def.instantiate("i"));
        assertTrue(instantiated.getMessage().contains("'done'"),
            "instantiate names the place. Got: " + instantiated.getMessage());
    }

    @Test
    void terminalsSurviveBindActionsAndFollowFusionToTheCanonicalPlace_EXEC042() {
        var net = PetriNet.builder("n")
            .transition(Transition.builder("finish").inputs(one(A)).outputs(place(DONE)).build())
            .terminal(DONE)
            .build();
        var bound = net.bindActions(name -> ctx -> {
            ctx.output(DONE, ctx.input(A));
            return CompletableFuture.completedFuture(null);
        });
        assertEquals(Set.of(DONE), bound.terminals(), "bindActions carries the terminals");

        var alias = Place.of("alias", String.class);
        var fused = PetriNet.builder("f")
            .transition(Transition.builder("finish").inputs(one(A)).outputs(place(alias)).build())
            .terminal(alias)
            .fuse(FusionSet.builder("s").member(DONE).member(alias).build())
            .build();
        assertEquals(Set.of(DONE), fused.terminals(),
            "a fused terminal is remapped to the canonical place");
    }
}
