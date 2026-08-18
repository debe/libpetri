package org.libpetri.runtime;

import java.time.Duration;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentLinkedQueue;

import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.EnumSource;

import org.libpetri.core.Arc;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Token;
import org.libpetri.core.Transition;
import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Regression tests for behavioral divergences between {@link PrecompiledNetExecutor} and the
 * {@link BitmapNetExecutor} reference, mirroring the Rust backend-divergence suite. Each test
 * runs against both backends; the canonical behavior is pinned by the spec:
 *
 * <ul>
 *   <li>EXEC-013 AC4 — in-firing order: input consumption → read-arc peeks → reset draining</li>
 *   <li>CORE-030 AC3 — duplicate input arcs on one place rejected at compile time</li>
 *   <li>CORE-072 AC3 — tokens on places the compiled net does not know are retained</li>
 *   <li>EXEC-002 AC3/AC4, CONC-023 AC4 — ready order within a priority level is
 *       enablement time ASC, tid ASC as the tie-break</li>
 * </ul>
 *
 * <p>The legacy {@link NetExecutor} (which walks the {@link PetriNet} directly and never
 * compiles) participates wherever its direct-walk semantics are comparable; the compile-time
 * rejection and CORE-072 AC4 diagnostic tests stay scoped to the two bitmap-compiled
 * backends, whose seams they pin.
 */
@Timeout(60)
class BackendDivergenceRegressionTest {

    record SimpleValue(String data) {}
    record CounterValue(int count) {}

    enum Backend {
        BITMAP {
            @Override
            PetriNetExecutor create(PetriNet net, Map<Place<?>, List<Token<?>>> initial) {
                return BitmapNetExecutor.create(net, initial);
            }

            @Override
            PetriNetExecutor createWithEnvPlaces(PetriNet net, Map<Place<?>, List<Token<?>>> initial,
                                                 Set<EnvironmentPlace<?>> envPlaces) {
                return BitmapNetExecutor.builder(net, initial).environmentPlaces(envPlaces).build();
            }

            @Override
            PetriNetExecutor createWithEventStore(PetriNet net, Map<Place<?>, List<Token<?>>> initial,
                                                  EventStore eventStore) {
                return BitmapNetExecutor.builder(net, initial).eventStore(eventStore).build();
            }
        },
        PRECOMPILED {
            @Override
            PetriNetExecutor create(PetriNet net, Map<Place<?>, List<Token<?>>> initial) {
                return PrecompiledNetExecutor.create(net, initial);
            }

            @Override
            PetriNetExecutor createWithEnvPlaces(PetriNet net, Map<Place<?>, List<Token<?>>> initial,
                                                 Set<EnvironmentPlace<?>> envPlaces) {
                return PrecompiledNetExecutor.builder(net, initial).environmentPlaces(envPlaces).build();
            }

            @Override
            PetriNetExecutor createWithEventStore(PetriNet net, Map<Place<?>, List<Token<?>>> initial,
                                                  EventStore eventStore) {
                return PrecompiledNetExecutor.builder(net, initial).eventStore(eventStore).build();
            }
        },
        LEGACY {
            @Override
            PetriNetExecutor create(PetriNet net, Map<Place<?>, List<Token<?>>> initial) {
                return NetExecutor.create(net, initial);
            }

            @Override
            PetriNetExecutor createWithEnvPlaces(PetriNet net, Map<Place<?>, List<Token<?>>> initial,
                                                 Set<EnvironmentPlace<?>> envPlaces) {
                return NetExecutor.builder(net, initial).environmentPlaces(envPlaces).build();
            }

            @Override
            PetriNetExecutor createWithEventStore(PetriNet net, Map<Place<?>, List<Token<?>>> initial,
                                                  EventStore eventStore) {
                return NetExecutor.builder(net, initial).eventStore(eventStore).build();
            }
        };

        abstract PetriNetExecutor create(PetriNet net, Map<Place<?>, List<Token<?>>> initial);

        abstract PetriNetExecutor createWithEnvPlaces(PetriNet net, Map<Place<?>, List<Token<?>>> initial,
                                                      Set<EnvironmentPlace<?>> envPlaces);

        abstract PetriNetExecutor createWithEventStore(PetriNet net, Map<Place<?>, List<Token<?>>> initial,
                                                       EventStore eventStore);
    }

    /**
     * Read and reset arcs on the SAME place: the read must observe the pre-reset front token
     * (EXEC-013 AC4). The precompiled executor used to drain the reset before peeking reads,
     * so {@code ctx.read()} failed where the bitmap reference delivered the token.
     */
    @ParameterizedTest
    @EnumSource(Backend.class)
    void readAndResetSamePlace_readSeesPreResetFrontToken(Backend backend) throws Exception {
        var in = Place.of("In", SimpleValue.class);
        var both = Place.of("Both", CounterValue.class);
        var out = Place.of("Out", CounterValue.class);

        var t = Transition.builder("t")
            .inputs(Arc.In.one(in))
            .read(both)
            .reset(both)
            .outputs(Arc.Out.place(out))
            .action(ctx -> {
                ctx.output(out, ctx.read(both));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var net = PetriNet.builder("ReadResetSamePlace").transitions(t).build();
        var initial = Map.<Place<?>, List<Token<?>>>of(
            in, List.of(Token.of(new SimpleValue("go"))),
            both, List.of(Token.of(new CounterValue(7)), Token.of(new CounterValue(8)))
        );

        try (var executor = backend.create(net, initial)) {
            var result = executor.run();

            assertEquals(0, result.tokenCount(both), "reset drained the place");
            assertEquals(1, result.tokenCount(out), "read arc satisfied the action");
            assertEquals(7, result.peekFirst(out).value().count(),
                "read saw the pre-reset front token");
        }
    }

    /**
     * Two input arcs on one place have no coherent consumption semantics (the bitmap
     * reference tolerantly under-consumed, the precompiled executor corrupted its token
     * rings) and are rejected at compile time (CORE-030 AC3). The Transition builder stays
     * permissive; the check lives in {@link CompiledNet}, which both backends compile through.
     */
    @ParameterizedTest
    @EnumSource(value = Backend.class, names = {"BITMAP", "PRECOMPILED"})
    void duplicateInputArcsOnOnePlace_rejectedAtCompileTime(Backend backend) {
        var p = Place.of("P", CounterValue.class);

        var t = Transition.builder("t")
            .inputs(Arc.In.one(p), Arc.In.one(p))
            .action(ctx -> CompletableFuture.completedFuture(null))
            .build();

        var net = PetriNet.builder("DuplicateInput").transitions(t).build();
        var initial = Map.<Place<?>, List<Token<?>>>of(
            p, List.of(Token.of(new CounterValue(1)))
        );

        var error = assertThrows(IllegalStateException.class,
            () -> backend.create(net, initial));
        assertTrue(error.getMessage().contains("two input arcs"),
            "expected the duplicate-input-place rejection message, got: " + error.getMessage());
    }

    /**
     * A place named in the initial marking but never declared to the net: both backends must
     * retain its tokens in the observable marking (CORE-072 AC3). The precompiled executor
     * used to drop them (its ring pool only stores compiled places) while the bitmap
     * reference kept its whole {@link Marking} — a literal lost token.
     */
    @ParameterizedTest
    @EnumSource(Backend.class)
    void unknownPlaceInitialTokens_retainedInFinalMarking(Backend backend) throws Exception {
        var p1 = Place.of("P1", SimpleValue.class);
        var p2 = Place.of("P2", SimpleValue.class);
        var ghost = Place.of("Ghost", CounterValue.class);

        var t = Transition.builder("t")
            .inputs(Arc.In.one(p1))
            .outputs(Arc.Out.place(p2))
            .action(ctx -> {
                ctx.output(p2, ctx.input(p1));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var net = PetriNet.builder("GhostPlace").transitions(t).build();
        var initial = Map.<Place<?>, List<Token<?>>>of(
            p1, List.of(Token.of(new SimpleValue("go"))),
            ghost, List.of(Token.of(new CounterValue(99)))
        );

        try (var executor = backend.create(net, initial)) {
            var result = executor.run();

            assertFalse(result.hasTokens(p1), "declared place consumed normally");
            assertEquals(1, result.tokenCount(p2), "declared place produced normally");
            assertEquals(1, result.tokenCount(ghost), "unknown-place token retained");
            assertEquals(99, result.peekFirst(ghost).value().count(),
                "unknown-place token unchanged");
        }
    }

    /**
     * An action producing to a place the compiled net does not know (via the raw collector,
     * the seam output validation defends against): the token must be retained (CORE-072 AC3)
     * and validation must skip the unknown entry. The precompiled {@code Out.Place} fast path
     * used to unbox a null place-index lookup on the ghost entry (NPE, failing the whole
     * firing and dropping every output).
     */
    @ParameterizedTest
    @EnumSource(Backend.class)
    void produceToUnknownPlace_retainedAndValidationSkipsGhostEntry(Backend backend) throws Exception {
        var in = Place.of("In", SimpleValue.class);
        var out = Place.of("Out", CounterValue.class);
        var ghost = Place.of("Ghost", CounterValue.class);

        var t = Transition.builder("t")
            .inputs(Arc.In.one(in))
            .outputs(Arc.Out.place(out))
            .action(ctx -> {
                // rawOutput() skips the declared-outputs check, so the ghost entry reaches
                // validateOutput; ghost FIRST so the entry scan hits it before the match.
                ctx.rawOutput().add(ghost, new CounterValue(99));
                ctx.output(out, new CounterValue(1));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var net = PetriNet.builder("GhostProduce").transitions(t).build();
        var initial = Map.<Place<?>, List<Token<?>>>of(
            in, List.of(Token.of(new SimpleValue("go")))
        );

        try (var executor = backend.create(net, initial)) {
            var result = executor.run();

            assertFalse(result.hasTokens(in), "declared place consumed normally");
            assertEquals(1, result.tokenCount(out), "declared output produced (firing not failed)");
            assertEquals(1, result.tokenCount(ghost), "unknown-place token retained");
            assertEquals(99, result.peekFirst(ghost).value().count(),
                "unknown-place token unchanged");
        }
    }

    /**
     * Injection into an environment place whose backing place the compiled net does not know:
     * the token must be retained in the observable marking (CORE-072 AC3). The precompiled
     * executor used to drop it silently (its ring pool only stores compiled places).
     */
    @ParameterizedTest
    @EnumSource(Backend.class)
    void injectIntoUnknownPlace_retainedInFinalMarking(Backend backend) throws Exception {
        var p1 = Place.of("P1", SimpleValue.class);
        var p2 = Place.of("P2", SimpleValue.class);
        var ghost = Place.of("GhostEnv", CounterValue.class);
        var ghostEnv = EnvironmentPlace.of(ghost);

        var t = Transition.builder("t")
            .inputs(Arc.In.one(p1))
            .outputs(Arc.Out.place(p2))
            .action(ctx -> {
                ctx.output(p2, ctx.input(p1));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var net = PetriNet.builder("GhostInject").transitions(t).build();
        var initial = Map.<Place<?>, List<Token<?>>>of(
            p1, List.of(Token.of(new SimpleValue("go")))
        );

        try (var executor = backend.createWithEnvPlaces(net, initial, Set.of(ghostEnv))) {
            // inject() before run() is legitimate; drain() lets the loop process the queued
            // event and then terminate instead of waiting for more external events.
            var accepted = executor.inject(ghostEnv, Token.of(new CounterValue(9)));
            executor.drain();
            var result = executor.run();

            assertTrue(accepted.join(), "inject accepted");
            assertEquals(1, result.tokenCount(p2), "declared flow ran normally");
            assertEquals(1, result.tokenCount(ghost), "unknown-place token retained");
            assertEquals(9, result.peekFirst(ghost).value().count(),
                "unknown-place token unchanged");
        }
    }

    /**
     * CORE-072 AC4: an unknown place is reported once per executor, not once per token —
     * the diagnostic rides the existing EVT-013 log-message event, and a hot loop writing to
     * a typo'd place must not flood the store. Retention (AC3) is independent: every token
     * still lands in the final marking.
     */
    @ParameterizedTest
    @EnumSource(value = Backend.class, names = {"BITMAP", "PRECOMPILED"})
    void unknownPlaceWrites_warnOncePerDistinctPlace(Backend backend) throws Exception {
        var in = Place.of("In", SimpleValue.class);
        var out = Place.of("Out", CounterValue.class);
        var ghostA = Place.of("GhostA", CounterValue.class);
        var ghostB = Place.of("GhostB", CounterValue.class);

        var t = Transition.builder("t")
            .inputs(Arc.In.one(in))
            .outputs(Arc.Out.place(out))
            .action(ctx -> {
                ctx.rawOutput().add(ghostA, new CounterValue(1));
                ctx.rawOutput().add(ghostB, new CounterValue(2));
                ctx.output(out, new CounterValue(3));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var net = PetriNet.builder("GhostWarn").transitions(t).build();
        var initial = Map.<Place<?>, List<Token<?>>>of(
            in, List.of(Token.of(new SimpleValue("a")),
                        Token.of(new SimpleValue("b")),
                        Token.of(new SimpleValue("c")))
        );

        var eventStore = EventStore.inMemory();
        try (var executor = backend.createWithEventStore(net, initial, eventStore)) {
            var result = executor.run();

            assertEquals(3, result.tokenCount(ghostA), "every unknown-place token retained");
            assertEquals(3, result.tokenCount(ghostB), "every unknown-place token retained");

            var warnings = runtimeWarnings(eventStore);
            assertEquals(2, warnings.size(),
                "one warning per distinct unknown place across 3 firings, got: " + warnings);
            assertTrue(warnings.stream().allMatch(w -> "WARN".equals(w.level())
                    && "t".equals(w.transitionName())
                    && w.throwable() == null && w.throwableMessage() == null),
                "WARN, attributed to the producing transition, no throwable: " + warnings);
            assertTrue(warnings.stream().anyMatch(w -> w.message().contains("'GhostA'"))
                    && warnings.stream().anyMatch(w -> w.message().contains("'GhostB'")),
                "each unknown place named exactly once: " + warnings);
            assertTrue(warnings.get(0).message().contains("retained in the marking but inert"),
                "message states retention, got: " + warnings.get(0).message());
        }
    }

    /**
     * The initial-marking seam reports with an empty transition name (nothing is firing), and
     * a later production to the SAME unknown place does not report it a second time.
     */
    @ParameterizedTest
    @EnumSource(value = Backend.class, names = {"BITMAP", "PRECOMPILED"})
    void unknownPlaceInInitialMarking_warnsOnceWithNoTransitionName(Backend backend) throws Exception {
        var in = Place.of("In", SimpleValue.class);
        var ghost = Place.of("Ghost", CounterValue.class);

        var t = Transition.builder("t")
            .inputs(Arc.In.one(in))
            .action(ctx -> {
                ctx.rawOutput().add(ghost, new CounterValue(2));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var net = PetriNet.builder("GhostInitial").transitions(t).build();
        var initial = Map.<Place<?>, List<Token<?>>>of(
            in, List.of(Token.of(new SimpleValue("go"))),
            ghost, List.of(Token.of(new CounterValue(1)))
        );

        var eventStore = EventStore.inMemory();
        try (var executor = backend.createWithEventStore(net, initial, eventStore)) {
            var result = executor.run();

            assertEquals(2, result.tokenCount(ghost),
                "initial and produced unknown-place tokens both retained");

            var warnings = runtimeWarnings(eventStore);
            assertEquals(1, warnings.size(),
                "the produce seam must not re-report an already-reported place, got: " + warnings);
            assertEquals("", warnings.get(0).transitionName(),
                "no transition is firing at the initial-marking seam");
        }
    }

    /** The CORE-072 AC4 diagnostics only — never an action's captured log output. */
    private static List<NetEvent.LogMessage> runtimeWarnings(EventStore store) {
        return store.eventsOfType(NetEvent.LogMessage.class).stream()
            .filter(e -> "libpetri.runtime".equals(e.loggerName()))
            .toList();
    }

    /**
     * Ready order within one firing cycle is priority DESC, then enablement time ASC, with
     * tid ASC only as the tie-break for equal timestamps (EXEC-002 AC3/AC4, CONC-023 AC4).
     * The precompiled executor's per-priority ready queues used to substitute tid order for
     * enablement-time order when same-priority transitions became enabled in different cycles.
     *
     * <p>Declaration order is deliberately the OPPOSITE of enablement order: {@code t_late}
     * (tid 0) enables ~50ms after {@code t_early} (tid 1), and {@code t_hi} (tid 2, higher
     * priority) enables last but must fire first.
     *
     * <p>Java's executors read {@code System.nanoTime()} internally — there is no synthetic
     * clock seam like the Rust backend tests use — so this test staggers enablement with real
     * wall time. Actions run <b>inline on the orchestrator thread</b>, so a sleeping gate
     * action deterministically blocks the loop while the delayed transitions' windows elapse,
     * forcing all three to become ready in the same firing cycle. Margins are generous
     * (50/100/300ms) to stay far from scheduler jitter.
     */
    @ParameterizedTest
    @EnumSource(Backend.class)
    void staggeredEnablement_firesInPriorityThenEnablementOrder(Backend backend) throws Exception {
        var a = Place.of("A", CounterValue.class);
        var b = Place.of("B", CounterValue.class);
        var c = Place.of("C", CounterValue.class);
        var g1 = Place.of("G1", SimpleValue.class);
        var g2 = Place.of("G2", SimpleValue.class);

        Queue<String> firingOrder = new ConcurrentLinkedQueue<>();

        var tLate = Transition.builder("t_late") // tid 0, enabled second
            .inputs(Arc.In.one(a))
            .timing(Timing.delayed(Duration.ofMillis(100)))
            .action(ctx -> {
                firingOrder.add("t_late");
                return CompletableFuture.completedFuture(null);
            })
            .build();
        var tEarly = Transition.builder("t_early") // tid 1, enabled first
            .inputs(Arc.In.one(b))
            .timing(Timing.delayed(Duration.ofMillis(100)))
            .action(ctx -> {
                firingOrder.add("t_early");
                return CompletableFuture.completedFuture(null);
            })
            .build();
        var tHi = Transition.builder("t_hi") // tid 2, higher priority, enabled second
            .inputs(Arc.In.one(c))
            .timing(Timing.delayed(Duration.ofMillis(100)))
            .priority(5)
            .action(ctx -> {
                firingOrder.add("t_hi");
                return CompletableFuture.completedFuture(null);
            })
            .build();

        // Blocks the orchestrator ~50ms, then enables t_late and t_hi and hands off to gate2.
        var gate1 = Transition.builder("gate1")
            .inputs(Arc.In.one(g1))
            .outputs(Arc.Out.and(a, c, g2))
            .action(ctx -> {
                sleepUninterruptibly(50);
                ctx.output(a, new CounterValue(1));
                ctx.output(c, new CounterValue(2));
                ctx.output(g2, new SimpleValue("handoff"));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        // Blocks the orchestrator until every delayed window has elapsed, so all three
        // delayed transitions are ready in the SAME cycle when the loop resumes.
        var gate2 = Transition.builder("gate2")
            .inputs(Arc.In.one(g2))
            .action(ctx -> {
                sleepUninterruptibly(300);
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var net = PetriNet.builder("StaggeredReadyOrder")
            .transitions(tLate, tEarly, tHi, gate1, gate2)
            .build();
        var initial = Map.<Place<?>, List<Token<?>>>of(
            b, List.of(Token.of(new CounterValue(0))),   // t_early enabled from t=0
            g1, List.of(Token.of(new SimpleValue("go")))
        );

        try (var executor = backend.create(net, initial)) {
            executor.run();

            assertEquals(List.of("t_hi", "t_early", "t_late"), List.copyOf(firingOrder),
                "priority DESC first, then enablement time ASC within the shared level "
                    + "(declaration/tid order must not override enablement order)");
        }
    }

    /**
     * Same-cycle sync-action deposits must be <b>invisible</b> to intra-pass firing rechecks
     * (backend divergence #5): outputs deposit in loop step 1 while firing is step 5
     * (EXEC-001), and losers within one pass are disabled by consumption alone (EXEC-003).
     *
     * <p>{@code t_high} (priority 1) consumes one(a), resets b, and synchronously re-produces
     * one token to b; {@code t_low} (priority 0) consumes one(a) and reads b. In every cycle
     * t_high fires first and drains b, so the token its action deposits back must not revive
     * t_low's recheck within the same pass: t_high monopolizes a (fires 3x) and t_low starves.
     * Both compiled backends used to recheck against the live presence bitmap, letting the
     * deposit leak into the pass and produce the interleaving [t_high, t_low, t_high]; the
     * legacy executor routes all outputs through its completion queue and was already correct.
     */
    @ParameterizedTest
    @EnumSource(Backend.class)
    void sameCycleSyncDeposit_invisibleToIntraPassRecheck(Backend backend) throws Exception {
        var a = Place.of("a", CounterValue.class);
        var b = Place.of("b", CounterValue.class);
        Queue<String> firingOrder = new ConcurrentLinkedQueue<>();

        var tLow = Transition.builder("t_low")
            .inputs(Arc.In.one(a))
            .read(b)
            .action(ctx -> {
                firingOrder.add("t_low");
                return CompletableFuture.completedFuture(null);
            })
            .build();
        var tHigh = Transition.builder("t_high")
            .inputs(Arc.In.one(a))
            .reset(b)
            .outputs(Arc.Out.place(b))
            .priority(1)
            .action(ctx -> {
                firingOrder.add("t_high");
                ctx.output(b, new CounterValue(1));
                return CompletableFuture.completedFuture(null);
            })
            .build();

        var net = PetriNet.builder("SameCycleDeposit").transitions(tLow, tHigh).build();
        var initial = Map.<Place<?>, List<Token<?>>>of(
            a, List.of(Token.of(new CounterValue(10)),
                       Token.of(new CounterValue(11)),
                       Token.of(new CounterValue(12))),
            b, List.of(Token.of(new CounterValue(0)))
        );

        var eventStore = EventStore.inMemory();
        try (var executor = backend.createWithEventStore(net, initial, eventStore)) {
            var result = executor.run();

            assertEquals(List.of("t_high", "t_high", "t_high"), List.copyOf(firingOrder),
                "same-cycle deposit must not revive t_low inside the firing pass");
            assertFalse(result.hasTokens(a), "t_high monopolized a");
            assertEquals(1, result.tokenCount(b), "only the final re-deposit remains");

            var started = eventStore.eventsOfType(NetEvent.TransitionStarted.class).stream()
                .map(NetEvent.TransitionStarted::transitionName)
                .toList();
            assertEquals(List.of("t_high", "t_high", "t_high"), started,
                "event sequence pins the firing order (no t_low TransitionStarted)");
        }
    }

    private static void sleepUninterruptibly(long millis) {
        try {
            Thread.sleep(millis);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new IllegalStateException(e);
        }
    }
}
