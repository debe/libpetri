package org.libpetri.runtime;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.libpetri.core.*;
import org.libpetri.event.EventStore;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.BooleanSupplier;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.core.Arc.In.one;
import static org.libpetri.core.Arc.Out.place;

/**
 * <b>CORE-073</b> restore and <b>ENV-014</b> {@code snapshot()} <i>through an executor</i>,
 * against both of them.
 *
 * <p>The two executors share neither path: the Precompiled one loads a restore into ring
 * buffers (plus a side map for places the program does not know) and reads its in-flight state
 * from a counter, where the Bitmap one seeds a {@link Marking} and reads a map. A test written
 * against one proves nothing about the other, so every case here runs on both. The pure
 * {@link Marking} form is pinned separately in {@link MarkingSnapshotTest}.
 */
@Timeout(60)
abstract class AbstractExecutorSnapshotTest {

    /** Builder knobs the cases below need; {@code null} leaves a knob at its default. */
    protected record Options(
        Map<String, List<Token<?>>> restore,
        ExecutionEnvironment environment,
        Set<EnvironmentPlace<?>> environmentPlaces,
        EventStore eventStore,
        java.util.concurrent.ExecutorService executor
    ) {
        Options(Map<String, List<Token<?>>> restore, ExecutionEnvironment environment,
                Set<EnvironmentPlace<?>> environmentPlaces, EventStore eventStore) {
            this(restore, environment, environmentPlaces, eventStore, null);
        }
        static Options none() { return new Options(null, null, null, null); }
        static Options restoring(Map<String, List<Token<?>>> snapshot) {
            return new Options(snapshot, null, null, null);
        }
    }

    protected abstract PetriNetExecutor create(
        PetriNet net, Map<Place<?>, List<Token<?>>> initial, Options options);

    /** Shortens the foreign-reader cap (2 s by default) through the executor's package-private hook. */
    protected abstract void snapshotCap(PetriNetExecutor executor, Duration cap);

    /** Whether the orchestrator is parked in its wait now ([ENV-014] AC#9). */
    protected abstract boolean parked(PetriNetExecutor executor);

    /** Foreign marking requests the executor has registered so far ([ENV-014] AC#9). */
    protected abstract long markingRequests(PetriNetExecutor executor);

    private static final Place<String> A = Place.of("a", String.class);
    private static final Place<String> B = Place.of("b", String.class);
    private static final Place<String> IN  = Place.of("in",  String.class);
    private static final Place<String> OUT = Place.of("out", String.class);

    private static final Instant T1 = Instant.parse("2020-01-01T00:00:00Z");
    private static final Instant T2 = Instant.parse("2021-06-15T12:30:00Z");

    private static PetriNet passThroughNet() {
        return PetriNet.builder("pass").transition(Transition.builder("t")
            .inputs(one(A)).outputs(place(B))
            .action(ctx -> { ctx.output(B, ctx.input(A)); return CompletableFuture.completedFuture(null); })
            .build()).build();
    }

    // ============================================================
    //  CORE-073 AC#7 / AC#9 / AC#10 / AC#11 — restore through the builder
    // ============================================================

    @Test
    void restoredTokensAreVisibleToTheNetsTransitions_AC10() {
        var snapshot = Map.<String, List<Token<?>>>of("a", List.of(new Token<>("x", T1)));

        try (var executor = create(passThroughNet(), Map.of(), Options.restoring(snapshot))) {
            var marking = executor.run();
            assertEquals(0, marking.tokenCount(A),
                "CORE-073 AC#10: the restored token was CONSUMED, not merely present. A "
                    + "presence check passes against a restore that put the tokens somewhere "
                    + "the executor can read but never fires from. Marking: " + marking);
            assertEquals("x", marking.peekFirst(B).value(),
                "CORE-073 AC#10: restored tokens must be visible to the net's transitions. "
                    + "Java's Place is a record over (name, tokenType), so a place synthesised "
                    + "from a name alone would not compare equal to the net's own and the tokens "
                    + "would sit in a map the executor never reads — firing nothing, silently. "
                    + "Marking: " + marking);
        }
    }

    @Test
    void restoreAndAnExplicitInitialMarkingCannotBothBeSupplied_AC11() {
        var snapshot = Map.<String, List<Token<?>>>of("a", List.of(new Token<>("x", T1)));
        var initial = Map.<Place<?>, List<Token<?>>>of(A, List.of(new Token<>("y", T2)));

        var ex = assertThrows(IllegalStateException.class,
            () -> create(passThroughNet(), initial, Options.restoring(snapshot)),
            "merging would invent a state neither caller described, and preferring either "
                + "would silently discard the other's tokens");
        assertTrue(ex.getMessage().contains("CORE-073 AC11"),
            "the error cites the criterion. Got: " + ex.getMessage());
    }

    @Test
    void restoreRetainsUnknownPlacesThroughTheExecutor_AC7_AC10() {
        // A snapshot from a net that has since lost 'goneAway'.
        var snapshot = Map.<String, List<Token<?>>>of(
            "a", List.of(new Token<>("x", T1)),
            "goneAway", List.of(new Token<>("orphan", T2)));

        try (var executor = create(passThroughNet(), Map.of(), Options.restoring(snapshot))) {
            var marking = executor.run();
            assertEquals("x", marking.peekFirst(B).value(), "the known place still drives the net");
            assertEquals("orphan",
                marking.peekFirst(Place.of("goneAway", Object.class)).value(),
                "CORE-072: the undeclared place's tokens are retained and inert, not dropped — "
                    + "a snapshot survives a round-trip through a net that lost a place");
            assertEquals(List.of("b", "goneAway"), List.copyOf(executor.snapshot().marking().keySet()),
                "and it is still there in the next snapshot, so a second resume keeps it too");
        }
    }

    @Test
    void aRestoredUnknownPlaceIsReportedOnce_CORE072_AC4() {
        // The diagnostic belongs to the SEED, whichever builder method supplied it: a restore
        // is exactly where an undeclared place turns up — the net lost the place between the
        // snapshot and the resume — so reporting it only for initial tokens would miss the
        // case it exists for.
        var snapshot = Map.<String, List<Token<?>>>of(
            "a", List.of(new Token<>("x", T1)),
            "goneAway", List.of(new Token<>("orphan-1", T2), new Token<>("orphan-2", T2)));
        var store = EventStore.inMemory();

        try (var executor = create(passThroughNet(), Map.of(), new Options(snapshot, null, null, store))) {
            executor.run();
        }

        var warnings = store.events().stream()
            .filter(e -> e instanceof org.libpetri.event.NetEvent.LogMessage m && "WARN".equals(m.level()))
            .map(e -> (org.libpetri.event.NetEvent.LogMessage) e).toList();
        assertEquals(1, warnings.size(),
            "CORE-072 AC#4: once per distinct unknown place, not once per token. Got: " + warnings);
        assertEquals("unknown place 'goneAway': tokens are retained in the marking but inert "
            + "(the net declares no arc on it)", warnings.get(0).message());
        assertEquals("", warnings.get(0).transitionName(), "the seed seam: no transition is firing");
        assertEquals("libpetri.runtime", warnings.get(0).loggerName());
    }

    /** Stamps everything at EPOCH; never waits, so only a net of immediate transitions suits it. */
    private static final class FrozenClock implements ExecutionEnvironment {
        @Override public long nanoTime() { return 0L; }
        @Override public Instant now() { return Instant.EPOCH; }
        @Override public void awaitWork(BooleanSupplier ready, long delayNanos) { }
    }

    @Test
    void restoredTimestampsAreNotRestampedUnderAnInjectedClock_AC9() {
        // Three restored tokens, each left untouched by a different route: one the net never
        // consumes because it already sits downstream, one in a place the net does not declare,
        // and one that IS consumed — whose successor is the control, proving the injected clock
        // is live and would have been the stamp had the engine re-stamped anything.
        var snapshot = Map.<String, List<Token<?>>>of(
            "a", List.of(new Token<>("x", T1)),
            "b", List.of(new Token<>("kept", T2)),
            "goneAway", List.of(new Token<>("orphan", T2)));

        var options = new Options(snapshot, new FrozenClock(), null, null);
        try (var executor = create(passThroughNet(), Map.of(), options)) {
            var marking = executor.run();

            var inB = List.copyOf(marking.peekTokens(B));
            assertEquals(List.of("kept", "x"), inB.stream().map(Token::value).toList(),
                "the restored token keeps its FIFO place ahead of the freshly produced one");
            assertEquals(T2, inB.get(0).createdAt(),
                "CORE-073 AC#9: a restored token keeps the created_at from the snapshot through "
                    + "a RUN under an injected epoch clock. Re-stamping would make a resume "
                    + "indistinguishable from a fresh start.");
            assertEquals(T2, marking.peekFirst(Place.of("goneAway", Object.class)).createdAt(),
                "the retained unknown place is not re-stamped either");
            assertEquals(Instant.EPOCH, inB.get(1).createdAt(),
                "control: the token the net PRODUCED carries the injected clock, so the clock "
                    + "was live and the assertions above are not passing for want of one");
        }
    }

    // ============================================================
    //  ENV-014 AC#4 / AC#5 / AC#6
    // ============================================================

    /** {@code in -t-> out}; {@code t} parks on {@code release} off-thread. */
    private static PetriNet gatedNet(CountDownLatch started, CountDownLatch release) {
        return PetriNet.builder("slow").transition(Transition.builder("t")
            .inputs(one(IN)).outputs(place(OUT))
            .action(ctx -> CompletableFuture.supplyAsync(() -> {
                started.countDown();
                try { release.await(10, TimeUnit.SECONDS); } catch (InterruptedException e) { Thread.currentThread().interrupt(); }
                ctx.output(OUT, "done");
                return null;
            }))
            .build()).build();
    }

    private static Map<Place<?>, List<Token<?>>> oneIn() {
        return Map.of(IN, List.of(new Token<>("x", T1)));
    }

    @Test
    void aSnapshotTakenMidFlightSaysSo_AndTheOneAtQuiescenceRestores_ENV014_AC5_AC6() throws Exception {
        var release = new CountDownLatch(1);
        var started = new CountDownLatch(1);

        SnapshotResult atRest;
        try (var executor = create(gatedNet(started, release), oneIn(), Options.none())) {
            var run = CompletableFuture.supplyAsync(executor::run);
            assertTrue(started.await(10, TimeUnit.SECONDS), "the action started");

            var mid = executor.snapshot();
            assertTrue(mid.actionInFlight(),
                "ENV-014 AC#5: a snapshot taken while an action is in flight must be "
                    + "distinguishable from one taken at rest — the flag travels WITH the "
                    + "marking so the two describe the same instant");
            assertFalse(mid.isRestorePoint(), "isRestorePoint() is the same fact, negated");
            assertFalse(mid.marking().containsKey("in"),
                "ENV-014 AC#6: the in-flight firing already consumed its input (EXEC-031, no "
                    + "rollback) and its output has not landed, so the only marked place is "
                    + "empty. That is why a mid-flight snapshot is an observation, not a "
                    + "restore point. Marking: " + mid.marking());

            release.countDown();
            run.get(20, TimeUnit.SECONDS);
            assertEquals(TerminationReason.QUIESCENT, executor.terminationReason());

            // The other half of the spec's own test derivation: "release the gate, snapshot
            // again at quiescence, and assert that one restores".
            atRest = executor.snapshot();
            assertFalse(atRest.actionInFlight(),
                "ENV-014 AC#5: nothing is in flight at quiescence, and the flag must describe "
                    + "THIS marking's instant. It used to be the last value a mid-run request "
                    + "happened to publish — still true here — so a checkpointer honouring it "
                    + "refused the one snapshot that IS a restore point. Got: " + atRest);
            assertTrue(atRest.isRestorePoint());
            assertEquals(List.of("out"), List.copyOf(atRest.marking().keySet()));
        }

        try (var resumed = create(gatedNet(new CountDownLatch(1), new CountDownLatch(0)),
                Map.of(), Options.restoring(atRest.marking()))) {
            assertEquals("done", resumed.run().peekFirst(OUT).value(), "and that one restores");
        }
    }

    @Test
    void aNeverStartedExecutorSnapshotsItsInitialMarkingAtRest_ENV014() {
        try (var executor = create(passThroughNet(), Map.of(A, List.of(new Token<>("x", T1))), Options.none())) {
            var snapshot = executor.snapshot();
            assertEquals(List.of("a"), List.copyOf(snapshot.marking().keySet()));
            assertFalse(snapshot.actionInFlight(), "nothing has fired, nothing is queued");
        }
    }

    @Test
    void snapshotIsRejectedAfterClose_ENV014_AC4() {
        var executor = create(passThroughNet(), Map.of(A, List.of(new Token<>("x", T1))), Options.none());
        executor.run();
        executor.close();
        var ex = assertThrows(IllegalStateException.class, executor::snapshot);
        assertTrue(ex.getMessage().contains("ENV-014"),
            "the error says which requirement and points at marking(). Got: " + ex.getMessage());
    }

    // ============================================================
    //  ENV-014 AC#5 — the pair is ONE value on the reading side too
    // ============================================================

    @Test
    void concurrentCallersNeverPairAMarkingWithAFlagFromAnotherInstant_ENV014_AC5() throws Exception {
        // One token circulating a -t1-> b -t2-> a, where t1's action completes off-thread. At
        // every instant the orchestrator can capture, EXACTLY ONE holds: the token is in the
        // marking, or t1 is in flight holding it. A snapshot showing neither (a "restore point"
        // with the only token missing) or both can only be a marking and a flag from two
        // different captures glued together on the caller's side.
        var net = PetriNet.builder("ping-pong")
            .transition(Transition.builder("t1").inputs(one(A)).outputs(place(B))
                .action(ctx -> {
                    var value = ctx.input(A);
                    return CompletableFuture.runAsync(() -> ctx.output(B, value));
                }).build())
            .transition(Transition.builder("t2").inputs(one(B)).outputs(place(A))
                .action(ctx -> { ctx.output(A, ctx.input(B)); return CompletableFuture.completedFuture(null); })
                .build())
            .build();

        int callers = 16;
        var snapshots = new AtomicLong();
        var torn = new AtomicReference<SnapshotResult>();
        var tornCount = new AtomicLong();

        try (var executor = create(net, Map.of(A, List.of(new Token<>("x", T1))), Options.none())) {
            var run = CompletableFuture.supplyAsync(executor::run);
            var threads = new ArrayList<Thread>();
            // 1 s, not more: with the pair read as two volatiles this tears 100-190 times in
            // ~11 000 snapshots per second on either executor, so a second is ample to go red.
            long deadline = System.nanoTime() + Duration.ofSeconds(1).toNanos();
            for (int i = 0; i < callers; i++) {
                threads.add(Thread.ofPlatform().start(() -> {
                    while (System.nanoTime() < deadline) {
                        var s = executor.snapshot();
                        snapshots.incrementAndGet();
                        if (s.marking().isEmpty() != s.actionInFlight()) {
                            tornCount.incrementAndGet();
                            torn.compareAndSet(null, s);
                        }
                    }
                }));
            }
            for (var t : threads) t.join();
            executor.close(); // the net never quiesces on its own
            run.get(20, TimeUnit.SECONDS);
        }

        assertTrue(snapshots.get() > 1_000, "the callers really did contend: " + snapshots.get());
        assertNull(torn.get(),
            "ENV-014 AC#5: the marking and the flag MUST describe the same instant. "
                + tornCount.get() + " of " + snapshots.get() + " snapshots did not — capturing the "
                + "pair atomically on the orchestrator is half of it; the caller must also READ "
                + "it as one value, not as two volatiles a later request can republish between. "
                + "First: " + torn.get());
    }

    // ============================================================
    //  ENV-014 — work in flight includes an accepted but un-injected event
    // ============================================================

    private static final EnvironmentPlace<String> EVENTS = EnvironmentPlace.of(Place.of("events", String.class));

    private static PetriNet reactiveNet(Runnable duringHold) {
        return PetriNet.builder("reactive")
            .transition(Transition.builder("hold").inputs(one(A)).outputs(place(B))
                .action(ctx -> {
                    duringHold.run(); // inline: the orchestrator is parked in here
                    ctx.output(B, ctx.input(A));
                    return CompletableFuture.completedFuture(null);
                }).build())
            .transition(Transition.builder("react").inputs(one(EVENTS.place())).outputs(place(OUT))
                .timing(Timing.delayed(Duration.ofHours(1))) // keeps the injected token visible
                .action(ctx -> { ctx.output(OUT, ctx.input(EVENTS.place())); return CompletableFuture.completedFuture(null); })
                .build())
            .build();
    }

    @Test
    void anAcceptedEventQueuedBeforeTheRunIsWorkInFlight_ENV014_AC7() {
        var options = new Options(null, null, Set.of(EVENTS), null);
        try (var executor = create(reactiveNet(() -> { }), Map.of(), options)) {
            executor.injectAsync(EVENTS, new Token<>("e", T1)); // accepted: queued, no loop yet

            var snapshot = executor.snapshot();
            assertFalse(snapshot.marking().containsKey("events"),
                "the event is queued, not injected — it is in no place yet");
            assertTrue(snapshot.actionInFlight(),
                "ENV-014: a snapshot is not a restore point while an ACCEPTED external event is "
                    + "not yet injected. The host was told the token was taken; it is in the "
                    + "queue and not in the marking, so restoring this snapshot drops it exactly "
                    + "as an in-flight action's inputs are dropped. Got: " + snapshot);
        }
    }

    @Test
    void aRestorePointNeverOmitsAnAcceptedEvent_ENV014_AC7() throws Exception {
        var holding = new CountDownLatch(1);
        var letGo = new CountDownLatch(1);
        Runnable hold = () -> {
            holding.countDown();
            try { letGo.await(10, TimeUnit.SECONDS); } catch (InterruptedException e) { Thread.currentThread().interrupt(); }
        };
        var options = new Options(null, null, Set.of(EVENTS), null);
        try (var executor = create(reactiveNet(hold), Map.of(A, List.of(new Token<>("x", T1))), options)) {
            var run = CompletableFuture.supplyAsync(executor::run);
            assertTrue(holding.await(10, TimeUnit.SECONDS), "the orchestrator is inside 'hold'");

            // Accepted while the orchestrator cannot reach its external-events phase…
            executor.injectAsync(EVENTS, new Token<>("e", T1));
            // …and a snapshot requested behind it, serviced on the first cycle after 'hold'.
            var pending = CompletableFuture.supplyAsync(executor::snapshot);
            Thread.sleep(100); // let the request register before the orchestrator moves on
            letGo.countDown();

            var snapshot = pending.get(20, TimeUnit.SECONDS);
            assertTrue(snapshot.marking().containsKey("events") || snapshot.actionInFlight(),
                "ENV-014: either the accepted event made it into the captured marking, or the "
                    + "snapshot says it is not a restore point. A snapshot that omits the event "
                    + "AND calls itself restorable loses the token on resume. Got: " + snapshot);

            executor.close();
            run.get(20, TimeUnit.SECONDS);
        }
    }

    @Test
    void anUnservedSnapshotIsNeverARestorePoint_ENV014_AC7() throws Exception {
        // The best-effort cap. 'consume' takes the injected event and then blocks INLINE, so
        // the orchestrator cannot service a request. The pair it last published is the
        // loop-start one: (empty marking, nothing in flight) — true when it was captured.
        var holding = new CountDownLatch(1);
        var letGo = new CountDownLatch(1);
        var net = PetriNet.builder("blocking-consumer")
            .transition(Transition.builder("consume").inputs(one(EVENTS.place())).outputs(place(OUT))
                .action(ctx -> {
                    holding.countDown();
                    try { letGo.await(20, TimeUnit.SECONDS); } catch (InterruptedException e) { Thread.currentThread().interrupt(); }
                    ctx.output(OUT, ctx.input(EVENTS.place()));
                    return CompletableFuture.completedFuture(null);
                }).build())
            .build();
        var started = new CountDownLatch(1);
        var store = new EventStore() {
            @Override public void append(org.libpetri.event.NetEvent event) {
                if (event instanceof org.libpetri.event.NetEvent.ExecutionStarted) started.countDown();
            }
            @Override public List<org.libpetri.event.NetEvent> events() { return List.of(); }
            @Override public boolean isEnabled() { return true; }
        };
        var options = new Options(null, null, Set.of(EVENTS), store);
        try (var executor = create(net, Map.of(), options)) {
            var run = CompletableFuture.supplyAsync(executor::run);
            try {
                // Only once the loop runs: its loop-start capture precedes ExecutionStarted, so
                // the pair published so far is the idle one — and a SERVED request confirms it.
                assertTrue(started.await(10, TimeUnit.SECONDS), "the loop is running");
                assertEquals(new SnapshotResult(Map.of(), false), executor.snapshot(), "idle and empty");
                snapshotCap(executor, Duration.ofMillis(100));

                executor.injectAsync(EVENTS, new Token<>("e", T1));
                assertTrue(holding.await(10, TimeUnit.SECONDS), "'consume' holds the accepted event");

                var snapshot = executor.snapshot(); // times out: nobody can serve it

                assertFalse(snapshot.marking().containsKey("events") || snapshot.marking().containsKey("out"),
                    "the premise: the accepted event is in no place of the returned marking. Got: " + snapshot);
                assertTrue(snapshot.actionInFlight(),
                    "ENV-014 AC#7: a request the orchestrator did not serve within the cap hands "
                        + "back the LAST PUBLISHED marking, and that pair's flag describes an older "
                        + "instant. An accepted event has since been consumed by a firing that is "
                        + "still running, so it is in neither the marking nor the old flag. An "
                        + "unserved request is never a restore point. Got: " + snapshot);
                assertFalse(snapshot.isRestorePoint());
            } finally {
                letGo.countDown();
                executor.close();
                run.get(20, TimeUnit.SECONDS);
            }
        }
    }

    // ============================================================
    //  snapshot() from inside an action (Java runs actions inline)
    // ============================================================

    @Test
    void snapshotFromInsideAnActionReturnsAtOnceAndIsNotARestorePoint_ENV014_AC8() {
        var self = new AtomicReference<PetriNetExecutor>();
        var taken = new AtomicReference<SnapshotResult>();
        var tookNanos = new AtomicLong();
        var net = PetriNet.builder("checkpointing").transition(Transition.builder("checkpoint")
            .inputs(one(A)).outputs(place(B))
            .action(ctx -> {
                long t0 = System.nanoTime();
                taken.set(self.get().snapshot());
                tookNanos.set(System.nanoTime() - t0);
                ctx.output(B, ctx.input(A));
                return CompletableFuture.completedFuture(null);
            }).build()).build();

        var initial = Map.<Place<?>, List<Token<?>>>of(
            A, List.of(new Token<>("x", T1)),
            B, List.of(new Token<>("already", T2)));
        try (var executor = create(net, initial, Options.none())) {
            self.set(executor);
            executor.run();
        }

        var snapshot = taken.get();
        assertNotNull(snapshot, "the action ran");
        assertTrue(tookNanos.get() < Duration.ofSeconds(1).toNanos(),
            "Java invokes actions inline on the orchestrator thread, so the only thread that "
                + "can service a snapshot request is the one asking. It must capture directly, "
                + "never park waiting for itself — that froze the whole net for the 2s cap. "
                + "Took: " + Duration.ofNanos(tookNanos.get()));
        assertEquals(List.of("b"), List.copyOf(snapshot.marking().keySet()),
            "the LIVE marking: this firing's input is already consumed (EXEC-031). The stale "
                + "published copy still showed it, which duplicates the token on resume. Got: "
                + snapshot.marking());
        assertTrue(snapshot.actionInFlight(),
            "the calling firing has consumed its inputs and not produced its outputs, so it "
                + "is in flight by definition and this is never a restore point. Got: " + snapshot);
    }

    @Test
    void snapshotFromAnActionsContinuationIsServedAndIsNotARestorePoint_ENV014_AC8() {
        // The other half of AC#8: the action has SUSPENDED — returned its future — and asks
        // from the continuation, on another thread. That is an ordinary foreign request: the
        // orchestrator is free, serves it within a cycle, and the asking firing is in flight.
        var self = new AtomicReference<PetriNetExecutor>();
        var taken = new AtomicReference<SnapshotResult>();
        var tookNanos = new AtomicLong();
        var net = PetriNet.builder("checkpointing-async").transition(Transition.builder("checkpoint")
            .inputs(one(A)).outputs(place(B))
            .action(ctx -> {
                var value = ctx.input(A);
                return CompletableFuture.runAsync(() -> {
                    long t0 = System.nanoTime();
                    taken.set(self.get().snapshot());
                    tookNanos.set(System.nanoTime() - t0);
                    ctx.output(B, value);
                }, CompletableFuture.delayedExecutor(20, TimeUnit.MILLISECONDS));
            }).build()).build();

        try (var executor = create(net, Map.of(A, List.of(new Token<>("x", T1))), Options.none())) {
            self.set(executor);
            var marking = executor.run();
            assertEquals(1, marking.tokenCount(B), "the run carried on afterwards (AC#2)");
        }

        var snapshot = taken.get();
        assertNotNull(snapshot, "the continuation ran");
        assertTrue(tookNanos.get() < Duration.ofSeconds(1).toNanos(),
            "served by the orchestrator, not timed out at the 2s cap. Took: " + Duration.ofNanos(tookNanos.get()));
        assertEquals(Map.of(), snapshot.marking(), "the firing's input is consumed, its output not yet produced");
        assertTrue(snapshot.actionInFlight(), "ENV-014 AC#8: not a restore point. Got: " + snapshot);
    }

    // ============================================================
    //  The start window: run() called, loop not yet running
    // ============================================================

    @Test
    void foreignReadersWaitOutTheStartWindowInsteadOfReadingTheLiveMarking() throws Exception {
        // run(Duration) hands the loop to an executor; until a thread picks it up there is no
        // orchestrator to ask. A foreign marking()/snapshot() that took that for "never
        // started" read — Precompiled: REBUILT — the live marking just as the loop's first
        // cycle began mutating it: ConcurrentModificationException, intermittently.
        var gate = new CountDownLatch(1);
        var pool = java.util.concurrent.Executors.newCachedThreadPool();
        java.util.concurrent.Executor gated = task -> pool.execute(() -> {
            try { gate.await(10, TimeUnit.SECONDS); } catch (InterruptedException e) { return; }
            task.run();
        });
        var gatedService = new java.util.concurrent.AbstractExecutorService() {
            @Override public void execute(Runnable command) { gated.execute(command); }
            @Override public void shutdown() { }
            @Override public List<Runnable> shutdownNow() { return List.of(); }
            @Override public boolean isShutdown() { return false; }
            @Override public boolean isTerminated() { return false; }
            @Override public boolean awaitTermination(long timeout, TimeUnit unit) { return true; }
        };
        var options = new Options(null, null, null, null, gatedService);
        try (var executor = create(passThroughNet(), Map.of(A, List.of(new Token<>("x", T1))), options)) {
            var run = executor.run(Duration.ofSeconds(20));           // started, loop still gated
            var marking = CompletableFuture.supplyAsync(executor::marking, pool);
            var snapshot = CompletableFuture.supplyAsync(executor::snapshot, pool);

            Thread.sleep(150);
            assertFalse(marking.isDone(), "marking() must not read the live marking behind a loop "
                + "that is about to start");
            assertFalse(snapshot.isDone(), "nor may snapshot()");

            gate.countDown();
            run.toCompletableFuture().get(20, TimeUnit.SECONDS);
            assertNotNull(marking.get(10, TimeUnit.SECONDS));
            assertNotNull(snapshot.get(10, TimeUnit.SECONDS));
        } finally {
            pool.shutdownNow();
        }
    }

    // ============================================================
    //  MOD-024 — two places, one name
    // ============================================================

    private static final Place<String>  X_STRING  = Place.of("x", String.class);
    private static final Place<Integer> X_INTEGER = Place.of("x", Integer.class);

    /** Legal in Java only: {@code Place} equality is structural over (name, tokenType). */
    private static PetriNet sameNamedPlacesNet() {
        return PetriNet.builder("same-name")
            .transition(Transition.builder("s").inputs(one(X_STRING)).outputs(place(OUT))
                .timing(Timing.delayed(Duration.ofHours(1)))
                .action(ctx -> CompletableFuture.completedFuture(null)).build())
            .transition(Transition.builder("i").inputs(one(X_INTEGER)).outputs(place(OUT))
                .timing(Timing.delayed(Duration.ofHours(1)))
                .action(ctx -> CompletableFuture.completedFuture(null)).build())
            .build();
    }

    @Test
    void snapshotRejectsANetWithTwoPlacesOfOneName_CORE073_AC10_MOD024() {
        var initial = Map.<Place<?>, List<Token<?>>>of(
            X_STRING, List.of(new Token<>("s", T1)),
            X_INTEGER, List.of(new Token<>(1, T1)));
        try (var executor = create(sameNamedPlacesNet(), initial, Options.none())) {
            var ex = assertThrows(IllegalStateException.class, executor::snapshot,
                "the snapshot form is keyed by place NAME, so two places named 'x' collapse "
                    + "into one entry and one place's tokens vanish from a restore point with "
                    + "no error. It must be loud, and on the caller's thread.");
            assertTrue(ex.getMessage().contains("'x'") && ex.getMessage().contains("MOD-024"),
                "names the place and the requirement. Got: " + ex.getMessage());
        }
    }

    @Test
    void restoreRejectsANetWithTwoPlacesOfOneName_CORE073_AC10_MOD024() {
        var snapshot = Map.<String, List<Token<?>>>of("x", List.of(new Token<>("s", T1)));
        var ex = assertThrows(IllegalArgumentException.class,
            () -> create(sameNamedPlacesNet(), Map.of(), Options.restoring(snapshot)),
            "which 'x' the tokens belong to is not recoverable from the name; picking one by "
                + "iteration order lands them on the wrong place or the right one by luck");
        assertTrue(ex.getMessage().contains("'x'") && ex.getMessage().contains("MOD-024"),
            "names the place and the requirement. Got: " + ex.getMessage());
    }

    @Test
    void theMarkingSnapshotEventNeverThrowsOnSuchANet_MOD024() {
        // emitMarkingSnapshot runs on the orchestrator thread at run start and in the loop's
        // finally. Throwing there aborts the run, or skips ExecutionCompleted — so the loud
        // failure belongs to snapshot()/restore() on the caller's thread, never to the event.
        var store = EventStore.inMemory();
        var initial = Map.<Place<?>, List<Token<?>>>of(
            X_STRING, List.of(new Token<>("s", T1)),
            X_INTEGER, List.of(new Token<>(1, T1)));
        var options = new Options(null, null, null, store);
        try (var executor = create(sameNamedPlacesNet(), initial, options)) {
            var self = executor;
            Thread.ofPlatform().start(() -> {
                try { Thread.sleep(200); } catch (InterruptedException e) { return; }
                self.close();
            });
            executor.run();
        }
        var snapshots = store.events().stream()
            .filter(e -> e instanceof org.libpetri.event.NetEvent.MarkingSnapshot).toList();
        assertEquals(2, snapshots.size(), "one at start, one at the end: " + store.events());
        var last = (org.libpetri.event.NetEvent.MarkingSnapshot) snapshots.getLast();
        assertEquals(2, last.marking().get("x").size(),
            "and the event keeps BOTH places' tokens under the shared name rather than letting "
                + "one overwrite the other: " + last.marking());
        assertTrue(store.events().stream()
                .anyMatch(e -> e instanceof org.libpetri.event.NetEvent.ExecutionCompleted),
            "the run reported completion");
    }

    // ============================================================
    //  ENV-014 AC#9 — a parked executor answers without waking
    // ============================================================

    /** {@code in -> out} (sync), and an environment place that keeps the run alive once done. */
    private static PetriNet parkingNet() {
        return PetriNet.builder("parking")
            .transition(Transition.builder("t").inputs(one(IN)).outputs(place(OUT))
                .action(ctx -> { ctx.output(OUT, ctx.input(IN)); return CompletableFuture.completedFuture(null); })
                .build())
            .transition(Transition.builder("absorb").inputs(one(EVENTS.place())).outputs(place(OUT))
                .action(ctx -> { ctx.output(OUT, ctx.input(EVENTS.place())); return CompletableFuture.completedFuture(null); })
                .build())
            .build();
    }

    private void awaitParked(PetriNetExecutor executor) {
        long giveUp = System.nanoTime() + Duration.ofSeconds(10).toNanos();
        while (!parked(executor) && System.nanoTime() < giveUp) Thread.onSpinWait();
        assertTrue(parked(executor), "the premise: the orchestrator is parked in its wait");
    }

    @Test
    void aParkedExecutorAnswersAForeignReadWithoutWaking_BuiltInWait_ENV014_AC9() throws Exception {
        try (var executor = create(parkingNet(), Map.of(IN, List.of(new Token<>("x", T1))),
                new Options(null, null, Set.of(EVENTS), null))) {
            var run = CompletableFuture.supplyAsync(executor::run);
            try {
                awaitParked(executor);
                long requestsBefore = markingRequests(executor);

                var marking = executor.marking();
                var snapshot = executor.snapshot();

                assertEquals(requestsBefore, markingRequests(executor),
                    "ENV-014 AC#9: a foreign read of a parked orchestrator is answered without its "
                        + "participation — no request is registered, so nothing wakes it");
                assertTrue(marking.hasTokens(OUT) && !marking.hasTokens(IN),
                    "AC#9: the CURRENT marking, not the loop-start one it published. Got: " + marking);
                assertEquals(List.of("x"), snapshot.marking().get("out").stream().map(Token::value).toList(),
                    "the snapshot is current too. Got: " + snapshot);
                assertFalse(snapshot.marking().containsKey("in"), "Got: " + snapshot);
                assertFalse(snapshot.actionInFlight(),
                    "AC#9: the work-in-flight flag is computed as for any capture — nothing is in "
                        + "flight and nothing is queued, so this is a restore point");
            } finally {
                executor.close();
                run.get(20, TimeUnit.SECONDS);
            }
        }
    }

    @Test
    void aParkedExecutorAnswersAForeignReadWithoutWaking_HostedWait_ENV014_AC9() throws Exception {
        // A host that holds its wait until told otherwise, as a deterministic workflow runtime
        // does while it answers a query under the lock the orchestrator would need to return.
        var entered = new CountDownLatch(1);
        var letGo = new CountDownLatch(1);
        var readiness = new AtomicReference<BooleanSupplier>();
        var host = new ExecutionEnvironment() {
            @Override public long nanoTime() { return System.nanoTime(); }
            @Override public Instant now() { return Instant.now(); }
            @Override public void awaitWork(BooleanSupplier ready, long delayNanos) {
                readiness.set(ready);
                entered.countDown();
                try { letGo.await(20, TimeUnit.SECONDS); } catch (InterruptedException e) { Thread.currentThread().interrupt(); }
            }
        };
        try (var executor = create(parkingNet(), Map.of(IN, List.of(new Token<>("x", T1))),
                new Options(null, host, Set.of(EVENTS), null))) {
            snapshotCap(executor, Duration.ofSeconds(30)); // an engaged protocol would stall 30 s
            var run = CompletableFuture.supplyAsync(executor::run);
            try {
                assertTrue(entered.await(10, TimeUnit.SECONDS), "the host's wait was entered");
                long requestsBefore = markingRequests(executor);

                var marking = CompletableFuture.supplyAsync(executor::marking).get(5, TimeUnit.SECONDS);
                var snapshot = CompletableFuture.supplyAsync(executor::snapshot).get(5, TimeUnit.SECONDS);

                assertEquals(requestsBefore, markingRequests(executor),
                    "ENV-014 AC#9: no request is registered against a parked orchestrator");
                assertFalse(readiness.get().getAsBoolean(),
                    "AC#9: the read did not make the host's readiness predicate true — the host "
                        + "is never asked to return from its wait to answer a read");
                assertTrue(marking.hasTokens(OUT) && !marking.hasTokens(IN),
                    "AC#9: the current marking. Got: " + marking);
                assertTrue(snapshot.marking().containsKey("out") && !snapshot.actionInFlight(),
                    "Got: " + snapshot);
            } finally {
                executor.close();
                letGo.countDown();
                run.get(20, TimeUnit.SECONDS);
            }
        }
    }

    @Test
    void aParkedReadReportsAnEventQueuedButNotAdmittedAsWorkInFlight_ENV014_AC9() throws Exception {
        var entered = new CountDownLatch(1);
        var letGo = new CountDownLatch(1);
        var host = new ExecutionEnvironment() {
            @Override public long nanoTime() { return System.nanoTime(); }
            @Override public Instant now() { return Instant.now(); }
            @Override public void awaitWork(BooleanSupplier ready, long delayNanos) {
                entered.countDown();
                try { letGo.await(20, TimeUnit.SECONDS); } catch (InterruptedException e) { Thread.currentThread().interrupt(); }
            }
        };
        try (var executor = create(parkingNet(), Map.of(), new Options(null, host, Set.of(EVENTS), null))) {
            var run = CompletableFuture.supplyAsync(executor::run);
            try {
                assertTrue(entered.await(10, TimeUnit.SECONDS), "the host's wait was entered");
                executor.injectAsync(EVENTS, new Token<>("e", T1)); // accepted, not yet admitted
                var snapshot = CompletableFuture.supplyAsync(executor::snapshot).get(5, TimeUnit.SECONDS);
                assertFalse(snapshot.marking().containsKey("events"),
                    "the premise: the event is still queued, so it is in no place. Got: " + snapshot);
                assertTrue(snapshot.actionInFlight(),
                    "AC#9 with AC#5-AC#7: a parked read computes the work-in-flight flag with the "
                        + "same expression as any capture, so an accepted but unadmitted event "
                        + "keeps it from being a restore point. Got: " + snapshot);
            } finally {
                executor.close();
                letGo.countDown();
                run.get(20, TimeUnit.SECONDS);
            }
        }
    }
}
