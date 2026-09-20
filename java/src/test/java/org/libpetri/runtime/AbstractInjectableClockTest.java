package org.libpetri.runtime;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.libpetri.core.*;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.function.BooleanSupplier;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.core.Arc.In.one;
import static org.libpetri.core.Arc.Out.place;

/**
 * Conformance suite for the <b>TIME-015</b> injectable clock, run against both executors.
 *
 * <p>The seam is behavioural, so these assert on executor runs. Where a criterion is about
 * what the executor did <i>not</i> do — wait out an interval it should have short-circuited,
 * fire before a bound — the {@link VirtualClock} records it, since the absence of a wait is
 * not otherwise observable.
 *
 * @see ExecutionEnvironment
 */
@Timeout(60)
abstract class AbstractInjectableClockTest {

    protected abstract PetriNetExecutor create(
        PetriNet net, Map<Place<?>, List<Token<?>>> initial, ExecutionEnvironment env);

    protected abstract PetriNetExecutor create(
        PetriNet net, Map<Place<?>, List<Token<?>>> initial, ExecutionEnvironment env,
        Duration deadlineTolerance, Set<EnvironmentPlace<?>> envPlaces);

    // ============================================================
    //  A host clock: advances only when the wait asks it to.
    // ============================================================

    static class VirtualClock implements ExecutionEnvironment {
        long nanos;
        /** Every wait, including ones that returned immediately. */
        int waits;
        /** Waits that actually advanced the clock. */
        int advancingWaits;
        /** Delays the executor asked for, in order. */
        final List<Long> requestedDelays = new ArrayList<>();
        /** Readings of {@link #nanoTime()}, to prove a coarse clock repeats (AC#10). */
        int firingClockReads;
        /** Run once, at the next wait, before anything else. */
        Runnable atNextWait;
        /** Like {@link #atNextWait}, but handed the live readiness predicate. */
        java.util.function.Consumer<BooleanSupplier> atNextWaitWithReady;
        /** Return without advancing this many times first (contract point 3). */
        int spuriousReturns;
        /**
         * Run when the executor waits with no timer and no work. A net holding environment
         * places waits for input indefinitely rather than terminating, so this is the host's
         * "nothing more is coming" hook, not an error.
         */
        Runnable atIdle;
        /**
         * Extra nanos added when advancing, modelling a host clock that lands past the
         * boundary rather than exactly on it.
         */
        long overshootNanos;

        @Override public long nanoTime() { firingClockReads++; return nanos; }
        @Override public Instant now() { return Instant.EPOCH.plusNanos(nanos); }

        @Override public void awaitWork(BooleanSupplier ready, long delayNanos) {
            waits++;
            requestedDelays.add(delayNanos);
            assertTrue(delayNanos >= 0, "delay must never be negative, was " + delayNanos);

            if (atNextWait != null) { var r = atNextWait; atNextWait = null; r.run(); }
            if (atNextWaitWithReady != null) {
                var c = atNextWaitWithReady; atNextWaitWithReady = null; c.accept(ready);
            }
            // The signal half: never wait out an interval when work is already available.
            if (ready.getAsBoolean()) return;
            if (spuriousReturns > 0) { spuriousReturns--; return; }
            if (delayNanos == Long.MAX_VALUE) {
                if (atIdle != null) { atIdle.run(); return; }
                throw new AssertionError("wait with no timer and no work — the net would hang");
            }
            nanos += delayNanos + overshootNanos;
            advancingWaits++;
        }
    }

    // ============================================================
    //  Fixtures
    // ============================================================

    private static final Place<String> IN  = Place.of("in",  String.class);
    private static final Place<String> OUT = Place.of("out", String.class);

    /** One transition, {@code in -> out}, carrying {@code timing}. */
    private static PetriNet timedNet(Timing timing) {
        return PetriNet.builder("timed").transition(Transition.builder("t")
            .inputs(one(IN)).outputs(place(OUT)).timing(timing)
            .action(ctx -> { ctx.output(OUT, ctx.input(IN)); return CompletableFuture.completedFuture(null); })
            .build()).build();
    }

    /** A seed marking at an explicit timestamp — the TIME-015 escape hatch (AC#12). */
    private static Map<Place<?>, List<Token<?>>> seed() {
        return Map.of(IN, List.of(new Token<>("x", Instant.EPOCH)));
    }

    // ============================================================
    //  AC#2 — per-executor, not per-process
    // ============================================================

    @Test
    void twoExecutorsOnIndependentClocksDoNotObserveEachOther_AC2() {
        var a = new VirtualClock();
        var b = new VirtualClock();

        try (var executorA = create(timedNet(Timing.delayed(Duration.ofSeconds(5))), seed(), a);
             var executorB = create(timedNet(Timing.delayed(Duration.ofSeconds(9))), seed(), b)) {
            executorA.run();
            assertEquals(Duration.ofSeconds(5).toNanos(), a.nanos, "A's clock advanced to its own bound");
            assertEquals(0L, b.nanos,
                "TIME-015 AC#2: advancing one executor's clock must not advance another's — "
                    + "the seam is per executor, never per net or per process");

            executorB.run();
            assertEquals(Duration.ofSeconds(9).toNanos(), b.nanos);
            assertEquals(Duration.ofSeconds(5).toNanos(), a.nanos, "A is unmoved by B's run");
        }
    }

    // ============================================================
    //  AC#3 — virtual time costs no real time
    // ============================================================

    @Test
    void delayedReachesQuiescenceWithoutRealTimeElapsing_AC3() {
        var clock = new VirtualClock();
        long realStart = System.nanoTime();
        try (var executor = create(timedNet(Timing.delayed(Duration.ofHours(6))), seed(), clock)) {
            var marking = executor.run();
            long realElapsed = System.nanoTime() - realStart;

            assertTrue(marking.hasTokens(OUT), "the delayed transition fired. Marking: " + marking);
            assertEquals(Duration.ofHours(6).toNanos(), clock.nanos, "logical time reached the bound");
            assertTrue(realElapsed < Duration.ofSeconds(10).toNanos(),
                "TIME-015 AC#3: a 6-hour delay under a host clock must cost negligible real time. "
                    + "The seam owns the wait, so nothing sleeps. Real elapsed: "
                    + Duration.ofNanos(realElapsed));
            assertEquals(Instant.EPOCH.plusNanos(clock.nanos), marking.peekFirst(OUT).createdAt(),
                "the produced token is stamped from the epoch clock, not the wall clock");
        }
    }

    // ============================================================
    //  AC#4 — spurious completion fires nothing early
    // ============================================================

    @Test
    void spuriousWaitCompletionDoesNotFireBeforeEarliestBound_AC4() {
        var clock = new VirtualClock();
        clock.spuriousReturns = 5;
        try (var executor = create(timedNet(Timing.delayed(Duration.ofSeconds(5))), seed(), clock)) {
            var marking = executor.run();

            assertTrue(clock.waits > clock.advancingWaits,
                "the clock returned spuriously at least once (waits=" + clock.waits
                    + ", advancing=" + clock.advancingWaits + ")");
            assertEquals(Duration.ofSeconds(5).toNanos(), clock.nanos,
                "TIME-015 AC#4: a wait completing early and for no reason must not fire a "
                    + "transition before its earliest bound — the executor re-checks the "
                    + "boundary and never reads 'the wait returned' as 'the boundary is reached'");
            assertEquals(Instant.EPOCH.plusSeconds(5), marking.peekFirst(OUT).createdAt());
        }
    }

    // ============================================================
    //  AC#5 — abort completes rather than fails
    // ============================================================

    @Test
    void waitAbortedDuringShutdownCompletesAndTerminatesCleanly_AC5() {
        var clock = new VirtualClock();
        var executor = create(timedNet(Timing.delayed(Duration.ofHours(1))), seed(), clock);
        // Shut down from inside the wait — the ENV-013 path, on which a failing wait is most
        // likely to escape unobserved.
        clock.atNextWait = executor::close;

        Marking marking = assertDoesNotThrow((org.junit.jupiter.api.function.ThrowingSupplier<Marking>) executor::run,
            "TIME-015 AC#5: a wait aborted during shutdown must complete rather than fail, "
                + "and the executor must terminate with no escaping failure (ENV-013)");
        assertNotNull(marking);
        assertDoesNotThrow(executor::close, "close is idempotent");
    }

    // ============================================================
    //  AC#6 — deadline reaped exactly at its bound under tolerance 0
    // ============================================================

    @Test
    void deadlineIsReapedAtExactlyItsBoundUnderZeroTolerance_AC6() {
        // A transition that may only fire in the single instant at 5s. The clock lands 1ms
        // PAST that instant, which is the discrepancy tolerance exists to absorb — and which
        // TIME-015 says a host verifying deadline behaviour must stop absorbing.
        var net = timedNet(Timing.window(Duration.ofSeconds(5), Duration.ofSeconds(5)));

        var strict = new VirtualClock();
        strict.overshootNanos = Duration.ofMillis(1).toNanos();
        try (var executor = create(net, seed(), strict, Duration.ZERO, Set.of())) {
            var marking = executor.run();
            assertFalse(marking.hasTokens(OUT),
                "TIME-015 AC#6: with tolerance 0 a transition whose deadline has passed is "
                    + "force-disabled at exactly its bound and never fires. Marking: " + marking);
        }

        // Same net, same clock behaviour, default tolerance: the grace band absorbs the
        // overshoot and the transition still fires. This is the masking TIME-015 warns about
        // — left at its default, the tolerance hides precisely what a virtual clock exposes.
        var lenient = new VirtualClock();
        lenient.overshootNanos = Duration.ofMillis(1).toNanos();
        try (var executor = create(net, seed(), lenient)) {
            var marking = executor.run();
            assertTrue(marking.hasTokens(OUT),
                "the default tolerance absorbs the same overshoot — which is why a host "
                    + "verifying deadline behaviour should set it to 0. Marking: " + marking);
        }
    }

    // ============================================================
    //  AC#7 — boundary already due advances rather than waits
    // ============================================================

    @Test
    void boundaryAlreadyDueAdvancesOnNextCycleRatherThanWaiting_AC7() {
        var clock = new VirtualClock();
        try (var executor = create(timedNet(Timing.immediate()), seed(), clock)) {
            var marking = executor.run();
            assertTrue(marking.hasTokens(OUT), "the immediate transition fired");
            assertEquals(0, clock.advancingWaits,
                "TIME-015 AC#7: with a boundary already due and nothing in flight the executor "
                    + "must return and let the next cycle act, not wait. Requested delays: "
                    + clock.requestedDelays);
            assertEquals(0L, clock.nanos, "no logical time passed");
        }
    }

    // ============================================================
    //  AC#8 — the signal half wakes the wait
    // ============================================================

    @Test
    void injectedEventWakesTheWaitWithoutTheIntervalElapsing_AC8() {
        var clock = new VirtualClock();
        var trigger = Place.of("trigger", String.class);
        var envPlace = EnvironmentPlace.of(trigger);
        var net = PetriNet.builder("signal").transition(Transition.builder("t")
            .inputs(one(trigger)).outputs(place(OUT))
            .timing(Timing.delayed(Duration.ofHours(3)))
            .action(ctx -> { ctx.output(OUT, ctx.input(trigger)); return CompletableFuture.completedFuture(null); })
            .build()).build();

        try (var executor = create(net, Map.of(), clock, Duration.ofMillis(0), Set.<EnvironmentPlace<?>>of(envPlace))) {
            // AC#11: inject() re-entrantly, from inside the wait the executor invoked. It may
            // only enqueue — the token must be admitted in the executor's own external-events
            // phase on a following cycle, never at the point of injection.
            // inject() is legal here and only enqueues. Its future must NOT be awaited from
            // inside the wait: the orchestrator thread is the one that completes it, so a
            // join() here deadlocks the executor against itself.
            clock.atNextWait = () -> executor.inject(envPlace, "go");
            // A net holding environment places waits for input rather than terminating, so
            // the host declares it is done once the injected token has been worked through.
            clock.atIdle = executor::drain;

            var marking = executor.run();
            assertTrue(marking.hasTokens(OUT),
                "TIME-015 AC#8/AC#11: an event injected from inside awaitWork must wake the "
                    + "wait and be admitted in the executor's normal phase order. Marking: " + marking);
            assertEquals(Duration.ofHours(3).toNanos(), clock.nanos,
                "the transition still respected its 3-hour delay after admission");
        }
    }

    @Test
    void drainDuringAHostedWaitIsObservedByTheReadinessPredicate() {
        // Under a host clock wakeUp() is silenced, so drain() — which sets `draining` and
        // signals nothing else — must reach the loop through `ready` instead. Without
        // shouldTerminate() in the predicate the host is asked to wait with no timer and is
        // never woken: the net hangs under an injected clock while working by default, which is
        // the injection-only silent failure TIME-015 exists to prevent.
        var clock = new VirtualClock();
        var trigger = Place.of("trigger", String.class);
        var envPlace = EnvironmentPlace.of(trigger);
        var net = PetriNet.builder("drainable").transition(Transition.builder("t")
            .inputs(one(trigger)).outputs(place(OUT))
            .action(ctx -> { ctx.output(OUT, ctx.input(trigger)); return CompletableFuture.completedFuture(null); })
            .build()).build();

        try (var executor = create(net, Map.of(), clock, Duration.ZERO,
                                   Set.<EnvironmentPlace<?>>of(envPlace))) {
            // No atIdle escape hatch: drain() on the first wait must itself make the net ready.
            clock.atNextWait = executor::drain;
            assertDoesNotThrow((org.junit.jupiter.api.function.ThrowingSupplier<Marking>) executor::run,
                "a drain during a hosted wait must terminate the run, not park it forever");
            assertEquals(TerminationReason.QUIESCENT, executor.terminationReason(),
                "the drained net reached quiescence");
        }
    }

    @Test
    void foreignMarkingRequestIsObservedByTheReadinessPredicate() {
        // marking() from a foreign thread signals the orchestrator through wakeUp() and
        // markingRequestSeq. Under a host clock wakeUp() is silenced, so the sequence counter is
        // the only carrier left — and a predicate built around the work queues omits it, exactly
        // as it omitted drain(). The caller then parks until its real-time cap, or forever.
        var clock = new VirtualClock();
        var trigger = Place.of("trigger", String.class);
        var envPlace = EnvironmentPlace.of(trigger);
        var net = PetriNet.builder("parked").transition(Transition.builder("t")
            .inputs(one(trigger)).outputs(place(OUT))
            .action(ctx -> { ctx.output(OUT, ctx.input(trigger)); return CompletableFuture.completedFuture(null); })
            .build()).build();

        try (var executor = create(net, Map.of(), clock, Duration.ZERO,
                                   Set.<EnvironmentPlace<?>>of(envPlace))) {
            clock.atNextWaitWithReady = ready -> {
                var foreign = new Thread(executor::marking, "foreign-marking");
                foreign.setDaemon(true);
                foreign.start();

                long deadline = System.nanoTime() + Duration.ofSeconds(5).toNanos();
                while (!ready.getAsBoolean() && System.nanoTime() < deadline) Thread.onSpinWait();
                assertTrue(ready.getAsBoolean(),
                    "a foreign marking() request must make the executor ready. With the request "
                        + "counter absent from the predicate the orchestrator is never woken, so "
                        + "the caller parks until its cap — and under an advance-on-demand clock "
                        + "a cap measured on the firing clock never retires at all.");
                executor.drain();
            };
            assertDoesNotThrow((org.junit.jupiter.api.function.ThrowingSupplier<Marking>) executor::run,
                "the run completes once the marking request has been served");
        }
    }

    // ============================================================
    //  AC#13 — every executor-stamped token follows the clock
    // ============================================================

    /**
     * AC#13 across <b>all three</b> origins, not just the easy one.
     *
     * <p>Tokens reach the marking three ways, and the third is the one a partial implementation
     * misses: the timeout path mints its tokens somewhere other than the collector the executor
     * handed the action, so a fix applied only to {@code ctx.output} leaves it on wall time — at
     * exactly the moment the requirement is under test. All three languages had this defect; all
     * three found it separately.
     *
     * <p>The seed token is stamped 2020 — distinct from both the injected epoch (1970-ish) and
     * wall time (now) — so an assertion cannot pass by coincidence, and so a future over-fix that
     * re-stamped host-supplied tokens would fail here rather than silently defeat [CORE-073].
     */
    @Test
    void everyExecutorStampedTokenFollowsTheClock_AC13() {
        var clock = new VirtualClock();
        var seedStamp = Instant.parse("2020-01-01T00:00:00Z");
        var trigger = Place.of("trigger", String.class);
        var envPlace = EnvironmentPlace.of(trigger);
        var viaOutput = Place.of("viaOutput", String.class);
        var recovered = Place.of("recovered", String.class);

        var net = PetriNet.builder("origins")
            // 1. ctx.output — the collector the executor handed the action.
            .transition(Transition.builder("emit")
                .inputs(one(IN)).outputs(place(viaOutput))
                .action(ctx -> { ctx.output(viaOutput, ctx.input(IN)); return CompletableFuture.completedFuture(null); })
                .build())
            // 3. timeout recovery — minted by the executor after severing the action's collector.
            .transition(Transition.builder("stalls")
                .inputs(one(trigger))
                .outputs(Arc.Out.timeout(Duration.ofMillis(50), recovered))
                .action(_ -> new CompletableFuture<>())   // never completes; the budget fires
                .build())
            .build();

        try (var executor = create(net, Map.of(IN, List.of(new Token<>("x", seedStamp))),
                                   clock, Duration.ZERO, Set.<EnvironmentPlace<?>>of(envPlace))) {
            // 2. raw-value injection — the executor mints the token from a bare value.
            clock.atNextWait = () -> executor.inject(envPlace, "go");
            clock.atIdle = executor::drain;

            var marking = executor.run();
            var injectedEpoch = Instant.EPOCH.plusNanos(clock.nanos);

            assertEquals(injectedEpoch, marking.peekFirst(viaOutput).createdAt(),
                "origin 1 (ctx.output): the collector the action writes to carries the clock");
            assertEquals(injectedEpoch, marking.peekFirst(recovered).createdAt(),
                "origin 3 (timeout recovery): TIME-015 AC#13 — detachForTimeout() replaces the "
                    + "harvest collector, and building a bare one there drops the clock so every "
                    + "recovery token silently reverts to wall time. Marking: " + marking);

            assertEquals(seedStamp, marking.peekFirst(IN) == null ? seedStamp
                    : marking.peekFirst(IN).createdAt(),
                "a host-supplied token is never re-stamped (CORE-073)");
        }
    }

    // ============================================================
    //  AC#10 — a coarse clock repeats readings, and that is normal
    // ============================================================

    @Test
    void constantReadingClockReachesTheSameOutcome_AC10() {
        var clock = new VirtualClock();
        try (var executor = create(timedNet(Timing.window(Duration.ofSeconds(2), Duration.ofSeconds(8))), seed(), clock)) {
            var marking = executor.run();

            assertTrue(clock.firingClockReads > clock.advancingWaits + 1,
                "the firing clock was read more often than it advanced, so successive readings "
                    + "returned the same value — the coarse-host-clock case (reads="
                    + clock.firingClockReads + ", advances=" + clock.advancingWaits + ")");
            assertTrue(marking.hasTokens(OUT),
                "TIME-015 AC#10: a non-decreasing clock that repeats readings must drive the net "
                    + "to the same outcome as a strictly increasing one — nothing may assume a "
                    + "tick between two reads. Marking: " + marking);
            assertEquals(Duration.ofSeconds(2).toNanos(), clock.nanos, "fired at its earliest bound");
        }
    }

    // ============================================================
    //  AC#12 — host-minted seed tokens are never re-stamped
    // ============================================================

    @Test
    void seedTokensKeepTheirHostSuppliedTimestamp_AC12() {
        var clock = new VirtualClock();
        var stamped = Instant.parse("2020-01-01T00:00:00Z");
        var net = PetriNet.builder("passthrough").transition(Transition.builder("t")
            .inputs(one(IN)).outputs(place(OUT))
            .action(ctx -> { ctx.output(OUT, ctx.input(IN)); return CompletableFuture.completedFuture(null); })
            .build()).build();

        try (var executor = create(net, Map.of(IN, List.of(new Token<>("x", stamped))), clock)) {
            var marking = executor.run();
            assertEquals(Instant.EPOCH, marking.peekFirst(OUT).createdAt(),
                "TIME-015: the token the EXECUTOR produced is stamped from the epoch clock");
        }

        // The seed token itself is never re-stamped — CORE-073's restore relies on that.
        var untouched = create(net, Map.of(IN, List.of(new Token<>("x", stamped))), clock);
        assertEquals(stamped, untouched.marking().peekFirst(IN).createdAt(),
            "TIME-015 AC#12: the executor must not silently re-stamp host-supplied tokens");
        untouched.close();
    }
}
