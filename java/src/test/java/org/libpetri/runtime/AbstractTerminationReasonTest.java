package org.libpetri.runtime;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.libpetri.core.*;
import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;

import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.core.Arc.In.one;
import static org.libpetri.core.Arc.Out.place;

/**
 * <b>EXEC-041</b>: termination cause must be observable, and ambient host state is not a stop
 * request.
 *
 * <p>These pin two defects that were silent in both senses — nothing thrown, nothing logged,
 * and a marking returned that looked exactly like a successful run:
 * <ul>
 *   <li>a thread's <b>pre-existing</b> interrupt flag made {@code run()} execute zero cycles
 *       and report completion holding the initial marking;</li>
 *   <li>an action calling {@code Thread.currentThread().interrupt()} — Java's conventional way
 *       to propagate a caught interrupt, and actions run <b>inline on the orchestrator
 *       thread</b> — truncated the net mid-chain and reported completion holding a partial
 *       marking.</li>
 * </ul>
 * The user writing that idiom did nothing wrong, which is what made it worth fixing rather
 * than documenting.
 */
@Timeout(60)
abstract class AbstractTerminationReasonTest {

    protected abstract PetriNetExecutor create(PetriNet net, Map<Place<?>, List<Token<?>>> initial);

    protected abstract PetriNetExecutor create(
        PetriNet net, Map<Place<?>, List<Token<?>>> initial, EventStore store);

    /** Either of {@code store} and {@code environment} may be null, leaving that knob at its default. */
    protected abstract PetriNetExecutor create(
        PetriNet net, Map<Place<?>, List<Token<?>>> initial, EventStore store,
        ExecutionEnvironment environment);

    private static final Place<String> A = Place.of("a", String.class);
    private static final Place<String> B = Place.of("b", String.class);
    private static final Place<String> C = Place.of("c", String.class);

    /** {@code a -t1-> b -t2-> c}; {@code t1} optionally runs {@code duringT1} while firing. */
    private static PetriNet chain(Runnable duringT1) {
        return PetriNet.builder("chain")
            .transition(Transition.builder("t1").inputs(one(A)).outputs(place(B))
                .action(ctx -> {
                    if (duringT1 != null) duringT1.run();
                    ctx.output(B, ctx.input(A));
                    return CompletableFuture.completedFuture(null);
                }).build())
            .transition(Transition.builder("t2").inputs(one(B)).outputs(place(C))
                .action(ctx -> { ctx.output(C, ctx.input(B)); return CompletableFuture.completedFuture(null); })
                .build())
            .build();
    }

    /** {@code a -t1-> b -t2(delayed 10s)-> c}; {@code t1} runs {@code duringT1} while firing. */
    private static PetriNet delayedChain(Runnable duringT1) {
        return PetriNet.builder("delayed-chain")
            .transition(Transition.builder("t1").inputs(one(A)).outputs(place(B))
                .action(ctx -> {
                    if (duringT1 != null) duringT1.run();
                    ctx.output(B, ctx.input(A));
                    return CompletableFuture.completedFuture(null);
                }).build())
            .transition(Transition.builder("t2").inputs(one(B)).outputs(place(C))
                .timing(Timing.delayed(java.time.Duration.ofSeconds(10)))
                .action(ctx -> { ctx.output(C, ctx.input(B)); return CompletableFuture.completedFuture(null); })
                .build())
            .build();
    }

    /**
     * {@code a -t1(async, 20ms)-> b -t2(delayed 20ms)-> c}: a net that really <b>waits</b>, in
     * both of the executor's waits — on an in-flight action, then on a timer. {@code t1} runs
     * {@code duringT1} inline before going async; {@code t2} runs {@code duringT2}.
     *
     * <p>The all-synchronous {@link #chain} never reaches a wait, and the wait is where an
     * interrupt flag bites: {@code Semaphore.tryAcquire}/{@code acquire} throw at once when the
     * flag is already set on entry. AC#4/AC#5 tests on {@code chain} alone could not fail for
     * the defect they were written against.
     */
    private static PetriNet waitingChain(Runnable duringT1, Runnable duringT2) {
        return PetriNet.builder("waiting-chain")
            .transition(Transition.builder("t1").inputs(one(A)).outputs(place(B))
                .action(ctx -> {
                    if (duringT1 != null) duringT1.run();
                    var value = ctx.input(A);
                    return CompletableFuture.runAsync(() -> ctx.output(B, value),
                        CompletableFuture.delayedExecutor(20, java.util.concurrent.TimeUnit.MILLISECONDS));
                }).build())
            .transition(Transition.builder("t2").inputs(one(B)).outputs(place(C))
                .timing(Timing.delayed(java.time.Duration.ofMillis(20)))
                .action(ctx -> {
                    if (duringT2 != null) duringT2.run();
                    ctx.output(C, ctx.input(B));
                    return CompletableFuture.completedFuture(null);
                }).build())
            .build();
    }

    private static Map<Place<?>, List<Token<?>>> seed() {
        return Map.of(A, List.of(Token.of("x")));
    }

    @Test
    void ambientInterruptBeforeRunDoesNotPreventExecution_AC4() {
        try (var executor = create(chain(null), seed())) {
            Thread.currentThread().interrupt();
            Marking marking;
            try {
                marking = executor.run();
            } finally {
                // Clear it whatever happens, so a failure here cannot poison the test runner.
                Thread.interrupted();
            }

            assertEquals(1, marking.tokenCount(C),
                "EXEC-041 AC#4: an interrupt flag already set before run() is host state the "
                    + "executor did not set — it may be left over from earlier work on a reused "
                    + "thread — and MUST NOT prevent the run. Before the fix this executed zero "
                    + "cycles and reported success holding the initial marking. Marking: " + marking);
            assertEquals(0, marking.tokenCount(A), "the seed token was consumed");
            assertEquals(TerminationReason.QUIESCENT, executor.terminationReason(),
                "the run reached quiescence and says so");
        }
    }

    @Test
    void actionRestoringTheInterruptFlagDoesNotTruncateTheRun_AC5() {
        try (var executor = create(chain(() -> Thread.currentThread().interrupt()), seed())) {
            Marking marking;
            try {
                marking = executor.run();
            } finally {
                Thread.interrupted();
            }

            assertEquals(1, marking.tokenCount(C),
                "EXEC-041 AC#5: `catch (InterruptedException e) { Thread.currentThread()"
                    + ".interrupt(); }` is the conventional Java idiom for not swallowing an "
                    + "interrupt, and actions run inline on the orchestrator thread — so writing "
                    + "it in an action must not truncate the net. Before the fix t1 fired, t2 "
                    + "never did, and the partial marking was reported as a completion. "
                    + "Marking: " + marking);
            assertEquals(TerminationReason.QUIESCENT, executor.terminationReason());
        }
    }

    @Test
    void ambientInterruptDoesNotTruncateANetThatWaits_AC4() {
        try (var executor = create(waitingChain(null, null), seed())) {
            Thread.currentThread().interrupt();
            Marking marking;
            boolean flagAfterRun;
            try {
                marking = executor.run();
            } finally {
                flagAfterRun = Thread.interrupted(); // read AND clear, whatever happens
            }

            assertEquals(1, marking.tokenCount(C),
                "EXEC-041 AC#4 on a net that WAITS: the flag was set before run(), t1 went "
                    + "async, and the orchestrator's wait on it threw at once — Semaphore "
                    + "throws on entry when the flag is already set — so an ambient flag was "
                    + "reported as 'interrupted while waiting' and t2 never fired. Marking: "
                    + marking);
            assertEquals(TerminationReason.QUIESCENT, executor.terminationReason());
            assertTrue(flagAfterRun,
                "the flag is the caller's: the run takes it down to wait, and puts it back "
                    + "when run() returns");
        }
    }

    @Test
    void actionRestoringTheInterruptFlagDoesNotTruncateANetThatWaits_AC5() {
        var seenByT2 = new java.util.concurrent.atomic.AtomicReference<Boolean>();
        var net = waitingChain(
            () -> Thread.currentThread().interrupt(),
            () -> seenByT2.set(Thread.currentThread().isInterrupted()));
        try (var executor = create(net, seed())) {
            Marking marking;
            boolean flagAfterRun;
            try {
                marking = executor.run();
            } finally {
                flagAfterRun = Thread.interrupted();
            }

            assertEquals(1, marking.tokenCount(C),
                "EXEC-041 AC#5: 'assert every downstream transition still fires'. t1 set the "
                    + "flag inline and went async, so the very next thing the orchestrator did "
                    + "was wait — and the wait threw. Marking: " + marking);
            assertEquals(TerminationReason.QUIESCENT, executor.terminationReason());
            assertEquals(Boolean.FALSE, seenByT2.get(),
                "the flag one action set does not leak into the next: a later action that "
                    + "blocks inline would otherwise throw InterruptedException for an "
                    + "interrupt nobody sent it");
            assertTrue(flagAfterRun,
                "not swallowed — deferred: the caller gets the flag back when run() returns");
        }
    }

    /**
     * An event store that re-interrupts on every append. Event stores run inline on the
     * orchestrator thread like actions do, but <i>between</i> an action's return and the next
     * wait — so this is the input only the clear <b>before the wait</b> can absorb; the clears
     * at loop start and after each action have already run by then.
     */
    private static EventStore interruptingStore() {
        var delegate = EventStore.inMemory();
        return new EventStore() {
            @Override public void append(NetEvent event) {
                delegate.append(event);
                Thread.currentThread().interrupt();
            }
            @Override public List<NetEvent> events() { return delegate.events(); }
            @Override public boolean isEnabled() { return true; }
        };
    }

    @Test
    void aFlagSetBetweenAnActionAndTheWaitDoesNotTruncateTheRun_AC5() {
        try (var executor = create(waitingChain(null, null), seed(), interruptingStore())) {
            Marking marking;
            try {
                marking = executor.run();
            } finally {
                Thread.interrupted();
            }
            assertEquals(1, marking.tokenCount(C),
                "EXEC-041: the flag is cleared-and-remembered before EVERY wait, not only after "
                    + "actions — inline host code other than an action (an event store here) "
                    + "can set it just as innocently. Marking: " + marking);
            assertEquals(TerminationReason.QUIESCENT, executor.terminationReason());
        }
    }

    @Test
    void theHostedWaitIsEnteredWithTheFlagClear_AC4_TIME015() {
        // Under an injected clock the host owns the wait. It is host code, it may well block
        // interruptibly, and it must not be handed a flag the run did not raise.
        var flagAtWait = new java.util.ArrayList<Boolean>();
        var clock = new AbstractInjectableClockTest.VirtualClock() {
            @Override public void awaitWork(java.util.function.BooleanSupplier ready, long delayNanos) {
                flagAtWait.add(Thread.currentThread().isInterrupted());
                super.awaitWork(ready, delayNanos);
            }
        };
        try (var executor = create(delayedChain(() -> Thread.currentThread().interrupt()), seed(),
                interruptingStore(), clock)) {
            Marking marking;
            boolean flagAfterRun;
            try {
                marking = executor.run();
            } finally {
                flagAfterRun = Thread.interrupted();
            }

            assertEquals(1, marking.tokenCount(C), "the virtual clock carried t2 past its delay");
            assertFalse(flagAtWait.isEmpty(), "the net really did wait on the host");
            assertEquals(List.of(), flagAtWait.stream().filter(f -> f).toList(),
                "EXEC-041 / TIME-015: clear-and-remember happens before the hosted wait too. "
                    + "Flags seen on entry: " + flagAtWait);
            assertTrue(flagAfterRun, "and is restored when run() returns");
        }
    }

    @Test
    void runStoppedEarlyIsDistinguishableFromQuiescence_AC3() {
        // close() from inside t1's action: t2 is left enabled and never fires.
        var closer = new java.util.concurrent.atomic.AtomicReference<PetriNetExecutor>();
        try (var executor = create(chain(() -> closer.get().terminateNow()), seed())) {
            closer.set(executor);
            var marking = executor.run();

            assertNotEquals(TerminationReason.QUIESCENT, executor.terminationReason(),
                "EXEC-041 AC#3: a run that stopped before quiescence MUST be distinguishable "
                    + "from one that reached it — a partial marking presented as final is "
                    + "silently accepted by every checkpoint and assertion downstream. "
                    + "Marking: " + marking);
            assertFalse(executor.terminationReason().isComplete(),
                "isComplete() is the caller-facing form of the same question");
        }
    }

    @Test
    void closeMidRunReportsClosedNotQuiescent_AC3() {
        // Distinct from the terminateNow() case above, and it exercises a different exit path.
        // close() does NOT set stopRequested, so the loop keeps going and leaves via
        // shouldTerminate() — which is ALSO true for "closed with nothing in flight". Reporting
        // that break as quiescence would call a truncated run finished, which is exactly the
        // confusion EXEC-041 forbids. t2 is left enabled and never fires.
        var self = new java.util.concurrent.atomic.AtomicReference<PetriNetExecutor>();
        try (var executor = create(chain(() -> self.get().close()), seed())) {
            self.set(executor);
            var marking = executor.run();

            assertEquals(0, marking.tokenCount(C),
                "t2 was still enabled when the close landed, so the run really was truncated. "
                    + "Marking: " + marking);
            assertEquals(TerminationReason.CLOSED, executor.terminationReason(),
                "EXEC-041 AC#3: a close that arrives while transitions are still enabled must "
                    + "report CLOSED. shouldTerminate() is true here for the close, not for "
                    + "quiescence, so it cannot itself be read as 'finished'. Marking: " + marking);
        }
    }

    @Test
    void quiescentRunReportsQuiescent_AC3() {
        try (var executor = create(chain(null), seed())) {
            var marking = executor.run();
            assertEquals(TerminationReason.QUIESCENT, executor.terminationReason());
            assertTrue(executor.terminationReason().isComplete(),
                "an undisturbed run to quiescence reports a final marking. Marking: " + marking);
            assertEquals(1, marking.tokenCount(C));
        }
    }


    // ============================================================
    //  EVT-013 AC#5: an engine diagnostic only where the caller did not ask
    // ============================================================

    /** WARN-level engine diagnostics ({@link NetEvent.LogMessage} with no transition name). */
    private static List<NetEvent.LogMessage> engineWarnings(EventStore store) {
        var out = new java.util.ArrayList<NetEvent.LogMessage>();
        for (var e : store.events()) {
            if (e instanceof NetEvent.LogMessage m && "WARN".equals(m.level()) && m.transitionName() == null) {
                out.add(m);
            }
        }
        return out;
    }

    @Test
    void interruptedRunEmitsAnEngineWarning_EVT013() throws Exception {
        var store = EventStore.inMemory();
        // A FOREIGN thread interrupts the orchestrator while it is parked on t2's 10s delay:
        // the one interrupt that is a request against this run, and the one termination nobody
        // on the caller's side asked for. (This used to have t1 set the flag itself — which is
        // AC#5's input, and asserted the truncation AC#5 forbids.)
        try (var executor = create(delayedChain(null), seed(), store)) {
            var flagAfterRun = new java.util.concurrent.atomic.AtomicBoolean();
            var runner = Thread.ofPlatform().start(() -> {
                executor.run();
                flagAfterRun.set(Thread.currentThread().isInterrupted());
            });

            // t1 has fired once b is marked; after that the loop has nothing to do but wait.
            long giveUp = System.nanoTime() + java.time.Duration.ofSeconds(10).toNanos();
            while (executor.marking().tokenCount(B) == 0 && System.nanoTime() < giveUp) Thread.sleep(5);
            // Repeated: an interrupt that lands in the sliver between two waits is absorbed as
            // ambient (by design) and deferred; one that lands IN the wait ends the run.
            while (runner.isAlive() && System.nanoTime() < giveUp) {
                Thread.sleep(50);
                runner.interrupt();
            }
            runner.join(10_000);
            assertFalse(runner.isAlive(), "the interrupt ended the run well inside t2's 10s delay");

            assertEquals(TerminationReason.INTERRUPTED, executor.terminationReason(),
                "the wait was entered with the flag clear and threw InterruptedException, so the "
                    + "run was truncated by something the caller did not request");
            assertEquals(0, executor.marking().tokenCount(C), "t2 never fired");
            assertTrue(flagAfterRun.get(), "the interrupt is handed back to the run's thread");
            assertEquals(1, engineWarnings(store).size(),
                "EVT-013: an interrupt is exactly the case the caller would otherwise not learn "
                    + "about, so it earns a diagnostic. Events: " + store.events());
        }
    }

    @Test
    void anInterruptDuringAHostedWaitEndsTheRunInterrupted_TIME015() throws Exception {
        // Under an injected clock the HOST owns the wait, and awaitWork cannot throw
        // InterruptedException: a host that blocks interruptibly catches it, restores the flag
        // — the convention — and returns. The wait was entered with the flag clear, so a flag
        // set on return arrived DURING the wait: the same request against this run that an
        // InterruptedException is from a built-in wait. Deferring it made an executor under
        // an injected clock uninterruptible.
        var store = EventStore.inMemory();
        var parked = new java.util.concurrent.CountDownLatch(1);
        var clock = new AbstractInjectableClockTest.VirtualClock() {
            boolean blockedOnce;
            @Override public void awaitWork(java.util.function.BooleanSupplier ready, long delayNanos) {
                if (!blockedOnce && !ready.getAsBoolean() && delayNanos != Long.MAX_VALUE) {
                    blockedOnce = true; // t2's 10s timer: block for REAL, as a wall-clock host would
                    parked.countDown();
                    try {
                        new java.util.concurrent.CountDownLatch(1).await(5, java.util.concurrent.TimeUnit.SECONDS);
                    } catch (InterruptedException e) {
                        Thread.currentThread().interrupt();
                    }
                    return; // spurious as far as the clock goes: nothing advanced
                }
                super.awaitWork(ready, delayNanos); // afterwards: virtual, so a deferred interrupt ends QUIESCENT
            }
        };
        try (var executor = create(delayedChain(null), seed(), store, clock)) {
            var flagAfterRun = new java.util.concurrent.atomic.AtomicBoolean();
            var runner = Thread.ofPlatform().start(() -> {
                executor.run();
                flagAfterRun.set(Thread.currentThread().isInterrupted());
            });
            assertTrue(parked.await(10, java.util.concurrent.TimeUnit.SECONDS), "the host is parked in its wait");
            Thread.sleep(50); // past countDown() and into await(); either side is inside awaitWork
            runner.interrupt();
            runner.join(20_000);
            assertFalse(runner.isAlive());

            assertEquals(TerminationReason.INTERRUPTED, executor.terminationReason(),
                "TIME-015 / EXEC-041: the hosted wait was entered with the flag clear and returned "
                    + "with it set, so the interrupt arrived during the wait. Marking: " + executor.marking());
            assertEquals(0, executor.marking().tokenCount(C), "t2 never fired — the run was truncated");
            assertTrue(flagAfterRun.get(), "the interrupt is handed back to the run's thread");
            assertEquals(1, engineWarnings(store).size(),
                "EVT-013: same diagnostic as for a built-in wait. Events: " + store.events());
        }
    }

    @Test
    void cleanCloseEmitsNoEngineWarning_EVT013_AC5() {
        var store = EventStore.inMemory();
        var self = new java.util.concurrent.atomic.AtomicReference<PetriNetExecutor>();
        try (var executor = create(delayedChain(() -> self.get().close()), seed(), store)) {
            self.set(executor);
            executor.run();

            assertEquals(TerminationReason.CLOSED, executor.terminationReason(),
                "the close truncated the run — t2 never fired");
            assertEquals(List.of(), engineWarnings(store),
                "EVT-013 AC#5: no engine diagnostic on a caller-requested termination path. A "
                    + "close() is something the caller already knows it asked for, and warning "
                    + "here fires on every clean shutdown of a reactive net designed never to "
                    + "quiesce — which teaches its reader to ignore the level. "
                    + "terminationReason() carries the distinction regardless.");
        }
    }

    @Test
    void terminationReasonBeforeAnyRunIsRunning() {
        try (var executor = create(chain(null), seed())) {
            assertEquals(TerminationReason.RUNNING, executor.terminationReason(),
                "before the first run there is no termination to report");
        }
    }
}
