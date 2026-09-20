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
    void interruptedRunEmitsAnEngineWarning_EVT013() {
        var store = EventStore.inMemory();
        // t1 sets the flag; t2's 10s delay then makes the orchestrator wait, and the wait
        // itself throws — which is the one termination nobody asked for.
        try (var executor = create(delayedChain(() -> Thread.currentThread().interrupt()), seed(), store)) {
            try {
                executor.run();
            } finally {
                Thread.interrupted();
            }

            assertEquals(TerminationReason.INTERRUPTED, executor.terminationReason(),
                "the wait was interrupted, so the run was truncated by something the caller "
                    + "did not request");
            assertEquals(1, engineWarnings(store).size(),
                "EVT-013: an interrupt is exactly the case the caller would otherwise not learn "
                    + "about, so it earns a diagnostic. Events: " + store.events());
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
