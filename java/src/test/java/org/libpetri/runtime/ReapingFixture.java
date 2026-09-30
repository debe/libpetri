package org.libpetri.runtime;

import java.time.Duration;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;

import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Token;
import org.libpetri.core.Transition;
import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;

/**
 * The TIME-013 reaping scenario shared by the per-executor engine suite and the
 * Bitmap-vs-Precompiled agreement test.
 *
 * <p>{@code t: p0 -> p1} has {@code window(50ms, 200ms)}. {@code u} (priority 5) blocks the
 * orchestrator inline for 400 ms, so {@code t} misses its deadline and is reaped at a marking
 * that still holds its token. {@code v} (priority 5) is an asynchronous action that keeps the
 * loop alive for about 800 ms more and then deposits a second token on {@code p0}.
 *
 * <p>Expected: {@code t} rests disabled while {@code v} is in flight (it is not re-armed at the
 * reaped marking), and the deposit on {@code p0} re-enables it with a fresh clock, so both of
 * its firings come after {@code v} completed. A re-arming executor fires {@code t} on the
 * reaped token about 50 ms after the reap, while {@code v} is still in flight.
 */
final class ReapingFixture {

    private ReapingFixture() {}

    static final Place<Integer> P0 = Place.of("p0", Integer.class);
    static final Place<Integer> P1 = Place.of("p1", Integer.class);
    static final Place<Integer> Q = Place.of("q", Integer.class);
    static final Place<Integer> R = Place.of("r", Integer.class);
    static final Place<Integer> S = Place.of("s", Integer.class);
    static final Place<Integer> W = Place.of("w", Integer.class);

    @FunctionalInterface
    interface Factory {
        PetriNetExecutor create(PetriNet net, Map<Place<?>, List<Token<?>>> initial, EventStore store);
    }

    /**
     * What the run did with {@code t}.
     *
     * @param p0 tokens left on t's input place
     * @param p1 tokens t produced
     * @param timedOut {@code TransitionTimedOut} events for t
     * @param startedBeforeV starts of t before v completed, while t should rest
     * @param startedAfterV starts of t after v completed
     */
    record Outcome(int p0, int p1, long timedOut, int startedBeforeV, int startedAfterV) {}

    static PetriNet net() {
        var t = Transition.builder("t")
            .inputs(Arc.In.one(P0)).outputs(Arc.Out.place(P1))
            .timing(Timing.window(Duration.ofMillis(50), Duration.ofMillis(200)))
            .action(ctx -> {
                ctx.output(P1, ctx.input(P0));
                return CompletableFuture.completedFuture(null);
            })
            .build();
        var u = Transition.builder("u").priority(5)
            .inputs(Arc.In.one(Q)).outputs(Arc.Out.place(R))
            .action(ctx -> {
                // Inline on the orchestrator thread: holds the loop past t's deadline.
                try {
                    Thread.sleep(400);
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                }
                ctx.output(R, 1);
                return CompletableFuture.completedFuture(null);
            })
            .build();
        var v = Transition.builder("v").priority(5)
            .inputs(Arc.In.one(S)).outputs(Arc.Out.and(W, P0))
            .action(ctx -> CompletableFuture.runAsync(() -> {
                ctx.output(W, 1);
                ctx.output(P0, 2);
            }, CompletableFuture.delayedExecutor(800, TimeUnit.MILLISECONDS)))
            .build();
        return PetriNet.builder("Reaping").transitions(t, u, v).build();
    }

    static Map<Place<?>, List<Token<?>>> initial() {
        return Map.of(
            P0, List.of(Token.of(1)),
            Q, List.of(Token.of(1)),
            S, List.of(Token.of(1)));
    }

    static Outcome run(Factory factory) {
        var store = EventStore.inMemory();
        try (var executor = factory.create(net(), initial(), store)) {
            var result = executor.run(Duration.ofSeconds(10)).toCompletableFuture().join();
            boolean vCompleted = false;
            int before = 0;
            int after = 0;
            for (var event : store.events()) {
                if (event instanceof NetEvent.TransitionCompleted c && c.transitionName().equals("v")) {
                    vCompleted = true;
                }
                if (event instanceof NetEvent.TransitionStarted s && s.transitionName().equals("t")) {
                    if (vCompleted) after++; else before++;
                }
            }
            long timedOut = store.eventsOfType(NetEvent.TransitionTimedOut.class).stream()
                .filter(e -> e.transitionName().equals("t")).count();
            return new Outcome(result.tokenCount(P0), result.tokenCount(P1), timedOut, before, after);
        }
    }
}
