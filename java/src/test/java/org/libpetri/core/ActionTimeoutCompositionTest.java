package org.libpetri.core;

import org.junit.jupiter.api.Test;
import org.libpetri.core.Arc.In;
import org.libpetri.core.Arc.Out;
import org.libpetri.event.EventStore;
import org.libpetri.event.NetEvent;
import org.libpetri.runtime.BitmapNetExecutor;

import java.time.Duration;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A transition's action timeout ({@code Out.Timeout}, per <b>IO-013</b> / <b>EXEC-022</b>) is
 * derived from its output spec, so every structural rewrite that rebuilds a transition must
 * carry that spec through intact — remapped places included. Pins both rewrite seams:
 * composition (<b>MOD-020</b>) and fusion (<b>MOD-061</b>).
 */
class ActionTimeoutCompositionTest {

    private static final Duration TIMEOUT = Duration.ofMillis(50);

    /** Never completes before {@link #TIMEOUT}, so the timeout branch always wins. */
    private static final TransitionAction SLOW = _ ->
        CompletableFuture.runAsync(() -> sleepUninterruptibly(400));

    @Test
    void compose_preservesActionTimeout() {
        Place<String> job = Place.of("job", String.class);
        Place<String> done = Place.of("done", String.class);
        Place<String> late = Place.of("late", String.class);

        var worker = SubnetDef.builder("SlowWorker")
            .transition(Transition.builder("work")
                .inputs(In.one(job))
                .outputs(Out.xor(Out.place(done), Out.timeout(TIMEOUT, late)))
                .action(SLOW)
                .build())
            .inputPort("job", job)
            .outputPort("late", late)
            .build();

        Place<String> hostJob = Place.of("hostJob", String.class);
        Place<String> hostLate = Place.of("hostLate", String.class);

        var net = PetriNet.builder("Host")
            .place(hostJob)
            .place(hostLate)
            .compose(worker.instantiate("w1"), Map.of("job", hostJob, "late", hostLate))
            .build();

        var work = findTransition(net, "w1/work");
        assertTrue(work.hasActionTimeout(), "compose must not drop the action timeout");
        assertEquals(TIMEOUT, work.actionTimeout().after());
        assertTrue(work.outputPlaces().contains(hostLate),
            "the timeout branch must follow the port merge. Outputs: " + work.outputPlaces());

        assertTimesOutInto(net, hostJob, hostLate, "w1/work");
    }

    @Test
    void fuse_preservesActionTimeout() {
        Place<String> job = Place.of("job", String.class);       // canonical
        Place<String> altJob = Place.of("altJob", String.class); // non-canonical
        Place<String> done = Place.of("done", String.class);
        Place<String> late = Place.of("late", String.class);

        var net = PetriNet.builder("Fused")
            .transitions(Transition.builder("work")
                .inputs(In.one(altJob))
                .outputs(Out.xor(Out.place(done), Out.timeout(TIMEOUT, late)))
                .action(SLOW)
                .build())
            .fuse(FusionSet.of("jobs", job, altJob))
            .build();

        var work = findTransition(net, "work");
        assertTrue(work.hasActionTimeout(), "fusion must not drop the action timeout");
        assertEquals(TIMEOUT, work.actionTimeout().after());
        assertTrue(work.inputPlaces().contains(job),
            "the input arc must be substituted to the canonical place. Inputs: " + work.inputPlaces());

        assertTimesOutInto(net, job, late, "work");
    }

    /** Runs {@code net} to quiescence and asserts the rewritten transition still times out. */
    private static void assertTimesOutInto(PetriNet net, Place<String> job, Place<String> late,
                                           String transitionName) {
        var store = EventStore.inMemory();
        var initial = Map.<Place<?>, List<Token<?>>>of(job, List.of(Token.of("j")));
        try (var executor = BitmapNetExecutor.builder(net, initial).eventStore(store).build()) {
            var marking = executor.run(Duration.ofSeconds(5)).toCompletableFuture().join();

            assertEquals(1, marking.tokenCount(late),
                "the timeout branch must produce. Marking: " + marking);
            var timeouts = store.eventsOfType(NetEvent.ActionTimedOut.class);
            assertEquals(1, timeouts.size(), "exactly one ActionTimedOut event");
            assertEquals(transitionName, timeouts.get(0).transitionName());
            assertEquals(TIMEOUT, timeouts.get(0).timeout());
        }
    }

    private static Transition findTransition(PetriNet net, String name) {
        for (var t : net.transitions()) {
            if (t.name().equals(name)) return t;
        }
        throw new AssertionError("no transition '" + name + "' in '" + net.name() + "'");
    }

    private static void sleepUninterruptibly(long millis) {
        try {
            Thread.sleep(millis);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }
}
