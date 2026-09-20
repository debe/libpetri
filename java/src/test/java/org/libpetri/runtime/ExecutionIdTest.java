package org.libpetri.runtime;

import org.junit.jupiter.api.Test;
import org.libpetri.core.*;

import java.time.Instant;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BooleanSupplier;

import static org.junit.jupiter.api.Assertions.*;

/**
 * <b>TIME-015</b> AC#14: an executor's id must not be a clock reading.
 *
 * <p>It used to be {@code Long.toHexString(startNanos)}. Under an injected clock that violates
 * contract point 1 — a reading is not a unique key — so two executors seeded at the same
 * virtual instant collided, and a replayed run collided with itself. The id is now drawn at
 * construction from a counter shared by <b>both</b> executor classes.
 */
class ExecutionIdTest {

    /** A clock frozen at the epoch: every executor built on one reads exactly the same time. */
    private static final class FrozenClock implements ExecutionEnvironment {
        @Override public long nanoTime() { return 0L; }
        @Override public Instant now() { return Instant.EPOCH; }
        @Override public void awaitWork(BooleanSupplier ready, long delayNanos) { }
    }

    private static PetriNet net() {
        Place<String> p = Place.of("p", String.class);
        return PetriNet.builder("n").place(p).build();
    }

    @Test
    void executorsOnIdenticalClocksGetDistinctIds_AC14() {
        var net = net();
        Map<Place<?>, List<Token<?>>> empty = Map.of();

        // Deliberately MIXED backends: a counter held per-class would give the first of each
        // the same value, and a same-class test would never catch it.
        try (var a = BitmapNetExecutor.builder(net, empty).environment(new FrozenClock()).build();
             var b = PrecompiledNetExecutor.builder(net, empty).environment(new FrozenClock()).build();
             var c = BitmapNetExecutor.builder(net, empty).environment(new FrozenClock()).build()) {

            var ids = Set.of(a.executionId(), b.executionId(), c.executionId());
            assertEquals(3, ids.size(),
                "TIME-015 AC#14: three executors constructed against clocks frozen at the same "
                    + "instant — two backends among them — must still get distinct ids. An id "
                    + "derived from a clock reading gives all three the same value, and a "
                    + "per-class counter gives the two backends the same one. Got: " + ids);

            assertEquals(a.executionId(), a.executionId(), "the id is stable across reads");
        }
    }

    @Test
    void idIsAssignedAtConstructionNotAtRunStart_AC14() {
        var net = net();
        Map<Place<?>, List<Token<?>>> empty = Map.of();
        try (var executor = BitmapNetExecutor.builder(net, empty).build()) {
            var beforeRun = executor.executionId();
            executor.run();
            assertEquals(beforeRun, executor.executionId(),
                "TIME-015 AC#14: the id is drawn at construction, so it is observable before the "
                    + "run and unchanged by it — a run-start assignment would make it unusable "
                    + "for correlating anything that happened before the loop began");
        }
    }
}
