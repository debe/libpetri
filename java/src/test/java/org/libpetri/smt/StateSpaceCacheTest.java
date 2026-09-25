package org.libpetri.smt;

import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.StateClassGraph;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;
import org.libpetri.fixtures.StructureOnly;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.*;
import static org.libpetri.core.Arc.In.one;
import static org.libpetri.core.Arc.Out.and;
import static org.libpetri.core.Arc.Out.place;

/**
 * [VER-017] "Reusing the state space across queries": the {@link StateSpaceCache} handle.
 * AC7 reuse, AC8 budgets, AC9 keying, AC10 concurrency, and a net with terminal places,
 * whose rewrite builds a new net per verification.
 */
class StateSpaceCacheTest {

    static boolean z3Available() {
        return SmtVerifier.z3Available();
    }

    private static final String REUSED = "Bounded state-space enumeration: reused cached state space (";
    private static final String CACHED_TRUNCATION =
        "Bounded state-space enumeration: cached truncation at ";

    private record Pipeline(PetriNet net, List<Place<String>> places, MarkingState m0) {}

    /** {@code p0 -> t0 -> p1 -> ... -> pn}: {@code n + 1} classes. */
    private static Pipeline pipeline(int n) {
        var places = new ArrayList<Place<String>>();
        places.add(Place.of("p0", String.class));
        var transitions = new ArrayList<Transition>();
        for (int i = 0; i < n; i++) {
            var next = Place.of("p" + (i + 1), String.class);
            places.add(next);
            transitions.add(Transition.builder("t" + i).inputs(one(places.get(i))).outputs(place(next)).build());
        }
        var net = StructureOnly.bind(PetriNet.builder("pipeline" + n)
            .transitions(transitions.toArray(new Transition[0])).build());
        return new Pipeline(net, List.copyOf(places), MarkingState.builder().tokens(places.get(0), 1).build());
    }

    private static SmtVerificationResult verify(
            PetriNet net, MarkingState m0, SmtProperty property, StateSpaceCache cache,
            UnaryOperator<SmtVerifier> configure) {
        var verifier = SmtVerifier.forNet(net).initialMarking(m0).property(property)
            .timeout(Duration.ofSeconds(30));
        if (cache != null) verifier.stateSpaceCache(cache);
        return configure.apply(verifier).verify();
    }

    private static SmtVerificationResult verify(
            PetriNet net, MarkingState m0, SmtProperty property, StateSpaceCache cache) {
        return verify(net, m0, property, cache, v -> v);
    }

    /** Verdict, witness and route: what the cache must not change. */
    private static void assertSameAnswer(SmtVerificationResult expected, SmtVerificationResult actual) {
        assertEquals(expected.verdict(), actual.verdict(), actual.report());
        assertEquals(expected.route(), actual.route(), actual.report());
        assertEquals(expected.counterexampleTrace(), actual.counterexampleTrace(), actual.report());
        assertEquals(expected.counterexampleTransitions(), actual.counterexampleTransitions(), actual.report());
        assertEquals(expected.counterexampleConfirmed(), actual.counterexampleConfirmed(), actual.report());
    }

    // === AC7: later queries build nothing and answer the same ===

    @Test
    void VER017_AC7_laterQueriesOnOneNetBuildNoGraph_andAnswerAsWithoutTheCache() {
        var p = pipeline(6);
        var cache = new StateSpaceCache();
        var bound = SmtProperty.placeBound(p.places().get(6), 1);
        var mutex = SmtProperty.mutualExclusion(p.places().get(0), p.places().get(6));
        var deadlock = SmtProperty.deadlockFree(); // no sink: the token strands in p6

        var first = verify(p.net(), p.m0(), bound, cache);
        assertEquals(1, cache.buildsForTesting());
        assertFalse(first.report().contains(REUSED), "the first query built the graph: " + first.report());

        var second = verify(p.net(), p.m0(), mutex, cache);
        var third = verify(p.net(), p.m0(), deadlock, cache);
        assertEquals(1, cache.buildsForTesting(), "VER-017 AC7: the second and third queries build no graph");
        assertEquals(1, cache.size());
        assertTrue(second.report().contains(REUSED + "7 classes) (VER-017).\n"), second.report());
        assertTrue(third.report().contains(REUSED + "7 classes) (VER-017).\n"), third.report());

        assertTrue(first.isProven(), first.report());
        assertTrue(second.isProven(), second.report());
        assertTrue(third.isViolated(), third.report());
        assertEquals(List.of("t0", "t1", "t2", "t3", "t4", "t5"), third.counterexampleTransitions());

        assertSameAnswer(verify(p.net(), p.m0(), bound, null), first);
        assertSameAnswer(verify(p.net(), p.m0(), mutex, null), second);
        assertSameAnswer(verify(p.net(), p.m0(), deadlock, null), third);
        assertEquals(SmtVerificationResult.Route.ENUMERATION, third.route());
    }

    @Test
    void VER017_AC7_theReportIsTheUncachedOnePlusOneLine() {
        var p = pipeline(4);
        var cache = new StateSpaceCache();
        var property = SmtProperty.deadlockFree();
        verify(p.net(), p.m0(), property, cache, v -> v.sinkPlaces(p.places().get(4)));
        var cached = verify(p.net(), p.m0(), property, cache, v -> v.sinkPlaces(p.places().get(4)));
        var plain = verify(p.net(), p.m0(), property, null, v -> v.sinkPlaces(p.places().get(4)));

        assertEquals(plain.report(),
            cached.report().replace(REUSED + "5 classes) (VER-017).\n", ""),
            "the cache adds exactly one report line");
    }

    // === AC8: budgets ===

    @Test
    @EnabledIf("z3Available")
    void VER017_AC8_aCachedTruncationDeclinesSmallerBudgets_andALargerOneBuildsAndReplaces() {
        var p = pipeline(6); // 7 classes
        var cache = new StateSpaceCache();
        var property = SmtProperty.placeBound(p.places().get(6), 1);

        var truncated = verify(p.net(), p.m0(), property, cache, v -> v.enumerationMaxClasses(3));
        assertEquals(1, cache.buildsForTesting());
        assertTrue(truncated.report().contains("Bounded state-space enumeration truncated at 3 classes"),
            truncated.report());
        assertFalse(truncated.report().contains(CACHED_TRUNCATION), truncated.report());

        for (int budget : new int[] {3, 2}) {
            var again = verify(p.net(), p.m0(), property, cache, v -> v.enumerationMaxClasses(budget));
            assertEquals(1, cache.buildsForTesting(), "VER-017 AC8: budget " + budget + " <= 3 builds nothing");
            assertTrue(again.report().contains(CACHED_TRUNCATION + budget + " classes (VER-017); verifying via the SMT pipeline.\n"),
                again.report());
            assertTrue(again.report().contains(CACHED_TRUNCATION + budget + " classes (VER-017); verifying via the SMT pipeline.\n"
                    + "Bounded state-space enumeration truncated at " + budget + " classes"),
                "the cached line comes right before the existing truncation line: " + again.report());
            assertSameAnswer(verify(p.net(), p.m0(), property, null, v -> v.enumerationMaxClasses(budget)), again);
        }

        // Larger, still truncating (a graph of 7 classes needs a budget above 7): builds again.
        verify(p.net(), p.m0(), property, cache, v -> v.enumerationMaxClasses(7));
        assertEquals(2, cache.buildsForTesting(), "VER-017 AC8: a larger budget builds");
        assertEquals(1, cache.size(), "and replaces the entry");

        var closed = verify(p.net(), p.m0(), property, cache, v -> v.enumerationMaxClasses(100));
        assertEquals(3, cache.buildsForTesting());
        assertEquals(SmtVerificationResult.Route.ENUMERATION, closed.route(), closed.report());

        // The closed graph of 7 classes answers budget 7 as truncated, and 8 from the graph.
        var atSize = verify(p.net(), p.m0(), property, cache, v -> v.enumerationMaxClasses(7));
        assertTrue(atSize.report().contains(CACHED_TRUNCATION + "7 classes"), atSize.report());
        assertSameAnswer(verify(p.net(), p.m0(), property, null, v -> v.enumerationMaxClasses(7)), atSize);
        var above = verify(p.net(), p.m0(), property, cache, v -> v.enumerationMaxClasses(8));
        assertTrue(above.report().contains(REUSED + "7 classes)"), above.report());
        assertEquals(SmtVerificationResult.Route.ENUMERATION, above.route());
        assertEquals(3, cache.buildsForTesting(), "neither budget builds");
    }

    @Test
    void VER017_AC8_budgetRulesAtTheCache() {
        var p = pipeline(6); // 7 classes
        var cache = new StateSpaceCache();
        var built = new ArrayList<Integer>();
        java.util.function.IntFunction<StateClassGraph> build = budget -> {
            built.add(budget);
            return StateClassGraph.build(p.net(), p.m0(), budget);
        };

        assertFalse(cache.lookup(p.net(), p.m0(), 3, build).closed());
        var declined = cache.lookup(p.net(), p.m0(), 3, build);
        assertFalse(declined.closed());
        assertTrue(declined.fromCache());
        assertEquals(List.of(3), built);

        var closed = cache.lookup(p.net(), p.m0(), 50, build);
        assertTrue(closed.closed());
        assertFalse(closed.fromCache());
        assertEquals(7, closed.classCount());
        assertEquals(List.of(3, 50), built);

        assertFalse(cache.lookup(p.net(), p.m0(), 7, build).closed(), "budget <= C is truncated");
        assertTrue(cache.lookup(p.net(), p.m0(), 8, build).closed(), "budget > C reuses the graph");
        assertEquals(List.of(3, 50), built);
    }

    @Test
    void aFailedBuildLeavesNoEntry_soALaterQueryRetries() {
        var p = pipeline(3);
        var cache = new StateSpaceCache();
        assertThrows(IllegalStateException.class, () -> cache.lookup(p.net(), p.m0(), 50, _ -> {
            throw new IllegalStateException("boom");
        }));
        assertEquals(0, cache.size());
        assertTrue(cache.lookup(p.net(), p.m0(), 50, b -> StateClassGraph.build(p.net(), p.m0(), b)).closed());
        assertEquals(1, cache.size());
        cache.clear();
        assertEquals(0, cache.size());
    }

    // === AC9: keying ===

    @Test
    void VER017_AC9_aDifferentMarkingOrANetInstanceNeverHitsAnotherEntry() {
        var p = pipeline(4);
        var cache = new StateSpaceCache();
        var property = SmtProperty.placeBound(p.places().get(4), 1);
        verify(p.net(), p.m0(), property, cache);
        assertEquals(1, cache.buildsForTesting());

        var otherMarking = MarkingState.builder().tokens(p.places().get(2), 1).build();
        var fromP2 = verify(p.net(), otherMarking, property, cache);
        assertEquals(2, cache.buildsForTesting(), "VER-017 AC9: a different initial marking misses");
        assertFalse(fromP2.report().contains(REUSED), fromP2.report());
        assertSameAnswer(verify(p.net(), otherMarking, property, null), fromP2);

        // A structurally equal marking built separately hits.
        verify(p.net(), MarkingState.builder().tokens(p.places().get(0), 1).build(), property, cache);
        assertEquals(2, cache.buildsForTesting(), "the marking is keyed structurally");

        // A net with a different structure misses; so does an equal one built separately
        // (identity keying: allowed to miss, never to hit across different graphs).
        var longer = pipeline(5);
        verify(longer.net(), longer.m0(), property, cache);
        assertEquals(3, cache.buildsForTesting());
        var twin = pipeline(4);
        verify(twin.net(), twin.m0(), property, cache);
        assertEquals(4, cache.buildsForTesting());
        assertEquals(4, cache.size());
    }

    @Test
    void VER017_AC7_aWitnessListsItsPlacesInTheCallersOwnOrder() {
        // Two equal markings that list their places in different orders. The witness's
        // markings keep the listing of the marking they were derived from, and reports read
        // that order, so the second query must not borrow the first query's graph.
        var p = pipeline(3);
        var side = Place.of("side", String.class);
        var sideFirst = MarkingState.builder().tokens(side, 1).tokens(p.places().get(0), 1).build();
        var p0First = MarkingState.builder().tokens(p.places().get(0), 1).tokens(side, 1).build();
        assertEquals(sideFirst, p0First);
        var cache = new StateSpaceCache();
        var property = SmtProperty.deadlockFree();

        verify(p.net(), sideFirst, property, cache);
        var cached = verify(p.net(), p0First, property, cache);
        var plain = verify(p.net(), p0First, property, null);
        assertTrue(plain.isViolated(), plain.report());
        assertSameAnswer(plain, cached);
        assertEquals(listings(plain.counterexampleTrace()), listings(cached.counterexampleTrace()),
            "VER-017 AC7: the witness is the one the caller's own marking yields");
    }

    private static List<List<String>> listings(List<MarkingState> trace) {
        return trace.stream()
            .map(m -> m.placesWithTokens().stream().map(Place::name).toList())
            .toList();
    }

    @Test
    void aRememberedTruncationDeclinesAtOnce_whileALargerBudgetRebuilds() throws Exception {
        var p = pipeline(6); // 7 classes
        var cache = new StateSpaceCache();
        assertFalse(cache.lookup(p.net(), p.m0(), 3, b -> StateClassGraph.build(p.net(), p.m0(), b)).closed());

        var building = new CountDownLatch(1);
        var release = new CountDownLatch(1);
        var pool = Executors.newFixedThreadPool(2);
        try {
            var rebuild = pool.submit(() -> cache.lookup(p.net(), p.m0(), 50, b -> {
                building.countDown();
                try {
                    release.await();
                } catch (InterruptedException e) {
                    throw new IllegalStateException(e);
                }
                return StateClassGraph.build(p.net(), p.m0(), b);
            }));
            assertTrue(building.await(10, java.util.concurrent.TimeUnit.SECONDS));

            // Budget 2 <= the remembered 3: declines without waiting for the rebuild.
            var small = pool.submit(() -> cache.lookup(p.net(), p.m0(), 2, _ -> fail("must not build")));
            var declined = small.get(5, java.util.concurrent.TimeUnit.SECONDS);
            assertFalse(declined.closed());
            assertTrue(declined.fromCache());

            release.countDown();
            assertTrue(rebuild.get(10, java.util.concurrent.TimeUnit.SECONDS).closed());
        } finally {
            release.countDown();
            pool.shutdownNow();
        }
    }

    @Test
    void aFailedRebuildKeepsTheRememberedTruncation() {
        var p = pipeline(6);
        var cache = new StateSpaceCache();
        cache.lookup(p.net(), p.m0(), 3, b -> StateClassGraph.build(p.net(), p.m0(), b));
        assertThrows(IllegalStateException.class, () -> cache.lookup(p.net(), p.m0(), 50, _ -> {
            throw new IllegalStateException("boom");
        }));
        var again = cache.lookup(p.net(), p.m0(), 3, _ -> fail("the truncation at 3 is still known"));
        assertFalse(again.closed());
        assertTrue(again.fromCache());
    }

    /** Blocks until {@code thread} parks, i.e. has joined the build in flight. */
    private static void awaitParked(java.util.concurrent.atomic.AtomicReference<Thread> thread)
            throws InterruptedException {
        long deadline = System.nanoTime() + java.util.concurrent.TimeUnit.SECONDS.toNanos(10);
        while (thread.get() == null || thread.get().getState() != Thread.State.WAITING) {
            assertTrue(System.nanoTime() < deadline, "the waiter never joined the build");
            Thread.sleep(1);
        }
    }

    @Test
    void waitersOnABuildThatThrows_retryInsteadOfInheritingTheFailure() throws Exception {
        runFailedForeignBuild(0);
    }

    @Test
    void waitersOnARebuildThatThrows_retryAgainstTheRestoredTruncation() throws Exception {
        runFailedForeignBuild(3);
    }

    /**
     * A builder at budget 50 throws while a waiter at budget 20 has joined its build (and,
     * with a remembered truncation, a waiter at budget 2 declines at once). The builder
     * propagates its own failure; the waiter does not inherit it, it retries the lookup and
     * builds its own graph; nothing hangs.
     */
    private static void runFailedForeignBuild(int rememberedTruncation) throws Exception {
        var p = pipeline(6); // 7 classes
        var cache = new StateSpaceCache();
        if (rememberedTruncation > 0) {
            assertFalse(cache.lookup(p.net(), p.m0(), rememberedTruncation,
                b -> StateClassGraph.build(p.net(), p.m0(), b)).closed());
        }
        var building = new CountDownLatch(1);
        var release = new CountDownLatch(1);
        var waiterThread = new java.util.concurrent.atomic.AtomicReference<Thread>();
        var pool = Executors.newFixedThreadPool(3);
        try {
            var builder = pool.submit(() -> cache.lookup(p.net(), p.m0(), 50, _ -> {
                building.countDown();
                try {
                    release.await();
                } catch (InterruptedException e) {
                    throw new IllegalStateException(e);
                }
                throw new StackOverflowError("boom");
            }));
            assertTrue(building.await(10, java.util.concurrent.TimeUnit.SECONDS));
            if (rememberedTruncation > 0) {
                var small = pool.submit(() -> cache.lookup(p.net(), p.m0(), 2, _ -> fail("must not build")));
                var declined = small.get(5, java.util.concurrent.TimeUnit.SECONDS);
                assertFalse(declined.closed(), "a budget <= the remembered truncation declines at once");
                assertTrue(declined.fromCache());
            }
            var waiter = pool.submit(() -> {
                waiterThread.set(Thread.currentThread());
                return cache.lookup(p.net(), p.m0(), 20, b -> StateClassGraph.build(p.net(), p.m0(), b));
            });
            awaitParked(waiterThread);
            release.countDown();

            var e1 = assertThrows(java.util.concurrent.ExecutionException.class,
                () -> builder.get(10, java.util.concurrent.TimeUnit.SECONDS));
            assertInstanceOf(StackOverflowError.class, e1.getCause(), "the builder propagates its own failure");
            var retried = waiter.get(10, java.util.concurrent.TimeUnit.SECONDS);
            assertTrue(retried.closed(), "the waiter retried and built its own graph");
            assertFalse(retried.fromCache());
        } finally {
            release.countDown();
            pool.shutdownNow();
        }
        assertEquals(1, cache.size());
        assertTrue(cache.lookup(p.net(), p.m0(), 50, _ -> fail("the waiter's graph is cached")).fromCache());
    }

    // === AC10: parallel queries build once ===

    @Test
    void VER017_AC10_parallelQueriesSharingACacheBuildTheGraphOnce() throws Exception {
        var p = pipeline(400);
        var cache = new StateSpaceCache();
        int threads = 8;
        var ready = new CountDownLatch(threads);
        var go = new CountDownLatch(1);
        var pool = Executors.newFixedThreadPool(threads);
        try {
            var futures = new ArrayList<Future<SmtVerificationResult>>();
            for (int i = 0; i < threads; i++) {
                var property = i % 2 == 0
                    ? SmtProperty.placeBound(p.places().get(i), 1)
                    : SmtProperty.deadlockFree();
                futures.add(pool.submit(() -> {
                    ready.countDown();
                    go.await();
                    return verify(p.net(), p.m0(), property, cache);
                }));
            }
            ready.await();
            go.countDown();
            for (int i = 0; i < threads; i++) {
                var result = futures.get(i).get();
                assertEquals(SmtVerificationResult.Route.ENUMERATION, result.route(), result.report());
                assertEquals(i % 2 == 0, result.isProven(), result.report());
            }
        } finally {
            pool.shutdownNow();
        }
        assertEquals(1, cache.buildsForTesting(), "VER-017 AC10: parallel queries build the graph once");
    }

    // === Terminals: the rewrite is a new net per verification ===

    @Test
    void aNetWithTerminalPlacesHitsAcrossQueries() {
        var in = Place.of("in", String.class);
        var a = Place.of("a", String.class);
        var b = Place.of("b", String.class);
        var done = Place.of("done", String.class);
        var late = Place.of("late", String.class);
        var net = StructureOnly.bind(PetriNet.builder("fork").transitions(
            Transition.builder("fork").inputs(one(in)).outputs(and(a, b)).build(),
            Transition.builder("finish").inputs(one(a)).outputs(place(done)).build(),
            Transition.builder("straggler").inputs(one(b)).outputs(place(late)).build())
            .terminal(done).build());
        var m0 = MarkingState.builder().tokens(in, 1).build();
        var cache = new StateSpaceCache();

        var deadlock = verify(net, m0, SmtProperty.deadlockFree(), cache);
        var mutex = verify(net, m0, SmtProperty.mutualExclusion(a, b), cache);
        assertEquals(1, cache.buildsForTesting(),
            "keyed by the caller's net, not by the terminal rewrite built per verification");
        assertTrue(mutex.report().contains(REUSED), mutex.report());

        assertTrue(deadlock.isProven(), deadlock.report());
        assertTrue(mutex.isViolated(), mutex.report());
        assertEquals(List.of("fork"), mutex.counterexampleTransitions());
        assertSameAnswer(verify(net, m0, SmtProperty.deadlockFree(), null), deadlock);
        assertSameAnswer(verify(net, m0, SmtProperty.mutualExclusion(a, b), null), mutex);
    }
}
