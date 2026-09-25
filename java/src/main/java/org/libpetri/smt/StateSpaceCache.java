package org.libpetri.smt;

import org.libpetri.analysis.MarkingState;
import org.libpetri.analysis.StateClassGraph;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;

import java.util.List;
import java.util.Objects;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionException;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.IntFunction;

/**
 * A state-space cache for the bounded enumeration route ([VER-017] "Reusing the state space
 * across queries"): the state-class graph of a net and its initial marking, built once and
 * read by every later query that passes the same cache.
 *
 * <p>The graph depends only on the net and its initial marking; the property and the sinks
 * only read it. A caller that asks many questions of one net would otherwise rebuild the
 * same graph for every question, and when the graph exceeds the class budget every question
 * pays the full attempt before it falls through to the SMT pipeline. Hand the same cache to
 * each verification instead:
 *
 * <pre>{@code
 * var cache = new StateSpaceCache();
 * var bounded = SmtVerifier.forNet(net).initialMarking(m0)
 *     .property(SmtProperty.placeBound(p, 1)).stateSpaceCache(cache).verify();
 * var live = SmtVerifier.forNet(net).initialMarking(m0)
 *     .property(SmtProperty.deadlockFree()).stateSpaceCache(cache).verify(); // no rebuild
 * }</pre>
 *
 * <p><b>Keying.</b> An entry is keyed by the net <em>as the caller passed it</em>, by
 * identity, and by the initial marking, structurally and in the order it lists its places
 * (a witness's markings inherit that order). A structurally equal net built separately, or
 * an equal marking listed in another order, misses; that is allowed, it only costs a build. The terminal rewrite of
 * [EXEC-042] is a deterministic function of the net, so the verifier keys on the net before
 * that rewrite and a net with terminals hits across queries.
 *
 * <p><b>Budgets.</b> A <em>closed</em> graph of {@code C} classes is reused for any class
 * budget greater than {@code C}; a budget of {@code C} or less would have truncated and is
 * answered as truncated, without a build. A <em>truncated</em> attempt at budget {@code B}
 * is remembered: a later budget of {@code B} or less declines at once, and a larger one
 * builds again and replaces the entry. The verdict, the witness and the route are the same
 * with and without the cache; the report says when a cached graph or a cached truncation was
 * used.
 *
 * <p><b>Concurrency.</b> The cache is thread-safe. Concurrent verifications that need the
 * same entry build it once; the others wait for that build. Graphs are frozen after
 * construction, so the waiters read them concurrently. While a larger budget rebuilds a
 * truncated entry, a budget no larger than the remembered truncation still declines at once
 * rather than wait. A build that throws propagates to the query that ran it and leaves the
 * entry as it found it — absent, or the truncation it was replacing. The queries waiting on
 * it do not inherit the failure: each looks again, and declines, reuses or builds as its own
 * budget requires. Waiting is not interruptible: a waiter keeps
 * its interrupt status and returns when the build it waits on finishes, as it would had it
 * built the graph itself.
 *
 * <p><b>Lifetime.</b> The caller owns the cache. It holds its nets and graphs strongly until
 * the caller drops it or calls {@link #clear()}; nothing is shared that the caller did not
 * ask for.
 */
public final class StateSpaceCache {

    /**
     * Identity on the net, structure on the marking, plus the order the marking lists its
     * places in. {@link MarkingState#equals} ignores that order, but a witness's markings
     * inherit it from the initial marking, and it is observable through
     * {@link MarkingState#placesWithTokens()}: two equal markings listed differently must not
     * share a graph, or the second caller's witness would list places in the first's order.
     */
    private record Key(PetriNet net, MarkingState initial, List<Place<?>> listing) {
        Key(PetriNet net, MarkingState initial) {
            this(net, initial, List.copyOf(initial.placesWithTokens()));
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof Key k && k.net == net && k.initial.equals(initial)
                && k.listing.equals(listing);
        }

        @Override
        public int hashCode() {
            return 31 * System.identityHashCode(net) + initial.hashCode();
        }
    }

    /** What one attempt left behind. */
    private sealed interface Entry {
        /** The graph closed with {@code classCount} classes. */
        record Closed(StateClassGraph graph, int classCount) implements Entry {}

        /** The graph did not close within {@code budget} classes. */
        record Truncated(int budget) implements Entry {}
    }

    /**
     * The answer to one lookup.
     *
     * @param graph      the closed graph, or {@code null} when the budget truncates
     * @param classCount the closed graph's class count, or the budget that truncated
     * @param fromCache  whether this query built nothing itself
     */
    record Lookup(StateClassGraph graph, int classCount, boolean fromCache) {
        boolean closed() {
            return graph != null;
        }
    }

    /**
     * One entry's attempt, possibly still in flight.
     *
     * @param future      completes with what the attempt left behind
     * @param truncatedAt the budget of the truncation this attempt replaces, or {@code 0}. A
     *                    rebuild at a larger budget is in flight for a while, and a budget no
     *                    larger than the remembered truncation must still decline at once
     *                    rather than wait for it; a rebuild that throws restores it.
     */
    private record Slot(CompletableFuture<Entry> future, int truncatedAt) {
        static Slot building(int truncatedAt) {
            return new Slot(new CompletableFuture<>(), truncatedAt);
        }
    }

    private final ConcurrentHashMap<Key, Slot> entries = new ConcurrentHashMap<>();
    private final AtomicInteger builds = new AtomicInteger();

    /** Creates an empty cache. */
    public StateSpaceCache() {}

    /** Drops every entry. A query in flight finishes against the entry it holds. */
    public void clear() {
        entries.clear();
    }

    /**
     * How many (net, initial marking) entries the cache holds, including a build still in
     * flight.
     */
    public int size() {
        return entries.size();
    }

    /** Test seam: how many graphs this cache has built. Package-private — not API. */
    int buildsForTesting() {
        return builds.get();
    }

    /**
     * Returns the graph of {@code key} at {@code initial} for class budget {@code budget},
     * building it with {@code build} only when no entry answers the budget.
     *
     * @param key     the net as the caller passed it, before any rewrite
     * @param initial the initial marking
     * @param budget  the class budget, positive
     * @param build   builds the graph at a budget; must be a deterministic function of
     *                {@code key} and {@code initial}
     */
    Lookup lookup(PetriNet key, MarkingState initial, int budget, IntFunction<StateClassGraph> build) {
        var k = new Key(Objects.requireNonNull(key), Objects.requireNonNull(initial));
        while (true) {
            var existing = entries.get(k);
            if (existing == null) {
                var mine = Slot.building(0);
                if (entries.putIfAbsent(k, mine) == null) {
                    return answer(buildInto(k, mine, budget, build), budget, false);
                }
                continue;
            }
            if (budget <= existing.truncatedAt()) {
                // A larger rebuild is in flight; the truncation it replaces already answers.
                return new Lookup(null, budget, true);
            }
            Entry entry = await(existing.future());
            if (entry == null) {
                // That build failed and already left the entry as it found it; its failure
                // is its builder's, not ours. Look again: decline, reuse or build.
                continue;
            }
            if (entry instanceof Entry.Truncated t && budget > t.budget()) {
                // A larger budget than the remembered truncation: build again and replace.
                var mine = Slot.building(t.budget());
                if (entries.replace(k, existing, mine)) {
                    return answer(buildInto(k, mine, budget, build), budget, false);
                }
                continue;
            }
            return answer(entry, budget, true);
        }
    }

    private Entry buildInto(Key k, Slot slot, int budget, IntFunction<StateClassGraph> build) {
        Entry entry;
        try {
            builds.incrementAndGet();
            var graph = build.apply(budget);
            entry = graph.isComplete()
                ? new Entry.Closed(graph, graph.stateClasses().size())
                : new Entry.Truncated(budget);
        } catch (Throwable failure) {
            // Leave the entry as it was before this attempt: absent, or the truncation it
            // was replacing. Either way no waiter can hang on it and a later query retries.
            if (slot.truncatedAt() > 0) {
                var restored = new Slot(
                    CompletableFuture.completedFuture(new Entry.Truncated(slot.truncatedAt())), 0);
                entries.replace(k, slot, restored);
            } else {
                entries.remove(k, slot);
            }
            slot.future().completeExceptionally(failure);
            throw failure;
        }
        slot.future().complete(entry);
        return entry;
    }

    private static Lookup answer(Entry entry, int budget, boolean fromCache) {
        return switch (entry) {
            // StateClassGraph.build checks its budget at the loop head, so a graph of C
            // classes closes only under a budget greater than C.
            case Entry.Closed c when budget > c.classCount() ->
                new Lookup(c.graph(), c.classCount(), fromCache);
            case Entry.Closed _ -> new Lookup(null, budget, fromCache);
            case Entry.Truncated _ -> new Lookup(null, budget, fromCache);
        };
    }

    /**
     * Waits for another query's build: its entry, or {@code null} when that build threw.
     * The builder propagates its own failure; a waiter retries instead, because the failure
     * belongs to that attempt (a budget this query may not share), not to this query.
     */
    private static Entry await(CompletableFuture<Entry> future) {
        try {
            return future.join();
        } catch (CompletionException | java.util.concurrent.CancellationException e) {
            return null;
        }
    }
}
