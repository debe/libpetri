package org.libpetri.runtime;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;

import org.libpetri.core.Arc;
import org.libpetri.core.MatchSpec;
import org.libpetri.core.NameId;
import org.libpetri.core.Place;
import org.libpetri.core.Token;
import org.libpetri.core.Transition;

/**
 * ν-net binding selection — the canonical name-correlation algorithm shared by
 * both executor backends (spec NU-020).
 *
 * <p>A transition carrying a {@link org.libpetri.core.MatchSpec} is enabled only
 * when there is a single name present in every correlated input with its
 * required token count. The two executors differ only in how they read tokens
 * ({@link Marking} FIFO queues vs ring buffers); the <i>selection</i> — which
 * name satisfies the join, and the deterministic tie-break — lives here so it is
 * identical across backends and matches the Rust/TypeScript ports.
 */
final class MatchEngine {

    private MatchEngine() {}

    /**
     * Per-correlated-input statistic for one name: how many (guard-passing)
     * tokens carry it, and the oldest such token's timestamp (epoch millis,
     * used for the tie-break).
     */
    record NameStat(int count, long minCreatedAt) {}

    /**
     * Required token count for {@code place} from the transition's input spec
     * (1 for One/All, n for Exactly(n), m for AtLeast(m)).
     */
    static int requiredFor(Transition t, Place<?> place) {
        for (var in : t.inputSpecs()) {
            if (in.place().equals(place)) {
                return switch (in) {
                    case Arc.In.Exactly e -> e.count();
                    case Arc.In.AtLeast a -> a.minimum();
                    default -> 1;
                };
            }
        }
        return 1;
    }

    /**
     * Finds the correlation name satisfying {@code t}'s {@link MatchSpec} over a
     * FIFO {@link Marking}, or {@code null} if the join is not enabled (NU-020).
     * Shared by the {@code Marking}-based executors (Bitmap, legacy); the
     * precompiled backend builds the same index over its ring buffers.
     */
    static NameId findBinding(Marking marking, Transition t) {
        MatchSpec ms = t.matchSpec();
        if (ms == null) {
            return null;
        }
        var perPlace = new ArrayList<Map<NameId, NameStat>>(ms.keys().size());
        int[] requireds = new int[ms.keys().size()];
        int k = 0;
        for (var key : ms.keys()) {
            var index = new HashMap<NameId, NameStat>();
            for (Token<?> token : marking.peekTokens(asObjectPlace(key.place()))) {
                NameId name = key.extract(token.value());
                if (name == null) {
                    continue;
                }
                long ts = token.createdAt().toEpochMilli();
                var prev = index.get(name);
                index.put(name, prev == null
                    ? new NameStat(1, ts)
                    : new NameStat(prev.count() + 1, Math.min(prev.minCreatedAt(), ts)));
            }
            perPlace.add(index);
            requireds[k++] = requiredFor(t, key.place());
        }
        return selectMatchName(perPlace, requireds);
    }

    @SuppressWarnings("unchecked")
    private static Place<Object> asObjectPlace(Place<?> place) {
        return (Place<Object>) place;
    }

    /**
     * Selects the satisfying correlation name across all correlated inputs, or
     * {@code null} when no single name is present in every input with at least
     * its required count.
     *
     * <p>Determinism (NU-020): among satisfying names, pick the one whose oldest
     * matched token (minimum {@code createdAt} across the correlated inputs) is
     * earliest; break remaining ties by {@link NameId} order. Byte-identical to
     * the Rust {@code select_match_name} and the TypeScript {@code selectMatchName}.
     *
     * @param perPlace  per-correlated-input name → statistic index
     * @param requireds required token count per correlated input (same order)
     * @return the satisfying name, or {@code null}
     */
    static NameId selectMatchName(List<Map<NameId, NameStat>> perPlace, int[] requireds) {
        if (perPlace.isEmpty()) {
            return null;
        }
        // Seed candidate names from the smallest index to minimise work; the
        // result is independent of which index seeds it.
        int seed = 0;
        for (int i = 1; i < perPlace.size(); i++) {
            if (perPlace.get(i).size() < perPlace.get(seed).size()) {
                seed = i;
            }
        }

        NameId bestName = null;
        long bestTs = 0;
        for (var entry : perPlace.get(seed).entrySet()) {
            NameId name = entry.getKey();
            if (entry.getValue().count() < requireds[seed]) {
                continue;
            }
            long repTs = Long.MAX_VALUE;
            boolean satisfied = true;
            for (int j = 0; j < perPlace.size(); j++) {
                NameStat stat = perPlace.get(j).get(name);
                if (stat == null || stat.count() < requireds[j]) {
                    satisfied = false;
                    break;
                }
                repTs = Math.min(repTs, stat.minCreatedAt());
            }
            if (!satisfied) {
                continue;
            }
            boolean take = bestName == null
                || repTs < bestTs
                || (repTs == bestTs && name.compareTo(bestName) < 0);
            if (take) {
                bestName = name;
                bestTs = repTs;
            }
        }
        return bestName;
    }

    /**
     * FIFO queue of timestamps with O(1)-amortised min-query (two-stack method).
     * Mirrors the executors' FIFO-within-name removal ({@code popFront} drops the
     * earliest-inserted token, like {@code ringRemoveMatching} / {@code
     * removeFirstMatching}) while answering "oldest remaining timestamp". A plain
     * min-heap would diverge from FIFO order when timestamps are not insertion-ordered.
     */
    static final class MinQueue {
        private long[] inVal = new long[4];
        private long[] inMin = new long[4];
        private int inSize = 0;
        private long[] outVal = new long[4];
        private long[] outMin = new long[4];
        private int outSize = 0;

        int size() {
            return inSize + outSize;
        }

        boolean isEmpty() {
            return inSize == 0 && outSize == 0;
        }

        void pushBack(long v) {
            if (inSize == inVal.length) {
                inVal = Arrays.copyOf(inVal, inVal.length * 2);
                inMin = Arrays.copyOf(inMin, inMin.length * 2);
            }
            inVal[inSize] = v;
            inMin[inSize] = inSize == 0 ? v : Math.min(inMin[inSize - 1], v);
            inSize++;
        }

        void popFront() {
            if (outSize == 0) {
                while (inSize > 0) {
                    long v = inVal[--inSize];
                    if (outSize == outVal.length) {
                        outVal = Arrays.copyOf(outVal, outVal.length * 2);
                        outMin = Arrays.copyOf(outMin, outMin.length * 2);
                    }
                    outVal[outSize] = v;
                    outMin[outSize] = outSize == 0 ? v : Math.min(outMin[outSize - 1], v);
                    outSize++;
                }
            }
            if (outSize > 0) {
                outSize--;
            }
        }

        long min() {
            long a = inSize > 0 ? inMin[inSize - 1] : Long.MAX_VALUE;
            long b = outSize > 0 ? outMin[outSize - 1] : Long.MAX_VALUE;
            return Math.min(a, b);
        }
    }

    /**
     * Incremental equivalent of {@link #selectMatchName} for the common case
     * where every correlated input is One/Exactly(n) (fixed consume count).
     *
     * <p>{@code selectMatchName} rebuilds a full name index over every token on
     * each call, so draining N ready correlation groups costs O(N²). This
     * maintains, per correlated input, a {@link MinQueue} of timestamps per name
     * plus a lazy-deletion min-heap of ready names keyed by the same
     * {@code (oldest_ts, name)} order, so {@code add}/{@code consume} are
     * O(log n) and {@link #best()} is an O(1) read. For any add/consume sequence
     * {@code best()} returns exactly what {@code selectMatchName} would —
     * verified by {@code MatchEngineIncrementalTest}. Callers with an AtLeast/All
     * correlated input must fall back to {@code selectMatchName}.
     */
    static final class IncrementalMatcher {
        private record ReadyEntry(long ts, NameId name) {}

        private final int[] requireds;
        private final List<Map<NameId, MinQueue>> ts;
        private final PriorityQueue<ReadyEntry> heap = new PriorityQueue<>(
            Comparator.comparingLong(ReadyEntry::ts).thenComparing(ReadyEntry::name));
        private final Map<NameId, Long> ready = new HashMap<>();

        IncrementalMatcher(int[] requireds) {
            this.requireds = requireds;
            this.ts = new ArrayList<>(requireds.length);
            for (int i = 0; i < requireds.length; i++) {
                ts.add(new HashMap<>());
            }
        }

        /** Add one token carrying {@code name} at {@code createdAt} to input {@code i}. */
        void add(int i, NameId name, long createdAt) {
            ts.get(i).computeIfAbsent(name, n -> new MinQueue()).pushBack(createdAt);
            refresh(name);
            cleanTop();
        }

        /** Remove the {@code required} earliest-inserted tokens of {@code name} from every input (NU-020). */
        void consume(NameId name) {
            for (int i = 0; i < requireds.length; i++) {
                MinQueue q = ts.get(i).get(name);
                if (q != null) {
                    for (int r = 0; r < requireds[i]; r++) {
                        q.popFront();
                    }
                    if (q.isEmpty()) {
                        ts.get(i).remove(name);
                    }
                }
            }
            refresh(name);
            cleanTop();
        }

        /** The name {@code selectMatchName} would pick, or {@code null}. O(1) read. */
        NameId best() {
            ReadyEntry top = heap.peek();
            return top == null ? null : top.name();
        }

        private Long repTs(NameId name) {
            long rep = Long.MAX_VALUE;
            for (int i = 0; i < requireds.length; i++) {
                MinQueue q = ts.get(i).get(name);
                if (q == null || q.size() < requireds[i]) {
                    return null;
                }
                rep = Math.min(rep, q.min());
            }
            return rep;
        }

        private void refresh(NameId name) {
            Long rep = repTs(name);
            if (rep != null) {
                if (!rep.equals(ready.get(name))) {
                    ready.put(name, rep);
                    heap.offer(new ReadyEntry(rep, name));
                }
            } else {
                ready.remove(name);
            }
        }

        private void cleanTop() {
            ReadyEntry top;
            while ((top = heap.peek()) != null) {
                Long cur = ready.get(top.name());
                if (cur == null || cur != top.ts()) {
                    heap.poll();
                } else {
                    break;
                }
            }
        }
    }
}
