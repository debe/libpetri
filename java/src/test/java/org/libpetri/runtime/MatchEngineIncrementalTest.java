package org.libpetri.runtime;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;
import org.libpetri.core.NameId;

/**
 * Differential test: {@link MatchEngine.IncrementalMatcher#best()} must equal
 * {@link MatchEngine#selectMatchName} for any add/consume sequence. Uses random,
 * non-monotonic timestamps and removes the ground truth in INSERTION order
 * (FIFO-within-name, like the executors) — exercising the FIFO-vs-oldest
 * distinction a plain min-heap would get wrong. Mirrors the Rust/TS tests.
 */
class MatchEngineIncrementalTest {

    private record TruthTok(NameId name, long ts) {}

    /** Tiny deterministic LCG (no java.util.Random — keeps the test reproducible/portable). */
    private static final class Lcg {
        private long s;
        Lcg(long seed) { this.s = seed; }
        long next() {
            s = s * 6364136223846793005L + 1442695040888963407L;
            return (s >>> 16) & 0x7fffffffffffffffL;
        }
    }

    private static NameId referenceSelect(List<List<TruthTok>> truth, int[] requireds) {
        List<Map<NameId, MatchEngine.NameStat>> perPlace = new ArrayList<>(truth.size());
        for (var toks : truth) {
            Map<NameId, MatchEngine.NameStat> idx = new HashMap<>();
            for (var tk : toks) {
                var prev = idx.get(tk.name());
                idx.put(tk.name(), prev == null
                    ? new MatchEngine.NameStat(1, tk.ts())
                    : new MatchEngine.NameStat(prev.count() + 1, Math.min(prev.minCreatedAt(), tk.ts())));
            }
            perPlace.add(idx);
        }
        return MatchEngine.selectMatchName(perPlace, requireds);
    }

    @Test
    void incrementalMatchesSelectByteForByte() {
        NameId[] names = { NameId.of("A"), NameId.of("B"), NameId.of("C"), NameId.of("D") };
        for (long seed = 0; seed < 400; seed++) {
            Lcg rng = new Lcg(seed * 0x9E3779B97F4A7C15L ^ 0xDEADBEEFL);
            int k = 2 + (int) (rng.next() % 2);
            int[] requireds = new int[k];
            for (int i = 0; i < k; i++) {
                requireds[i] = 1 + (int) (rng.next() % 2);
            }
            var m = new MatchEngine.IncrementalMatcher(requireds);
            List<List<TruthTok>> truth = new ArrayList<>();
            for (int i = 0; i < k; i++) {
                truth.add(new ArrayList<>());
            }

            for (int step = 0; step < 80; step++) {
                if (rng.next() % 3 < 2) {
                    int i = (int) (rng.next() % k);
                    NameId name = names[(int) (rng.next() % names.length)];
                    long ts = rng.next() % 40; // collisions + out-of-order on purpose
                    m.add(i, name, ts);
                    truth.get(i).add(new TruthTok(name, ts));
                } else {
                    NameId pick = referenceSelect(truth, requireds);
                    if (pick != null) {
                        assertEquals(pick, m.best(), "best() diverged before consume (seed=" + seed + ")");
                        m.consume(pick);
                        for (int i = 0; i < k; i++) {
                            final int req = requireds[i];
                            final NameId p = pick;
                            int[] removed = {0};
                            truth.get(i).removeIf(tk -> {
                                if (removed[0] < req && tk.name().equals(p)) {
                                    removed[0]++;
                                    return true;
                                }
                                return false;
                            });
                        }
                    }
                }
                assertEquals(referenceSelect(truth, requireds), m.best(),
                    "best() diverged after op (seed=" + seed + ")");
            }
        }
    }

    /**
     * Monotonic fast path: ready names arriving in non-decreasing (rep_ts, name)
     * order (canonical fork/join / time-ordered seed) keep the matcher on the O(1)
     * FIFO path (never heaps) while still matching {@code selectMatchName}.
     */
    @Test
    void monotonicStaysOnFifoFastPath() {
        int[] requireds = {1, 1};
        var m = new MatchEngine.IncrementalMatcher(requireds);
        List<List<TruthTok>> truth = new ArrayList<>();
        truth.add(new ArrayList<>());
        truth.add(new ArrayList<>());
        for (int i = 0; i < 60; i++) {
            NameId name = NameId.of(String.format("g%03d", i)); // zero-padded: lexical == numeric
            m.add(0, name, i);
            m.add(1, name, i);
            truth.get(0).add(new TruthTok(name, i));
            truth.get(1).add(new TruthTok(name, i));
            assertFalse(m.isHeaped(), "monotonic seed must stay on the FIFO fast path");
        }
        NameId pick;
        while ((pick = referenceSelect(truth, requireds)) != null) {
            assertEquals(pick, m.best());
            assertFalse(m.isHeaped(), "monotonic drain must stay on the FIFO fast path");
            m.consume(pick);
            final NameId p = pick;
            for (int i = 0; i < 2; i++) {
                int[] removed = {0};
                truth.get(i).removeIf(tk -> {
                    if (removed[0] < 1 && tk.name().equals(p)) {
                        removed[0]++;
                        return true;
                    }
                    return false;
                });
            }
            assertEquals(referenceSelect(truth, requireds), m.best());
        }
        assertNull(m.best());
    }

    /**
     * An out-of-order ready push (a later group with an earlier rep_ts) migrates
     * the matcher to the heap; best() stays correct, and the fast path is
     * re-entered once the structure fully drains.
     */
    @Test
    void inversionFallsBackThenReEntersFastPath() {
        int[] requireds = {1, 1};
        var m = new MatchEngine.IncrementalMatcher(requireds);
        NameId a = NameId.of("a");
        NameId b = NameId.of("b");
        m.add(0, a, 5);
        m.add(1, a, 5);
        assertFalse(m.isHeaped());
        assertEquals(a, m.best());
        // b ready at rep 2 < a's rep 5 -> inversion -> heap-backed, b is the pick
        m.add(0, b, 2);
        m.add(1, b, 2);
        assertTrue(m.isHeaped());
        assertEquals(b, m.best());
        m.consume(b);
        assertEquals(a, m.best());
        m.consume(a);
        assertNull(m.best());
        assertFalse(m.isHeaped(), "fully drained matcher re-enters the FIFO fast path");
    }
}
