package org.libpetri.runtime;

import static org.junit.jupiter.api.Assertions.assertEquals;

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
}
