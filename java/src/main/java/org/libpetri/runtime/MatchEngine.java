package org.libpetri.runtime;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
}
