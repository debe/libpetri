package org.libpetri.analysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.SortedSet;
import java.util.StringJoiner;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * The abstract <b>name-partition</b> layer for the &nu;-aware state class graph
 * (NU-050, Route B).
 *
 * <p>The plain {@link StateClassGraph} is name-blind: a marking is a per-place
 * token <i>count</i>, so a &nu;-join fires whenever the counts allow, ignoring
 * whether the consumed tokens share a correlation name. This carries, beside the
 * count marking, an abstract partition of the correlation tokens into
 * name-<i>symbols</i>.
 *
 * <p>A symbol is an opaque identity only (NU-001) — the analyzer never evaluates
 * the runtime name projection, so a symbol carries no value; only distinctness
 * matters. {@link #canonicalKey} quotients markings that differ only by a
 * permutation of symbols (the raw symbol ids never appear in a key), which keeps
 * the graph finite when the live-name count is structurally bounded — the lever
 * that replaces Route A's budget {@code k}. The key string format matches the
 * Rust and TypeScript implementations byte-for-byte.
 */
final class NameMarking {

    // place name -> (symbol -> count). Only coloured places appear; a place's
    // total here equals its count in the base MarkingState.
    private final TreeMap<String, TreeMap<Integer, Integer>> perPlace;

    NameMarking() {
        this.perPlace = new TreeMap<>();
    }

    private NameMarking(TreeMap<String, TreeMap<Integer, Integer>> perPlace) {
        this.perPlace = perPlace;
    }

    NameMarking copy() {
        var p = new TreeMap<String, TreeMap<Integer, Integer>>();
        for (var e : perPlace.entrySet()) {
            p.put(e.getKey(), new TreeMap<>(e.getValue()));
        }
        return new NameMarking(p);
    }

    /** Adds {@code count} tokens of symbol {@code sym} to a coloured place. */
    void add(String place, int sym, int count) {
        if (count == 0) return;
        perPlace.computeIfAbsent(place, _ -> new TreeMap<>()).merge(sym, count, Integer::sum);
    }

    /**
     * Removes {@code count} tokens of {@code sym} from {@code place}; returns
     * false (unchanged) if fewer than {@code count} are present.
     */
    boolean remove(String place, int sym, int count) {
        var syms = perPlace.get(place);
        if (syms == null) return false;
        var have = syms.get(sym);
        if (have == null || have < count) return false;
        int left = have - count;
        if (left == 0) {
            syms.remove(sym);
            if (syms.isEmpty()) perPlace.remove(place);
        } else {
            syms.put(sym, left);
        }
        return true;
    }

    int countOf(String place, int sym) {
        var syms = perPlace.get(place);
        return syms == null ? 0 : syms.getOrDefault(sym, 0);
    }

    List<Integer> symbolsIn(String place) {
        var syms = perPlace.get(place);
        return syms == null ? List.of() : new ArrayList<>(syms.keySet());
    }

    private SortedSet<Integer> liveSymbols() {
        var all = new TreeSet<Integer>();
        for (var m : perPlace.values()) all.addAll(m.keySet());
        return all;
    }

    /**
     * Symmetry-canonical key over {@code colouredOrder} (the finiteness
     * mechanism). Two markings differing only by a permutation of symbols produce
     * an identical key (NU-001). Each symbol's signature is its count vector over
     * {@code colouredOrder}; symbols are ranked by (signature, raw id) and emitted
     * per place as a rank-multiset — a complete invariant of the symbol-permutation
     * orbit.
     */
    String canonicalKey(List<String> colouredOrder) {
        var syms = new ArrayList<>(liveSymbols());
        // Rank symbols by (signature, raw id).
        var ranked = new ArrayList<int[]>(); // [sym] with a parallel signature list
        var sigs = new HashMap<Integer, List<Integer>>();
        for (int s : syms) {
            var sig = new ArrayList<Integer>(colouredOrder.size());
            for (var p : colouredOrder) sig.add(countOf(p, s));
            sigs.put(s, sig);
            ranked.add(new int[]{s});
        }
        ranked.sort((a, b) -> {
            int c = compareIntList(sigs.get(a[0]), sigs.get(b[0]));
            return c != 0 ? c : Integer.compare(a[0], b[0]);
        });
        var rankOf = new HashMap<Integer, Integer>();
        for (int r = 0; r < ranked.size(); r++) {
            rankOf.put(ranked.get(r)[0], r);
        }

        var parts = new ArrayList<String>(colouredOrder.size());
        for (var p : colouredOrder) {
            var entries = new ArrayList<int[]>(); // [rank, count]
            var syms2 = perPlace.get(p);
            if (syms2 != null) {
                for (var e : syms2.entrySet()) {
                    entries.add(new int[]{rankOf.get(e.getKey()), e.getValue()});
                }
            }
            entries.sort((a, b) -> a[0] != b[0] ? Integer.compare(a[0], b[0]) : Integer.compare(a[1], b[1]));
            var inner = new StringJoiner(",");
            for (var en : entries) inner.add(en[0] + "x" + en[1]);
            parts.add(p + ":{" + inner + "}");
        }
        return String.join("#", parts);
    }

    private static int compareIntList(List<Integer> a, List<Integer> b) {
        int n = Math.min(a.size(), b.size());
        for (int i = 0; i < n; i++) {
            int c = Integer.compare(a.get(i), b.get(i));
            if (c != 0) return c;
        }
        return Integer.compare(a.size(), b.size());
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof NameMarking other)) return false;
        return perPlace.equals(other.perPlace);
    }

    @Override
    public int hashCode() {
        return perPlace.hashCode();
    }
}
