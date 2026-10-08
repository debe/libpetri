package org.libpetri.analysis;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Transition;
import org.libpetri.core.internal.CodePointOrder;

/**
 * Stubborn sets of [VER-024]: at each class the enumeration expands only the enabled transitions
 * of one stubborn set, which keeps every reachable dead marking
 * ({@code lean/Libpetri/Novel/Stubborn.lean}). Footprints and indexes are computed once per net;
 * places are compared by name.
 */
final class StubbornSets {

    /** One enabling condition: a place that needs {@code need} tokens, or none for an inhibitor. */
    private record Condition(String place, int need, boolean inhibitor) {}

    private final List<Transition> transitions;
    private final Map<Transition, Integer> index = new IdentityHashMap<>();
    /** Per transition, every other transition dependent with it. */
    private final int[][] dependents;
    /** Per transition, its enabling conditions: inputs and reads by place name, then inhibitors. */
    private final List<List<Condition>> conditions = new ArrayList<>();
    /** Per place, the transitions with an outcome depositing into it. */
    private final Map<String, List<Integer>> increasers = new HashMap<>();
    /** Per place, the transitions with it among their inputs or resets. */
    private final Map<String, List<Integer>> decreasers = new HashMap<>();

    /** Computes the footprints of every transition of {@code net}. */
    StubbornSets(PetriNet net) {
        this.transitions = List.copyOf(net.transitions());
        int n = transitions.size();
        var tests = new ArrayList<Set<String>>();
        var writes = new ArrayList<Set<String>>();
        var overwrites = new ArrayList<Set<String>>();
        var testers = new HashMap<String, List<Integer>>();
        var writers = new HashMap<String, List<Integer>>();
        var overwriters = new HashMap<String, List<Integer>>();
        for (int i = 0; i < n; i++) {
            var t = transitions.get(i);
            index.put(t, i);
            var tst = new LinkedHashSet<String>();
            var wr = new LinkedHashSet<String>();
            var ow = new LinkedHashSet<String>();
            var dec = new LinkedHashSet<String>();
            var inc = new LinkedHashSet<String>();
            var enabling = new ArrayList<Condition>();
            for (var in : t.inputSpecs()) {
                String p = in.place().name();
                tst.add(p);
                wr.add(p);
                dec.add(p);
                if (in instanceof Arc.In.All || in instanceof Arc.In.AtLeast) ow.add(p);
                enabling.add(new Condition(p, in.requiredCount(), false));
            }
            for (var arc : t.reads()) {
                tst.add(arc.place().name());
                enabling.add(new Condition(arc.place().name(), 1, false));
            }
            // Stable: an input and a read on one place keep the input first.
            enabling.sort((x, y) -> CodePointOrder.compare(x.place(), y.place()));
            var inhibitors = new TreeSet<String>(CodePointOrder.COMPARATOR);
            for (var arc : t.inhibitors()) inhibitors.add(arc.place().name());
            for (var p : inhibitors) {
                tst.add(p);
                enabling.add(new Condition(p, 0, true));
            }
            for (var arc : t.resets()) {
                wr.add(arc.place().name());
                ow.add(arc.place().name());
                dec.add(arc.place().name());
            }
            for (var outcome : BranchOutcomes.outcomes(t)) {
                for (var p : outcome.deposits().keySet()) {
                    wr.add(p.name());
                    inc.add(p.name());
                }
            }
            tests.add(tst);
            writes.add(wr);
            overwrites.add(ow);
            conditions.add(List.copyOf(enabling));
            for (var p : tst) add(testers, p, i);
            for (var p : wr) add(writers, p, i);
            for (var p : ow) add(overwriters, p, i);
            for (var p : inc) add(increasers, p, i);
            for (var p : dec) add(decreasers, p, i);
        }
        // t and u are dependent when one writes what the other tests, or one overwrites what the
        // other writes ([VER-024] "Footprints").
        dependents = new int[n][];
        for (int i = 0; i < n; i++) {
            var dep = new TreeSet<Integer>();
            collect(dep, i, writes.get(i), testers);
            collect(dep, i, tests.get(i), writers);
            collect(dep, i, overwrites.get(i), writers);
            collect(dep, i, writes.get(i), overwriters);
            dependents[i] = dep.stream().mapToInt(Integer::intValue).toArray();
        }
    }

    private static void add(Map<String, List<Integer>> index, String place, int i) {
        var list = index.computeIfAbsent(place, _ -> new ArrayList<>());
        if (list.isEmpty() || list.getLast() != i) list.add(i);
    }

    private static void collect(Set<Integer> into, int self, Set<String> places, Map<String, List<Integer>> index) {
        for (var p : places) {
            for (int j : index.getOrDefault(p, List.of())) {
                if (j != self) into.add(j);
            }
        }
    }

    /**
     * The enabled transitions to expand at {@code marking}: those of the closure, over every
     * enabled seed, with the fewest enabled members, the code-point-smallest seed name breaking
     * ties. They are returned in the order of {@code enabled}.
     */
    List<Transition> select(MarkingState marking, List<Transition> enabled) {
        if (enabled.size() <= 1) return enabled;
        var isEnabled = new boolean[transitions.size()];
        for (var t : enabled) isEnabled[index.get(t)] = true;
        var counts = new HashMap<String, Integer>();
        for (var e : marking.asMap().entrySet()) counts.put(e.getKey().name(), e.getValue());
        var seeds = new ArrayList<>(enabled);
        seeds.sort((x, y) -> CodePointOrder.compare(x.name(), y.name()));
        boolean[] best = null;
        int bestCount = Integer.MAX_VALUE;
        for (var seed : seeds) {
            var set = new boolean[transitions.size()];
            int count = closure(index.get(seed), counts, isEnabled, bestCount, set);
            if (count < bestCount) {
                best = set;
                bestCount = count;
                if (count == 1) break;
            }
        }
        var chosen = best;
        return enabled.stream().filter(t -> chosen[index.get(t)]).toList();
    }

    /**
     * Fills {@code inSet} with the closure from {@code seed} under D1 / D2 and returns the
     * number of enabled members, or {@code bound} once it reaches it, since it can no longer win.
     */
    private int closure(int seed, Map<String, Integer> counts, boolean[] isEnabled, int bound, boolean[] inSet) {
        var work = new ArrayDeque<Integer>();
        work.push(seed);
        inSet[seed] = true;
        int enabledCount = 0;
        while (!work.isEmpty()) {
            int i = work.pop();
            int[] next;
            if (isEnabled[i]) {
                if (++enabledCount >= bound) return bound;
                next = dependents[i];
            } else {
                next = scapegoat(i, counts);
            }
            for (int j : next) {
                if (!inSet[j]) {
                    inSet[j] = true;
                    work.push(j);
                }
            }
        }
        return enabledCount;
    }

    /** D2: the transitions that can satisfy the first unsatisfied condition of disabled {@code i}. */
    private int[] scapegoat(int i, Map<String, Integer> counts) {
        for (var c : conditions.get(i)) {
            int have = counts.getOrDefault(c.place(), 0);
            if (c.inhibitor() ? have > 0 : have < c.need()) {
                var list = (c.inhibitor() ? decreasers : increasers).getOrDefault(c.place(), List.of());
                return list.stream().mapToInt(Integer::intValue).toArray();
            }
        }
        throw new IllegalStateException("stubborn set: transition '" + transitions.get(i).name()
            + "' is disabled with every condition satisfied");
    }
}
