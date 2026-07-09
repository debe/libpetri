package org.libpetri.analysis;

import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The &nu;-aware (name-partition quotient) State Class Graph (NU-050, Route B).
 *
 * <p>Mirrors {@link StateClassGraph} — same Berthomieu-Diaz BFS, same count + DBM
 * successor step (reused verbatim via {@link StateClassGraph#computeSuccessor}) —
 * but each class additionally carries the abstract {@link NameMarking} partition.
 * A &nu;-join is enabled only when one shared name is present at the required
 * multiplicity in every correlated input; a mint introduces a globally-fresh
 * name-symbol into its coloured outputs; dedup is by the symmetry-canonical key
 * so states differing only by a permutation of names collapse — the quotient that
 * keeps the graph finite when live names are structurally bounded.
 *
 * <p>&nu;-PN reachability is undecidable; if BFS closes within {@code maxClasses}
 * the graph is the complete reachable quotient (an exact answer), otherwise it is
 * truncated ({@link #isComplete()} returns false) and the verifier reports
 * {@code Unknown}.
 */
public final class NameStateClassGraph {

    /** An edge (transition firing) in the name-aware graph. */
    public record Edge(int from, int to, String transitionName) {}

    private final List<NameStateClass> classes = new ArrayList<>();
    private final List<Edge> edges = new ArrayList<>();
    private final List<List<Integer>> successors = new ArrayList<>();
    private boolean complete = true;

    private NameStateClassGraph() {}

    public boolean isComplete() {
        return complete;
    }

    public int classCount() {
        return classes.size();
    }

    public List<Integer> successorsOf(int idx) {
        return successors.get(idx);
    }

    /** The base count-marking of class {@code idx} (for property queries). */
    public MarkingState markingOf(int idx) {
        return classes.get(idx).base.marking();
    }

    public List<Edge> edges() {
        return edges;
    }

    public static NameStateClassGraph build(
            PetriNet net,
            MarkingState initialMarking,
            NameFragment fragment,
            int maxClasses,
            Set<EnvironmentPlace<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode
    ) {
        var envPlaces = new HashSet<Place<?>>();
        for (var ep : environmentPlaces) {
            envPlaces.add(ep.place());
        }

        var graph = new NameStateClassGraph();
        var base0 = StateClassGraph.initialStateClass(net, initialMarking, envPlaces, environmentMode);
        // Coloured places start empty in the supported fragment (the verifier
        // guards this), so the initial name partition is empty.
        var initial = new NameStateClass(base0, new NameMarking(), fragment.colouredOrder);

        var indexOf = new HashMap<NameStateClass, Integer>();
        graph.pushClass(initial, indexOf);

        int[] nextSym = {0};
        var queue = new ArrayDeque<Integer>();
        queue.add(0);

        while (!queue.isEmpty()) {
            if (graph.classes.size() >= maxClasses) {
                graph.complete = false;
                break;
            }
            int curIdx = queue.poll();
            var current = graph.classes.get(curIdx);

            for (var transition : current.base.enabledTransitions()) {
                var role = fragment.role(transition.name());
                for (var vt : StateClassGraph.expandTransition(transition)) {
                    var baseSucc = StateClassGraph.computeSuccessor(net, current.base, vt, envPlaces, environmentMode);
                    if (baseSucc == null || baseSucc.isEmpty()) {
                        continue; // DBM zone infeasible
                    }
                    var nameSuccs = nameSuccessors(role, current.names, vt.outputPlaces(), fragment, nextSym);
                    for (var nm : nameSuccs) {
                        var succ = new NameStateClass(baseSucc, nm, fragment.colouredOrder);
                        Integer toIdx = indexOf.get(succ);
                        if (toIdx == null) {
                            toIdx = graph.classes.size();
                            graph.pushClass(succ, indexOf);
                            queue.add(toIdx);
                        }
                        graph.addEdge(curIdx, toIdx, transition.name());
                    }
                }
            }
        }
        return graph;
    }

    private void pushClass(NameStateClass c, Map<NameStateClass, Integer> indexOf) {
        int idx = classes.size();
        classes.add(c);
        successors.add(new ArrayList<>());
        indexOf.put(c, idx);
    }

    private void addEdge(int from, int to, String name) {
        edges.add(new Edge(from, to, name));
        successors.get(from).add(to);
    }

    /**
     * Name-layer successors of one firing. {@code Ordinary} passes the layer
     * through; {@code Mint} stamps one globally-fresh symbol into the coloured
     * outputs of this branch (one symbol into several = same-mint siblings);
     * {@code Join} yields one successor per enabling symbol (none =&gt; the join is
     * name-disabled); {@code Consume} (EXTENDED) yields one successor per resident
     * symbol of its single coloured input, removing that symbol and re-emitting it
     * into the fired branch's coloured outputs, so a branch with no coloured output
     * drains the symbol and a branch with one relays it.
     */
    private static List<NameMarking> nameSuccessors(
            NameFragment.Role role,
            NameMarking names,
            Set<Place<?>> outputPlaces,
            NameFragment fragment,
            int[] nextSym
    ) {
        return switch (role) {
            case NameFragment.Role.Ordinary _ -> List.of(names.copy());
            case NameFragment.Role.Mint _ -> {
                var colouredOut = colouredOutputs(outputPlaces, fragment);
                var nm = names.copy();
                if (!colouredOut.isEmpty()) {
                    int fresh = nextSym[0]++;
                    for (var p : colouredOut) {
                        nm.add(p, fresh, 1);
                    }
                }
                yield List.of(nm);
            }
            case NameFragment.Role.Join j -> {
                var result = new ArrayList<NameMarking>();
                for (int s : enablingSymbols(names, j.colouredIn())) {
                    var nm = names.copy();
                    for (var e : j.colouredIn()) {
                        nm.remove(e.getKey(), s, e.getValue());
                    }
                    result.add(nm);
                }
                yield result;
            }
            case NameFragment.Role.Consume c -> {
                var inputPlace = c.colouredInput(); // classify restricts Consume to one coloured input at count 1
                var colouredOut = colouredOutputs(outputPlaces, fragment);
                // The consumed count is fixed at 1, so EVERY resident symbol (each
                // present at count >= 1) enables a firing — none is dropped, so no
                // base-enabled firing vanishes (Blocker 2). Each coloured output
                // receives EXACTLY ONE symbol, matching the base marking's single
                // token per output place (Blocker 1).
                var result = new ArrayList<NameMarking>();
                for (int s : names.symbolsIn(inputPlace)) {
                    var nm = names.copy();
                    nm.remove(inputPlace, s, 1);
                    for (var outP : colouredOut) {
                        nm.add(outP, s, 1); // relay: thread the same symbol; drain adds to none
                    }
                    result.add(nm);
                }
                yield result;
            }
        };
    }

    /**
     * The coloured output places of the fired branch (used by {@code Mint} to stamp
     * a fresh symbol and by {@code Consume} to relay the consumed symbol).
     */
    private static List<String> colouredOutputs(Set<Place<?>> outputPlaces, NameFragment fragment) {
        var result = new ArrayList<String>();
        for (var p : outputPlaces) {
            if (fragment.isColoured(p.name())) {
                result.add(p.name());
            }
        }
        return result;
    }

    /**
     * Symbols that enable a join: present at the required multiplicity in EVERY
     * correlated input — the exactness core of NU-050 (a count-only check would
     * wrongly fire on two distinct names).
     */
    private static List<Integer> enablingSymbols(NameMarking names, List<Map.Entry<String, Integer>> colouredIn) {
        if (colouredIn.isEmpty()) {
            return List.of();
        }
        var first = colouredIn.get(0);
        var result = new ArrayList<Integer>();
        for (int s : names.symbolsIn(first.getKey())) {
            if (names.countOf(first.getKey(), s) < first.getValue()) {
                continue;
            }
            boolean ok = true;
            for (int i = 1; i < colouredIn.size(); i++) {
                var e = colouredIn.get(i);
                if (names.countOf(e.getKey(), s) < e.getValue()) {
                    ok = false;
                    break;
                }
            }
            if (ok) {
                result.add(s);
            }
        }
        return result;
    }
}
