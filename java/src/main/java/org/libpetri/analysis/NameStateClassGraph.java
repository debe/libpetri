package org.libpetri.analysis;

import org.libpetri.core.Arc;
import org.libpetri.core.EnvironmentPlace;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Transition;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
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

    /** The full class at {@code idx} (package-private, for the interning tests). */
    NameStateClass classAt(int idx) {
        return classes.get(idx);
    }

    public static NameStateClassGraph build(
            PetriNet net,
            MarkingState initialMarking,
            NameFragment fragment,
            int maxClasses,
            Set<EnvironmentPlace<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode,
            PrioritySemantics prioritySemantics
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
        // Hash-consing (memory only, no semantic effect): the base class and the name
        // layer are each shared between every state class that carries an equal one. Two
        // name layers with the same canonical key are the same partition up to a renaming
        // of symbols, and every consumer of the layer is symmetric under renaming
        // (successor steps, willFire, the key itself); freshness stays sound because
        // minted symbols come from a monotone counter that never revisits an id. The base
        // is shared only when marking, zone AND readyEarliest agree (see BaseKey), so the
        // shared object carries everything the successor step reads — Interning.lean,
        // interned_keys_eq; equivariance_is_necessary is the witness for that clause.
        // Without this a class costs ~4 KB (TreeMap-of-TreeMaps + key string dominate) and a
        // few million classes exhaust the heap before a medium-sized ν-net closes.
        var baseIntern = new HashMap<BaseKey, StateClass>();
        var nameIntern = new HashMap<String, NameStateClass>();
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

            var enabled = current.base.enabledTransitions();
            for (int idxL = 0; idxL < enabled.size(); idxL++) {
                var transition = enabled.get(idxL);
                if (prioritySemantics == PrioritySemantics.CONFLICT
                        && priorityDominated(transition, idxL, enabled, current.base.readyEarliest(),
                                current.base.marking(), current.names, fragment)) {
                    // A ready, conflicting, strictly-higher-priority transition would win this
                    // token at the executor, so this firing is not runtime-reachable (NU-052).
                    continue;
                }
                var role = fragment.role(transition.name());
                for (var vt : StateClassGraph.expandTransition(transition)) {
                    var baseSucc = StateClassGraph.computeSuccessor(net, current.base, vt, envPlaces, environmentMode);
                    if (baseSucc == null || baseSucc.isEmpty()) {
                        continue; // DBM zone infeasible
                    }
                    var nameSuccs = nameSuccessors(role, current.names, vt.outputPlaces(), fragment, nextSym);
                    var sharedBase = baseIntern.computeIfAbsent(new BaseKey(baseSucc), _ -> baseSucc);
                    for (var nm : nameSuccs) {
                        var succ = new NameStateClass(sharedBase, nm, fragment.colouredOrder);
                        var sharedNames = nameIntern.get(succ.nameKey());
                        if (sharedNames == null) {
                            nameIntern.put(succ.nameKey(), succ);
                        } else {
                            succ = new NameStateClass(sharedBase, sharedNames.names, sharedNames.nameKey());
                        }
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
     * Intern key for the base layer. {@link StateClass#equals(Object)} is marking + zone, which
     * is all base timed-reachability needs — but the NU-052 conflict prune also reads
     * {@link StateClass#readyEarliest()}, the class-relative earliest-ready times captured
     * before {@code letTimePass}, and two arrivals at one zone can disagree on those (a
     * transition freshly enabled here versus one persistent through an unbounded delay).
     * Sharing a base across name layers is semantics-free only if the shared object carries
     * everything the successor step reads ({@code Interning.lean},
     * {@code equivariance_is_necessary}), so the key is all three. Bit-exact on the doubles
     * ({@link Arrays#equals(double[], double[])}).
     */
    private record BaseKey(StateClass base, double[] readyEarliest) {
        BaseKey(StateClass base) {
            this(base, base.readyEarliest());
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof BaseKey other
                && base.equals(other.base)
                && Arrays.equals(readyEarliest, other.readyEarliest);
        }

        @Override
        public int hashCode() {
            return 31 * base.hashCode() + Arrays.hashCode(readyEarliest);
        }
    }

    /** Float slack for the class-relative earliest-ready comparison (matches the DBM's own EPSILON). */
    private static final double READY_EPS = 1e-9;

    /**
     * True if a firing of {@code l} is pre-empted by conflict-only priority: some other enabled
     * transition {@code h} has strictly higher priority, shares a consumed input place with
     * {@code l} <b>under real competition</b>, becomes ready no later than {@code l}, and actually
     * fires in this class (produces a name-successor). The executor fires ready transitions in
     * descending priority order within a pass, so {@code h} takes the contested token and {@code l}
     * cannot fire — the pruned firing is not runtime-reachable. See {@link PrioritySemantics#CONFLICT}.
     *
     * <p><b>Readiness (DBM residual-earliest).</b> The name-SCG carries a DBM, so a static
     * {@code h.earliest() <= l.earliest()} does NOT entail "H ready no later than L": their
     * class-relative enabling epochs can put H's clock behind L's. We compare the class-relative
     * earliest-ready times captured on the base class ({@link StateClass#readyEarliest()}, the DBM
     * lower bounds before {@code letTimePass}): H pre-empts L only when
     * {@code readyEarliest[H] <= readyEarliest[L] + EPS}. This is fully precise on the zone
     * off-diagonal and subsumes the previously-shipped {@code earliest()==0} case (an immediate H has
     * {@code readyEarliest[H] == 0 <= readyEarliest[L]}), so no capability is lost.
     *
     * <p><b>Real competition (multiplicity).</b> Sharing a consumed place is not enough: if the place
     * holds enough tokens for H and L at once they do not compete, and pruning L would be unsound —
     * see {@link #sharesConsumedInput(Transition, Transition, MarkingState)}.
     *
     * <p>The {@code willFire} guard is essential on a &nu;-net: a match (join) transition can be
     * base-enabled yet <b>name-disabled</b> (its inputs carry no shared name). Such a join never
     * consumes the contested token, so it must not pre-empt a conflicting drain — otherwise a
     * genuine straggler would strand.
     */
    private static boolean priorityDominated(
            Transition l, int idxL, List<Transition> enabled, double[] readyEarliest,
            MarkingState marking, NameMarking names, NameFragment fragment) {
        for (int idxH = 0; idxH < enabled.size(); idxH++) {
            var h = enabled.get(idxH);
            if (h == l) {
                continue;
            }
            if (h.priority() > l.priority()
                    && readyEarliest[idxH] <= readyEarliest[idxL] + READY_EPS
                    && willFire(h, names, fragment)
                    && sharesConsumedInput(h, l, marking)) {
                return true;
            }
        }
        return false;
    }

    /**
     * True if base-enabled {@code h} actually produces a name-successor from this class — i.e. a
     * join finds a shared enabling name and a consumer finds a resident symbol. {@code Ordinary}
     * and {@code Mint} always fire. Only a name-disabled join (or an empty-input consumer) does not,
     * and such a transition must not pre-empt a conflicting firing.
     */
    private static boolean willFire(Transition h, NameMarking names, NameFragment fragment) {
        return switch (fragment.role(h.name())) {
            case NameFragment.Role.Join j -> !enablingSymbols(names, j.colouredIn()).isEmpty();
            case NameFragment.Role.Consume c -> !names.symbolsIn(c.colouredInput()).isEmpty();
            // Explicit (not `default`) so a future Role variant forces a compile-time
            // decision here rather than silently defaulting to will-fire=true.
            case NameFragment.Role.Ordinary _ -> true;
            case NameFragment.Role.Mint _ -> true;
        };
    }

    /**
     * True if {@code h} and {@code l} genuinely compete for a consumed token — they share a consumed
     * input place {@code p} whose token count in {@code marking} cannot satisfy both demands at once
     * ({@code count(p) < demand_h(p) + demand_l(p)}). Read and inhibitor arcs are excluded
     * ({@link Transition#inputPlaces()} is consumed inputs only), since they do not remove a token
     * another transition competes for.
     *
     * <p>The multiplicity clause is a soundness guard for the NU-052 prune: if the shared place holds
     * enough tokens for both, {@code h} does NOT rob {@code l}, so pruning {@code l} would drop a
     * runtime-reachable firing.
     */
    private static boolean sharesConsumedInput(Transition h, Transition l, MarkingState marking) {
        var lIns = l.inputPlaces();
        for (var p : h.inputPlaces()) {
            if (lIns.contains(p)
                    && marking.tokens(p) < consumedDemand(h, p) + consumedDemand(l, p)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Tokens {@code t} consumes from {@code place} on one firing (summed across its input specs
     * referencing that place — normally a single spec). Uses the enablement {@code requiredCount} so
     * {@code All}/{@code AtLeast} demand their minimum, matching the base SCG's consumption model.
     */
    private static int consumedDemand(Transition t, Place<?> place) {
        int demand = 0;
        for (var in : t.inputSpecs()) {
            if (in.place().name().equals(place.name())) {
                demand += switch (in) {
                    case Arc.In.One _ -> 1;
                    case Arc.In.Exactly e -> e.count();
                    case Arc.In.All _ -> 1;
                    case Arc.In.AtLeast a -> a.minimum();
                };
            }
        }
        return demand;
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
     *
     * <p>Package-private for {@code NameStateClassGraphInterningTest}: this step's
     * equivariance under symbol renaming is the hypothesis {@code Interning.lean} rests on.
     */
    static List<NameMarking> nameSuccessors(
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
