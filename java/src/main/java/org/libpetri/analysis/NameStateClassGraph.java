package org.libpetri.analysis;

import org.libpetri.core.internal.VerificationDeadline;
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
import java.util.function.Predicate;

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
 * truncated ({@link #isComplete()} returns false): the verifier then reads only its explored
 * prefix — a violation among the stored classes stands, nothing is proven — and otherwise
 * reports {@code Unknown} ([VER-012] AC3).
 */
public final class NameStateClassGraph {

    /** An edge (transition firing) in the name-aware graph. */
    public record Edge(int from, int to, String transitionName) {}

    private final List<NameStateClass> classes = new ArrayList<>();
    private final List<Edge> edges = new ArrayList<>();
    private final List<List<Integer>> successors = new ArrayList<>();
    /** The transition name of each entry of {@link #successors}, index for index. */
    private final List<List<String>> successorLabels = new ArrayList<>();
    private boolean complete = true;
    private int expandedCount = 0;
    private int stoppedAt = -1;

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

    /**
     * The transition name of each successor edge of class {@code idx}, in the order of
     * {@link #successorsOf(int)}: the labelled adjacency a shortest witness path is read from
     * in {@code O(V + E)}.
     */
    public List<String> successorLabelsOf(int idx) {
        return successorLabels.get(idx);
    }

    /**
     * How many classes the build expanded before it closed or hit its class budget. The
     * worklist is first-in-first-out, so they are exactly classes {@code 0 .. expandedCount()-1};
     * on a closed graph, all of them. A frontier class of a truncated graph has no successors
     * only because nobody looked ([VER-017], "Verdicts from a truncated graph").
     */
    public int expandedCount() {
        return expandedCount;
    }

    /**
     * The class the build stopped at because it met the stop predicate ([VER-012]), or
     * {@code -1} when it closed or hit its class budget. It is the last class stored, and the
     * graph is then not complete: an early-stopped graph is a prefix of the breadth-first
     * build, never a closed one.
     */
    public int stoppedAt() {
        return stoppedAt;
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
        return build(net, initialMarking, fragment, maxClasses, environmentPlaces, environmentMode,
            prioritySemantics, null);
    }

    /**
     * As {@link #build(PetriNet, MarkingState, NameFragment, int, Set, EnvironmentAnalysisMode,
     * PrioritySemantics)}, stopping at the first class whose marking meets {@code stopAt}
     * ({@code null}: never) — tested on each class as it is discovered, the initial one first.
     * Discovery order is index order, so the class stopped at is the lowest-index class meeting
     * the predicate in the graph built without stopping, and every edge a breadth-first path to
     * it uses is already recorded: the witness path is the same one ([VER-012]).
     */
    public static NameStateClassGraph build(
            PetriNet net,
            MarkingState initialMarking,
            NameFragment fragment,
            int maxClasses,
            Set<EnvironmentPlace<?>> environmentPlaces,
            EnvironmentAnalysisMode environmentMode,
            PrioritySemantics prioritySemantics,
            Predicate<MarkingState> stopAt
    ) {
        var envPlaces = new HashSet<Place<?>>();
        for (var ep : environmentPlaces) {
            envPlaces.add(ep.place());
        }

        var graph = new NameStateClassGraph();
        var clockOrder = StateClassGraph.ClockOrder.of(net);
        // No join is enabled here: every correlated input consumes at least one token (NU-020,
        // IO-002, IO-004) and coloured places start empty (the verifier guards this), so the
        // count test alone gives the clocks.
        var base0 = StateClassGraph.initialStateClass(net, initialMarking, envPlaces, environmentMode, false, clockOrder);
        // Coloured places start empty in the supported fragment (the verifier
        // guards this), so the initial name partition is empty.
        var initial = new NameStateClass(base0, new NameMarking(), fragment.colouredOrder);


        var indexOf = new HashMap<ClassId, Integer>();
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
        //
        // The intern ids are also the class identity: a class is a (base id, name id) pair, so
        // two arrivals that share a marking, a zone and a name layer but disagree on
        // readyEarliest stay two classes and each keeps its own NU-052 prune input.
        var baseIntern = new HashMap<BaseKey, InternedBase>();
        var nameIntern = new HashMap<String, InternedNames>();
        var interned0 = internBase(baseIntern, base0);
        var names0 = internNames(nameIntern, new NameMarking(), fragment.colouredOrder);
        graph.pushClass(initial, new ClassId(interned0.id(), names0.id()), indexOf);
        if (stopAt != null && stopAt.test(initial.base.marking())) {
            graph.stop(0);
            return graph;
        }

        int[] nextSym = {0};
        var queue = new ArrayDeque<Integer>();
        queue.add(0);

        while (!queue.isEmpty()) {
            if (graph.classes.size() >= maxClasses) {
                graph.complete = false;
                break;
            }
            // [VER-013] total budget or cancellation, when a verifier bound a deadline (see
            // StateClassGraph.build).
            VerificationDeadline.checkpoint();
            int curIdx = queue.poll();
            graph.expandedCount++;
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
                    // Name-layer steps of this firing (the join may yield 0). The base successor
                    // is computed per step: a ν-join holds a clock only while one name is present
                    // in every correlated input (NU-020), judged on the step's intermediate and
                    // new layers (TIME-012).
                    for (var step : nameSuccessors(role, current.names, vt.outputPlaces(), fragment, nextSym)) {
                        var between = step.intermediate() != null ? step.intermediate() : current.names;
                        var baseSucc = StateClassGraph.computeSuccessor(
                            net, current.base, vt, envPlaces, environmentMode, false, clockOrder,
                            t -> nameEnabled(t, between, fragment),
                            t -> nameEnabled(t, step.after(), fragment));
                        if (baseSucc == null || baseSucc.isEmpty()) {
                            continue; // DBM zone infeasible
                        }
                        var sharedBase = internBase(baseIntern, baseSucc);
                        var sharedNames = internNames(nameIntern, step.after(), fragment.colouredOrder);
                        var id = new ClassId(sharedBase.id(), sharedNames.id());
                        Integer toIdx = indexOf.get(id);
                        if (toIdx == null) {
                            toIdx = graph.classes.size();
                            graph.pushClass(
                                new NameStateClass(sharedBase.base(), sharedNames.names(), sharedNames.nameKey()),
                                id, indexOf);
                            queue.add(toIdx);
                            if (stopAt != null && stopAt.test(sharedBase.base().marking())) {
                                graph.addEdge(curIdx, toIdx, transition.name());
                                // Partly expanded: not counted, so it is never read as quiescent.
                                graph.expandedCount--;
                                graph.stop(toIdx);
                                return graph;
                            }
                        }
                        graph.addEdge(curIdx, toIdx, transition.name());
                    }
                }
            }
        }
        return graph;
    }

    private void stop(int idx) {
        stoppedAt = idx;
        complete = false;
    }

    private void pushClass(NameStateClass c, ClassId id, Map<ClassId, Integer> indexOf) {
        int idx = classes.size();
        classes.add(c);
        successors.add(new ArrayList<>());
        successorLabels.add(new ArrayList<>());
        indexOf.put(id, idx);
    }

    /**
     * Class identity: the pair of intern ids, mirroring the Rust reference
     * ({@code name_state_class_graph.rs}, {@code index_of}). The base id already carries
     * {@code readyEarliest} (see {@link BaseKey}), which {@link StateClass#equals(Object)}
     * deliberately does not, so keying on the id and not on the class object is what keeps the
     * NU-052 prune reading each arrival's own earliest-ready times.
     */
    private record ClassId(int baseId, int nameId) {}

    /** An interned base class with the id that identifies it. */
    private record InternedBase(int id, StateClass base) {}

    /** An interned name layer with the id that identifies it and its canonical key. */
    private record InternedNames(int id, NameMarking names, String nameKey) {}

    private static InternedBase internBase(Map<BaseKey, InternedBase> intern, StateClass base) {
        int next = intern.size();
        return intern.computeIfAbsent(new BaseKey(base), _ -> new InternedBase(next, base));
    }

    private static InternedNames internNames(
            Map<String, InternedNames> intern, NameMarking names, List<String> colouredOrder) {
        var key = names.canonicalKey(colouredOrder);
        int next = intern.size();
        return intern.computeIfAbsent(key, _ -> new InternedNames(next, names, key));
    }

    private void addEdge(int from, int to, String name) {
        edges.add(new Edge(from, to, name));
        successors.get(from).add(to);
        successorLabels.get(from).add(name);
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
     *
     * <p>A pruner in flight ({@code inflight:<H>} marked, [VER-004]) pre-empts nothing
     * ({@link InFlight#conflictDemand}).
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
                    // [VER-004]: a pruner whose action is in flight pre-empts nothing; the Java and
                    // TypeScript executors do not start it again while it runs. A no-op on a net
                    // without the split's place.
                    && marking.tokens(Place.of(InFlight.inFlightPlace(h.name()), Object.class)) == 0
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
     * One name-layer step of a firing: the layer once the firing has taken its inputs
     * ({@code null} when it takes no symbol, so the layer is the class's own) and the layer once
     * its outputs have landed. The first is the name half of the intermediate marking of TIME-012.
     */
    record NameStep(NameMarking intermediate, NameMarking after) {}

    /**
     * Whether {@code t} is enabled by the name layer {@code names}, given that the count marking
     * enables it: a ν-join needs one symbol present at the required multiplicity in every
     * correlated input (NU-020); every other role is enabled by counts alone (a consumer's input
     * count is its symbol count).
     */
    private static boolean nameEnabled(Transition t, NameMarking names, NameFragment fragment) {
        return !(fragment.role(t.name()) instanceof NameFragment.Role.Join j)
            || !enablingSymbols(names, j.colouredIn()).isEmpty();
    }

    /**
     * Name-layer successors of one firing, as {@link NameStep}s. {@code Ordinary} passes the layer
     * through; {@code Mint} stamps one globally-fresh symbol into the coloured
     * outputs of this branch (one symbol into several = same-mint siblings);
     * {@code Join} yields one successor per enabling symbol (none =&gt; the join is
     * name-disabled), removing it from the keys and adding it once to each relay target
     * of the fired branch (EXTENDED, NU-054); {@code Consume} (EXTENDED) yields one successor per resident
     * symbol of its single coloured input, removing that symbol and re-emitting it
     * into the fired branch's coloured outputs, so a branch with no coloured output
     * drains the symbol and a branch with one relays it. Both emit one successor per
     * distinct symbol <em>signature</em> only ({@link #distinctSignatures}, [VER-012]
     * orbit dedup): symbols with equal signatures give the same canonical key. A join or consume
     * step's intermediate layer is the class's layer with the chosen symbol removed from the
     * consumed places; it is renamed with the successor, and {@link #nameEnabled} reads only
     * whether some symbol enables a join, so the clocks it decides are invariant too.
     *
     * <p>Package-private for {@code NameStateClassGraphInterningTest}: this step's
     * equivariance under symbol renaming is the hypothesis {@code Interning.lean} rests on.
     */
    static List<NameStep> nameSuccessors(
            NameFragment.Role role,
            NameMarking names,
            Set<Place<?>> outputPlaces,
            NameFragment fragment,
            int[] nextSym
    ) {
        return switch (role) {
            case NameFragment.Role.Ordinary _ -> List.of(new NameStep(null, names.copy()));
            case NameFragment.Role.Mint _ -> {
                var colouredOut = colouredOutputs(outputPlaces, fragment);
                var nm = names.copy();
                if (!colouredOut.isEmpty()) {
                    int fresh = nextSym[0]++;
                    for (var p : colouredOut) {
                        nm.add(p, fresh, 1);
                    }
                }
                yield List.of(new NameStep(null, nm));
            }
            case NameFragment.Role.Join j -> {
                // NU-054: the relay targets of the fired branch. Relaying adds back the symbol
                // the join removed, so the step mints nothing, and it stays equivariant under
                // renaming: the orbit dedup below reads signatures on the PRE-step layer, and a
                // transposition of two equal-signature symbols fixes that layer and maps one
                // successor onto the other — equal keys, as for a drain.
                var relays = new ArrayList<String>();
                if (!j.relayTo().isEmpty()) {
                    for (var p : outputPlaces) {
                        if (j.relayTo().contains(p.name())) relays.add(p.name());
                    }
                }
                var result = new ArrayList<NameStep>();
                for (int s : distinctSignatures(enablingSymbols(names, j.colouredIn()), names, fragment)) {
                    var between = names.copy();
                    for (var e : j.colouredIn()) {
                        between.remove(e.getKey(), s, e.getValue());
                    }
                    var after = between.copy();
                    for (var p : relays) {
                        after.add(p, s, 1);
                    }
                    result.add(new NameStep(between, after));
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
                var result = new ArrayList<NameStep>();
                for (int s : distinctSignatures(names.symbolsIn(inputPlace), names, fragment)) {
                    var between = names.copy();
                    between.remove(inputPlace, s, 1);
                    var after = between.copy();
                    for (var outP : colouredOut) {
                        after.add(outP, s, 1); // relay: thread the same symbol; drain adds to none
                    }
                    result.add(new NameStep(between, after));
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
     * The first symbol of each distinct signature among {@code symbols}, in their order
     * ([VER-012] orbit dedup). A symbol's signature is its count vector over
     * {@code colouredOrder}. Two symbols with equal signatures are swapped by a transposition
     * that fixes the name marking, so firing with either yields the same canonical key:
     * emitting both only builds a copy and a key that collapse onto the class the first one
     * produced. Dropping them leaves the class set, the discovery order and the (label, key) set
     * of every class's successors unchanged — only parallel identical edges disappear. A join
     * over {@code N} live names otherwise costs {@code N} copies and keys per class, about
     * {@code O(N² log N)} over the graph.
     *
     * <p>Renaming-equivariance, the hypothesis of {@code Interning.lean}, still holds: the
     * number of distinct signatures, and the signature each class of symbols has, is invariant
     * under a renaming, so renamed layers keep equal (label, key) successor sets.
     */
    private static List<Integer> distinctSignatures(List<Integer> symbols, NameMarking names, NameFragment fragment) {
        if (symbols.size() < 2) {
            return symbols;
        }
        var order = fragment.colouredOrder;
        var seen = new HashSet<IntArrayKey>();
        var result = new ArrayList<Integer>(symbols.size());
        for (int s : symbols) {
            int[] signature = new int[order.size()];
            for (int i = 0; i < signature.length; i++) {
                signature[i] = names.countOf(order.get(i), s);
            }
            if (seen.add(new IntArrayKey(signature))) {
                result.add(s);
            }
        }
        return result;
    }

    /** An {@code int[]} compared by content, for the signature set. */
    private record IntArrayKey(int[] values) {
        @Override
        public boolean equals(Object o) {
            return o instanceof IntArrayKey k && Arrays.equals(values, k.values);
        }

        @Override
        public int hashCode() {
            return Arrays.hashCode(values);
        }
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
