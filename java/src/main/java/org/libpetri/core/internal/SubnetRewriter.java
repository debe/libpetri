package org.libpetri.core.internal;

import org.libpetri.core.Arc;
import org.libpetri.core.PetriNet;
import org.libpetri.core.Place;
import org.libpetri.core.Timing;
import org.libpetri.core.Transition;
import org.libpetri.core.TransitionAction;
import org.libpetri.core.TransitionContext;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletionStage;

/**
 * Internal utility encapsulating the structural rewrite primitive used by
 * {@link org.libpetri.core.SubnetDef#instantiate(String, Object)} and (later)
 * {@code PetriNet.Builder.compose(...)} per <b>MOD-020</b>.
 *
 * <p>The rewrite is purely structural: every place reference in every arc is
 * replaced according to a supplied {@code Map<Place<?>, Place<?>>} (the
 * "remap"); every transition is rebuilt with rewritten arcs, preserving its
 * timing, priority, and action by reference per <b>MOD-030</b>.
 *
 * <h2>Design</h2>
 * <p>One engine, multiple callers. The {@link #renameNet(PetriNet, String, Map, Map)}
 * entry point is specialised to the rename pass: it allocates fresh prefixed
 * places, records the old-to-new mapping in caller-supplied {@code Map}s (so
 * callers can build port/channel handle maps), and emits a renamed
 * {@link PetriNet}. The arc-rewrite helpers ({@link #rewriteIn},
 * {@link #rewriteOut}, etc.) are factored out so the future
 * {@code compose(...)} caller can substitute port-place mappings against an
 * arbitrary {@code Map<Place<?>, Place<?>>} without renaming everything.
 *
 * <h2>Performance</h2>
 * <p>The rewrite is on the build-time hot path. {@code Arc.Out.And} and
 * {@code Arc.Out.Xor} children are walked with explicit {@code ArrayList} +
 * indexed {@code for} loops (not {@code Stream}); the per-list allocation is
 * sized to {@code children.size()} so we avoid the
 * {@link java.util.Spliterator} + {@code Collectors.toList()} overhead the
 * streaming alternative would incur.
 *
 * <h2>Visibility</h2>
 * <p>This class lives in {@code org.libpetri.core.internal} so it is reachable
 * from {@link org.libpetri.core.SubnetDef} (different package, so the static
 * methods are {@code public}) but the package name itself is the visibility
 * convention: user code is not expected to consume this API.
 */
public final class SubnetRewriter {

    private SubnetRewriter() { }

    // ============================================================
    //  Public entry points
    // ============================================================

    /**
     * Renames every place and transition of {@code body}, prefixing each name
     * with {@code prefix + "/"}.
     *
     * <p>Side effects: fills the two supplied maps so the caller can resolve
     * original-place / original-transition references against the rewritten
     * equivalents:
     * <ul>
     *   <li>{@code placeRemap} — original place identity → renamed place</li>
     *   <li>{@code transitionRemap} — original transition identity → renamed transition</li>
     * </ul>
     *
     * <p>Both maps are cleared on entry, then populated in iteration order.
     *
     * @param body            the subnet body to rewrite (non-null)
     * @param prefix          the rename prefix (non-null)
     * @param placeRemap      caller-allocated map filled with old → new place bindings
     * @param transitionRemap caller-allocated map filled with old → new transition bindings
     * @return a fresh {@link PetriNet} whose name is {@code prefix + "/" +
     *         body.name()} and whose places/transitions are renamed copies
     */
    public static PetriNet renameNet(
        PetriNet body,
        String prefix,
        Map<Place<?>, Place<?>> placeRemap,
        Map<Transition, Transition> transitionRemap
    ) {
        placeRemap.clear();
        transitionRemap.clear();

        // Pass 1: rename every place. We must do this before transitions so
        // arc rewriting can resolve every place reference unambiguously.
        for (var orig : body.places()) {
            placeRemap.put(orig, renamePlace(orig, prefix));
        }

        // Pass 2: rebuild every transition with arcs rewritten via placeRemap.
        var renamedTransitions = new LinkedHashSet<Transition>(body.transitions().size());
        for (var t : body.transitions()) {
            var renamed = rewriteTransition(t, prefix, placeRemap);
            transitionRemap.put(t, renamed);
            renamedTransitions.add(renamed);
        }

        // Build the renamed PetriNet. Add places explicitly: some may not be
        // referenced by any transition arc, but were declared on the body —
        // we preserve that membership.
        var builder = PetriNet.builder(prefix + "/" + body.name());
        for (var renamedPlace : placeRemap.values()) {
            builder.place(renamedPlace);
        }
        for (var renamed : renamedTransitions) {
            builder.transition(renamed);
        }
        return builder.build();
    }

    /**
     * Returns a renamed copy of {@code orig}: same {@code tokenType}, with
     * {@code prefix + "/" + orig.name()} as the new name.
     */
    public static <T> Place<T> renamePlace(Place<T> orig, String prefix) {
        return new Place<>(prefix + "/" + orig.name(), orig.tokenType());
    }

    /**
     * Rebuilds {@code t} with name {@code prefix + "/" + t.name()} and every
     * arc rewritten through {@code placeRemap}. Timing, priority, and action
     * are carried through by reference (action sharing per <b>MOD-030</b>).
     *
     * <p>If a place referenced by an arc is not present in {@code placeRemap},
     * the arc retains the original place — partial remaps are valid (used by
     * the future {@code compose(...)} caller).
     */
    public static Transition rewriteTransition(
        Transition t,
        String prefix,
        Map<Place<?>, Place<?>> placeRemap
    ) {
        return rebuildWithName(t, prefix + "/" + t.name(), placeRemap);
    }

    /**
     * Rebuilds {@code t} with the <b>same</b> name, substituting every arc
     * place reference through {@code remap}. Timing, priority, and action are
     * carried through by reference (action sharing per <b>MOD-030</b>).
     *
     * <p>This is the rewrite primitive used by
     * {@code PetriNet.Builder.compose(...)} when merging an instance's renamed
     * body into an enclosing net: the transition's prefixed name is already
     * unique within the host (per [MOD-010]), so no further renaming is
     * needed — only port-place references are substituted with the caller's
     * places.
     *
     * <p>If a place referenced by an arc is not present in {@code remap},
     * the arc retains the original place — partial remaps are valid.
     *
     * @param t     the transition to rewrite
     * @param remap original place identity → substituted place
     * @return a fresh {@link Transition} with arc places substituted, same name
     */
    public static Transition substitutePlaces(Transition t, Map<Place<?>, Place<?>> remap) {
        return rebuildWithName(t, t.name(), remap);
    }

    /**
     * Shared implementation: rebuilds {@code t} with the supplied {@code name}
     * and arc places rewritten through {@code remap}. Used by both
     * {@link #rewriteTransition} (which prefixes the name) and
     * {@link #substitutePlaces} (which keeps the name unchanged).
     */
    private static Transition rebuildWithName(
        Transition t,
        String name,
        Map<Place<?>, Place<?>> remap
    ) {
        var builder = Transition.builder(name)
            .timing(t.timing())
            .priority(t.priority())
            .action(t.action());

        // Build the declared→actual place correspondence (MOD-031) BEFORE the
        // arcs, from the same `remap` the arcs are rewritten through, so an
        // action hardcoding a declared place constant resolves to the composed
        // place at run time. Chains through any pre-existing alias so nested
        // instantiation ([MOD-013]) resolves declared → final composed place.
        var alias = buildPlaceAlias(t, remap);
        if (!alias.isEmpty()) {
            builder.placeAlias(alias);
        }

        if (!t.inputSpecs().isEmpty()) {
            var inputs = new Arc.In[t.inputSpecs().size()];
            for (int i = 0; i < t.inputSpecs().size(); i++) {
                inputs[i] = rewriteIn(t.inputSpecs().get(i), remap);
            }
            builder.inputs(inputs);
        }

        if (t.outputSpec() != null) {
            builder.outputs(rewriteOut(t.outputSpec(), remap));
        }

        for (var inh : t.inhibitors()) builder.inhibitorArc(rewriteInhibitor(inh, remap));
        for (var rd  : t.reads())      builder.readArc(rewriteRead(rd, remap));
        for (var rs  : t.resets())     builder.resetArc(rewriteReset(rs, remap));

        return builder.build();
    }

    // ============================================================
    //  Declared→actual place correspondence (MOD-031)
    // ============================================================

    /**
     * Builds the per-transition <b>declared&rarr;actual</b> place correspondence
     * (per <b>MOD-031</b>) for a transition being rewritten through
     * {@code remap}. Mirrors the Rust {@code build_local_name_map} algorithm so
     * all three implementations agree.
     *
     * <p><b>Chained path</b> — when {@code t} already carries a non-empty alias
     * (from an earlier rewrite pass: nested instantiation [MOD-013], or
     * instantiate-then-compose), each {@code declared → prev} entry is carried
     * forward as {@code declared → remap.getOrDefault(prev, prev)}; identity
     * results are dropped. The arcs are deliberately <b>not</b> walked in this
     * case — their places are intermediate-pass names, not author-original, so
     * recording them would leak intermediate keys the user never declared (see
     * the Rust regression {@code build_local_name_map_chained_compose_*}).
     *
     * <p><b>First-pass path</b> — when {@code t} carries no alias, every arc
     * place {@code p} maps to {@code remap.getOrDefault(p, p)} keyed by the
     * author-original declared place; identity entries are skipped. The
     * ForwardInput {@code from} place is captured via the input walk and its
     * {@code to} via {@code outputSpec().allPlaces()}.
     *
     * @return a fresh map (possibly empty for an identity / no-op rewrite)
     */
    private static Map<Place<?>, Place<?>> buildPlaceAlias(
        Transition t,
        Map<Place<?>, Place<?>> remap
    ) {
        var prev = t.placeAlias();
        if (remap.isEmpty() && prev.isEmpty()) {
            return Map.of();
        }

        var alias = new HashMap<Place<?>, Place<?>>();

        if (!prev.isEmpty()) {
            for (var e : prev.entrySet()) {
                var declared = e.getKey();
                var finalActual = remap.getOrDefault(e.getValue(), e.getValue());
                if (!finalActual.equals(declared)) {
                    alias.put(declared, finalActual);
                }
            }
            return alias;
        }

        for (var in  : t.inputSpecs())  recordAlias(in.place(),  remap, alias);
        for (var rd  : t.reads())       recordAlias(rd.place(),  remap, alias);
        for (var inh : t.inhibitors())  recordAlias(inh.place(), remap, alias);
        for (var rs  : t.resets())      recordAlias(rs.place(),  remap, alias);
        if (t.outputSpec() != null) {
            for (var p : t.outputSpec().allPlaces()) recordAlias(p, remap, alias);
        }
        return alias;
    }

    /** Records {@code declared → remap(declared)} into {@code alias}, skipping identity and duplicates. */
    private static void recordAlias(
        Place<?> declared,
        Map<Place<?>, Place<?>> remap,
        Map<Place<?>, Place<?>> alias
    ) {
        if (alias.containsKey(declared)) return;
        var actual = remap.getOrDefault(declared, declared);
        if (!actual.equals(declared)) {
            alias.put(declared, actual);
        }
    }

    // ============================================================
    //  Arc rewrite helpers (sealed switches — exhaustive, no default)
    // ============================================================

    /**
     * Rewrites an {@link Arc.In} via the place remap. Exhaustive switch over
     * the sealed permits of {@link Arc.In}.
     */
    public static Arc.In rewriteIn(Arc.In in, Map<Place<?>, Place<?>> remap) {
        return switch (in) {
            case Arc.In.One o     -> new Arc.In.One(resolve(o.place(), remap));
            case Arc.In.Exactly e -> new Arc.In.Exactly(resolve(e.place(), remap), e.count());
            case Arc.In.All a     -> new Arc.In.All(resolve(a.place(), remap));
            case Arc.In.AtLeast a -> new Arc.In.AtLeast(resolve(a.place(), remap), a.minimum());
        };
    }

    /**
     * Rewrites an {@link Arc.Out} via the place remap. Exhaustive recursive
     * switch over the sealed permits of {@link Arc.Out}. {@code And}/{@code Xor}
     * traversal uses explicit {@code ArrayList} + indexed {@code for} (no
     * streams) per the perf notes on this class.
     */
    public static Arc.Out rewriteOut(Arc.Out out, Map<Place<?>, Place<?>> remap) {
        return switch (out) {
            case Arc.Out.Place p -> new Arc.Out.Place(resolve(p.place(), remap));

            case Arc.Out.ForwardInput f ->
                new Arc.Out.ForwardInput(resolve(f.from(), remap), resolve(f.to(), remap));

            case Arc.Out.And a -> {
                var children = a.children();
                var rewritten = new ArrayList<Arc.Out>(children.size());
                for (int i = 0; i < children.size(); i++) {
                    rewritten.add(rewriteOut(children.get(i), remap));
                }
                yield new Arc.Out.And(rewritten);
            }

            case Arc.Out.Xor x -> {
                var children = x.children();
                var rewritten = new ArrayList<Arc.Out>(children.size());
                for (int i = 0; i < children.size(); i++) {
                    rewritten.add(rewriteOut(children.get(i), remap));
                }
                yield new Arc.Out.Xor(rewritten);
            }

            case Arc.Out.Timeout t ->
                new Arc.Out.Timeout(t.after(), rewriteOut(t.child(), remap));
        };
    }

    /** Rewrites an {@link Arc.Inhibitor} via the place remap. */
    public static Arc.Inhibitor<?> rewriteInhibitor(Arc.Inhibitor<?> inh, Map<Place<?>, Place<?>> remap) {
        return rewriteInhibitorHelper(inh, remap);
    }

    private static <T> Arc.Inhibitor<T> rewriteInhibitorHelper(Arc.Inhibitor<T> inh, Map<Place<?>, Place<?>> remap) {
        return new Arc.Inhibitor<>(resolveTyped(inh.place(), remap));
    }

    /** Rewrites an {@link Arc.Read} via the place remap. */
    public static Arc.Read<?> rewriteRead(Arc.Read<?> rd, Map<Place<?>, Place<?>> remap) {
        return rewriteReadHelper(rd, remap);
    }

    private static <T> Arc.Read<T> rewriteReadHelper(Arc.Read<T> rd, Map<Place<?>, Place<?>> remap) {
        return new Arc.Read<>(resolveTyped(rd.place(), remap));
    }

    /** Rewrites an {@link Arc.Reset} via the place remap. */
    public static Arc.Reset<?> rewriteReset(Arc.Reset<?> rs, Map<Place<?>, Place<?>> remap) {
        return rewriteResetHelper(rs, remap);
    }

    private static <T> Arc.Reset<T> rewriteResetHelper(Arc.Reset<T> rs, Map<Place<?>, Place<?>> remap) {
        return new Arc.Reset<>(resolveTyped(rs.place(), remap));
    }

    // ============================================================
    //  Resolution helpers
    // ============================================================

    /**
     * Looks up {@code p} in {@code remap}; returns the original if absent
     * (partial-remap semantics for the future {@code compose} caller).
     */
    private static Place<?> resolve(Place<?> p, Map<Place<?>, Place<?>> remap) {
        var replaced = remap.get(p);
        return replaced != null ? replaced : p;
    }

    /**
     * Typed counterpart of {@link #resolve} — preserves the static {@code <T>}
     * for the typed arc records ({@code Inhibitor<T>}, {@code Read<T>},
     * {@code Reset<T>}). The unchecked cast is safe at runtime: the remap is
     * populated by {@link #renamePlace}, which preserves {@code tokenType};
     * future callers that put non-rename mappings in must preserve the same
     * invariant.
     */
    @SuppressWarnings("unchecked")
    private static <T> Place<T> resolveTyped(Place<T> p, Map<Place<?>, Place<?>> remap) {
        var replaced = remap.get(p);
        return replaced != null ? (Place<T>) replaced : p;
    }

    // ============================================================
    //  Channel composition: transition merge (MOD-021)
    // ============================================================

    /**
     * Merges a caller-side transition with an instance-side (renamed) channel
     * transition into a single {@link Transition} per <b>MOD-021</b>.
     *
     * <p>Merge semantics:
     * <ul>
     *   <li><b>Identity / name</b> — caller wins. The merged transition's name
     *       is {@code mergedName} (typically {@code caller.name()}), so the
     *       merged transition remains discoverable from caller-side code paths.</li>
     *   <li><b>Arcs</b> — union: caller-side arcs first, then instance-side
     *       arcs. Duplicates (by {@link Place} record equality on the
     *       underlying record) are deduped; arc-list order is preserved
     *       caller-first to give the executor a deterministic shape.</li>
     *   <li><b>Output spec</b> — if both sides have an output spec, they are
     *       combined into an {@code Arc.Out.And(caller, instance)} so both
     *       sides' outputs fire on a successful merged firing. If only one
     *       side has an output spec, that one wins. If neither side has an
     *       output spec, the merged transition has none.</li>
     *   <li><b>Timing</b> — see {@link #mergeTimings(Timing, Timing, String)}.
     *       Caller wins when one side is {@link Timing.Immediate}; equal
     *       non-{@code Immediate} timings collapse; conflicting non-{@code Immediate}
     *       timings throw {@link IllegalArgumentException}.</li>
     *   <li><b>Priority</b> — see {@link #pickPriority(int, int)}. Caller wins
     *       (policy, not a bug).</li>
     *   <li><b>Action</b> — see {@link #composeActions(TransitionAction, TransitionAction)}.
     *       Sequential composition: caller-side action runs first, then the
     *       instance-side action. The runtime sees one transition firing,
     *       per [CORE-021] / [EXEC-001].</li>
     * </ul>
     *
     * <h3>Output-spec union design note</h3>
     * <p>The output spec is the only arc-list-with-tree-structure the
     * transition carries (input/inhibitor/read/reset are flat lists).
     * Wrapping both sides under a single {@code Arc.Out.And} preserves the
     * "produce both sides' outputs" semantics while flowing through the
     * existing output-validation and tree-walking machinery in
     * {@link Transition} and the executor unchanged. {@code Out.And} permits
     * heterogeneous children (recursive trees), so wrapping a possibly-{@code And}
     * child under a new outer {@code And} is structurally legal.
     *
     * @param caller     caller-side transition (its name, priority become the merged identity)
     * @param instance   instance-side renamed channel transition
     * @param mergedName name to assign to the merged transition (caller-wins convention)
     * @return a fresh {@link Transition} representing the synchronous fusion
     * @throws IllegalArgumentException when timings conflict (per [MOD-021])
     */
    public static Transition mergeTransitions(
        Transition caller,
        Transition instance,
        String mergedName
    ) {
        if (caller == null) throw new IllegalArgumentException("caller must not be null");
        if (instance == null) throw new IllegalArgumentException("instance must not be null");
        if (mergedName == null || mergedName.isBlank()) {
            throw new IllegalArgumentException("mergedName must be non-blank");
        }

        // Resolve timing first so a conflict short-circuits before any building.
        Timing mergedTiming = mergeTimings(caller.timing(), instance.timing(), mergedName);
        int mergedPriority  = pickPriority(caller.priority(), instance.priority());
        TransitionAction mergedAction = composeActions(caller.action(), instance.action());

        var builder = Transition.builder(mergedName)
            .timing(mergedTiming)
            .priority(mergedPriority);
        if (mergedAction != null) {
            builder.action(mergedAction);
        }

        // Inputs: union (caller first, then instance), dedupe by record equality.
        var unionedInputs = unionArcs(caller.inputSpecs(), instance.inputSpecs());
        if (!unionedInputs.isEmpty()) {
            builder.inputs(unionedInputs.toArray(new Arc.In[0]));
        }

        // Outputs: combine. If both sides carry an output spec, produce an
        // outer And(caller, instance). If only one, that one wins.
        Arc.Out mergedOutput = mergeOutputs(caller.outputSpec(), instance.outputSpec());
        if (mergedOutput != null) {
            builder.outputs(mergedOutput);
        }

        // Inhibitors / reads / resets: arc-record union (caller first, then instance).
        for (var arc : unionArcs(caller.inhibitors(), instance.inhibitors())) {
            builder.inhibitorArc(arc);
        }
        for (var arc : unionArcs(caller.reads(), instance.reads())) {
            builder.readArc(arc);
        }
        for (var arc : unionArcs(caller.resets(), instance.resets())) {
            builder.resetArc(arc);
        }

        return builder.build();
    }

    /**
     * Merges two timings per <b>MOD-021</b>:
     * <ul>
     *   <li>If both are {@link Timing.Immediate}, the result is {@code Immediate}.</li>
     *   <li>If one is {@code Immediate}, the other wins.</li>
     *   <li>If both are non-{@code Immediate} and equal, that value collapses.</li>
     *   <li>Otherwise the conflict is rejected with an exception naming the
     *       channel and both timings — the user must resolve it explicitly.</li>
     * </ul>
     */
    public static Timing mergeTimings(Timing caller, Timing instance, String channelName) {
        if (caller instanceof Timing.Immediate && instance instanceof Timing.Immediate) {
            return new Timing.Immediate();
        }
        if (caller instanceof Timing.Immediate) {
            return instance;
        }
        if (instance instanceof Timing.Immediate) {
            return caller;
        }
        if (caller.equals(instance)) {
            return caller;
        }
        throw new IllegalArgumentException(
            "Channel composition '" + channelName + "': conflicting non-Immediate timings — "
                + "caller-side " + caller + " vs instance-side " + instance
                + ". Resolve explicitly by aligning the timings on either side (MOD-021).");
    }

    /**
     * Caller-side priority wins per <b>MOD-021</b>. Documented as policy: the
     * instance-side priority is ignored, not blended.
     */
    public static int pickPriority(int callerPriority, int instancePriority) {
        return callerPriority;
    }

    /**
     * Composes two transition actions sequentially: the caller-side action
     * runs first, then on its completion the instance-side action runs against
     * the same {@link TransitionContext}. The combined action surfaces a
     * single {@link CompletionStage} so the executor sees one transition
     * firing per [CORE-021] / [EXEC-001].
     *
     * <p>Null-handling: if either side is {@code null}, the other side is
     * returned by reference (no extra wrapping). If both are {@code null},
     * {@code null} is returned (the caller — {@link #mergeTransitions} —
     * leaves the builder's default action in place).
     *
     * <p>Note: the production {@link Transition.Builder} defaults action to
     * {@link TransitionAction#passthrough()} (never {@code null}), so the
     * null branches are defensive — they exist so this helper is robust if
     * upstream surfaces a literal {@code null} action.
     */
    public static TransitionAction composeActions(TransitionAction caller, TransitionAction instance) {
        if (caller == null && instance == null) return null;
        if (caller == null) return instance;
        if (instance == null) return caller;
        return ctx -> {
            CompletionStage<Void> first = caller.execute(ctx);
            return first.thenCompose(_ -> instance.execute(ctx));
        };
    }

    /**
     * Combines two output specs per the merge contract: if both are present,
     * wrap them under a single {@link Arc.Out.And}; otherwise return the
     * non-null side (or {@code null} if both are missing).
     */
    private static Arc.Out mergeOutputs(Arc.Out caller, Arc.Out instance) {
        if (caller == null && instance == null) return null;
        if (caller == null) return instance;
        if (instance == null) return caller;
        return new Arc.Out.And(List.of(caller, instance));
    }

    /**
     * Returns the union of two arc lists, caller-first then instance, with
     * duplicates removed by record equality. Order is preserved within each
     * source list. Used for input, inhibitor, read, and reset arcs.
     *
     * <p>Implementation: {@link LinkedHashSet} preserves first-seen order and
     * dedupes via {@code equals}. Records (e.g., {@code Arc.In.One},
     * {@code Arc.Inhibitor}) get value equality automatically; identical arcs
     * referencing the same {@link Place} compare equal and collapse.
     */
    private static <A> List<A> unionArcs(List<? extends A> caller, List<? extends A> instance) {
        if (caller.isEmpty() && instance.isEmpty()) return List.of();
        var union = new LinkedHashSet<A>(caller.size() + instance.size());
        union.addAll(caller);
        union.addAll(instance);
        return new ArrayList<>(union);
    }

    // ============================================================
    //  Fusion: bulk place substitution across a transition set (MOD-061)
    // ============================================================

    /**
     * Applies a fusion remap to every transition in {@code transitions},
     * substituting non-canonical → canonical place references in each
     * transition's arcs. Returns a fresh insertion-ordered
     * {@link LinkedHashSet}; the input collection is not mutated.
     *
     * <p>This is the loop wrapper around {@link #substitutePlaces(Transition, Map)};
     * it exists so callers — notably {@code PetriNet.Builder.build()} during
     * fusion resolution per <b>MOD-061</b> — do not duplicate the per-transition
     * dispatch. Transitions whose arcs do not reference any key of
     * {@code fusionMap} pass through unchanged in shape but are still
     * rebuilt by {@link #substitutePlaces} (a fresh {@link Transition}
     * record); callers that care about identity preservation for un-affected
     * transitions should instead skip the rewrite entirely when
     * {@code fusionMap.isEmpty()}.
     *
     * @param transitions the transitions to rewrite (non-null, may be empty)
     * @param fusionMap   non-canonical → canonical place remap (non-null)
     * @return a fresh, insertion-ordered set of rewritten transitions
     */
    public static java.util.Set<Transition> applyFusion(
        java.util.Collection<Transition> transitions,
        Map<Place<?>, Place<?>> fusionMap
    ) {
        var rewritten = new LinkedHashSet<Transition>(transitions.size());
        for (var t : transitions) {
            rewritten.add(substitutePlaces(t, fusionMap));
        }
        return rewritten;
    }

    // ============================================================
    //  Convenience: pre-allocated empty remap factories
    // ============================================================

    /** Returns a fresh empty place remap. */
    public static Map<Place<?>, Place<?>> newPlaceRemap() {
        return new HashMap<>();
    }

    /** Returns a fresh empty transition remap. */
    public static Map<Transition, Transition> newTransitionRemap() {
        return new HashMap<>();
    }
}
