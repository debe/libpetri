package org.libpetri.core;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.Function;

import org.libpetri.core.internal.SubnetRewriter;

/**
 * Immutable definition of a Time Petri Net structure.
 * <p>
 * A PetriNet is a reusable definition that can be executed multiple times
 * with different initial markings. It consists of:
 * <ul>
 *   <li>{@link Place Places} - typed containers for tokens</li>
 *   <li>{@link Transition Transitions} - actions that consume and produce tokens</li>
 * </ul>
 *
 * <h3>Example</h3>
 * <pre>{@code
 * var net = PetriNet.builder("RequestProcessor")
 *     .transitions(
 *         receiveRequest,
 *         validateRequest,
 *         processRequest,
 *         sendResponse
 *     )
 *     .build();
 *
 * // Places are auto-collected from transition arcs
 * // Execute with NetExecutor (see runtime package)
 * }</pre>
 *
 * <h3>Thread Safety</h3>
 * PetriNet is immutable and thread-safe. Multiple executors can run the
 * same net definition concurrently with different markings.
 *
 * @see org.libpetri.runtime.NetExecutor NetExecutor for execution
 */
public final class PetriNet {
    private final String name;
    private final Set<Place<?>> places;
    private final Set<Transition> transitions;

    private PetriNet(String name, Set<Place<?>> places, Set<Transition> transitions) {
        this.name = name;
        // Preserve the builder's LinkedHashSet insertion order — Set.copyOf
        // would discard it (its iteration order is unspecified per the JDK
        // contract). The DOT exporter's cross-language byte-parity contract
        // depends on stable iteration order, see PetriNet.Builder.
        this.places = java.util.Collections.unmodifiableSet(new java.util.LinkedHashSet<>(places));
        this.transitions = java.util.Collections.unmodifiableSet(new java.util.LinkedHashSet<>(transitions));
    }

    public String name() { return name; }
    public Set<Place<?>> places() { return places; }
    public Set<Transition> transitions() { return transitions; }

    /**
     * Creates a new PetriNet with actions bound to transitions.
     *
     * <p>This method is designed for separating static net structure from
     * runtime behavior. Define the net structure once (places, arcs, intervals),
     * then bind CDI-injected actions at runtime.
     *
     * <h3>Example</h3>
     * <pre>{@code
     * // Static structure defined at compile time
     * public static final PetriNet STRUCTURE = PetriNet.builder("Workflow")
     *     .transitions(
     *         Transition.builder("Validate").input(REQUEST).output(RESULT).build(),
     *         Transition.builder("Process").input(RESULT).output(RESPONSE).build()
     *     )
     *     .build();
     *
     * // Runtime binding with CDI services
     * @Produces
     * public PetriNet workflow(ValidationService vs, ProcessingService ps) {
     *     return STRUCTURE.bindActions(Map.of(
     *         "Validate", (in, out) -> vs.validate(in.value(REQUEST))
     *             .thenAccept(r -> out.add(RESULT, r)),
     *         "Process", (in, out) -> ps.process(in.value(RESULT))
     *             .thenAccept(r -> out.add(RESPONSE, r))
     *     ));
     * }
     * }</pre>
     *
     * @param actionBindings map from transition name to action
     * @return new PetriNet with bound actions
     * @throws IllegalArgumentException if a transition name is not found
     */
    public PetriNet bindActions(Map<String, TransitionAction> actionBindings) {
        return bindActions(name -> actionBindings.getOrDefault(name, TransitionAction.passthrough()));
    }

    /**
     * Creates a new PetriNet with actions bound via a resolver function.
     *
     * <p>The resolver is called for each transition with the transition name,
     * and should return the action to use. This allows for flexible binding
     * strategies (e.g., CDI lookup, method references).
     *
     * @param actionResolver function that resolves transition name to action
     * @return new PetriNet with bound actions
     */
    public PetriNet bindActions(Function<String, TransitionAction> actionResolver) {
        var boundTransitions = new LinkedHashSet<Transition>();
        for (var t : transitions) {
            var action = actionResolver.apply(t.name());
            if (action != null && action != t.action()) {
                boundTransitions.add(rebuildWithAction(t, action));
            } else {
                boundTransitions.add(t);
            }
        }
        return new PetriNet(name, places, boundTransitions);
    }

    /**
     * Creates a new transition with a different action while preserving all arc specifications.
     *
     * @param t the original transition
     * @param action the new action to bind
     * @return a new transition with the given action and all original specifications
     */
    private static Transition rebuildWithAction(Transition t, TransitionAction action) {
        var builder = Transition.builder(t.name())
            .timing(t.timing())
            .priority(t.priority())
            .action(action);

        if (!t.inputSpecs().isEmpty()) {
            builder.inputs(t.inputSpecs().toArray(new Arc.In[0]));
        }
        if (t.outputSpec() != null) {
            builder.outputs(t.outputSpec());
        }

        t.inhibitors().forEach(builder::inhibitorArc);
        t.reads().forEach(builder::readArc);
        t.resets().forEach(builder::resetArc);

        return builder.build();
    }

    public static Builder builder(String name) {
        return new Builder(name);
    }

    public static class Builder {
        private final String name;
        // LinkedHashSet (rather than HashSet) so the resulting net's
        // places/transitions iterate in a deterministic, insertion-ordered
        // fashion. Cross-language byte-parity in the DOT exporter (per
        // [EXP-014], see scripts/cross-lang-dot-parity.sh) requires this:
        // TS uses Set / Map iteration which is insertion-ordered, Rust uses
        // an explicit Vec. With a plain HashSet the rendered cluster
        // contents would shuffle nondeterministically across JVM runs.
        private final java.util.LinkedHashSet<Place<?>> places = new java.util.LinkedHashSet<>();
        private final java.util.LinkedHashSet<Transition> transitions = new java.util.LinkedHashSet<>();
        private final List<FusionSet> fusionSets = new ArrayList<>();

        private Builder(String name) {
            this.name = name;
        }

        public <T> Builder place(Place<T> place) {
            places.add(place);
            return this;
        }

        public Builder places(Place<?>... places) {
            this.places.addAll(List.of(places));
            return this;
        }

        public Builder transition(Transition transition) {
            transitions.add(transition);
            // Auto-add places from transition arcs
            for (var in : transition.inputSpecs()) places.add(in.place());
            if (transition.outputSpec() != null) places.addAll(transition.outputSpec().allPlaces());
            transition.inhibitors().forEach(arc -> places.add(arc.place()));
            transition.reads().forEach(arc -> places.add(arc.place()));
            return this;
        }

        public Builder transitions(Transition... transitions) {
            for (var t : transitions) {
                transition(t);
            }
            return this;
        }

        /**
         * Composes a subnet {@link Instance} into this builder using
         * <b>identity-default port inference</b> per <b>MOD-024</b>.
         *
         * <p>Each declared interface port auto-binds to its own
         * {@code port.place()} — the {@link Place} the SubnetDef builder
         * declared via {@code .inputPort(name, hostPlace)} (or {@code
         * outputPort} / {@code inoutPort}). That place is the SubnetDef's
         * statement of "which host place this port shares with." If the host
         * builder already has an equal place declared, the two merge by
         * {@link Place} record equality; if not, the place arrives implicitly
         * via the rewritten transitions' arcs (same flow as explicit
         * {@code bindPort}).
         *
         * <p>If the subnet declares no interface ports at all, every body
         * place is checked against this builder's place set; matches are
         * auto-bound, the rest stay private (prefix-renamed). This supports
         * SubnetDefs that omit explicit {@code inputPort/outputPort/inoutPort}
         * declarations and rely entirely on body-level place identity.
         *
         * <h3>Channels (MOD-021)</h3>
         * <p>This overload does <b>not</b> auto-bind channels — transition
         * identity is more delicate than place identity. If the subnet's
         * interface declares any channel, an {@link IllegalStateException} is
         * raised; use {@link #compose(Instance, Consumer)} with explicit
         * {@link ComposeBindings#bindChannel(String, Transition)} calls.
         *
         * <h3>Use the {@code Consumer} overload when</h3>
         * <ul>
         *   <li>you need to rewire a port to a host place <i>other</i> than
         *       the one carried by the subnet's interface (a rename),</li>
         *   <li>the subnet declares any channel,</li>
         *   <li>the subnet defines reusable / parametric ports whose host
         *       targets differ across instances.</li>
         * </ul>
         *
         * @param instance the subnet instance to compose
         * @return this builder, for chaining
         * @throws IllegalStateException when the subnet declares channels
         */
        public Builder compose(Instance<?> instance) {
            Objects.requireNonNull(instance, "instance");
            var iface = instance.def().iface();

            if (!iface.channels().isEmpty()) {
                throw new IllegalStateException(
                    "compose(Instance): subnet '" + instance.def().name()
                        + "' (instance prefix '" + instance.prefix()
                        + "') declares channels " + ifaceChannelNames(iface)
                        + "; auto-compose does not bind channels."
                        + " Use compose(instance, Consumer) with explicit bindChannel(...).");
            }

            if (!iface.ports().isEmpty()) {
                // Explicit interface: each declared port auto-binds to its own
                // declared place. The SubnetDef's .inputPort(name, hostPlace)
                // statement IS the host wiring — trust it.
                var portMappings = new LinkedHashMap<String, Place<?>>();
                for (var port : iface.ports()) {
                    portMappings.put(port.name(), port.place());
                }
                return composeInternal(instance, portMappings, Map.of());
            }

            // No declared interface — infer the merge set from body places that
            // are also on the host builder. Bypass the iface.port name lookup
            // (compose_internal would error on the absent port) and build the
            // mergeMap directly from (renamed body place → host place).
            var renamedPlaces = instance.renamedBody().places();
            var mergeMap = new HashMap<Place<?>, Place<?>>(renamedPlaces.size());
            var prefix = instance.prefix() + "/";
            for (var renamed : renamedPlaces) {
                // Defensive: rename pass should always prefix every body place,
                // but SubnetDef.fromNet retrofits may carry un-prefixed places.
                if (!renamed.name().startsWith(prefix)) continue;
                var originalName = renamed.name().substring(prefix.length());
                var probe = Place.of(originalName, renamed.tokenType());
                if (places.contains(probe)) {
                    mergeMap.put(renamed, probe);
                }
            }
            return applyComposition(instance, mergeMap, Map.of());
        }

        /**
         * Composes a subnet {@link Instance} into this builder per
         * <b>MOD-020</b> (composition operation), <b>MOD-022</b> (type
         * compatibility), and <b>MOD-023</b> (composition produces a flat net).
         *
         * <p>This overload accepts a runtime-checked {@code Map<String, Place<?>>}
         * keyed by the subnet's <b>original</b> (pre-prefix) port names.
         * Each binding merges the named interface port with the supplied
         * caller place by structural arc rewriting: every transition of the
         * instance's renamed body is rebuilt with port-place references
         * substituted for the caller place, then added to this builder via
         * {@link #transition}. Internal (non-merged) renamed places of the
         * instance flow through with their prefixed names.
         *
         * <h3>Type compatibility (MOD-022)</h3>
         * <p>For each binding, the interface port's token type must equal the
         * caller place's token type — a mismatch raises
         * {@link IllegalArgumentException}.
         *
         * <h3>Channel composition (MOD-021)</h3>
         * <p>Channels declared on the subnet's {@link Interface} but not bound
         * by the caller flow through as ordinary renamed transitions.
         * <b>This overload does not accept channel bindings</b>; use the
         * {@link #compose(Instance, Consumer)} overload to record channel
         * bindings.
         *
         * @param instance     the subnet instance to compose
         * @param portMappings map from subnet port name (original) to caller place
         * @return this builder, for chaining
         * @throws IllegalArgumentException when a port name is unknown on the
         *         instance's interface, or when the port and caller place
         *         token types disagree (per [MOD-022])
         */
        public Builder compose(Instance<?> instance, Map<String, Place<?>> portMappings) {
            return composeInternal(instance, portMappings, Map.of());
        }

        /**
         * Typed overload of {@link #compose(Instance, Map)} per <b>MOD-020</b>
         * and <b>MOD-021</b>.
         *
         * <p>The {@link Consumer} receives a fresh {@link ComposeBindings}
         * instance; the caller registers port bindings via
         * {@link ComposeBindings#bindPort(String, Place)}. The typed
         * {@code <T>} parameter on {@code bindPort} ensures the caller place
         * matches the interface port's token type at compile time — runtime
         * verification per [MOD-022] still applies as a defence-in-depth
         * against erased generics.
         *
         * <h3>Channel bindings (MOD-021)</h3>
         * <p>Callers register channel bindings via
         * {@link ComposeBindings#bindChannel(String, Transition)}. For each
         * binding {@code (channelName -> callerTransition)}, the instance's
         * renamed channel transition and the supplied caller transition are
         * <b>merged</b> into a single transition in the resulting flat net.
         * The merge unions both sides' arcs (deduped by {@link Place} record
         * equality), composes their actions sequentially (caller-first), and
         * applies the timing/priority resolution per [MOD-021].
         *
         * <p>If the caller-side transition has not been added to this builder
         * yet, it is added implicitly during the merge step — callers that
         * use a channel binding need not also call {@link #transition} for
         * the same caller-side transition.
         *
         * @param instance the subnet instance to compose
         * @param bind     binding consumer that registers port and channel bindings
         * @return this builder, for chaining
         * @throws IllegalArgumentException per {@link #compose(Instance, Map)};
         *         additionally, when a channel binding refers to an unknown
         *         channel name on the instance interface, or when caller-
         *         and instance-side transition timings conflict (per [MOD-021])
         */
        public Builder compose(Instance<?> instance, Consumer<ComposeBindings> bind) {
            Objects.requireNonNull(bind, "bind");
            var bindings = new ComposeBindings();
            bind.accept(bindings);
            return composeInternal(instance, bindings.portBindings(), bindings.channelBindings());
        }

        /**
         * Shared implementation: validates port and channel bindings, builds
         * the place-substitution map, walks every renamed-body transition
         * through {@link SubnetRewriter#substitutePlaces}, and applies channel
         * merges per <b>MOD-021</b>.
         *
         * <p>Channel-merge flow (MOD-021):
         * <ol>
         *   <li>Collect rewritten instance transitions into a working set
         *       (deferred — not yet added to the builder's transition set).</li>
         *   <li>For each channel binding, resolve the renamed instance-side
         *       transition through {@link Instance#channel(String)}, then
         *       look up its rewritten counterpart in the working set.</li>
         *   <li>Replace the rewritten instance-side transition with a
         *       {@link SubnetRewriter#mergeTransitions merged} transition
         *       that fuses caller-side + instance-side; and replace (or add)
         *       the caller-side transition in this builder's transition set
         *       with the same merged result.</li>
         *   <li>Add the working set's surviving entries to this builder.</li>
         * </ol>
         *
         * <p>The deferral is essential: writing the rewritten instance
         * transitions to the builder eagerly would force a second
         * "remove-then-replace" pass to apply the channel merges, complicating
         * the place-collection invariants. Collecting first and merging
         * second keeps the builder's transition set finalized exactly once.
         */
        private Builder composeInternal(
            Instance<?> instance,
            Map<String, Place<?>> portMappings,
            Map<String, Transition> channelBindings
        ) {
            Objects.requireNonNull(instance, "instance");
            Objects.requireNonNull(portMappings, "portMappings");
            Objects.requireNonNull(channelBindings, "channelBindings");

            var iface = instance.def().iface();
            var mergeMap = new HashMap<Place<?>, Place<?>>(portMappings.size() * 2);

            for (var entry : portMappings.entrySet()) {
                var portName = entry.getKey();
                var callerPlace = entry.getValue();
                Objects.requireNonNull(callerPlace,
                    "compose: caller place for port '" + portName + "' must not be null");

                var port = iface.port(portName).orElseThrow(() ->
                    new IllegalArgumentException(
                        "compose: no port named '" + portName + "' on subnet '"
                            + instance.def().name() + "' (instance prefix '"
                            + instance.prefix() + "'). Known ports: "
                            + ifacePortNames(iface)));

                // Resolve the renamed interface place via the typed accessor;
                // this gives us the rewritten Place<?> in the instance body.
                @SuppressWarnings({"unchecked", "rawtypes"})
                Place<?> ifacePlace = instance.port(portName, (Class) port.place().tokenType());

                // MOD-022: token-type compatibility check (defence-in-depth
                // against erased generics on the runtime-map overload).
                if (!ifacePlace.tokenType().equals(callerPlace.tokenType())) {
                    throw new IllegalArgumentException(
                        "compose: port '" + portName + "' on subnet '"
                            + instance.def().name() + "' has token type "
                            + ifacePlace.tokenType().getName()
                            + " but caller place '" + callerPlace.name()
                            + "' has token type " + callerPlace.tokenType().getName()
                            + " (MOD-022)");
                }

                mergeMap.put(ifacePlace, callerPlace);
            }

            return applyComposition(instance, mergeMap, channelBindings);
        }

        /**
         * Shared post-mergeMap pipeline: rewrites renamed-body transitions
         * through the supplied {@code mergeMap}, applies channel merges per
         * <b>MOD-021</b>, and adds the surviving transitions to the builder.
         *
         * <p>Used by both the explicit-binding paths
         * ({@link #composeInternal} → {@link #compose(Instance, Map)} /
         * {@link #compose(Instance, Consumer)}) and the auto-compose path
         * ({@link #compose(Instance)}). The two paths differ only in how
         * {@code mergeMap} (renamed-instance Place → host Place) is built.
         */
        private Builder applyComposition(
            Instance<?> instance,
            Map<Place<?>, Place<?>> mergeMap,
            Map<String, Transition> channelBindings
        ) {
            var iface = instance.def().iface();

            // Step 1: Walk every transition of the renamed body and substitute
            // port places. Stage the rewritten transitions in a working map
            // keyed by transition name so we can resolve channel-side handles
            // in step 2 by name. Keying by name (rather than identity) is the
            // robust choice because a prior {@link Instance#bindActions} call
            // may have rebuilt the renamed-body transitions, breaking
            // identity equality between the body and the channel-handle map
            // — but the prefixed names remain stable.
            var rewrittenByName = new LinkedHashMap<String, Transition>(
                instance.renamedBody().transitions().size());
            for (var t : instance.renamedBody().transitions()) {
                rewrittenByName.put(t.name(), SubnetRewriter.substitutePlaces(t, mergeMap));
            }

            // Step 2: Apply channel merges. For each binding, locate the
            // rewritten instance-side transition by name, fuse it with the
            // caller-side transition, and replace the working-set entry.
            // Also replace the caller-side transition in this builder's
            // transition set with the merged transition (or add it if the
            // caller did not pre-add the caller-side transition).
            for (var entry : channelBindings.entrySet()) {
                var channelName = entry.getKey();
                var callerTrans = entry.getValue();

                // Resolve the renamed instance-side channel transition (its
                // name is what we use to look it up in the working set).
                Transition instanceRenamedChannel;
                try {
                    instanceRenamedChannel = instance.channel(channelName);
                } catch (IllegalArgumentException ex) {
                    throw new IllegalArgumentException(
                        "compose: no channel named '" + channelName + "' on subnet '"
                            + instance.def().name() + "' (instance prefix '"
                            + instance.prefix() + "'). Known channels: "
                            + ifaceChannelNames(iface), ex);
                }

                // Look up the rewritten (port-substituted) version of the
                // renamed channel transition by name.
                //
                // Defensive: the channel handle returned by
                // {@link Instance#channel(String)} MUST reference a transition
                // whose name is present in {@code instance.renamedBody()
                // .transitions()}. If the lookup fails, the instance's
                // channel-handle map is stale relative to its renamed body —
                // typically caused by a {@link Instance#bindActions} (or a
                // future derivation method) that violated the documented
                // contract by recomputing channel-transition identity. The
                // resulting net would silently lose the channel binding, so
                // we fail loudly here instead.
                var rewrittenInstanceChannel = rewrittenByName.get(instanceRenamedChannel.name());
                if (rewrittenInstanceChannel == null) {
                    throw new IllegalStateException(
                        "compose: channel '" + channelName + "' on instance '"
                            + instance.prefix() + "' (subnet '" + instance.def().name()
                            + "') resolved to transition '" + instanceRenamedChannel.name()
                            + "', but no transition with that name is present in the"
                            + " instance's renamed body. The channel-handle map is stale"
                            + " — Instance.bindActions (and any other Instance derivation)"
                            + " MUST preserve the identity (name and arc structure) of"
                            + " every transition referenced by an Interface channel.");
                }

                // Build the merged transition (caller-wins identity per MOD-021).
                var merged = SubnetRewriter.mergeTransitions(
                    callerTrans, rewrittenInstanceChannel, callerTrans.name());

                // Step 2a: Remove the rewritten instance-side transition from
                // the working set (it merges away — only the merged result
                // remains under the caller's transition slot in the builder).
                rewrittenByName.remove(instanceRenamedChannel.name());

                // Step 2b: Replace the caller-side transition (if present) in
                // this builder's transition set with the merged result. If
                // the caller did not pre-add it, simply add the merged
                // transition — the user's intent to use callerTrans is
                // captured via the binding itself, so this is non-surprising.
                transitions.remove(callerTrans);
                transition(merged);
            }

            // Step 3: Add the surviving (un-merged) rewritten transitions to
            // the builder. transition() auto-collects places — internal
            // (non-merged) renamed places are added; caller places already in
            // the builder's place set get deduped via Place record equality.
            for (var rewritten : rewrittenByName.values()) {
                transition(rewritten);
            }

            return this;
        }

        private static String ifacePortNames(Interface iface) {
            var names = new ArrayList<String>(iface.ports().size());
            for (var p : iface.ports()) names.add(p.name());
            return names.toString();
        }

        private static String ifaceChannelNames(Interface iface) {
            var names = new ArrayList<String>(iface.channels().size());
            for (var c : iface.channels()) names.add(c.name());
            return names.toString();
        }

        /**
         * Registers one or more {@link FusionSet} declarations on this builder,
         * per <b>MOD-060</b> (fusion set declaration) and <b>MOD-061</b>
         * (fusion resolution at build).
         *
         * <p>Fusion is <b>orthogonal to subnet composition</b>: fuse sets are
         * accumulated here and applied during {@link #build()} <i>after</i>
         * all {@code compose(...)} calls have flattened subnet instances
         * into the builder's transition set. Registration order is irrelevant
         * to semantics — {@code fuse(set)} BEFORE {@code compose(...)} and
         * {@code fuse(set)} AFTER {@code compose(...)} both apply at the same
         * point in the build pipeline.
         *
         * <h3>Validation</h3>
         * Per-set type homogeneity is already enforced at {@link FusionSet}
         * construction time. Cross-set overlap (a place appearing in two
         * fusion sets) is detected at {@link #build()} and reported as an
         * {@link IllegalStateException} naming the offending place and both
         * sets.
         *
         * @param sets the fusion sets to register (non-null)
         * @return this builder, for chaining
         */
        public Builder fuse(FusionSet... sets) {
            Objects.requireNonNull(sets, "sets");
            for (var s : sets) {
                Objects.requireNonNull(s, "fuse: fusion set must not be null");
                fusionSets.add(s);
            }
            return this;
        }

        /**
         * Sugar overload of {@link #fuse(FusionSet...)} that constructs the
         * fusion set inline via a {@link Consumer} on a fresh
         * {@link FusionSet.Builder}, named after this enclosing net.
         *
         * <p>Equivalent to:
         * <pre>{@code
         *   var b = FusionSet.builder("<netName>-fusion");
         *   declarer.accept(b);
         *   fuse(b.build());
         * }</pre>
         *
         * @param declarer consumer that registers fusion-set members
         * @return this builder, for chaining
         */
        public Builder fuse(Consumer<FusionSet.Builder> declarer) {
            Objects.requireNonNull(declarer, "declarer");
            var fb = FusionSet.builder(name + "-fusion");
            declarer.accept(fb);
            return fuse(fb.build());
        }

        /**
         * Builds the immutable {@link PetriNet}, applying fusion resolution
         * (per <b>MOD-061</b>) AFTER all transition/composition accumulation:
         *
         * <ol>
         *   <li>Detect overlapping fusion sets — a single place declared in
         *       two sets is rejected with an {@link IllegalStateException}.</li>
         *   <li>Build the {@code non-canonical → canonical} substitution map
         *       across all sets.</li>
         *   <li>Walk every transition through {@link SubnetRewriter#applyFusion}
         *       to rewrite arc place references.</li>
         *   <li>Re-derive the place set from the rewritten transitions plus
         *       any caller-declared standalone places, dropping non-canonical
         *       members. Caller-declared standalone places that happen to be
         *       non-canonical members are also dropped.</li>
         * </ol>
         *
         * <p>If no fusion sets were registered, the build is the trivial
         * {@code new PetriNet(name, places, transitions)} — the fusion
         * machinery has no per-build cost when unused.
         *
         * @return a fresh, immutable {@link PetriNet}
         * @throws IllegalStateException when two fusion sets share a place
         */
        public PetriNet build() {
            if (fusionSets.isEmpty()) {
                return new PetriNet(name, places, transitions);
            }
            return buildWithFusion();
        }

        /**
         * Fusion-resolution pass per <b>MOD-061</b>. Split out from {@link #build()}
         * so the no-fusion fast path stays trivial.
         */
        private PetriNet buildWithFusion() {
            // Step 1: detect overlap. The same place identity (Place is a
            // record, so equality is structural on name+tokenType) MUST NOT
            // appear in more than one fusion set in v1 per the spec note.
            var ownership = new HashMap<Place<?>, FusionSet>();
            for (var set : fusionSets) {
                for (var member : set.members()) {
                    var prior = ownership.put(member, set);
                    if (prior != null && prior != set) {
                        throw new IllegalStateException(
                            "Fusion overlap: place '" + member.name()
                                + "' appears in two fusion sets ('" + prior.name()
                                + "' and '" + set.name()
                                + "'). A place may appear in at most one fusion set (MOD-060).");
                    }
                }
            }

            // Step 2: build the non-canonical → canonical substitution map.
            // Single-member sets contribute nothing (no non-canonical members),
            // so the map is naturally empty for the degenerate case.
            var fusionMap = new HashMap<Place<?>, Place<?>>();
            for (var set : fusionSets) {
                var canonical = set.canonical();
                for (var nc : set.nonCanonical()) {
                    fusionMap.put(nc, canonical);
                }
            }

            // Step 3: rewrite every transition's arcs through the fusion map.
            // applyFusion always returns a fresh set; if fusionMap is empty
            // (single-member-only sets) the rewrite is structurally a no-op
            // but still rebuilds Transition records — no observable difference.
            var rewrittenTransitions = SubnetRewriter.applyFusion(transitions, fusionMap);

            // Step 4: re-derive the place set. Strategy: start from the
            // current place set, drop every non-canonical member (they are
            // gone from the net), then union in the places auto-discovered
            // from the rewritten transitions. This preserves caller-declared
            // standalone places that are unrelated to fusion, drops any
            // standalone declarations of non-canonical members, and ensures
            // canonical places end up present even if a caller never declared
            // them standalone.
            var nonCanonicalSet = fusionMap.keySet();
            var rebuiltPlaces = new HashSet<Place<?>>(places.size() + 16);
            for (var p : places) {
                if (!nonCanonicalSet.contains(p)) {
                    rebuiltPlaces.add(p);
                }
            }
            for (var t : rewrittenTransitions) {
                for (var in : t.inputSpecs()) rebuiltPlaces.add(in.place());
                if (t.outputSpec() != null) rebuiltPlaces.addAll(t.outputSpec().allPlaces());
                for (var inh : t.inhibitors()) rebuiltPlaces.add(inh.place());
                for (var rd  : t.reads())      rebuiltPlaces.add(rd.place());
                for (var rs  : t.resets())     rebuiltPlaces.add(rs.place());
            }

            return new PetriNet(name, rebuiltPlaces, rewrittenTransitions);
        }
    }
}
