package org.libpetri.core;

import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * A typed module instance produced by {@link SubnetDef#instantiate(String, Object)},
 * per {@code spec/11-modular-composition.md} requirements <b>MOD-010</b>
 * (creation), <b>MOD-011</b> (typed handle map), <b>MOD-012</b>
 * (per-instance state isolation), and <b>MOD-030</b> (action binding).
 *
 * <p>An instance carries:
 * <ul>
 *   <li>The {@link #prefix()} string used to rename body elements
 *       (per [MOD-010] separator {@code "/"});</li>
 *   <li>A reference to the originating {@link SubnetDef};</li>
 *   <li>The renamed body — a structurally valid {@link PetriNet} per
 *       [CORE-040];</li>
 *   <li>Typed lookup handles for ports and channels keyed by their
 *       <b>original</b> (pre-prefix) names;</li>
 *   <li>The {@code params} value supplied at instantiation.</li>
 * </ul>
 *
 * <h2>Scaffolding status</h2>
 * <p>This class ships in scaffolding form: the constructor is
 * package-private and the rich {@link #bindActions(Map)} method throws
 * {@link UnsupportedOperationException} until the {@code instantiate} rename
 * pass lands in the next task. Direct accessors are wired up so downstream
 * code can take dependencies on the API shape today without waiting for the
 * rename pass.
 *
 * @param <P> parameter type (use {@link Void} for unparameterised subnets)
 */
public final class Instance<P> {

    private final String prefix;
    private final SubnetDef<P> def;
    private final PetriNet renamedBody;
    private final Map<String, Place<?>> portHandles;
    private final Map<String, Transition> channelHandles;
    private final P params;

    /**
     * Package-private constructor invoked by {@link SubnetDef#instantiate}.
     * Direct construction by user code is not permitted; the rename pass and
     * handle population are responsibilities of {@code SubnetDef}.
     */
    Instance(
        String prefix,
        SubnetDef<P> def,
        PetriNet renamedBody,
        Map<String, Place<?>> portHandles,
        Map<String, Transition> channelHandles,
        P params
    ) {
        this.prefix = Objects.requireNonNull(prefix, "prefix");
        this.def = Objects.requireNonNull(def, "def");
        this.renamedBody = Objects.requireNonNull(renamedBody, "renamedBody");
        this.portHandles = Map.copyOf(portHandles);
        this.channelHandles = Map.copyOf(channelHandles);
        this.params = params;
    }

    /** Returns the prefix string supplied at {@link SubnetDef#instantiate}. */
    public String prefix() {
        return prefix;
    }

    /** Returns the originating subnet definition. */
    public SubnetDef<P> def() {
        return def;
    }

    /** Returns the renamed body net (structurally valid {@link PetriNet}). */
    public PetriNet renamedBody() {
        return renamedBody;
    }

    /** Returns the parameter value supplied at instantiation, or {@code null} for unparameterised instances. */
    public P params() {
        return params;
    }

    /**
     * Returns the renamed {@link Place} corresponding to the named port.
     *
     * <p>The port name is the <b>original</b> (pre-prefix) name as declared
     * in the subnet's {@link Interface}. The {@code tokenType} parameter is
     * cross-checked against the underlying place's declared token type;
     * a mismatch raises {@link IllegalArgumentException} per [MOD-011].
     *
     * @throws IllegalArgumentException when the port name is unknown or
     *         when {@code tokenType} disagrees with the declared port type
     */
    @SuppressWarnings("unchecked")
    public <T> Place<T> port(String name, Class<T> tokenType) {
        var place = portHandles.get(name);
        if (place == null) {
            throw new IllegalArgumentException(
                "No port named '" + name + "' in instance '" + prefix + "'");
        }
        if (!place.tokenType().equals(tokenType)) {
            throw new IllegalArgumentException(
                "Port '" + name + "' has token type " + place.tokenType().getName()
                    + " but was requested as " + tokenType.getName());
        }
        return (Place<T>) place;
    }

    /**
     * Returns the renamed {@link Transition} corresponding to the named channel.
     *
     * @throws IllegalArgumentException when the channel name is unknown
     */
    public Transition channel(String name) {
        var t = channelHandles.get(name);
        if (t == null) {
            throw new IllegalArgumentException(
                "No channel named '" + name + "' in instance '" + prefix + "'");
        }
        return t;
    }

    /**
     * Returns the debug-UI descriptor for this instance per <b>MOD-041</b>.
     */
    public SubnetInstance descriptor() {
        return new SubnetInstance(
            prefix,
            def.name(),
            renamedBody.transitions(),
            Set.copyOf(portHandles.values()),
            params,
            Optional.empty()
        );
    }

    /**
     * Produces a derived instance whose specified transitions (named by their
     * <b>original</b>, pre-prefix names) carry the supplied actions per
     * <b>MOD-030</b>.
     *
     * <p>Mapping semantics:
     * <ul>
     *   <li>The keys of {@code actionsByOriginalName} are the
     *       <b>un-prefixed</b> transition names from the subnet definition's body.
     *       They are translated internally to the prefixed names of the renamed
     *       body before forwarding to {@link PetriNet#bindActions(Map)}.</li>
     *   <li>Transitions not named in the override map retain their shared
     *       default action (the action carried through from the body, by
     *       reference per [MOD-030]).</li>
     *   <li>Override is per-instance: invoking {@code bindActions} on this
     *       instance does not affect any other instance of the same
     *       {@link SubnetDef}.</li>
     *   <li>An override key that does not correspond to any transition in the
     *       subnet body is rejected with {@link IllegalArgumentException},
     *       naming the offending key.</li>
     * </ul>
     *
     * <p>The returned instance has the same {@link #prefix()}, {@link #def()},
     * {@link #portHandles port handles}, {@link #channelHandles channel
     * handles}, and {@link #params()} as this instance — only the action
     * bindings differ.
     *
     * <h3>Channel-identity invariant (compose contract)</h3>
     * <p>Implementations of this method (and any future {@link Instance}
     * derivation that returns a new {@code Instance} reusing the existing
     * {@code channelHandles} map) <b>MUST</b> preserve the identity — both
     * <i>name</i> and <i>arc structure</i> — of every transition referenced
     * by an {@link Interface} channel. The returned derived {@code Instance}
     * shares the same port and channel handle maps as {@code this}; those
     * handles must continue to resolve to a transition that is a member of
     * the derived {@link #renamedBody()} (lookup is by transition name).
     *
     * <p>If a refactor were to recompute channel-transition identity (for
     * example by renaming or re-keying the transitions while updating
     * actions), the channel-handle map would silently fall out of sync with
     * the renamed body and {@link PetriNet.Builder#compose(Instance, java.util.function.Consumer)}
     * would resolve channels to transitions that no longer exist in the
     * composed flat net. This invariant is checked at compose-time in
     * {@link PetriNet.Builder#compose(Instance, java.util.function.Consumer)};
     * a violation raises {@link IllegalStateException}.
     *
     * @param actionsByOriginalName map from original (un-prefixed) transition
     *                              name to the action to bind on this instance
     * @return a fresh {@link Instance} whose renamed body carries the override actions
     * @throws IllegalArgumentException when {@code actionsByOriginalName} contains
     *                                  a key that does not match any transition
     *                                  in the subnet body
     */
    public Instance<P> bindActions(Map<String, TransitionAction> actionsByOriginalName) {
        Objects.requireNonNull(actionsByOriginalName, "actionsByOriginalName");

        if (actionsByOriginalName.isEmpty()) {
            return this;
        }

        // Build the original-name set so we can validate keys cheaply.
        var bodyTransitionNames = new java.util.HashSet<String>(def.body().transitions().size());
        for (var t : def.body().transitions()) {
            bodyTransitionNames.add(t.name());
        }

        // Translate the override map keys: original-name -> prefixed-name.
        var prefixedActions = new java.util.LinkedHashMap<String, TransitionAction>();
        for (var entry : actionsByOriginalName.entrySet()) {
            var original = entry.getKey();
            if (!bodyTransitionNames.contains(original)) {
                throw new IllegalArgumentException(
                    "bindActions: no transition named '" + original
                        + "' in subnet '" + def.name() + "' (instance prefix '" + prefix + "')");
            }
            prefixedActions.put(prefix + "/" + original, entry.getValue());
        }

        // Delegate to the existing PetriNet.bindActions infrastructure (CORE-042).
        // The resolver leaves un-named transitions untouched (returning their
        // current action), per MOD-030 share-by-default semantics.
        var rebound = renamedBody.bindActions(name -> {
            var override = prefixedActions.get(name);
            if (override != null) return override;
            // Returning null tells PetriNet.bindActions to leave the existing action in place.
            return null;
        });

        return new Instance<>(prefix, def, rebound, portHandles, channelHandles, params);
    }
}
