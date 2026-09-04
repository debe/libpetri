package org.libpetri.core;

import org.libpetri.analysis.EnvironmentAnalysisMode;
import org.libpetri.core.internal.SubnetRewriter;
import org.libpetri.smt.SmtVerificationResult;
import org.libpetri.smt.SmtVerifier;
import org.libpetri.verification.VerificationHarness;
import org.libpetri.verification.VerificationResult;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;

/**
 * An open Petri net fragment paired with a declared {@link Interface}, per
 * {@code spec/11-modular-composition.md} requirement <b>MOD-001</b>.
 *
 * <p>A subnet definition is the reusable unit of composition. It carries:
 * <ul>
 *   <li>A {@link #name()} (used as the originating-def label in
 *       {@link SubnetInstance} per [MOD-041]);</li>
 *   <li>A {@link #body()} — a structurally complete {@link PetriNet} per
 *       [CORE-040];</li>
 *   <li>An {@link #iface()} — the set of exposed ports and channels per
 *       [MOD-003] / [MOD-005];</li>
 *   <li>A {@link #paramType()} describing the {@link Instance#params()}
 *       value supplied at {@link #instantiate(String, Object) instantiate}.</li>
 * </ul>
 *
 * <p>{@code SubnetDef} implements {@link Subnet.Open} so it slots into the
 * sealed sum-type defined in {@link Subnet} per <b>MOD-002</b>.
 *
 * <p>The {@link #fromNet(PetriNet, Interface)} retrofit factory per
 * <b>MOD-014</b> wraps an existing closed {@link PetriNet} plus an
 * {@link Interface} into an unparameterised {@code SubnetDef<Void>},
 * applying the same per-element validation as {@link Builder#build()}.
 * The {@link #verify(org.libpetri.verification.VerificationHarness)}
 * method per <b>MOD-051</b> proves safety properties of the subnet in
 * isolation by wrapping it in a synthetic enclosing net.
 *
 * @param <P> parameter type carried through to {@link Instance#params()}
 *            (use {@link Void} for unparameterised subnets)
 */
public final class SubnetDef<P> implements Subnet.Open {

    private final String name;
    private final PetriNet body;
    private final Interface iface;
    private final Class<P> paramType;

    private SubnetDef(String name, PetriNet body, Interface iface, Class<P> paramType) {
        this.name = Objects.requireNonNull(name, "name");
        this.body = Objects.requireNonNull(body, "body");
        this.iface = Objects.requireNonNull(iface, "iface");
        this.paramType = Objects.requireNonNull(paramType, "paramType");
    }

    public String name() {
        return name;
    }

    public PetriNet body() {
        return body;
    }

    public Interface iface() {
        return iface;
    }

    public Class<P> paramType() {
        return paramType;
    }

    /**
     * Produces a renamed module instance per <b>MOD-010</b>, <b>MOD-011</b>,
     * <b>MOD-012</b>, and <b>MOD-030</b>.
     *
     * <p>The rename pass walks every place and transition of the body net,
     * substituting each name with {@code prefix + "/" + originalName}, and
     * rebuilds every arc with rewritten place references. Transition
     * timing, priority, and action are carried through by reference (action
     * sharing per [MOD-030]). The renamed body is itself a structurally
     * valid {@link PetriNet} per [CORE-040]; per-instance state isolation
     * per [MOD-012] is a structural consequence of distinct prefixed names.
     *
     * <h2>Prefix validation</h2>
     * The {@code "/"} character is reserved as the prefix separator
     * (per [MOD-010]). User-supplied prefixes MUST NOT contain {@code "/"};
     * nested instantiation is performed by the future
     * {@code PetriNet.Builder.compose(...)} mechanism (per [MOD-013]). A
     * prefix containing {@code "/"} raises {@link IllegalArgumentException}.
     *
     * @param prefix the rename prefix (non-null, non-empty, must not contain {@code "/"})
     * @param params the parameter value carried through to {@link Instance#params()}
     *               (may be {@code null} when {@code P} is {@link Void})
     * @return a fresh {@link Instance} wrapping the renamed body
     * @throws IllegalArgumentException when {@code prefix} is null, empty,
     *                                  or contains {@code "/"}
     */
    public Instance<P> instantiate(String prefix, P params) {
        validatePrefix(prefix);

        // Allocate the two remap maps. SubnetRewriter fills them as side effects
        // so we can resolve interface place/transition references afterward.
        var placeRemap = SubnetRewriter.newPlaceRemap();
        var transitionRemap = SubnetRewriter.newTransitionRemap();

        var renamedBody = SubnetRewriter.renameNet(body, prefix, placeRemap, transitionRemap);

        // Resolve the port handles: original-port-name -> renamed body place.
        var portHandles = new LinkedHashMap<String, Place<?>>();
        for (var port : iface.ports()) {
            var renamed = placeRemap.get(port.place());
            if (renamed == null) {
                // Defensive: should be impossible because MOD-006 validation at
                // SubnetDef.Builder.build() guarantees port.place() is in the body.
                throw new IllegalStateException(
                    "Port '" + port.name() + "' references place '" + port.place().name()
                        + "' that was not found in the renamed body. "
                        + "This indicates a SubnetDef invariant violation.");
            }
            portHandles.put(port.name(), renamed);
        }

        // Resolve the channel handles: original-channel-name -> renamed body transition.
        var channelHandles = new LinkedHashMap<String, Transition>();
        for (var channel : iface.channels()) {
            var renamed = transitionRemap.get(channel.transition());
            if (renamed == null) {
                throw new IllegalStateException(
                    "Channel '" + channel.name() + "' references transition '"
                        + channel.transition().name()
                        + "' that was not found in the renamed body. "
                        + "This indicates a SubnetDef invariant violation.");
            }
            channelHandles.put(channel.name(), renamed);
        }

        return new Instance<>(prefix, this, renamedBody, portHandles, channelHandles, params);
    }

    /**
     * Convenience overload for unparameterised subnets ({@code P = Void}).
     * Equivalent to {@code instantiate(prefix, null)}.
     */
    public Instance<P> instantiate(String prefix) {
        return instantiate(prefix, null);
    }

    // ============================================================
    //  MOD-051: local property verification via synthetic harness
    // ============================================================

    /**
     * Verifies safety properties of this subnet definition <b>in isolation</b>
     * per <b>MOD-051</b>, by wrapping it in a synthetic enclosing net where
     * each input port is fed by an {@link EnvironmentPlace} (token-source per
     * the harness generator) and each output port is observed via a
     * synthetic place. The standard {@link SmtVerifier} (per [MOD-050]) is
     * invoked once per property declared in the harness; the resulting
     * per-property outcomes are aggregated into a {@link VerificationResult}.
     *
     * <h3>Synthetic-net construction</h3>
     * The synthetic enclosing net is built by:
     * <ol>
     *   <li>Instantiating this {@code SubnetDef} with the prefix
     *       {@code "sut"} (system-under-test) and {@code harness.params()}.</li>
     *   <li>For each {@link Interface.Port.Input} or
     *       {@link Interface.Port.InOut} on the interface, looking up the
     *       harness generator by port name, allocating a synthetic
     *       {@link Place}{@code <T>} of the same token type as the port,
     *       wrapping it in an {@link EnvironmentPlace}, and binding the
     *       port to that synthetic place via
     *       {@link PetriNet.Builder#compose(Instance, java.util.function.Consumer)}.
     *       The supplier is invoked once at construction time to materialize
     *       the seed token type — its presence is what bounds the input
     *       behavior under analysis. <b>If the harness map is missing a
     *       generator for a required input port, an
     *       {@link IllegalArgumentException} is thrown.</b></li>
     *   <li>For each {@link Interface.Port.Output} or
     *       {@link Interface.Port.InOut}, allocating a synthetic observation
     *       {@link Place}{@code <T>} and binding the port to it via the
     *       same {@code compose(...)} call. The verifier inspects this
     *       place's reachability / marking through the standard property
     *       APIs ({@link org.libpetri.smt.SmtProperty.PlaceBound},
     *       {@link org.libpetri.smt.SmtProperty.Unreachable}, etc.).</li>
     *   <li>Building the resulting flat {@link PetriNet} per [MOD-023]
     *       (the verifier is composition-unaware per [MOD-050]).</li>
     * </ol>
     *
     * <h3>Per-property invocation</h3>
     * Each {@link org.libpetri.smt.SmtProperty} in the harness is verified
     * independently against the same synthetic net. The synthetic
     * environment places are passed through to the verifier so that places
     * driven by the harness generators are treated under the
     * verifier's environment-analysis semantics rather than as ordinary
     * sink places.
     *
     * @param harness the verification harness — supplies parameters,
     *                input-port token generators, and the property set
     * @return a {@link VerificationResult} aggregating per-property
     *         {@link SmtVerificationResult}s
     * @throws IllegalArgumentException when an input or in-out port is
     *         missing a harness generator
     * @throws IllegalStateException when the synthetic net violates [CORE-043]
     */
    public VerificationResult verify(VerificationHarness<P> harness) {
        return verify(harness, EnvironmentAnalysisMode.alwaysAvailable());
    }

    /**
     * As {@link #verify(VerificationHarness)}, with an explicit environment-analysis
     * mode for the synthetic environment places ([VER-006], [MOD-051] AC3).
     *
     * <p>The synthetic net has environment places by construction, so this mode decides
     * what a verdict means. The default,
     * {@link EnvironmentAnalysisMode#alwaysAvailable()}, over-approximates: a
     * {@code Proven} under it holds for any environment. Pass
     * {@link EnvironmentAnalysisMode#bounded(int)} to prove a property that holds only
     * when the environment injects at most {@code k} tokens — that is the mode that
     * expresses a generator bounding the input.
     *
     * <p>{@link EnvironmentAnalysisMode#ignore()} is accepted but cannot yield
     * {@code Proven}: [VER-006] refuses to certify a proof that holds only because
     * injection was never modelled.
     *
     * @param harness the verification harness
     * @param environmentMode how injection into the synthetic environment places is
     *                        modeled
     * @return a {@link VerificationResult} aggregating per-property
     *         {@link SmtVerificationResult}s
     */
    public VerificationResult verify(
            VerificationHarness<P> harness, EnvironmentAnalysisMode environmentMode) {
        Objects.requireNonNull(harness, "harness");
        Objects.requireNonNull(environmentMode, "environmentMode");

        // Step 1: instantiate this SubnetDef under the "sut" prefix.
        var sut = instantiate("sut", harness.params());

        // Step 2: allocate synthetic harness places per port direction.
        // Track the environment places (one per input/inout port) for the
        // SmtVerifier so the verifier knows to treat their underlying places
        // as boundary places rather than ordinary internals.
        var envPlaces = new LinkedHashSet<EnvironmentPlace<?>>();
        var portMappings = new LinkedHashMap<String, Place<?>>();

        for (var port : iface.ports()) {
            var portName = port.name();
            var underlyingTokenType = port.place().tokenType();

            switch (port) {
                case Interface.Port.Input<?> in -> {
                    var generator = harness.portInputGenerators().get(portName);
                    if (generator == null) {
                        throw new IllegalArgumentException(
                            "verify: harness is missing an input generator for port '"
                                + portName + "' on subnet '" + name + "' (MOD-051)");
                    }
                    // Touch the supplier to surface user-supplied errors at
                    // construction time rather than at verification time.
                    Objects.requireNonNull(generator.get(),
                        "verify: input generator for port '" + portName
                            + "' on subnet '" + name + "' produced null");

                    var synthPlace = newSyntheticPlace(
                        "harness_in_" + portName, underlyingTokenType);
                    envPlaces.add(EnvironmentPlace.of(synthPlace));
                    portMappings.put(portName, synthPlace);
                }
                case Interface.Port.Output<?> out -> {
                    var synthPlace = newSyntheticPlace(
                        "harness_out_" + portName, underlyingTokenType);
                    portMappings.put(portName, synthPlace);
                }
                case Interface.Port.InOut<?> inout -> {
                    var generator = harness.portInputGenerators().get(portName);
                    if (generator == null) {
                        throw new IllegalArgumentException(
                            "verify: harness is missing an input generator for in-out port '"
                                + portName + "' on subnet '" + name + "' (MOD-051)");
                    }
                    Objects.requireNonNull(generator.get(),
                        "verify: input generator for in-out port '" + portName
                            + "' on subnet '" + name + "' produced null");

                    var synthPlace = newSyntheticPlace(
                        "harness_io_" + portName, underlyingTokenType);
                    envPlaces.add(EnvironmentPlace.of(synthPlace));
                    portMappings.put(portName, synthPlace);
                }
            }
        }

        // Step 3: build the synthetic enclosing net.
        // Channels declared on the interface (but not bound here) flow
        // through as ordinary renamed transitions per MOD-021.
        var syntheticNet = PetriNet.builder("verify_" + name)
            .compose(sut, portMappings)
            .build();

        // CORE-043, checked here rather than left to SmtVerifier so an empty property set
        // cannot skip it.
        org.libpetri.core.internal.OutputActionCheck.requireOutputProducingActions(syntheticNet);

        // Step 4: invoke the SmtVerifier once per property and aggregate
        // results. Iteration order is preserved (LinkedHashSet from the
        // harness compact constructor + LinkedHashMap accumulation here).
        var perProperty = new LinkedHashMap<
            org.libpetri.smt.SmtProperty, SmtVerificationResult>(
                harness.properties().size() * 2);
        for (var property : harness.properties()) {
            // Set explicitly rather than inherited: the synthetic env places are
            // the harness's own, so how injection is modelled is the harness's
            // call ([MOD-051] AC3), not the verifier default's. Under
            // EnvironmentAnalysisMode.ignore() [VER-006] downgrades every proof
            // about a net with env places to Unknown, so a subnet with an input
            // port could never be proven.
            var result = SmtVerifier.forNet(syntheticNet)
                .property(property)
                .environmentPlaces(envPlaces.toArray(new EnvironmentPlace<?>[0]))
                .environmentMode(environmentMode)
                .verify();
            perProperty.put(property, result);
        }

        return new VerificationResult(syntheticNet, perProperty);
    }

    /**
     * Allocates a synthetic harness {@link Place} of the supplied token type
     * with the supplied name. Centralised so the (otherwise unchecked) cast
     * from {@code Class<?>} to {@code Class<T>} is contained in one helper.
     */
    @SuppressWarnings({"unchecked", "rawtypes"})
    private static Place<?> newSyntheticPlace(String name, Class<?> tokenType) {
        return Place.of(name, (Class) tokenType);
    }

    private static void validatePrefix(String prefix) {
        if (prefix == null) {
            throw new IllegalArgumentException("prefix must be non-null");
        }
        if (prefix.isEmpty()) {
            throw new IllegalArgumentException("prefix must be non-empty");
        }
        if (prefix.indexOf('/') >= 0) {
            throw new IllegalArgumentException(
                "prefix must not contain '/' (reserved as the prefix separator per MOD-010); "
                    + "use compose(...) for nested instantiation. Got: '" + prefix + "'");
        }
    }

    // ============================================================
    //  Static factories
    // ============================================================

    public static Builder<Void> builder(String name) {
        return new Builder<>(name, Void.class);
    }

    public static <P> Builder<P> builder(String name, Class<P> paramType) {
        return new Builder<>(name, paramType);
    }

    /**
     * Retrofit utility per <b>MOD-014</b>: wraps an existing closed
     * {@link PetriNet} plus an {@link Interface} into an unparameterised
     * {@code SubnetDef<Void>}.
     *
     * <p>Validation per <b>MOD-014</b> / <b>MOD-006</b> is enforced before
     * the result is constructed:
     * <ul>
     *   <li>Every {@link Interface.Port}'s underlying {@link Place} MUST be
     *       present in {@code net.places()}.</li>
     *   <li>Every {@link Interface.Channel}'s underlying {@link Transition}
     *       MUST be present in {@code net.transitions()}.</li>
     *   <li>Port and channel name uniqueness is already enforced at
     *       {@link Interface.Builder#build()} — re-validated defensively
     *       here so callers that bypass the builder still see a clear
     *       error.</li>
     * </ul>
     *
     * <p>On failure, an {@link IllegalArgumentException} is thrown naming
     * the offending element. The resulting subnet definition is
     * unparameterised (parameter type is {@link Void}).
     *
     * @param net   the closed Petri net to wrap (non-null)
     * @param iface the interface declaration referencing places /
     *              transitions of {@code net} (non-null)
     * @return a fresh, immutable {@code SubnetDef<Void>}
     * @throws IllegalArgumentException when a port place is not in
     *         {@code net.places()}, when a channel transition is not in
     *         {@code net.transitions()}, or when port/channel names are
     *         not unique within their respective namespaces
     */
    public static SubnetDef<Void> fromNet(PetriNet net, Interface iface) {
        Objects.requireNonNull(net, "net");
        Objects.requireNonNull(iface, "iface");

        var bodyPlaces = net.places();
        var bodyTransitions = net.transitions();

        // Validate every port's place is present in the net.
        // Defence-in-depth name-uniqueness check (Interface.Builder enforces
        // this at construction, but a hand-built Interface bypasses that
        // path; SubnetDef.fromNet is the documented retrofit entry point so
        // we re-check here to keep failures crisp).
        var seenPortNames = new HashSet<String>(iface.ports().size() * 2);
        for (var port : iface.ports()) {
            if (!seenPortNames.add(port.name())) {
                throw new IllegalArgumentException(
                    "fromNet: duplicate port name '" + port.name()
                        + "' on interface for net '" + net.name() + "' (MOD-006)");
            }
            if (!bodyPlaces.contains(port.place())) {
                throw new IllegalArgumentException(
                    "fromNet: port '" + port.name() + "' references place '"
                        + port.place().name() + "' which is not in net '"
                        + net.name() + "' (MOD-014/MOD-006)");
            }
        }

        // Validate every channel's transition is present in the net.
        var seenChannelNames = new HashSet<String>(iface.channels().size() * 2);
        for (var channel : iface.channels()) {
            if (!seenChannelNames.add(channel.name())) {
                throw new IllegalArgumentException(
                    "fromNet: duplicate channel name '" + channel.name()
                        + "' on interface for net '" + net.name() + "' (MOD-006)");
            }
            if (!bodyTransitions.contains(channel.transition())) {
                throw new IllegalArgumentException(
                    "fromNet: channel '" + channel.name() + "' references transition '"
                        + channel.transition().name() + "' which is not in net '"
                        + net.name() + "' (MOD-014/MOD-006)");
            }
        }

        return new SubnetDef<>(net.name(), net, iface, Void.class);
    }

    // ============================================================
    //  Builder
    // ============================================================

    /**
     * Fluent builder for {@link SubnetDef}.
     *
     * <p>Validation per <b>MOD-006</b> is enforced at {@link #build()}:
     * <ul>
     *   <li>Every port's underlying place must be in the body net.</li>
     *   <li>Every channel's underlying transition must be in the body net.</li>
     *   <li>Port names must be unique within the port namespace.</li>
     *   <li>Channel names must be unique within the channel namespace.</li>
     * </ul>
     *
     * @param <P> parameter type carried through to the produced {@link SubnetDef}
     */
    public static final class Builder<P> {
        private final String name;
        private final Class<P> paramType;
        private final PetriNet.Builder bodyBuilder;
        private final List<Interface.Port> ports = new ArrayList<>();
        private final List<Interface.Channel> channels = new ArrayList<>();

        private Builder(String name, Class<P> paramType) {
            this.name = Objects.requireNonNull(name, "name");
            this.paramType = Objects.requireNonNull(paramType, "paramType");
            this.bodyBuilder = PetriNet.builder(name);
        }

        // -------- body construction (delegates to PetriNet.Builder) --------

        public Builder<P> transition(Transition transition) {
            bodyBuilder.transition(transition);
            return this;
        }

        public Builder<P> transitions(Transition... transitions) {
            bodyBuilder.transitions(transitions);
            return this;
        }

        public <T> Builder<P> place(Place<T> place) {
            bodyBuilder.place(place);
            return this;
        }

        // -------- interface declarations --------

        public <T> Builder<P> inputPort(String portName, Place<T> place) {
            ports.add(new Interface.Port.Input<>(portName, place));
            return this;
        }

        public <T> Builder<P> outputPort(String portName, Place<T> place) {
            ports.add(new Interface.Port.Output<>(portName, place));
            return this;
        }

        public <T> Builder<P> inoutPort(String portName, Place<T> place) {
            ports.add(new Interface.Port.InOut<>(portName, place));
            return this;
        }

        public Builder<P> channel(String channelName, Transition transition) {
            channels.add(new Interface.Channel.SyncChannel(channelName, transition));
            return this;
        }

        // -------- build & validate (MOD-006) --------

        public SubnetDef<P> build() {
            var built = bodyBuilder.build();
            var bodyPlaces = built.places();
            var bodyTransitions = built.transitions();

            // 2. Validate port-name uniqueness (MOD-006).
            var portNames = new LinkedHashSet<String>();
            for (var port : ports) {
                if (!portNames.add(port.name())) {
                    throw new IllegalArgumentException(
                        "Subnet '" + name + "': duplicate port name '" + port.name() + "'");
                }
                // 3. Validate port place membership (MOD-006).
                if (!bodyPlaces.contains(port.place())) {
                    throw new IllegalArgumentException(
                        "Subnet '" + name + "': port '" + port.name()
                            + "' references place '" + port.place().name()
                            + "' which is not in the body");
                }
            }

            // 4. Validate channel-name uniqueness and transition membership (MOD-006).
            var channelNames = new LinkedHashSet<String>();
            for (var channel : channels) {
                if (!channelNames.add(channel.name())) {
                    throw new IllegalArgumentException(
                        "Subnet '" + name + "': duplicate channel name '" + channel.name() + "'");
                }
                if (!bodyTransitions.contains(channel.transition())) {
                    throw new IllegalArgumentException(
                        "Subnet '" + name + "': channel '" + channel.name()
                            + "' references transition '" + channel.transition().name()
                            + "' which is not in the body");
                }
            }

            var iface = Interface.builder()
                .portsAll(ports)
                .channelsAll(channels)
                .build();

            return new SubnetDef<>(name, built, iface, paramType);
        }
    }
}
