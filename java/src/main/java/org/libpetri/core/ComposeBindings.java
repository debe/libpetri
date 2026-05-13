package org.libpetri.core;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;

/**
 * Typed binding builder for {@link PetriNet.Builder#compose(Instance, java.util.function.Consumer)},
 * per {@code spec/11-modular-composition.md} requirements <b>MOD-020</b>
 * (composition operation) and <b>MOD-022</b> (type compatibility).
 *
 * <p>{@code ComposeBindings} is a write-only collector: callers register port
 * and channel bindings against an instance's interface, and the host
 * builder consumes the recorded mappings as it merges the instance into the
 * enclosing net.
 *
 * <h2>Port bindings (MOD-020, MOD-022)</h2>
 * <p>{@link #bindPort(String, Place)} merges an interface port with a
 * caller-side place. The port name is the <b>original</b> (pre-prefix) name
 * declared in the subnet's {@link Interface}; the caller place takes the
 * port's slot in the resulting net. Token-type compatibility is enforced at
 * compose time per [MOD-022].
 *
 * <h2>Channel bindings (MOD-021)</h2>
 * <p>{@link #bindChannel(String, Transition)} records a synchronous channel
 * binding: at compose time, the named instance-side interface transition is
 * <b>merged</b> with the supplied caller-side {@link Transition} into one
 * transition in the resulting flat net. Arc union, sequential action
 * composition, and timing/priority resolution follow the merge contract per
 * [MOD-021]; see {@link PetriNet.Builder#compose(Instance, java.util.function.Consumer)}.
 *
 * <h2>Identity</h2>
 * <p>{@code ComposeBindings} is a final class — not a record, not extensible.
 * It carries mutable state during the {@code Consumer<ComposeBindings>}
 * callback and is then drained by the compose call.
 */
public final class ComposeBindings {

    private final LinkedHashMap<String, Place<?>> portBindings = new LinkedHashMap<>();
    private final LinkedHashMap<String, Transition> channelBindings = new LinkedHashMap<>();

    /**
     * Package-private constructor — instances are produced by
     * {@link PetriNet.Builder#compose(Instance, java.util.function.Consumer)}
     * and supplied to the caller's {@link java.util.function.Consumer}.
     */
    ComposeBindings() { }

    /**
     * Binds the named interface port to the given caller place per <b>MOD-020</b>.
     *
     * <p>The port name is the <b>original</b> (pre-prefix) name declared in
     * the subnet's {@link Interface}. The caller place's token type must
     * match the interface place's token type per <b>MOD-022</b> — this is
     * verified at compose time, not at {@code bindPort} time, because the
     * lookup needs the resolved {@link Instance}.
     *
     * @param portName     the port name as declared in the subnet's {@link Interface}
     * @param callerPlace  the caller-side place to merge with the interface port
     * @param <T>          token type of the caller place
     * @return this binding builder, for chaining
     * @throws IllegalArgumentException when {@code portName} or {@code callerPlace}
     *         is null, or when {@code portName} was already bound
     */
    public <T> ComposeBindings bindPort(String portName, Place<T> callerPlace) {
        Objects.requireNonNull(portName, "portName");
        Objects.requireNonNull(callerPlace, "callerPlace");
        if (portBindings.containsKey(portName)) {
            throw new IllegalArgumentException(
                "Port '" + portName + "' is already bound");
        }
        portBindings.put(portName, callerPlace);
        return this;
    }

    /**
     * Records a synchronous channel binding per <b>MOD-021</b>: at compose
     * time, the instance-side renamed channel transition (resolved by name on
     * the {@link Instance}) is merged with {@code callerTransition} into a
     * single transition in the resulting flat net.
     *
     * <p>The arc set, action, timing, and priority of the merged transition
     * are computed per {@link PetriNet.Builder#compose(Instance, java.util.function.Consumer)}.
     * The caller-side transition's name and identity become the merged
     * transition's name and identity (caller-wins convention).
     *
     * @param channelName        the channel name as declared in the subnet's {@link Interface}
     * @param callerTransition   the caller-side transition to fuse with the interface channel
     * @return this binding builder, for chaining
     * @throws IllegalArgumentException when {@code channelName} or
     *         {@code callerTransition} is null, or when {@code channelName}
     *         was already bound
     */
    public ComposeBindings bindChannel(String channelName, Transition callerTransition) {
        Objects.requireNonNull(channelName, "channelName");
        Objects.requireNonNull(callerTransition, "callerTransition");
        if (channelBindings.containsKey(channelName)) {
            throw new IllegalArgumentException(
                "Channel '" + channelName + "' is already bound");
        }
        channelBindings.put(channelName, callerTransition);
        return this;
    }

    /** Returns an unmodifiable view of the recorded port bindings. */
    public Map<String, Place<?>> portBindings() {
        return Collections.unmodifiableMap(portBindings);
    }

    /** Returns an unmodifiable view of the recorded channel bindings. */
    public Map<String, Transition> channelBindings() {
        return Collections.unmodifiableMap(channelBindings);
    }
}
