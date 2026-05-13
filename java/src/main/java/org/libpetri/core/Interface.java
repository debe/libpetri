package org.libpetri.core;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * Immutable declaration of a subnet's <b>interface</b>: the set of
 * {@link Port ports} (interface places) and {@link Channel channels}
 * (interface transitions) exposed for composition with an enclosing net.
 *
 * <p>Specified by {@code spec/11-modular-composition.md} requirements
 * <b>MOD-003</b> (port declaration) and <b>MOD-005</b> (channel declaration).
 * Validation rules per <b>MOD-006</b> are enforced by
 * {@link SubnetDef.Builder} at subnet build time, not here — this class
 * is a pure carrier.
 *
 * <h2>Identity</h2>
 * Interfaces are compared by structural value equality of their
 * {@code (ports, channels)} sets, not by reference identity.
 *
 * @see SubnetDef
 * @see Port
 * @see Channel
 */
public final class Interface {

    private final Set<Port> ports;
    private final Set<Channel> channels;

    private Interface(Set<Port> ports, Set<Channel> channels) {
        this.ports = Set.copyOf(ports);
        this.channels = Set.copyOf(channels);
    }

    /** Returns the unmodifiable set of declared ports. */
    public Set<Port> ports() {
        return ports;
    }

    /** Returns the unmodifiable set of declared channels. */
    public Set<Channel> channels() {
        return channels;
    }

    /** Looks up a port by name. */
    public Optional<Port> port(String name) {
        for (var p : ports) {
            if (p.name().equals(name)) return Optional.of(p);
        }
        return Optional.empty();
    }

    /** Looks up a channel by name. */
    public Optional<Channel> channel(String name) {
        for (var c : channels) {
            if (c.name().equals(name)) return Optional.of(c);
        }
        return Optional.empty();
    }

    /**
     * Looks up a port by name and returns its underlying place, type-checked
     * against the supplied {@code tokenType}. Returns empty when the port
     * does not exist or the token-type does not match.
     *
     * @param name port name
     * @param tokenType expected token type of the underlying place
     * @param <T> expected token type
     */
    @SuppressWarnings("unchecked")
    public <T> Optional<Place<T>> portPlaceAs(String name, Class<T> tokenType) {
        var port = port(name);
        if (port.isEmpty()) return Optional.empty();
        var place = port.get().place();
        if (!place.tokenType().equals(tokenType)) return Optional.empty();
        return Optional.of((Place<T>) place);
    }

    @Override
    public boolean equals(Object o) {
        return o instanceof Interface other
            && ports.equals(other.ports)
            && channels.equals(other.channels);
    }

    @Override
    public int hashCode() {
        return Objects.hash(ports, channels);
    }

    @Override
    public String toString() {
        return "Interface[ports=" + ports + ", channels=" + channels + "]";
    }

    public static Builder builder() {
        return new Builder();
    }

    // ============================================================
    //  Port (interface place)
    // ============================================================

    /**
     * A typed interface place exposed for composition. Direction is
     * <b>advisory metadata only</b> per <b>MOD-004</b>: it does not constrain
     * arc flow at runtime.
     */
    public sealed interface Port permits Port.Input, Port.Output, Port.InOut {

        /** Port name, unique within the {@link Interface}. */
        String name();

        /** The body place exposed by this port. */
        Place<?> place();

        /** Input port: tokens flow from caller into the subnet (advisory). */
        record Input<T>(String name, Place<T> place) implements Port {
            public Input {
                requireNonBlank(name, "Port.Input.name");
                Objects.requireNonNull(place, "Port.Input.place");
            }
        }

        /** Output port: tokens flow from the subnet to the caller (advisory). */
        record Output<T>(String name, Place<T> place) implements Port {
            public Output {
                requireNonBlank(name, "Port.Output.name");
                Objects.requireNonNull(place, "Port.Output.place");
            }
        }

        /** Bidirectional port: tokens flow both ways (advisory). */
        record InOut<T>(String name, Place<T> place) implements Port {
            public InOut {
                requireNonBlank(name, "Port.InOut.name");
                Objects.requireNonNull(place, "Port.InOut.place");
            }
        }
    }

    // ============================================================
    //  Channel (interface transition)
    // ============================================================

    /**
     * An interface transition exposed for synchronous composition with a
     * caller-side transition. The only present variant in this scaffolding
     * is {@link SyncChannel}; the sealed surface leaves room for future
     * channel kinds without breaking existing pattern matches.
     */
    public sealed interface Channel permits Channel.SyncChannel {

        /** Channel name, unique within the channel namespace. */
        String name();

        /** The body transition exposed by this channel. */
        Transition transition();

        /** Synchronous channel: caller and instance transitions fuse atomically. */
        record SyncChannel(String name, Transition transition) implements Channel {
            public SyncChannel {
                requireNonBlank(name, "Channel.SyncChannel.name");
                Objects.requireNonNull(transition, "Channel.SyncChannel.transition");
            }
        }
    }

    // ============================================================
    //  Builder
    // ============================================================

    public static final class Builder {
        private final LinkedHashMap<String, Port> ports = new LinkedHashMap<>();
        private final LinkedHashMap<String, Channel> channels = new LinkedHashMap<>();

        private Builder() { }

        public Builder port(Port port) {
            Objects.requireNonNull(port, "port");
            if (ports.containsKey(port.name())) {
                throw new IllegalArgumentException(
                    "Duplicate port name: '" + port.name() + "'");
            }
            ports.put(port.name(), port);
            return this;
        }

        public <T> Builder inputPort(String name, Place<T> place) {
            return port(new Port.Input<>(name, place));
        }

        public <T> Builder outputPort(String name, Place<T> place) {
            return port(new Port.Output<>(name, place));
        }

        public <T> Builder inoutPort(String name, Place<T> place) {
            return port(new Port.InOut<>(name, place));
        }

        public Builder channel(Channel channel) {
            Objects.requireNonNull(channel, "channel");
            if (channels.containsKey(channel.name())) {
                throw new IllegalArgumentException(
                    "Duplicate channel name: '" + channel.name() + "'");
            }
            channels.put(channel.name(), channel);
            return this;
        }

        public Builder syncChannel(String name, Transition transition) {
            return channel(new Channel.SyncChannel(name, transition));
        }

        /**
         * Internal: bulk-add already-validated port and channel collections.
         * Used by {@link SubnetDef.Builder} to seed an interface from
         * port/channel records collected during the subnet-builder flow.
         */
        Builder portsAll(Collection<Port> ports) {
            for (var p : ports) port(p);
            return this;
        }

        Builder channelsAll(Collection<Channel> channels) {
            for (var c : channels) channel(c);
            return this;
        }

        public Interface build() {
            return new Interface(new LinkedHashSet<>(ports.values()),
                                 new LinkedHashSet<>(channels.values()));
        }
    }

    // ============================================================
    //  Helpers
    // ============================================================

    private static void requireNonBlank(String value, String label) {
        if (value == null || value.isBlank()) {
            throw new IllegalArgumentException(label + " must be non-blank");
        }
    }
}
