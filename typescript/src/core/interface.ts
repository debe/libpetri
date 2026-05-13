import type { Place } from './place.js';
import type { Transition } from './transition.js';

/**
 * Advisory direction metadata for an interface place.
 *
 * Per **MOD-004**, direction is metadata only — it does NOT constrain arc flow
 * at runtime. Token movement is governed by arcs declared per CORE-030..CORE-035.
 */
export type PortDirection = 'input' | 'output' | 'inout';

/**
 * A typed interface place exposed for composition, per **MOD-003**.
 *
 * Direction is advisory metadata only (per **MOD-004**); the underlying
 * `Place<T>` reference is what is rewired at compose time.
 */
export interface Port<T = unknown> {
  /** Port name, unique within the {@link Interface}. */
  readonly name: string;
  /** Direction (advisory). */
  readonly direction: PortDirection;
  /** The body place exposed by this port. */
  readonly place: Place<T>;
}

/**
 * An interface transition exposed for synchronous fusion with a caller-side
 * transition, per **MOD-005**.
 *
 * The only present variant in this scaffolding is the synchronous channel.
 * The interface is left structurally open for future channel kinds without
 * breaking existing pattern matches on `name`/`transition`.
 */
export interface Channel {
  /** Channel name, unique within the channel namespace. */
  readonly name: string;
  /** The body transition exposed by this channel. */
  readonly transition: Transition;
}

/** @internal Symbol key restricting construction to the builder. */
const INTERFACE_KEY = Symbol('Interface.internal');

/**
 * Immutable declaration of a subnet's **interface**: the set of {@link Port}
 * (interface places) and {@link Channel} (interface transitions) exposed for
 * composition with an enclosing net.
 *
 * Specified by `spec/11-modular-composition.md` requirements **MOD-003**
 * (port declaration) and **MOD-005** (channel declaration). Validation rules
 * per **MOD-006** are enforced by `SubnetDef.builder()` at subnet build
 * time; this class itself enforces only port/channel name uniqueness within
 * its respective namespaces (used both by `SubnetDef` and by hand-built
 * interfaces fed into `SubnetDef.fromNet`).
 */
export class Interface {
  readonly ports: ReadonlyMap<string, Port<unknown>>;
  readonly channels: ReadonlyMap<string, Channel>;

  /** @internal Use {@link Interface.builder} to create instances. */
  constructor(
    key: symbol,
    ports: ReadonlyMap<string, Port<unknown>>,
    channels: ReadonlyMap<string, Channel>,
  ) {
    if (key !== INTERFACE_KEY) throw new Error('Use Interface.builder() to create instances');
    this.ports = ports;
    this.channels = channels;
  }

  /** Looks up a port by name. Returns undefined when absent. */
  port<T = unknown>(name: string): Port<T> | undefined {
    return this.ports.get(name) as Port<T> | undefined;
  }

  /** Looks up a channel by name. Returns undefined when absent. */
  channel(name: string): Channel | undefined {
    return this.channels.get(name);
  }

  /**
   * Looks up a port by name and returns its underlying place, narrowed to
   * `Place<T>`. Returns undefined when the port does not exist.
   *
   * Note: TypeScript erases generics at runtime, so unlike Java's
   * `portPlaceAs(name, Class<T>)` this method cannot verify the token type at
   * runtime — the caller is trusted to supply the correct `T`. Per **MOD-022**,
   * type compatibility is enforced at compile time only in TypeScript.
   */
  placeAs<T>(name: string): Place<T> | undefined {
    const p = this.ports.get(name);
    if (p === undefined) return undefined;
    return p.place as Place<T>;
  }

  static builder(): InterfaceBuilder {
    return new InterfaceBuilder();
  }
}

export class InterfaceBuilder {
  private readonly _ports = new Map<string, Port<unknown>>();
  private readonly _channels = new Map<string, Channel>();

  /** Add a pre-built port (rejects duplicate names). */
  port(port: Port<unknown>): this {
    if (this._ports.has(port.name)) {
      throw new Error(`Duplicate port name: '${port.name}'`);
    }
    this._ports.set(port.name, port);
    return this;
  }

  /** Add an input port (advisory direction). */
  inputPort<T>(name: string, place: Place<T>): this {
    return this.port({ name, direction: 'input', place: place as Place<unknown> });
  }

  /** Add an output port (advisory direction). */
  outputPort<T>(name: string, place: Place<T>): this {
    return this.port({ name, direction: 'output', place: place as Place<unknown> });
  }

  /** Add an in-out port (advisory direction). */
  inoutPort<T>(name: string, place: Place<T>): this {
    return this.port({ name, direction: 'inout', place: place as Place<unknown> });
  }

  /** Add a pre-built channel (rejects duplicate names). */
  channel(channel: Channel): this;
  /** Declare a synchronous channel by name + transition (rejects duplicate names). */
  channel(name: string, transition: Transition): this;
  channel(channelOrName: Channel | string, transition?: Transition): this {
    const ch: Channel = typeof channelOrName === 'string'
      ? { name: channelOrName, transition: transition! }
      : channelOrName;
    if (this._channels.has(ch.name)) {
      throw new Error(`Duplicate channel name: '${ch.name}'`);
    }
    this._channels.set(ch.name, ch);
    return this;
  }

  /** @internal Bulk-add ports already validated by the caller. */
  portsAll(ports: Iterable<Port<unknown>>): this {
    for (const p of ports) this.port(p);
    return this;
  }

  /** @internal Bulk-add channels already validated by the caller. */
  channelsAll(channels: Iterable<Channel>): this {
    for (const c of channels) this.channel(c);
    return this;
  }

  build(): Interface {
    // Freeze maps by handing them off as ReadonlyMap. Defensive copies guard
    // against post-build mutation through retained builder references.
    return new Interface(
      INTERFACE_KEY,
      new Map(this._ports),
      new Map(this._channels),
    );
  }
}
