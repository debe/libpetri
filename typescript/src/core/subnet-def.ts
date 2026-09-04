import type { PetriNet } from './petri-net.js';
import type { Transition } from './transition.js';
import type { Place } from './place.js';
import { environmentPlace, place as makePlace, type EnvironmentPlace } from './place.js';
import { Interface, type Channel, type Port } from './interface.js';
import type { Instance } from './instance.js';
import { __createInstance } from './instance.js';
import { PetriNet as PetriNetClass } from './petri-net.js';
import { renameNet } from './internal/subnet-rewriter.js';
import { SmtVerifier } from '../verification/smt-verifier.js';
import { alwaysAvailable } from '../verification/analysis/environment-analysis-mode.js';
import type { EnvironmentAnalysisMode } from '../verification/analysis/environment-analysis-mode.js';
import type { SmtProperty } from '../verification/smt-property.js';
import type { SmtVerificationResult } from '../verification/smt-verification-result.js';
import {
  buildVerificationResult,
  normaliseGenerators,
  normaliseProperties,
  type VerificationHarness,
  type VerificationResult,
  type TokenSupplier,
} from '../verification/verification-harness.js';
import { requireOutputProducingActions } from './internal/output-action-check.js';

// Re-export the real harness types from the verification module for callers
// that import from `core/subnet-def.js`. The previous task-#10 placeholder
// shape is removed; the surface is now backed by `verification/verification-harness.ts`.
export type { VerificationHarness, VerificationResult, TokenSupplier };

/** @internal Symbol key restricting construction to {@link SubnetDef.builder} and {@link SubnetDef.fromNet}. */
const SUBNET_DEF_KEY = Symbol('SubnetDef.internal');

/**
 * An open Petri net fragment paired with a declared {@link Interface}, per
 * `spec/11-modular-composition.md` requirement **MOD-001**.
 *
 * A subnet definition is the reusable unit of composition. It carries:
 * - A {@link name} (used as the originating-def label in `SubnetInstance` per [MOD-041]);
 * - A {@link body} — a structurally complete `PetriNet` per [CORE-040];
 * - An {@link iface} — the set of exposed ports and channels per [MOD-003] / [MOD-005].
 *
 * `SubnetDef` is the open variant of the {@link Subnet} discriminated union
 * defined in `subnet.ts` per **MOD-002**.
 *
 * The {@link SubnetDef.fromNet} retrofit factory per **MOD-014** wraps an
 * existing closed `PetriNet` plus an `Interface` into an unparameterised
 * `SubnetDef<void>`, applying the same per-element validation as the
 * builder's `build()`.
 *
 * @typeParam P parameter type carried through to `Instance.params`
 *               (use `void` for unparameterised subnets)
 */
export class SubnetDef<P = void> {
  readonly name: string;
  readonly body: PetriNet;
  readonly iface: Interface;

  /** @internal Use {@link SubnetDef.builder} or {@link SubnetDef.fromNet} to create instances. */
  constructor(key: symbol, name: string, body: PetriNet, iface: Interface) {
    if (key !== SUBNET_DEF_KEY) {
      throw new Error('Use SubnetDef.builder() or SubnetDef.fromNet() to create instances');
    }
    this.name = name;
    this.body = body;
    this.iface = iface;
  }

  /**
   * Produces a renamed module instance per **MOD-010**, **MOD-011**, **MOD-012**,
   * and **MOD-030**.
   *
   * The rename pass walks every place and transition of the body net,
   * substituting each name with `prefix + "/" + originalName`, and rebuilds
   * every arc with rewritten place references. Transition timing, priority,
   * and action are carried through by reference (action sharing per
   * [MOD-030]). The renamed body is itself a structurally valid `PetriNet`
   * per [CORE-040]; per-instance state isolation per [MOD-012] is a
   * structural consequence of distinct prefixed names.
   *
   * ## Prefix validation
   *
   * The `"/"` character is reserved as the prefix separator (per [MOD-010]).
   * User-supplied prefixes MUST NOT contain `"/"`; nested instantiation is
   * performed by the future `PetriNetBuilder.compose(...)` mechanism (per
   * [MOD-013]). A prefix containing `"/"` raises an `Error`.
   *
   * @param prefix the rename prefix (non-empty, must not contain `"/"`)
   * @param params the parameter value carried through to `Instance.params`
   *               (may be omitted when `P` is `void`)
   * @throws when `prefix` is empty or contains `"/"`
   */
  instantiate(prefix: string, params?: P): Instance<P> {
    validatePrefix(prefix);

    // Allocate the two remap maps. The rewriter fills them as side effects so
    // we can resolve interface place/transition references afterward. Maps
    // are keyed by ORIGINAL name strings (TypeScript Place identity is
    // name-based per `runtime/compiled-net.ts`).
    const placeRemap = new Map<string, Place<unknown>>();
    const transitionRemap = new Map<string, Transition>();

    const renamedBody = renameNet(this.body, prefix, placeRemap, transitionRemap);

    // Resolve port handles: original-port-name -> renamed body place.
    const portHandles = new Map<string, Place<unknown>>();
    for (const port of this.iface.ports.values()) {
      const renamed = placeRemap.get(port.place.name);
      if (renamed === undefined) {
        // Defensive: should be impossible because MOD-006 validation at
        // SubnetDef.builder.build() guarantees port.place is in the body.
        throw new Error(
          `Port '${port.name}' references place '${port.place.name}' that was not found ` +
          `in the renamed body. This indicates a SubnetDef invariant violation.`,
        );
      }
      portHandles.set(port.name, renamed);
    }

    // Resolve channel handles: original-channel-name -> renamed body transition.
    const channelHandles = new Map<string, Transition>();
    for (const channel of this.iface.channels.values()) {
      const renamed = transitionRemap.get(channel.transition.name);
      if (renamed === undefined) {
        throw new Error(
          `Channel '${channel.name}' references transition '${channel.transition.name}' that was not found ` +
          `in the renamed body. This indicates a SubnetDef invariant violation.`,
        );
      }
      channelHandles.set(channel.name, renamed);
    }

    return __createInstance<P>(
      prefix,
      this,
      renamedBody,
      portHandles,
      channelHandles,
      params as P,
    );
  }

  /**
   * Verifies safety properties of this subnet definition **in isolation** per
   * **MOD-051**, by wrapping it in a synthetic enclosing net where each input
   * port is fed by an {@link EnvironmentPlace} (token-source per the harness
   * generator) and each output port is observed via a synthetic place. The
   * standard {@link SmtVerifier} (per [MOD-050]) is invoked once per property
   * declared in the harness; the resulting per-property outcomes are
   * aggregated into a {@link VerificationResult}.
   *
   * ## Synthetic-net construction
   *
   * The synthetic enclosing net is built by:
   * 1. Instantiating this `SubnetDef` with the prefix `"sut"` (system-under-test)
   *    and `harness.params`.
   * 2. For each input or in-out port on the interface, looking up the
   *    harness generator by port name, allocating a synthetic
   *    {@link Place}`<unknown>` of the same conceptual token type as the
   *    port, wrapping it in an {@link EnvironmentPlace}, and binding the
   *    port to that synthetic place via
   *    {@link import('./petri-net.js').PetriNetBuilder.compose}. The supplier
   *    is invoked once at construction time to materialize the seed token —
   *    its presence is what bounds the input behavior under analysis. **If
   *    the harness map is missing a generator for a required input or in-out
   *    port, an `Error` is thrown.**
   * 3. For each output or in-out port, allocating a synthetic observation
   *    {@link Place}`<unknown>` and binding the port to it via the same
   *    `compose(...)` call. The verifier inspects this place's reachability
   *    / marking through the standard property APIs ({@link SmtProperty}).
   * 4. Building the resulting flat {@link PetriNet} per [MOD-023] (the
   *    verifier is composition-unaware per [MOD-050]).
   *
   * ## Per-property invocation
   *
   * Each {@link SmtProperty} in the harness is verified independently against
   * the same synthetic net. The synthetic environment places are passed
   * through to the verifier so that places driven by the harness generators
   * are treated under the verifier's environment-analysis semantics rather
   * than as ordinary sink places.
   *
   * @param harness the verification harness — supplies parameters, input-port
   *                token generators, and the property set
   * @returns a {@link VerificationResult} aggregating per-property
   *          {@link SmtVerificationResult}s
   * @throws when an input or in-out port is missing a harness generator
   */
  async verify(
    harness: VerificationHarness<P>,
    /**
     * How injection into the synthetic environment places is modeled (VER-006,
     * MOD-051 AC3).
     *
     * The synthetic net has environment places by construction, so this decides what a
     * verdict means. The default over-approximates: a `proven` under
     * `alwaysAvailable()` holds for any environment. Pass `bounded(k)` to prove a
     * property that holds only when the environment injects at most `k` tokens.
     * `ignore()` is accepted but cannot yield `proven` — VER-006 refuses to certify a
     * proof that holds only because injection was never modeled.
     */
    environmentMode: EnvironmentAnalysisMode = alwaysAvailable(),
  ): Promise<VerificationResult> {
    if (harness === null || harness === undefined) {
      throw new Error('SubnetDef.verify: harness must not be null/undefined');
    }

    // Step 1: instantiate this SubnetDef under the "sut" prefix. Uses an
    // underscore in the synthetic enclosing net's name to avoid colliding
    // with the "/" prefix separator (matches Java).
    const sut = this.instantiate('sut', harness.params);

    // Normalise the harness's generator map / property collection up front so
    // we can check membership and iterate deterministically below.
    const generators = normaliseGenerators(harness.portInputGenerators);
    const properties = normaliseProperties(harness.properties);

    // Step 2: allocate synthetic harness places per port direction. Track
    // the environment places (one per input/inout port) for the SmtVerifier
    // so the verifier knows to treat their underlying places as boundary
    // places rather than ordinary internals.
    const envPlaces: EnvironmentPlace<unknown>[] = [];
    const portMappings = new Map<string, Place<unknown>>();

    for (const port of this.iface.ports.values()) {
      const portName = port.name;

      switch (port.direction) {
        case 'input': {
          const generator = generators.get(portName);
          if (generator === undefined) {
            throw new Error(
              `verify: harness is missing an input generator for port '${portName}' ` +
              `on subnet '${this.name}' (MOD-051)`,
            );
          }
          // Touch the supplier to surface user-supplied errors at synthetic-
          // net construction time rather than at verification time. Mirrors
          // Java's Objects.requireNonNull(generator.get(), ...).
          const seed = generator();
          if (seed === null || seed === undefined) {
            throw new Error(
              `verify: input generator for port '${portName}' on subnet ` +
              `'${this.name}' produced null/undefined`,
            );
          }
          const synth = makePlace<unknown>(`harness_in_${portName}`);
          envPlaces.push(environmentPlace<unknown>(synth.name));
          portMappings.set(portName, synth);
          break;
        }
        case 'output': {
          const synth = makePlace<unknown>(`harness_out_${portName}`);
          portMappings.set(portName, synth);
          break;
        }
        case 'inout': {
          const generator = generators.get(portName);
          if (generator === undefined) {
            throw new Error(
              `verify: harness is missing an input generator for in-out port ` +
              `'${portName}' on subnet '${this.name}' (MOD-051)`,
            );
          }
          const seed = generator();
          if (seed === null || seed === undefined) {
            throw new Error(
              `verify: input generator for in-out port '${portName}' on subnet ` +
              `'${this.name}' produced null/undefined`,
            );
          }
          const synth = makePlace<unknown>(`harness_io_${portName}`);
          envPlaces.push(environmentPlace<unknown>(synth.name));
          portMappings.set(portName, synth);
          break;
        }
      }
    }

    // Step 3: build the synthetic enclosing net. Channels declared on the
    // interface (but not bound here) flow through as ordinary renamed
    // transitions per MOD-021. The `verify_` prefix uses an underscore (not
    // `/`) so the enclosing-net name does not collide with the prefix
    // separator reserved by [MOD-010].
    const syntheticNet = PetriNetClass.builder('verify_' + this.name)
      .compose(sut as Instance<unknown>, portMappings)
      .build();

    // CORE-043, checked here rather than left to SmtVerifier so an empty property set
    // cannot skip it.
    requireOutputProducingActions(syntheticNet);

    // Step 4: invoke the SmtVerifier once per property and aggregate
    // results. Iteration order matches the harness's property collection
    // for deterministic per-property reporting.
    const perProperty = new Map<SmtProperty, SmtVerificationResult>();
    for (const property of properties) {
      // Set explicitly rather than inherited: the synthetic env places are the
      // harness's own, so how injection is modelled is the harness's call
      // ([MOD-051] AC3), not the verifier default's. Under ignore() [VER-006]
      // downgrades every proof about a net with env places to Unknown, so a
      // subnet with an input port could never be proven.
      const verifier = SmtVerifier.forNet(syntheticNet).property(property);
      if (envPlaces.length > 0) {
        verifier.environmentPlaces(...envPlaces);
        verifier.environmentMode(environmentMode);
      }
      const result = await verifier.verify();
      perProperty.set(property, result);
    }

    return buildVerificationResult(syntheticNet, perProperty);
  }

  // ============================================================
  //  Static factories
  // ============================================================

  static builder<P = void>(name: string): SubnetDefBuilder<P> {
    return new SubnetDefBuilder<P>(name);
  }

  /**
   * Retrofit utility per **MOD-014**: wraps an existing closed {@link PetriNet}
   * plus an {@link Interface} into an unparameterised `SubnetDef<void>`.
   *
   * Validation per **MOD-014** / **MOD-006** is enforced before the result is
   * constructed:
   * - Every port's underlying `Place` must be present in `net.places`.
   * - Every channel's underlying `Transition` must be present in `net.transitions`.
   * - Port and channel name uniqueness is re-validated defensively (the
   *   `Interface` builder already enforces this; hand-built `Interface`
   *   values bypass that path).
   *
   * The resulting subnet definition is unparameterised (parameter type is `void`).
   *
   * @throws when a port place is not in `net.places`, a channel transition is
   *         not in `net.transitions`, or port/channel names are not unique.
   */
  static fromNet(net: PetriNet, iface: Interface): SubnetDef<void> {
    const bodyPlaces = net.places;
    const bodyTransitions = net.transitions;

    // Re-validate port-name uniqueness (defence in depth — InterfaceBuilder
    // enforces it for the builder route, but a hand-built `Interface`
    // bypasses that path; SubnetDef.fromNet is the documented retrofit
    // entry point so we re-check here to keep failures crisp). Note: do NOT
    // use `Set#add`'s return value — `Set#add` returns the Set itself
    // (truthy) and cannot signal "already present"; check with `has` first.
    const seenPortNames = new Set<string>();
    for (const port of iface.ports.values()) {
      if (seenPortNames.has(port.name)) {
        throw new Error(
          `fromNet: duplicate port name '${port.name}' on interface for net '${net.name}' (MOD-006)`,
        );
      }
      seenPortNames.add(port.name);
      if (!bodyPlaces.has(port.place as Place<unknown>)) {
        throw new Error(
          `fromNet: port '${port.name}' references place '${port.place.name}' which is not in net '${net.name}' (MOD-014/MOD-006)`,
        );
      }
    }

    // Re-validate channel-name uniqueness and transition membership.
    const seenChannelNames = new Set<string>();
    for (const channel of iface.channels.values()) {
      if (seenChannelNames.has(channel.name)) {
        throw new Error(
          `fromNet: duplicate channel name '${channel.name}' on interface for net '${net.name}' (MOD-006)`,
        );
      }
      seenChannelNames.add(channel.name);
      if (!bodyTransitions.has(channel.transition)) {
        throw new Error(
          `fromNet: channel '${channel.name}' references transition '${channel.transition.name}' which is not in net '${net.name}' (MOD-014/MOD-006)`,
        );
      }
    }

    return new SubnetDef<void>(SUBNET_DEF_KEY, net.name, net, iface);
  }
}

/**
 * Fluent builder for {@link SubnetDef}.
 *
 * Validation per **MOD-006** is enforced at {@link build}:
 * - Every port's underlying place must be in the body net.
 * - Every channel's underlying transition must be in the body net.
 * - Port names must be unique within the port namespace.
 * - Channel names must be unique within the channel namespace.
 */
export class SubnetDefBuilder<P = void> {
  private readonly _name: string;
  private readonly _bodyBuilder: ReturnType<typeof PetriNetClass.builder>;
  private readonly _ports: Port<unknown>[] = [];
  private readonly _channels: Channel[] = [];

  constructor(name: string) {
    this._name = name;
    this._bodyBuilder = PetriNetClass.builder(name);
  }

  // -------- body construction (delegates to PetriNet.Builder) --------

  transition(transition: Transition): this {
    this._bodyBuilder.transition(transition);
    return this;
  }

  transitions(...transitions: Transition[]): this {
    this._bodyBuilder.transitions(...transitions);
    return this;
  }

  place<T>(place: Place<T>): this {
    this._bodyBuilder.place(place);
    return this;
  }

  // -------- interface declarations --------

  inputPort<T>(name: string, place: Place<T>): this {
    this._ports.push({ name, direction: 'input', place: place as Place<unknown> });
    return this;
  }

  outputPort<T>(name: string, place: Place<T>): this {
    this._ports.push({ name, direction: 'output', place: place as Place<unknown> });
    return this;
  }

  inoutPort<T>(name: string, place: Place<T>): this {
    this._ports.push({ name, direction: 'inout', place: place as Place<unknown> });
    return this;
  }

  channel(name: string, transition: Transition): this {
    this._channels.push({ name, transition });
    return this;
  }

  // -------- build & validate (MOD-006) --------

  build(): SubnetDef<P> {
    const built = this._bodyBuilder.build();
    const bodyPlaces = built.places;
    const bodyTransitions = built.transitions;

    // 1. Validate port-name uniqueness (MOD-006). Note: do NOT use
    // `Set#add`'s return value — it returns the Set itself (truthy) and
    // cannot signal "already present"; check with `has` first.
    const portNames = new Set<string>();
    for (const port of this._ports) {
      if (portNames.has(port.name)) {
        throw new Error(`Subnet '${this._name}': duplicate port name '${port.name}'`);
      }
      portNames.add(port.name);
      // 2. Validate port place membership (MOD-006).
      if (!bodyPlaces.has(port.place as Place<unknown>)) {
        throw new Error(
          `Subnet '${this._name}': port '${port.name}' references place '${port.place.name}' which is not in the body`,
        );
      }
    }

    // 3. Validate channel-name uniqueness and transition membership (MOD-006).
    const channelNames = new Set<string>();
    for (const channel of this._channels) {
      if (channelNames.has(channel.name)) {
        throw new Error(`Subnet '${this._name}': duplicate channel name '${channel.name}'`);
      }
      channelNames.add(channel.name);
      if (!bodyTransitions.has(channel.transition)) {
        throw new Error(
          `Subnet '${this._name}': channel '${channel.name}' references transition '${channel.transition.name}' which is not in the body`,
        );
      }
    }

    const ifaceBuilder = Interface.builder();
    ifaceBuilder.portsAll(this._ports);
    ifaceBuilder.channelsAll(this._channels);
    const iface = ifaceBuilder.build();

    return new SubnetDef<P>(SUBNET_DEF_KEY, this._name, built, iface);
  }
}

/**
 * @internal Validates the prefix supplied to {@link SubnetDef.instantiate}
 * per **MOD-010**:
 * - non-empty;
 * - no `"/"` (reserved as the prefix separator; nested instantiation is
 *   performed by `PetriNetBuilder.compose(...)` per [MOD-013]).
 *
 * Throws an `Error` with a descriptive message on failure.
 */
function validatePrefix(prefix: string): void {
  if (typeof prefix !== 'string' || prefix.length === 0) {
    throw new Error('SubnetDef.instantiate: prefix must be a non-empty string');
  }
  if (prefix.indexOf('/') >= 0) {
    throw new Error(
      `SubnetDef.instantiate: prefix must not contain '/' (reserved as the prefix ` +
      `separator per MOD-010); use compose(...) for nested instantiation. Got: '${prefix}'`,
    );
  }
}
