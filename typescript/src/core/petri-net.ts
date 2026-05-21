import type { Place } from './place.js';
import type { TransitionAction } from './transition-action.js';
import { passthrough } from './transition-action.js';
import { Transition } from './transition.js';
import type { Instance } from './instance.js';
import { SubnetDef } from './subnet-def.js';
import { ComposeBindings, __createComposeBindings } from './compose-bindings.js';
import { applyFusion, mergeTransitions, substitutePlaces } from './internal/subnet-rewriter.js';
import { FusionSet, FusionSetBuilder } from './fusion-set.js';

/** @internal Symbol key restricting construction to the builder and bindActions. */
const PETRI_NET_KEY = Symbol('PetriNet.internal');

/**
 * Immutable definition of a Time Petri Net structure.
 *
 * A PetriNet is a reusable definition that can be executed multiple times
 * with different initial markings. Places are auto-collected from transitions.
 */
export class PetriNet {
  readonly name: string;
  readonly places: ReadonlySet<Place<any>>;
  readonly transitions: ReadonlySet<Transition>;

  /**
   * Subnet-membership metadata per **MOD-026**: maps each node name (place or
   * transition) contributed by exactly one directly-composed subnet to that
   * subnet's name. Shared places contributed by two or more subnets, and every
   * node of a net not built via {@link PetriNetBuilder.compose}`(SubnetDef)`,
   * are absent. Never null — an empty map when there is no metadata. The DOT
   * exporter renders `subgraph cluster_*` blocks from this map.
   *
   * V8 `Map` is insertion-ordered, preserving compose order so cluster
   * subgraphs render deterministically (cross-language byte-parity).
   */
  readonly subnetMembership: ReadonlyMap<string, string>;

  /** @internal Use {@link PetriNet.builder} to create instances. */
  constructor(
    key: symbol,
    name: string,
    places: ReadonlySet<Place<any>>,
    transitions: ReadonlySet<Transition>,
    subnetMembership: ReadonlyMap<string, string> = new Map(),
  ) {
    if (key !== PETRI_NET_KEY) throw new Error('Use PetriNet.builder() to create instances');
    this.name = name;
    this.places = places;
    this.transitions = transitions;
    this.subnetMembership = subnetMembership;
  }

  /**
   * Creates a new PetriNet with actions bound to transitions by name.
   * Unbound transitions keep passthrough action.
   */
  bindActions(actionBindings: Map<string, TransitionAction> | Record<string, TransitionAction>): PetriNet {
    const bindings = actionBindings instanceof Map
      ? actionBindings
      : new Map(Object.entries(actionBindings));

    return this.bindActionsWithResolver(
      (name) => bindings.get(name) ?? passthrough(),
    );
  }

  /**
   * Creates a new PetriNet with actions bound via a resolver function.
   */
  bindActionsWithResolver(actionResolver: (name: string) => TransitionAction): PetriNet {
    const boundTransitions = new Set<Transition>();
    for (const t of this.transitions) {
      const action = actionResolver(t.name);
      if (action !== null && action !== t.action) {
        boundTransitions.add(rebuildWithAction(t, action));
      } else {
        boundTransitions.add(t);
      }
    }
    // MOD-026: bindActions rebuilds transitions but preserves their names, so
    // name-keyed membership metadata survives a session bind unchanged.
    return new PetriNet(PETRI_NET_KEY, this.name, this.places, boundTransitions,
      this.subnetMembership);
  }

  static builder(name: string): PetriNetBuilder {
    return new PetriNetBuilder(name);
  }
}

export class PetriNetBuilder {
  private readonly _name: string;
  private readonly _places = new Set<Place<any>>();
  private readonly _transitions = new Set<Transition>();
  private readonly _fusionSets: FusionSet[] = [];
  // MOD-026: node name -> set of subnet names that contributed it via
  // compose(SubnetDef), in first-contribution order. Resolved to single-owner
  // membership at build(). V8 Map/Set iterate in insertion order, preserving
  // compose order for cross-language byte-parity.
  private readonly _subnetContributions = new Map<string, Set<string>>();

  constructor(name: string) {
    this._name = name;
  }

  /** Add an explicit place. */
  place(place: Place<any>): this {
    this._places.add(place);
    return this;
  }

  /** Add explicit places. */
  places(...places: Place<any>[]): this {
    for (const p of places) this._places.add(p);
    return this;
  }

  /** Add a transition (auto-collects places from arcs). */
  transition(transition: Transition): this {
    this._transitions.add(transition);
    for (const spec of transition.inputSpecs) {
      this._places.add(spec.place);
    }
    for (const p of transition.outputPlaces()) {
      this._places.add(p);
    }
    for (const inh of transition.inhibitors) {
      this._places.add(inh.place);
    }
    for (const r of transition.reads) {
      this._places.add(r.place);
    }
    for (const r of transition.resets) {
      this._places.add(r.place);
    }
    return this;
  }

  /** Add transitions (auto-collects places from arcs). */
  transitions(...transitions: Transition[]): this {
    for (const t of transitions) this.transition(t);
    return this;
  }

  /**
   * Composes a subnet {@link Instance} into this builder per **MOD-020**
   * (composition operation), **MOD-021** (channel composition), **MOD-022**
   * (type compatibility), and **MOD-023** (composition produces a flat net).
   *
   * Two overloads are supported:
   *
   * 1. **Map / Record overload** — the runtime-checked form. Pass a
   *    `Map<string, Place<unknown>>` or a `Record<string, Place<unknown>>`
   *    keyed by the subnet's **original** (pre-prefix) port names. No
   *    channel bindings are recorded by this overload.
   *
   * 2. **Callback overload** — the typed form. Pass a callback receiving a
   *    fresh {@link ComposeBindings}; register port bindings via
   *    `bindings.bindPort<T>(name, place)` so TypeScript checks each
   *    binding's token type at compile time per [MOD-022]. Synchronous
   *    channels may be merged with caller-side transitions via
   *    `bindings.bindChannel(name, t)` per [MOD-021].
   *
   * For each port binding `(portName -> callerPlace)`, the instance's
   * renamed port place is substituted with the caller place at every arc
   * in the instance's renamed body via the `subnet-rewriter` module.
   * Internal (non-port) places of the instance flow through with their
   * prefixed names. Composition is **eager** — the rewrite happens here,
   * not at `build()` (per [MOD-020] AC #5).
   *
   * For each channel binding `(channelName -> callerTransition)`, the
   * instance's renamed channel transition and the caller-side transition
   * are merged into one transition in the resulting flat net per [MOD-021].
   * If the caller-side transition has not been added to this builder yet,
   * it is added implicitly during the merge step.
   *
   * @throws when a port name is unknown on the instance's interface, when a
   *         channel name is unknown on the interface, or when caller- and
   *         instance-side transition timings conflict (per [MOD-021]).
   */
  compose(instance: Instance<unknown>): this;
  compose(
    instance: Instance<unknown>,
    portMappings: ReadonlyMap<string, Place<unknown>> | Record<string, Place<unknown>>,
  ): this;
  compose(
    instance: Instance<unknown>,
    bind: (b: ComposeBindings) => void,
  ): this;
  compose(def: SubnetDef<unknown>): this;
  compose(
    instanceOrDef: Instance<unknown> | SubnetDef<unknown>,
    arg?:
      | ReadonlyMap<string, Place<unknown>>
      | Record<string, Place<unknown>>
      | ((b: ComposeBindings) => void),
  ): this {
    if (instanceOrDef instanceof SubnetDef) {
      return this.composeDirect(instanceOrDef);
    }
    const instance = instanceOrDef;
    if (arg === undefined) {
      return this.composeAuto(instance);
    }
    if (typeof arg === 'function') {
      const bindings = __createComposeBindings();
      arg(bindings);
      return this.composeInternal(instance, bindings.portBindings(), bindings.channelBindings());
    }

    const portMappings: ReadonlyMap<string, Place<unknown>> =
      arg instanceof Map ? arg : new Map(Object.entries(arg));
    return this.composeInternal(instance, portMappings, new Map());
  }

  /**
   * Composes a subnet {@link SubnetDef} **directly** into this builder per
   * **MOD-025** — **without instantiation**, and without the prefix-renaming
   * of {@link SubnetDef.instantiate}.
   *
   * Every body place and transition is added under its **original**
   * (un-prefixed) name. Places merge into this builder by name: a body place
   * whose name equals an enclosing-net place *is* that place in the composed
   * flat net. This is the mode for wiring a subnet in as a single shared copy.
   *
   * Direct composition is **order-independent**: composing the same set of
   * subnets in any order yields the same flat net, because merging is by
   * place name and not by a probe of the builder's place set at call time —
   * contrast the no-interface body-inference branch of {@link composeAuto}
   * (MOD-024), which is order-sensitive.
   *
   * For multiple *independent* copies — each with isolated per-instance state
   * per [MOD-012] — use {@link SubnetDef.instantiate} + the `compose(instance)`
   * overload instead.
   *
   * Rejections: a body transition whose name already exists in this builder
   * (use `instantiate(prefix)` for independent copies); a subnet whose
   * interface declares any channel (direct composition does not bind
   * channels — use `instantiate` + the channel-binding `compose` overload).
   *
   * Token-type conflicts on a same-named place cannot be detected: TS
   * {@link Place} equality is name-only at runtime (the documented carve-out,
   * same as MOD-024).
   *
   * @throws when the subnet declares channels, or a body transition name
   *         collides with a transition already in this builder.
   */
  private composeDirect(def: SubnetDef<unknown>): this {
    const iface = def.iface;

    // MOD-025: direct composition does not bind channels.
    if (iface.channels.size > 0) {
      const channelNames: string[] = [];
      for (const c of iface.channels.values()) channelNames.push(c.name);
      channelNames.sort();
      throw new Error(
        `compose(SubnetDef): subnet '${def.name}' declares channels ` +
        `[${channelNames.join(', ')}]; direct composition does not bind channels.` +
        ` Use def.instantiate(prefix) + compose(instance, bind => bind.bindChannel(...)).`,
      );
    }

    const body = def.body;

    // MOD-025: a body transition whose name already exists here is almost
    // always a mistake — instantiate(prefix) is the multi-copy path.
    const hostTransitionNames = new Set<string>();
    for (const t of this._transitions) hostTransitionNames.add(t.name);
    for (const t of body.transitions) {
      if (hostTransitionNames.has(t.name)) {
        throw new Error(
          `compose(SubnetDef): transition '${t.name}' from subnet '${def.name}' ` +
          `collides with a transition already in net '${this._name}'. Direct ` +
          `composition merges by name; for independent copies use ` +
          `def.instantiate(prefix) + compose(instance).`,
        );
      }
    }

    // Canonicalize place references. TS `Set<Place>` dedups by reference, so
    // a body place value-equal-by-name to a host place must be funnelled
    // through the single host reference (same intent as composeAuto). Body
    // places with a new name are canonical as themselves; arcs referencing
    // them are left untouched by substitutePlaces.
    const hostByName = new Map<string, Place<unknown>>();
    for (const p of this._places) hostByName.set(p.name, p);

    // MOD-026: record which subnet each node came from so cluster-aware DOT
    // export can reconstruct subgraphs without prefix names. The subnet name
    // is sanitised of '/' so it never triggers spurious nested-cluster
    // splitting in the exporter.
    const subnetName = def.name.replace(/\//g, '_');

    const mergeMap = new Map<string, Place<unknown>>();
    for (const p of body.places) {
      const host = hostByName.get(p.name);
      this.place(host ?? p);
      if (host !== undefined) mergeMap.set(p.name, host);
      this.recordContribution(p.name, subnetName);
    }
    for (const t of body.transitions) {
      this.transition(substitutePlaces(t, mergeMap));
      this.recordContribution(t.name, subnetName);
    }
    return this;
  }

  /** @internal MOD-026: records a node as contributed by the named subnet. */
  private recordContribution(nodeName: string, subnetName: string): void {
    let owners = this._subnetContributions.get(nodeName);
    if (owners === undefined) {
      owners = new Set<string>();
      this._subnetContributions.set(nodeName, owners);
    }
    owners.add(subnetName);
  }

  /**
   * Identity-default auto-compose per **MOD-024**.
   *
   * Each declared interface port auto-binds to its own `port.place` — the
   * Place the SubnetDef builder declared via `.inputPort(name, hostPlace)`
   * (or `outputPort` / `inoutPort`). If the host builder already declares
   * the equal place, the two merge; if not, the place arrives implicitly
   * via the rewritten transitions' arcs (same flow as explicit `bindPort`).
   *
   * If the subnet declares no interface ports at all, body places are
   * checked against this builder's place set **by name** (matching the
   * existing TS Place equality semantics; see [CORE-002] note in
   * `spec/11-modular-composition.md` MOD-024). Body places that don't match
   * stay private under their prefixed names per [MOD-010].
   *
   * Channels are NOT auto-bound — transition identity is too delicate for
   * inference. If the subnet declares any channel, this overload throws.
   */
  private composeAuto(instance: Instance<unknown>): this {
    const iface = instance.def.iface;

    if (iface.channels.size > 0) {
      const channelNames: string[] = [];
      for (const c of iface.channels.values()) channelNames.push(c.name);
      channelNames.sort();
      throw new Error(
        `compose(Instance): subnet '${instance.def.name}' ` +
        `(instance prefix '${instance.prefix}') declares channels [${channelNames.join(', ')}]` +
        `; auto-compose does not bind channels.` +
        ` Use compose(instance, bind => bind.bindChannel(...)) with explicit channel bindings.`,
      );
    }

    // Pre-index host places by name. The TS `_places: Set<Place>` dedupes
    // by reference (Place is an interface with only `name`), so when the
    // host pre-declared a Place object that is value-equal-by-name but a
    // different reference from the SubnetDef port's carried place, we
    // prefer the host reference: arc rewriting funnels through it and the
    // port's own Place object never enters `_places`. Same intent as
    // Rust's `place_index.get(&probe).cloned().unwrap_or(probe)` and
    // Java's record-equality `places.contains(probe)` in this branch.
    const hostByName = new Map<string, Place<unknown>>();
    for (const p of this._places) hostByName.set(p.name, p);

    if (iface.ports.size > 0) {
      // Explicit interface: each declared port auto-binds to its own
      // declared place. The SubnetDef's inputPort/outputPort/inoutPort
      // statement IS the host wiring — trust it. When a host place with
      // the same name already exists, use the host reference so the
      // merged net has a single Place per name.
      const portMappings = new Map<string, Place<unknown>>();
      for (const port of iface.ports.values()) {
        const hostMatch = hostByName.get(port.place.name);
        portMappings.set(port.name, hostMatch ?? port.place);
      }
      return this.composeInternal(instance, portMappings, new Map());
    }

    // No declared interface — infer the merge set from body places that
    // also exist on the host builder (matched by name). Build the
    // renamed-name -> host-place map directly and apply the composition.

    const mergeMap = new Map<string, Place<unknown>>();
    const prefix = instance.prefix + '/';
    for (const renamed of instance.renamedBody.places) {
      if (!renamed.name.startsWith(prefix)) continue;
      const originalName = renamed.name.substring(prefix.length);
      const hostMatch = hostByName.get(originalName);
      if (hostMatch !== undefined) {
        mergeMap.set(renamed.name, hostMatch);
      }
    }
    return this.applyComposition(instance, mergeMap, new Map());
  }

  /**
   * @internal Shared compose implementation: validates port and channel
   * bindings, builds the place-substitution map, walks every renamed-body
   * transition through {@link substitutePlaces}, applies channel merges per
   * [MOD-021], and adds the resulting transitions to this builder.
   *
   * ## Channel-merge flow ([MOD-021])
   *
   * 1. Collect rewritten instance transitions into a working `Map<string,
   *    Transition>` keyed by prefixed transition name (deferred — not yet
   *    added to the builder's transition set).
   * 2. For each channel binding, resolve the renamed instance-side
   *    transition through `instance.channel(channelName)`, then look up its
   *    rewritten counterpart in the working map by name.
   * 3. Replace the working-map entry with a {@link mergeTransitions} result
   *    that fuses caller-side + instance-side; remove the rewritten
   *    instance-side entry. Also replace (or add) the caller-side
   *    transition in this builder's transition set with the same merged
   *    result, indexed under the caller's name slot.
   * 4. Add the surviving (un-merged) entries to this builder.
   *
   * The deferral matters: writing the rewritten instance transitions to the
   * builder eagerly would force a second "remove-then-replace" pass to
   * apply the channel merges, complicating the place-collection invariants.
   * Collecting first and merging second keeps the builder's transition set
   * finalized exactly once.
   *
   * Keying the working map by prefixed transition name (rather than by
   * Transition reference) is also robust against a prior
   * {@link Instance.bindActions} call that may have rebuilt the renamed-body
   * transitions, breaking identity equality between the body and the
   * channel-handle map — but the prefixed names remain stable.
   */
  private composeInternal(
    instance: Instance<unknown>,
    portMappings: ReadonlyMap<string, Place<unknown>>,
    channelBindings: ReadonlyMap<string, Transition>,
  ): this {
    const iface = instance.def.iface;

    // Build mergeMap: keyed by RENAMED instance-side place name -> caller
    // place. The subnet-rewriter resolves arc-place references by name
    // (matching TS Place identity model: name-based equality per
    // runtime/compiled-net.ts), so we key by the renamed name.
    const mergeMap = new Map<string, Place<unknown>>();

    for (const [portName, callerPlace] of portMappings) {
      const port = iface.port(portName);
      if (port === undefined) {
        const knownPorts: string[] = [];
        for (const p of iface.ports.values()) knownPorts.push(p.name);
        throw new Error(
          `compose: no port named '${portName}' on subnet '${instance.def.name}' ` +
          `(instance prefix '${instance.prefix}'). Known ports: [${knownPorts.join(', ')}]`,
        );
      }

      // Resolve the renamed instance-side place via the typed accessor;
      // this gives us the rewritten Place<unknown> in the instance body.
      const ifacePlace = instance.port<unknown>(portName);
      mergeMap.set(ifacePlace.name, callerPlace);
    }

    return this.applyComposition(instance, mergeMap, channelBindings);
  }

  /**
   * Shared post-mergeMap pipeline: rewrites renamed-body transitions
   * through `mergeMap`, applies channel merges per **MOD-021**, and adds
   * the surviving transitions to the builder.
   *
   * Used by both the explicit-binding path (`composeInternal`) and the
   * auto-compose path (`composeAuto` per **MOD-024**). The two paths differ
   * only in how the (renamed Place name → host Place) `mergeMap` is built.
   */
  private applyComposition(
    instance: Instance<unknown>,
    mergeMap: Map<string, Place<unknown>>,
    channelBindings: ReadonlyMap<string, Transition>,
  ): this {
    const iface = instance.def.iface;

    // Step 1: Stage rewritten instance transitions in a working map keyed
    // by prefixed transition name. The substitutePlaces primitive keeps
    // the prefixed transition name unchanged (per MOD-010 — prefixed names
    // are already unique within the host) and rewrites only the arc place
    // references.
    const rewrittenByName = new Map<string, Transition>();
    for (const t of instance.renamedBody.transitions) {
      rewrittenByName.set(t.name, substitutePlaces(t, mergeMap));
    }

    // Step 2: Apply channel merges. For each binding, locate the rewritten
    // instance-side transition by name, fuse it with the caller-side
    // transition, and replace the working-map entry. Also replace the
    // caller-side transition in this builder's transition set with the
    // merged result (or add it if the caller did not pre-add it).
    for (const [channelName, callerTrans] of channelBindings) {
      // Resolve the renamed instance-side channel transition. instance.channel
      // throws on unknown name; we re-wrap with a more contextual message.
      let instanceRenamedChannel: Transition;
      try {
        instanceRenamedChannel = instance.channel(channelName);
      } catch (cause) {
        const knownChannels: string[] = [];
        for (const c of iface.channels.values()) knownChannels.push(c.name);
        const err = new Error(
          `compose: no channel named '${channelName}' on subnet '${instance.def.name}' ` +
          `(instance prefix '${instance.prefix}'). Known channels: [${knownChannels.join(', ')}]`,
        );
        // Preserve cause chain for diagnostics (Node 16.9+ supports the
        // standard Error cause option).
        (err as Error & { cause?: unknown }).cause = cause;
        throw err;
      }

      // Look up the rewritten (port-substituted) version of the renamed
      // channel transition by name.
      const rewrittenInstanceChannel = rewrittenByName.get(instanceRenamedChannel.name);
      if (rewrittenInstanceChannel === undefined) {
        // Defensive: SubnetDef.builder validation guarantees the channel's
        // transition is a member of the renamed body.
        /* istanbul ignore next */
        throw new Error(
          `compose: channel '${channelName}' resolved to a transition ` +
          `'${instanceRenamedChannel.name}' that is not present in the renamed body. ` +
          `This indicates a SubnetDef invariant violation.`,
        );
      }

      // Build the merged transition (caller-wins identity per MOD-021).
      const merged = mergeTransitions(callerTrans, rewrittenInstanceChannel, callerTrans.name);

      // Step 2a: Remove the rewritten instance-side transition from the
      // working map (it merges away — only the merged result remains under
      // the caller's transition slot in the builder).
      rewrittenByName.delete(instanceRenamedChannel.name);

      // Step 2b: Replace the caller-side transition (if present) in this
      // builder's transition set with the merged result. If the caller did
      // not pre-add it, simply add the merged transition — the user's
      // intent to use callerTrans is captured via the binding itself.
      this._transitions.delete(callerTrans);
      this.transition(merged);
    }

    // Step 3: Add the surviving (un-merged) rewritten transitions to the
    // builder. transition() auto-collects places — internal (non-merged)
    // renamed places are added under their prefixed names; caller places
    // already in the builder's place set get deduped via Place name.
    for (const rewritten of rewrittenByName.values()) {
      this.transition(rewritten);
    }

    return this;
  }

  /**
   * Registers one or more {@link FusionSet} declarations on this builder, per
   * **MOD-060** (fusion set declaration) and **MOD-061** (fusion resolution
   * at build).
   *
   * Fusion is **orthogonal to subnet composition**: fuse sets are accumulated
   * here and applied during {@link build} **after** all `compose(...)` calls
   * have flattened subnet instances into the builder's transition set.
   * Registration order is irrelevant to semantics — `fuse(set)` BEFORE
   * `compose(...)` and `fuse(set)` AFTER `compose(...)` both apply at the
   * same point in the build pipeline.
   *
   * ## Validation
   *
   * Cross-set overlap (a place appearing in two fusion sets) is detected at
   * {@link build} and reported as an `Error` naming the offending place and
   * both sets.
   *
   * Two overloads are supported:
   *
   * 1. **Spread overload** — pass one or more pre-built {@link FusionSet}
   *    values (e.g., from `FusionSet.of(...)` or
   *    `FusionSet.builder(...).build()`).
   * 2. **Sugar overload** — pass a callback receiving a fresh
   *    {@link FusionSetBuilder} named after the enclosing net; register
   *    members via `b.member(place)`. Equivalent to
   *    `FusionSet.builder('<netName>-fusion').<callback>.build()` followed by
   *    `fuse(...)` on the result.
   */
  fuse(...sets: FusionSet[]): this;
  fuse(declarer: (b: FusionSetBuilder) => void): this;
  fuse(...args: [(b: FusionSetBuilder) => void] | FusionSet[]): this {
    if (args.length === 1 && typeof args[0] === 'function') {
      const declarer = args[0] as (b: FusionSetBuilder) => void;
      const fb = FusionSet.builder(this._name + '-fusion');
      declarer(fb);
      this._fusionSets.push(fb.build());
      return this;
    }
    for (const s of args as FusionSet[]) {
      if (s === undefined || s === null) {
        throw new Error('fuse: fusion set must not be null');
      }
      this._fusionSets.push(s);
    }
    return this;
  }

  /**
   * Builds the immutable {@link PetriNet}, applying fusion resolution (per
   * **MOD-061**) AFTER all transition/composition accumulation:
   *
   * 1. Detect overlapping fusion sets — a single place declared in two sets
   *    is rejected with an `Error`.
   * 2. Build the `non-canonical → canonical` substitution map across all
   *    sets, keyed by non-canonical place name (matching the rewriter's
   *    Map<string, Place<unknown>> convention — TypeScript Place identity is
   *    name-based per `runtime/compiled-net.ts`).
   * 3. Walk every transition through {@link applyFusion} to rewrite arc place
   *    references.
   * 4. Re-derive the place set from the rewritten transitions plus any
   *    caller-declared standalone places, dropping non-canonical members.
   *    Caller-declared standalone places that happen to be non-canonical
   *    members are also dropped.
   *
   * If no fusion sets were registered, the build is the trivial
   * `new PetriNet(...)` — the fusion machinery has no per-build cost when
   * unused.
   *
   * @throws when two fusion sets share a place
   */
  build(): PetriNet {
    const membership = this.resolveSubnetMembership();
    if (this._fusionSets.length === 0) {
      return new PetriNet(PETRI_NET_KEY, this._name, this._places, this._transitions,
        membership);
    }
    return this.buildWithFusion(membership);
  }

  /**
   * @internal Resolves the per-compose contributions recorded by
   * `composeDirect` into the final node-name → subnet-name membership map per
   * **MOD-026**. A node contributed by exactly one subnet maps to that subnet;
   * a place contributed by two or more subnets is a shared rendezvous place
   * and is omitted (it renders top-level, outside any cluster). Returns an
   * empty map — the common case — when no subnet was composed directly.
   */
  private resolveSubnetMembership(): Map<string, string> {
    const resolved = new Map<string, string>();
    for (const [nodeName, owners] of this._subnetContributions) {
      if (owners.size === 1) {
        resolved.set(nodeName, owners.values().next().value as string);
      }
    }
    return resolved;
  }

  /**
   * @internal Drops membership entries for places removed by fusion: a
   * non-canonical fused member no longer exists in the net, so its
   * `node-name → subnet` entry would dangle. The surviving canonical place
   * keeps its own entry. Per **MOD-026**.
   */
  private static filterFusedMembership(
    membership: Map<string, string>,
    nonCanonicalNames: ReadonlySet<string>,
  ): Map<string, string> {
    if (membership.size === 0 || nonCanonicalNames.size === 0) {
      return membership;
    }
    const filtered = new Map<string, string>();
    for (const [key, value] of membership) {
      if (!nonCanonicalNames.has(key)) {
        filtered.set(key, value);
      }
    }
    return filtered;
  }

  /**
   * @internal Fusion-resolution pass per **MOD-061**. Split out from
   * {@link build} so the no-fusion fast path stays trivial.
   */
  private buildWithFusion(membership: Map<string, string>): PetriNet {
    // Step 1: detect overlap. The same place name MUST NOT appear in more
    // than one fusion set (TypeScript Place identity is name-based per
    // `runtime/compiled-net.ts`).
    const ownership = new Map<string, FusionSet>();
    for (const set of this._fusionSets) {
      for (const member of set.members) {
        const prior = ownership.get(member.name);
        if (prior !== undefined && prior !== set) {
          throw new Error(
            `Fusion overlap: place '${member.name}' appears in two fusion sets ` +
              `('${prior.name}' and '${set.name}'). A place may appear in at most ` +
              `one fusion set (MOD-060).`,
          );
        }
        ownership.set(member.name, set);
      }
    }

    // Step 2: build the non-canonical-name → canonical-place substitution
    // map. Single-member sets contribute nothing (no non-canonical members),
    // so the map is naturally empty for the degenerate case.
    const fusionMap = new Map<string, Place<unknown>>();
    const nonCanonicalNames = new Set<string>();
    for (const set of this._fusionSets) {
      const canonical = set.canonical;
      for (const nc of set.nonCanonical()) {
        fusionMap.set(nc.name, canonical);
        nonCanonicalNames.add(nc.name);
      }
    }

    // Step 3: rewrite every transition's arcs through the fusion map.
    // applyFusion always returns a fresh set; if fusionMap is empty (single-
    // member-only sets) the rewrite is structurally a no-op but still rebuilds
    // Transition records — no observable difference.
    const rewrittenTransitions = applyFusion(this._transitions, fusionMap);

    // Step 4: re-derive the place set. Strategy: start from the current
    // place set, drop every non-canonical member (they are gone from the
    // net), then union in the places auto-discovered from the rewritten
    // transitions. This preserves caller-declared standalone places that are
    // unrelated to fusion, drops any standalone declarations of non-canonical
    // members, and ensures canonical places end up present even if a caller
    // never declared them standalone.
    const rebuiltPlaces = new Set<Place<any>>();
    for (const p of this._places) {
      if (!nonCanonicalNames.has(p.name)) {
        rebuiltPlaces.add(p);
      }
    }
    for (const t of rewrittenTransitions) {
      for (const spec of t.inputSpecs) rebuiltPlaces.add(spec.place);
      for (const p of t.outputPlaces()) rebuiltPlaces.add(p);
      for (const inh of t.inhibitors) rebuiltPlaces.add(inh.place);
      for (const r of t.reads) rebuiltPlaces.add(r.place);
      for (const r of t.resets) rebuiltPlaces.add(r.place);
    }

    return new PetriNet(PETRI_NET_KEY, this._name, rebuiltPlaces, rewrittenTransitions,
      PetriNetBuilder.filterFusedMembership(membership, nonCanonicalNames));
  }
}

/** Creates a new transition with a different action while preserving all arc specs. */
function rebuildWithAction(t: Transition, action: TransitionAction): Transition {
  const builder = Transition.builder(t.name)
    .timing(t.timing)
    .priority(t.priority)
    .action(action);

  if (t.inputSpecs.length > 0) {
    builder.inputs(...t.inputSpecs);
  }
  if (t.outputSpec !== null) {
    builder.outputs(t.outputSpec);
  }

  for (const inh of t.inhibitors) {
    builder.inhibitor(inh.place);
  }
  for (const r of t.reads) {
    builder.read(r.place);
  }
  for (const r of t.resets) {
    builder.reset(r.place);
  }

  return builder.build();
}
