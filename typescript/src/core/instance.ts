import type { PetriNet } from './petri-net.js';
import type { Place } from './place.js';
import type { SubnetDef } from './subnet-def.js';
import type { SubnetInstance } from './subnet-instance.js';
import type { Transition } from './transition.js';
import type { TransitionAction } from './transition-action.js';

/**
 * @internal Symbol key restricting construction to {@link SubnetDef.instantiate}
 * and the (future) `subnet-rewriter` module. Exported via the package-internal
 * factory {@link __createInstance} so the rewriter can construct Instances
 * without exposing the constructor publicly.
 */
const INSTANCE_KEY = Symbol('Instance.internal');

/**
 * A typed module instance produced by {@link SubnetDef.instantiate}, per
 * `spec/11-modular-composition.md` requirements **MOD-010** (creation),
 * **MOD-011** (typed handle map), **MOD-012** (per-instance state isolation),
 * and **MOD-030** (action binding).
 *
 * An instance carries:
 * - The {@link prefix} used to rename body elements (per [MOD-010] separator `"/"`);
 * - A reference to the originating {@link SubnetDef};
 * - The renamed body — a structurally valid `PetriNet` per [CORE-040];
 * - Typed lookup handles for ports and channels keyed by their **original**
 *   (pre-prefix) names;
 * - The `params` value supplied at instantiation.
 *
 * **Scaffolding status**: this class ships in scaffolding form. The
 * {@link bindActions} method throws `Error("not implemented")` until the
 * `instantiate` rename pass lands in the next task. Direct accessors are
 * wired up so downstream code can take dependencies on the API shape today.
 *
 * @typeParam P parameter type (use `void` for unparameterised subnets)
 */
export class Instance<P = void> {
  readonly prefix: string;
  readonly def: SubnetDef<P>;
  readonly renamedBody: PetriNet;
  readonly portHandles: ReadonlyMap<string, Place<unknown>>;
  readonly channelHandles: ReadonlyMap<string, Transition>;
  readonly params: P;

  /**
   * @internal Use {@link SubnetDef.instantiate} (or the internal factory
   * {@link __createInstance}) to create instances.
   */
  constructor(
    key: symbol,
    prefix: string,
    def: SubnetDef<P>,
    renamedBody: PetriNet,
    portHandles: ReadonlyMap<string, Place<unknown>>,
    channelHandles: ReadonlyMap<string, Transition>,
    params: P,
  ) {
    if (key !== INSTANCE_KEY) {
      throw new Error('Use SubnetDef.instantiate() to create Instance values');
    }
    this.prefix = prefix;
    this.def = def;
    this.renamedBody = renamedBody;
    this.portHandles = portHandles;
    this.channelHandles = channelHandles;
    this.params = params;
  }

  /**
   * Returns the renamed {@link Place} corresponding to the named port.
   *
   * The port name is the **original** (pre-prefix) name as declared in the
   * subnet's `Interface`. Per **MOD-022**, TypeScript enforces token-type
   * compatibility at compile time only; this method does not validate `T`
   * at runtime. A missing name raises an `Error`.
   *
   * @throws when the port name is unknown
   */
  port<T>(name: string): Place<T> {
    const p = this.portHandles.get(name);
    if (p === undefined) {
      throw new Error(`No port named '${name}' in instance '${this.prefix}'`);
    }
    return p as Place<T>;
  }

  /**
   * Returns the renamed {@link Transition} corresponding to the named channel.
   *
   * @throws when the channel name is unknown
   */
  channel(name: string): Transition {
    const t = this.channelHandles.get(name);
    if (t === undefined) {
      throw new Error(`No channel named '${name}' in instance '${this.prefix}'`);
    }
    return t;
  }

  /**
   * Returns the debug-UI descriptor for this instance per **MOD-041**.
   */
  descriptor(): SubnetInstance {
    const transitions: string[] = [];
    for (const t of this.renamedBody.transitions) transitions.push(t.name);
    const exposedPlaces: string[] = [];
    for (const p of this.portHandles.values()) exposedPlaces.push(p.name);
    return {
      prefix: this.prefix,
      defName: this.def.name,
      transitions,
      exposedPlaces,
      params: this.params,
      parentPrefix: null,
    };
  }

  /**
   * Produces a derived instance whose specified transitions (named by their
   * **original**, pre-prefix names) carry the supplied actions per **MOD-030**.
   *
   * For each entry `[originalName, action]`, the renamed body is searched for
   * the transition whose name equals `prefix + "/" + originalName`. The
   * resulting instance shares the original `def`, `prefix`, `params`, and
   * port/channel handle topology — only the renamed body is rebuilt with new
   * actions. Per **MOD-030**, calling `bindActions` on one instance does NOT
   * affect the actions held by other instances of the same `def`.
   *
   * Unrecognised original names raise an `Error` so typos surface eagerly.
   */
  bindActions(actionsByOriginalName: Record<string, TransitionAction>): Instance<P> {
    // Build a Map<prefixedName, TransitionAction> for the resolver.
    // Validate every supplied original name against the renamed body's
    // transition set to surface typos eagerly.
    const prefixedByName = new Map<string, TransitionAction>();
    const renamedNames = new Set<string>();
    for (const t of this.renamedBody.transitions) {
      renamedNames.add(t.name);
    }

    for (const originalName of Object.keys(actionsByOriginalName)) {
      const prefixed = this.prefix + '/' + originalName;
      if (!renamedNames.has(prefixed)) {
        throw new Error(
          `Instance.bindActions: no transition '${originalName}' (resolved as ` +
          `'${prefixed}') in instance '${this.prefix}' of subnet '${this.def.name}'`,
        );
      }
      prefixedByName.set(prefixed, actionsByOriginalName[originalName]!);
    }

    // Use the existing PetriNet.bindActionsWithResolver — it preserves the
    // existing action when the resolver returns it (see petri-net.ts), so
    // unaffected transitions land in the new net by reference (sharing per
    // MOD-030).
    const reboundBody = this.renamedBody.bindActionsWithResolver((name) => {
      const action = prefixedByName.get(name);
      if (action !== undefined) return action;
      // Return the existing action so PetriNet.bindActionsWithResolver
      // short-circuits the rebuild for unaffected transitions.
      for (const t of this.renamedBody.transitions) {
        if (t.name === name) return t.action;
      }
      // Unreachable — the resolver is only called for transitions in this.renamedBody.
      /* istanbul ignore next */
      throw new Error(`Instance.bindActions: resolver invoked with unknown name '${name}'`);
    });

    // Rebuild the channel handles against the rebound body so callers see
    // the post-rebind transition (with its new action) when they ask for a
    // channel by name.
    const reboundChannelHandles = new Map<string, Transition>();
    if (this.channelHandles.size > 0) {
      const byName = new Map<string, Transition>();
      for (const t of reboundBody.transitions) {
        byName.set(t.name, t);
      }
      for (const [name, oldT] of this.channelHandles) {
        const refreshed = byName.get(oldT.name);
        if (refreshed === undefined) {
          /* istanbul ignore next */
          throw new Error(
            `Instance.bindActions: channel '${name}' transition '${oldT.name}' not found in rebound body`,
          );
        }
        reboundChannelHandles.set(name, refreshed);
      }
    }

    return __createInstance<P>(
      this.prefix,
      this.def,
      reboundBody,
      this.portHandles,
      reboundChannelHandles,
      this.params,
    );
  }
}

/**
 * @internal Package-internal factory used by {@link SubnetDef.instantiate}
 * and the (future) `subnet-rewriter` module to construct {@link Instance}
 * values without re-exporting the Symbol-guarded constructor key publicly.
 *
 * NOT part of the public API surface — do NOT re-export from `core/index.ts`.
 */
export function __createInstance<P>(
  prefix: string,
  def: SubnetDef<P>,
  renamedBody: PetriNet,
  portHandles: ReadonlyMap<string, Place<unknown>>,
  channelHandles: ReadonlyMap<string, Transition>,
  params: P,
): Instance<P> {
  return new Instance<P>(
    INSTANCE_KEY,
    prefix,
    def,
    renamedBody,
    portHandles,
    channelHandles,
    params,
  );
}
