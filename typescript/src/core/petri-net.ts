import type { Place } from './place.js';
import type { TransitionAction } from './transition-action.js';
import { passthrough } from './transition-action.js';
import { Transition } from './transition.js';

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

  /** @internal Use {@link PetriNet.builder} to create instances. */
  constructor(
    key: symbol,
    name: string,
    places: ReadonlySet<Place<any>>,
    transitions: ReadonlySet<Transition>,
  ) {
    if (key !== PETRI_NET_KEY) throw new Error('Use PetriNet.builder() to create instances');
    this.name = name;
    this.places = places;
    this.transitions = transitions;
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
    return new PetriNet(PETRI_NET_KEY, this.name, this.places, boundTransitions);
  }

  static builder(name: string): PetriNetBuilder {
    return new PetriNetBuilder(name);
  }
}

export class PetriNetBuilder {
  private readonly _name: string;
  private readonly _places = new Set<Place<any>>();
  private readonly _transitions = new Set<Transition>();

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

  build(): PetriNet {
    return new PetriNet(PETRI_NET_KEY, this._name, this._places, this._transitions);
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
