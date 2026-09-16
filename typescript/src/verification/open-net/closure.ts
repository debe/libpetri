/**
 * @module open-net/closure
 *
 * An open net closed by the environment its contract describes ([VER-022]).
 *
 * Each arrival group becomes ordinary net structure. A source place holds the tokens the
 * group must deliver, with one transition per target place that moves a token across. The
 * part the group may withhold gets a second source, whose tokens can also be declined by a
 * transition with no output. The contract's environment transitions, the neighbours that
 * react to what the subnet sends, join unchanged. Every interleaving of the environment's
 * steps with the subnet's own firings is then a run of the closed net. A run of the closed
 * net is quiescent only once the environment has delivered what it must and decided about
 * the rest.
 *
 * Nothing else changes. The closed net is a plain net, so the state-class graph and the SMT
 * pipeline verify it as they verify any other, and no route needs a notion of environment.
 *
 * The closure uses ordinary places rather than the environment places of [VER-006] on
 * purpose. Under `alwaysAvailable` or `bounded(k)` an environment place never runs dry, so a
 * net with one is never quiescent, and every quiescence property holds vacuously. An arrival
 * group that runs dry after `max` tokens is what a bounded contract means.
 */
import { PetriNet } from '../../core/petri-net.js';
import { place, type Place } from '../../core/place.js';
import { Transition } from '../../core/transition.js';
import { one } from '../../core/in.js';
import { outPlace } from '../../core/out.js';
import { fork, isPassthrough, transform } from '../../core/transition-action.js';
import { MarkingState } from '../marking-state.js';
import { transitionPlaces, type OpenNetContract } from './contract.js';

/** What an environment transition of the closure does, for the port trace. */
export type EnvironmentStep =
  | { readonly kind: 'arrival'; readonly group: number; readonly place: string }
  | { readonly kind: 'decline'; readonly group: number }
  /** One of the contract's own environment transitions. */
  | { readonly kind: 'transition' };

/** An open net and its environment, as one closed net. */
export interface ClosedNet {
  readonly net: PetriNet;
  readonly initialMarking: MarkingState;
  /** Each environment transition by name, with what it does. */
  readonly environment: ReadonlyMap<string, EnvironmentStep>;
  /**
   * Places only the contract's environment transitions touch: the environment's own state.
   * A token left on one at quiescence is never stranded.
   */
  readonly environmentPlaces: readonly Place<any>[];
  /**
   * Places the contract names that no arc touches, in contract order. They join the closed
   * net as places of their own, so every route resolves them. A clause over a place nothing
   * writes then counts zero there, which is the finding, not an error.
   */
  readonly undeclared: readonly string[];
}

/** The action an environment transition that declares outputs gets when it has none: it never runs. */
const ENVIRONMENT_ACTION = transform(() => null);

/**
 * Closes `net` with the environment of `contract`: its environment transitions, and for
 * arrival group `i` a source `env:arrivals[i]` holding `min` tokens and a source
 * `env:optional[i]` holding `max − min`, with transitions `env:arrive[i]:<place>` /
 * `env:arrive?[i]:<place>` moving a token onto each of the group's places, and
 * `env:decline[i]` discarding an optional one.
 *
 * @throws when a name the closure would add is already taken in `net`
 */
export function closeOpenNet(net: PetriNet, contract: OpenNetContract): ClosedNet {
  const byName = new Map<string, Place<any>>();
  for (const p of net.places) if (!byName.has(p.name)) byName.set(p.name, p);
  const taken = new Set<string>(byName.keys());
  for (const t of net.transitions) taken.add(t.name);
  const fresh = (name: string): string => {
    if (taken.has(name)) {
      throw new Error(`VER-022: closing the net would add '${name}', which the net already declares`);
    }
    taken.add(name);
    return name;
  };

  const environment = new Map<string, EnvironmentStep>();
  const environmentPlaces = new Map<string, Place<any>>();
  for (const t of contract.environment) {
    environment.set(fresh(t.name), { kind: 'transition' });
    for (const p of transitionPlaces(t)) {
      if (!byName.has(p.name) && !environmentPlaces.has(p.name)) environmentPlaces.set(p.name, p);
    }
  }
  // Before the undeclared sweep below, so an environment place is never also reported as a
  // place the contract named and nothing declares.
  for (const [name, p] of environmentPlaces) {
    taken.add(name);
    byName.set(name, p);
  }

  // Every place the contract names joins the closed net, a terminal's excused places included
  // — `contract.places()` leaves those out. This is also what keeps the two routes deciding
  // the same rest set: the SMT encoder resolves each sink and marker through
  // `flatNet.placeIndex` and silently drops what does not resolve, while the graph route
  // matches by name and drops nothing. An arc-less excused place that never got registered
  // here would therefore lose its excuse on the SMT route alone, and that route would report a
  // stranding the graph route proves cannot happen.
  const undeclared: string[] = [];
  const extra: Place<any>[] = [];
  const named = [...contract.places(), ...contract.terminals.flatMap(t => t.excused)];
  for (const p of named) {
    if (byName.has(p.name)) continue;
    undeclared.push(p.name);
    byName.set(p.name, p);
    extra.push(p);
  }
  // The net's own place objects, so an arc and a contract place with one name stay one place.
  const canonical = (p: Place<any>): Place<any> => byName.get(p.name) ?? p;

  const envTransitions: Transition[] = [];
  const marking = MarkingState.builder().copyFrom(contract.initialMarking);
  const inject = (group: number, source: Place<any>, target: Place<any>, optional: boolean): void => {
    const name = fresh(`env:arrive${optional ? '?' : ''}[${group}]:${target.name}`);
    envTransitions.push(
      Transition.builder(name).inputs(one(source)).outputs(outPlace(target)).action(fork()).build(),
    );
    environment.set(name, { kind: 'arrival', group, place: target.name });
  };

  contract.arrivals.forEach((group, i) => {
    if (group.min > 0) {
      const source = place<unknown>(fresh(`env:arrivals[${i}]`));
      marking.tokens(source, group.min);
      for (const p of group.places) inject(i, source, canonical(p), false);
    }
    if (group.max > group.min) {
      const source = place<unknown>(fresh(`env:optional[${i}]`));
      marking.tokens(source, group.max - group.min);
      for (const p of group.places) inject(i, source, canonical(p), true);
      const name = fresh(`env:decline[${i}]`);
      envTransitions.push(Transition.builder(name).inputs(one(source)).build());
      environment.set(name, { kind: 'decline', group: i });
    }
  });

  // An environment transition's action never runs, so it need not produce: give one that
  // declares outputs a placeholder rather than refuse it under CORE-043.
  const placeholder = new Set(contract.environment
    .filter(t => t.outputSpec !== null && isPassthrough(t.action))
    .map(t => t.name));
  const closed = PetriNet.builder(`${net.name}+environment`)
    .places(...net.places, ...extra)
    .transitions(...net.transitions, ...contract.environment, ...envTransitions)
    .build()
    .bindActionsWithResolver(name => (placeholder.has(name) ? ENVIRONMENT_ACTION : null));
  return {
    net: closed,
    initialMarking: marking.build(),
    environment,
    environmentPlaces: [...environmentPlaces.values()],
    undeclared,
  };
}
