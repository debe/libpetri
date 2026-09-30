/**
 * @module net-flattener
 *
 * Flattens a PetriNet into integer-indexed pre/post vectors for SMT encoding.
 *
 * **XOR expansion**: Transitions are expanded into one flat transition per way a
 * firing can end (`branch-outcomes`): each XOR branch the action may write, and a
 * timeout that deposits differently (only the timeout child's places, a forward
 * depositing one token per consumed token, [IO-014]). This converts non-deterministic
 * output routing into separate transitions that the SMT solver can reason about
 * independently.
 *
 * **Vector construction**: For each flat transition, builds:
 * - `preVector[p]`: tokens consumed from place p (input cardinality)
 * - `postVector[p]`: tokens produced to place p (from the selected outcome)
 * - `consumeAll[p]`: true for `all`/`at-least` inputs (consume everything)
 * - Index arrays for inhibitor, read, and reset arcs
 *
 * Places are sorted by name, in Unicode code-point order, for stable indexing across
 * runs, hosts and implementations.
 */
import type { PetriNet } from '../../core/petri-net.js';
import type { Transition } from '../../core/transition.js';
import { isReapable } from '../reaping.js';
import type { Place, EnvironmentPlace } from '../../core/place.js';
import type { FlatNet } from './flat-net.js';
import { flatTransition } from './flat-transition.js';
import { allPlaces as outAllPlaces } from '../../core/out.js';
import { requiredCount } from '../../core/in.js';
import { depositCount, outcomes } from '../analysis/branch-outcomes.js';
import { compareCodePoints } from '../../core/internal/code-point-order.js';
import { type EnvironmentAnalysisMode, alwaysAvailable, arrivalsNotModelled } from '../analysis/environment-analysis-mode.js';

// The SMT path shares the single 3-mode EnvironmentAnalysisMode with the state
// class graph (VER-006): AlwaysAvailable / Bounded(k) / Ignore. Re-exported here
// for the encoding barrel so existing `libpetri/verification` consumers resolve it.
export { type EnvironmentAnalysisMode, alwaysAvailable, arrivals, bounded, ignore } from '../analysis/environment-analysis-mode.js';

/**
 * Flattens a PetriNet into a FlatNet suitable for SMT encoding.
 *
 * Flattening involves:
 * 1. Assigning each place a stable integer index (sorted by name)
 * 2. Expanding each transition into one flat transition per way a firing can end:
 *    each XOR branch, then the timeout outcome when it deposits differently
 * 3. Building pre/post vectors from input/output specs
 * 4. Recording inhibitor, read, and reset arcs
 * 5. Setting environment bounds for bounded analysis mode
 *
 * A flat transition is `reapable` exactly when `reapable(source)` holds: by default when the
 * source's timing is `deadline` or `window` ([TIME-013]); the verifier passes its own set, empty
 * under `assumeNoReaping`.
 */
export function flatten(
  net: PetriNet,
  environmentPlaces: Set<EnvironmentPlace<any>> = new Set(),
  environmentMode: EnvironmentAnalysisMode = alwaysAvailable(),
  reapable: (t: Transition) => boolean = t => isReapable(t.timing),
): FlatNet {
  // 1. Collect ALL places
  const allPlacesSet = new Map<string, Place<any>>();
  for (const p of net.places) {
    allPlacesSet.set(p.name, p);
  }
  for (const t of net.transitions) {
    for (const inSpec of t.inputSpecs) {
      allPlacesSet.set(inSpec.place.name, inSpec.place);
    }
    if (t.outputSpec !== null) {
      for (const p of outAllPlaces(t.outputSpec)) {
        allPlacesSet.set(p.name, p);
      }
    }
    for (const arc of t.inhibitors) allPlacesSet.set(arc.place.name, arc.place);
    for (const arc of t.reads) allPlacesSet.set(arc.place.name, arc.place);
    for (const arc of t.resets) allPlacesSet.set(arc.place.name, arc.place);
  }

  // Sort by name for stable indexing. Unicode code-point order (not the host's
  // locale, and not UTF-16 code units), so the index agrees with the Rust and Java
  // flatteners on every name and the emitted scripts stay byte-identical (VER-013).
  const places = [...allPlacesSet.values()].sort((a, b) => compareCodePoints(a.name, b.name));

  const placeIndex = new Map<string, number>();
  for (let i = 0; i < places.length; i++) {
    placeIndex.set(places[i]!.name, i);
  }

  // 2. Compute environment bounds (legacy post-cap) and the injection map.
  //    The injection map drives the encoder's env-injection rule and the
  //    incidence-matrix injector columns. Below the injection guard the post-cap
  //    bites only when a transition deposits into an environment place or M0
  //    holds more than k there, and there it removes executor steps; the
  //    verifier refuses both cases before encoding (VER-006 AC3).
  const environmentBounds = new Map<string, number>();
  const environmentInjection = new Map<string, number | null>();
  switch (environmentMode.type) {
    case 'always-available':
      for (const ep of environmentPlaces) {
        environmentInjection.set(ep.place.name, null);
      }
      break;
    case 'bounded':
      for (const ep of environmentPlaces) {
        environmentBounds.set(ep.place.name, environmentMode.maxTokens);
        environmentInjection.set(ep.place.name, environmentMode.maxTokens);
      }
      break;
    case 'ignore':
      // Not modeled: env places stay ordinary (frozen at their initial count).
      break;
    case 'arrivals':
      if (environmentPlaces.size > 0) throw arrivalsNotModelled('flatten');
      break;
  }

  // 3. Expand transitions
  const n = places.length;
  const flatTransitions = [];

  for (const transition of net.transitions) {
    // One flat transition per way a firing can end (`branch-outcomes`): each branch the
    // action may write, one token per place ([IO-016]), then the timeout outcome when it
    // deposits differently — only the timeout child's places, a forward depositing one token
    // per consumed token ([IO-013] AC5, [IO-014]).
    const branches = outcomes(transition);

    for (let branchIdx = 0; branchIdx < branches.length; branchIdx++) {
      const outcome = branches[branchIdx]!;
      const name = branches.length > 1
        ? `${transition.name}_b${branchIdx}`
        : transition.name;

      // Build pre-vector and consumeAll flags
      const preVector = new Array<number>(n).fill(0);
      const consumeAll = new Array<boolean>(n).fill(false);

      for (const inSpec of transition.inputSpecs) {
        const idx = placeIndex.get(inSpec.place.name);
        if (idx === undefined) continue;

        switch (inSpec.type) {
          case 'one':
            preVector[idx] = 1;
            break;
          case 'exactly':
            preVector[idx] = inSpec.count;
            break;
          case 'all':
            preVector[idx] = 1;
            consumeAll[idx] = true;
            break;
          case 'at-least':
            preVector[idx] = inSpec.minimum;
            consumeAll[idx] = true;
            break;
        }
      }

      // Build post-vector from the outcome's deposits. A forward of an `all` / `atLeast`
      // input deposits the drained batch, which no post vector can hold; its minimum stands
      // in, and the verifier refuses the net before any flat route reads it (`drainedForward`);
      // the graph routes, which count the batch, decide it first.
      const minimum = (from: Place<any>): number => {
        const spec = transition.inputSpecs.find(s => s.place.name === from.name);
        return spec === undefined ? 0 : requiredCount(spec);
      };
      const postVector = new Array<number>(n).fill(0);
      for (const { place: p, deposit } of outcome.deposits) {
        const idx = placeIndex.get(p.name);
        if (idx !== undefined) {
          postVector[idx] = postVector[idx]! + depositCount(deposit, minimum);
        }
      }

      // Inhibitor places
      const inhibitorPlaces = transition.inhibitors
        .map(arc => placeIndex.get(arc.place.name))
        .filter((idx): idx is number => idx !== undefined);

      // Read places
      const readPlaces = transition.reads
        .map(arc => placeIndex.get(arc.place.name))
        .filter((idx): idx is number => idx !== undefined);

      // Reset places
      const resetPlaces = transition.resets
        .map(arc => placeIndex.get(arc.place.name))
        .filter((idx): idx is number => idx !== undefined);

      flatTransitions.push(flatTransition(
        name,
        transition,
        branches.length > 1 ? branchIdx : -1,
        preVector,
        postVector,
        inhibitorPlaces,
        readPlaces,
        resetPlaces,
        consumeAll,
        reapable(transition),
      ));
    }
  }

  return {
    places,
    placeIndex,
    transitions: flatTransitions,
    environmentBounds,
    environmentInjection,
  };
}
