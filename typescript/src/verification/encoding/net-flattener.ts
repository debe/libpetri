/**
 * @module net-flattener
 *
 * Flattens a PetriNet into integer-indexed pre/post vectors for SMT encoding.
 *
 * **XOR expansion**: Transitions with XOR output specs are expanded into multiple
 * flat transitions — one per deterministic branch. Each branch produces tokens to
 * exactly one XOR child's places. This converts non-deterministic output routing
 * into separate transitions that the SMT solver can reason about independently.
 *
 * **Vector construction**: For each flat transition, builds:
 * - `preVector[p]`: tokens consumed from place p (input cardinality)
 * - `postVector[p]`: tokens produced to place p (from the selected branch)
 * - `consumeAll[p]`: true for `all`/`at-least` inputs (consume everything)
 * - Index arrays for inhibitor, read, and reset arcs
 *
 * Places are sorted by name for stable, deterministic indexing across runs.
 */
import type { PetriNet } from '../../core/petri-net.js';
import type { Place, EnvironmentPlace } from '../../core/place.js';
import type { Out } from '../../core/out.js';
import type { FlatNet } from './flat-net.js';
import { flatTransition } from './flat-transition.js';
import { enumerateBranches, allPlaces as outAllPlaces } from '../../core/out.js';

/**
 * How to treat environment places during analysis.
 */
export type EnvironmentAnalysisMode =
  | { readonly type: 'unbounded' }
  | { readonly type: 'bounded'; readonly maxTokens: number };

export function unbounded(): EnvironmentAnalysisMode {
  return { type: 'unbounded' };
}

export function bounded(maxTokens: number): EnvironmentAnalysisMode {
  return { type: 'bounded', maxTokens };
}

/**
 * Flattens a PetriNet into a FlatNet suitable for SMT encoding.
 *
 * Flattening involves:
 * 1. Assigning each place a stable integer index (sorted by name)
 * 2. Expanding XOR outputs into separate flat transitions (one per branch)
 * 3. Building pre/post vectors from input/output specs
 * 4. Recording inhibitor, read, and reset arcs
 * 5. Setting environment bounds for bounded analysis mode
 */
export function flatten(
  net: PetriNet,
  environmentPlaces: Set<EnvironmentPlace<any>> = new Set(),
  environmentMode: EnvironmentAnalysisMode = unbounded(),
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

  // Sort by name for stable indexing
  const places = [...allPlacesSet.values()].sort((a, b) => a.name.localeCompare(b.name));

  const placeIndex = new Map<string, number>();
  for (let i = 0; i < places.length; i++) {
    placeIndex.set(places[i]!.name, i);
  }

  // 2. Compute environment bounds
  const environmentBounds = new Map<string, number>();
  if (environmentMode.type === 'bounded') {
    for (const ep of environmentPlaces) {
      environmentBounds.set(ep.place.name, environmentMode.maxTokens);
    }
  }

  // 3. Expand transitions
  const n = places.length;
  const flatTransitions = [];

  for (const transition of net.transitions) {
    const branches = enumerateOutputBranches(transition);

    for (let branchIdx = 0; branchIdx < branches.length; branchIdx++) {
      const branchPlaces = branches[branchIdx]!;
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

      // Build post-vector from branch output places
      const postVector = new Array<number>(n).fill(0);
      for (const p of branchPlaces) {
        const idx = placeIndex.get(p.name);
        if (idx !== undefined) {
          postVector[idx] = 1;
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
      ));
    }
  }

  return {
    places,
    placeIndex,
    transitions: flatTransitions,
    environmentBounds,
  };
}

function enumerateOutputBranches(t: { outputSpec: Out | null }): ReadonlySet<Place<any>>[] {
  if (t.outputSpec !== null) {
    return enumerateBranches(t.outputSpec) as ReadonlySet<Place<any>>[];
  }
  // No outputs (sink transition)
  return [new Set()];
}
