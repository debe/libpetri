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
import { type EnvironmentAnalysisMode, alwaysAvailable } from '../analysis/environment-analysis-mode.js';

// The SMT path shares the single 3-mode EnvironmentAnalysisMode with the state
// class graph (VER-006): AlwaysAvailable / Bounded(k) / Ignore. Re-exported here
// for the encoding barrel so existing `libpetri/verification` consumers resolve it.
export { type EnvironmentAnalysisMode, alwaysAvailable, bounded, ignore } from '../analysis/environment-analysis-mode.js';

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
  environmentMode: EnvironmentAnalysisMode = alwaysAvailable(),
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

  // Sort by name for stable indexing. Unicode code-point order (not the
  // locale-sensitive `localeCompare`), so the index agrees with the Rust and Java
  // flatteners on every name and the emitted scripts stay byte-identical (VER-013).
  const places = [...allPlacesSet.values()].sort((a, b) => compareCodePoints(a.name, b.name));

  const placeIndex = new Map<string, number>();
  for (let i = 0; i < places.length; i++) {
    placeIndex.set(places[i]!.name, i);
  }

  // 2. Compute environment bounds (legacy post-cap) and the injection map.
  //    The injection map drives the encoder's env-injection rule and the
  //    incidence-matrix injector columns; bounds remain a harmless extra cap.
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
    environmentInjection,
  };
}

function enumerateOutputBranches(t: { outputSpec: Out | null }): ReadonlySet<Place<any>>[] {
  if (t.outputSpec !== null) {
    return enumerateBranches(t.outputSpec) as ReadonlySet<Place<any>>[];
  }
  // No outputs (sink transition)
  return [new Set()];
}

/** Lexicographic order on Unicode code points (what Rust's `String` order is). */
export function compareCodePoints(a: string, b: string): number {
  const ia = a[Symbol.iterator]();
  const ib = b[Symbol.iterator]();
  for (;;) {
    const na = ia.next();
    const nb = ib.next();
    if (na.done && nb.done) return 0;
    if (na.done) return -1;
    if (nb.done) return 1;
    const ca = na.value.codePointAt(0)!;
    const cb = nb.value.codePointAt(0)!;
    if (ca !== cb) return ca - cb;
  }
}
