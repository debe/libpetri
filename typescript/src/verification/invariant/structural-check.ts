/**
 * @module structural-check
 *
 * Structural deadlock pre-check using siphon/trap analysis (Commoner's theorem).
 *
 * **Commoner's theorem**: A Petri net is deadlock-free if every siphon contains
 * an initially marked trap.
 *
 * **Siphon**: A set of places S where every transition that outputs to S also
 * inputs from S. Key property: once all places in a siphon become empty,
 * they can never be re-marked. An empty siphon can cause deadlock.
 *
 * **Trap**: A set of places S where every transition that inputs from S also
 * outputs to S. Key property: once any place in a trap is marked,
 * the trap remains marked forever.
 *
 * **Algorithm**: For each place, compute the minimal siphon containing it via
 * fixed-point expansion. For each siphon, find the maximal trap within it
 * (fixed-point contraction). If every siphon contains an initially-marked
 * trap, deadlock-freedom is proven structurally — no SMT query needed.
 *
 * Limited to nets with ≤50 places to bound enumeration cost.
 */
import type { FlatNet } from '../encoding/flat-net.js';
import type { MarkingState } from '../marking-state.js';

const MAX_PLACES_FOR_SIPHON_ANALYSIS = 50;

/**
 * Result of structural deadlock check using siphon/trap analysis.
 */
export type StructuralCheckResult =
  | { readonly type: 'no-potential-deadlock' }
  | { readonly type: 'potential-deadlock'; readonly siphon: ReadonlySet<number> }
  | { readonly type: 'inconclusive'; readonly reason: string };

/**
 * Structural deadlock pre-check using siphon/trap analysis.
 *
 * Commoner's theorem: a Petri net is deadlock-free if every siphon
 * contains a marked trap.
 *
 * A siphon is a set of places S such that every transition with
 * an output in S also has an input in S. Once empty, a siphon stays empty.
 *
 * A trap is a set of places S such that every transition with
 * an input in S also has an output in S. Once marked, a trap stays marked.
 */
export function structuralCheck(flatNet: FlatNet, initialMarking: MarkingState): StructuralCheckResult {
  const P = flatNet.places.length;

  if (P === 0) {
    return { type: 'no-potential-deadlock' };
  }

  if (P > MAX_PLACES_FOR_SIPHON_ANALYSIS) {
    return { type: 'inconclusive', reason: `Net has ${P} places, siphon enumeration skipped` };
  }

  const siphons = findMinimalSiphons(flatNet);

  if (siphons.length === 0) {
    return { type: 'no-potential-deadlock' };
  }

  for (const siphon of siphons) {
    const trap = findMaximalTrapIn(flatNet, siphon);

    if (trap.size === 0 || !isMarked(trap, flatNet, initialMarking)) {
      return { type: 'potential-deadlock', siphon };
    }
  }

  return { type: 'no-potential-deadlock' };
}

/**
 * Finds minimal siphons by checking all non-empty subsets of deadlock-enabling places.
 * Uses a fixed-point approach: start from each place and grow the siphon.
 */
export function findMinimalSiphons(flatNet: FlatNet): ReadonlySet<number>[] {
  const P = flatNet.places.length;
  const siphons: Set<number>[] = [];

  // Pre-compute: for each place, which transitions have it as output?
  const placeAsOutput: number[][] = [];
  for (let p = 0; p < P; p++) {
    placeAsOutput.push([]);
  }

  for (let t = 0; t < flatNet.transitions.length; t++) {
    const ft = flatNet.transitions[t]!;
    for (let p = 0; p < P; p++) {
      if (ft.postVector[p]! > 0) {
        placeAsOutput[p]!.push(t);
      }
    }
  }

  for (let startPlace = 0; startPlace < P; startPlace++) {
    const siphon = computeSiphonContaining(startPlace, flatNet, placeAsOutput);
    if (siphon !== null && siphon.size > 0) {
      let isMinimal = true;
      const toRemove: number[] = [];
      for (let i = 0; i < siphons.length; i++) {
        const existing = siphons[i]!;
        if (setsEqual(existing, siphon)) {
          isMinimal = false;
          break;
        }
        if (isSubsetOf(existing, siphon)) {
          isMinimal = false;
          break;
        }
        if (isSubsetOf(siphon, existing)) {
          toRemove.push(i);
        }
      }
      for (let i = toRemove.length - 1; i >= 0; i--) {
        siphons.splice(toRemove[i]!, 1);
      }
      if (isMinimal) {
        siphons.push(siphon);
      }
    }
  }

  return siphons;
}

function computeSiphonContaining(
  startPlace: number,
  flatNet: FlatNet,
  placeAsOutput: number[][],
): Set<number> | null {
  const siphon = new Set<number>();
  siphon.add(startPlace);

  let changed = true;
  while (changed) {
    changed = false;
    const snapshot = [...siphon];

    for (const p of snapshot) {
      for (const t of placeAsOutput[p]!) {
        const ft = flatNet.transitions[t]!;

        let hasInputInSiphon = false;
        for (let q = 0; q < flatNet.places.length; q++) {
          if (ft.preVector[q]! > 0 && siphon.has(q)) {
            hasInputInSiphon = true;
            break;
          }
        }

        if (!hasInputInSiphon) {
          let added = false;
          for (let q = 0; q < flatNet.places.length; q++) {
            if (ft.preVector[q]! > 0) {
              if (!siphon.has(q)) {
                siphon.add(q);
                changed = true;
              }
              added = true;
              break;
            }
          }
          if (!added) {
            return null;
          }
        }
      }
    }
  }

  return siphon;
}

/**
 * Finds the maximal trap within a given set of places.
 * Uses fixed-point: start with the full set and remove places that violate the trap condition.
 */
export function findMaximalTrapIn(flatNet: FlatNet, places: ReadonlySet<number>): ReadonlySet<number> {
  const trap = new Set(places);

  let changed = true;
  while (changed) {
    changed = false;
    const toRemove: number[] = [];

    for (const p of trap) {
      let satisfies = true;
      for (let t = 0; t < flatNet.transitions.length; t++) {
        const ft = flatNet.transitions[t]!;
        if (ft.preVector[p]! > 0) {
          let outputsToTrap = false;
          for (const q of trap) {
            if (ft.postVector[q]! > 0) {
              outputsToTrap = true;
              break;
            }
          }
          if (!outputsToTrap) {
            satisfies = false;
            break;
          }
        }
      }
      if (!satisfies) {
        toRemove.push(p);
      }
    }

    if (toRemove.length > 0) {
      for (const p of toRemove) trap.delete(p);
      changed = true;
    }
  }

  return trap;
}

function isMarked(placeIndices: ReadonlySet<number>, flatNet: FlatNet, marking: MarkingState): boolean {
  for (const idx of placeIndices) {
    const place = flatNet.places[idx]!;
    if (marking.tokens(place) > 0) return true;
  }
  return false;
}

function setsEqual(a: ReadonlySet<number>, b: ReadonlySet<number>): boolean {
  if (a.size !== b.size) return false;
  for (const v of a) {
    if (!b.has(v)) return false;
  }
  return true;
}

function isSubsetOf(sub: ReadonlySet<number>, sup: ReadonlySet<number>): boolean {
  if (sub.size > sup.size) return false;
  for (const v of sub) {
    if (!sup.has(v)) return false;
  }
  return true;
}
