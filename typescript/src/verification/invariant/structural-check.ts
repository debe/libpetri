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
 * **Algorithm**: Find every minimal siphon by a branching search: grow a set from
 * each place and, where a producer into the set has no input in it, branch on each
 * of that producer's inputs. For each minimal siphon, find its maximal trap
 * (fixed-point contraction). If every such trap is marked in the initial marking,
 * deadlock-freedom is proven structurally and no SMT query is needed. The search is
 * capped at SIPHON_SEARCH_BUDGET nodes; past it the check is inconclusive.
 *
 * Limited to nets with ≤50 places to bound enumeration cost.
 */
import type { FlatNet } from '../encoding/flat-net.js';
import type { MarkingState } from '../marking-state.js';

const MAX_PLACES_FOR_SIPHON_ANALYSIS = 50;

/**
 * Search budget for the siphon search, in search nodes. Deciding Commoner's
 * condition is co-NP-complete, so the search is exponential in the worst case;
 * past this budget the check answers `inconclusive` and the SMT pipeline
 * decides. Identical in every implementation.
 */
const SIPHON_SEARCH_BUDGET = 10_000;

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
 *
 * Checking every *minimal* siphon suffices, since a trap inside a minimal siphon
 * lies inside every siphon containing it. So `no-potential-deadlock` needs the
 * search to have found **every** minimal siphon, and each one's maximal trap to
 * hold a token in the initial marking.
 */
export function structuralCheck(flatNet: FlatNet, initialMarking: MarkingState): StructuralCheckResult {
  const P = flatNet.places.length;

  if (P === 0) {
    return { type: 'no-potential-deadlock' };
  }

  if (P > MAX_PLACES_FOR_SIPHON_ANALYSIS) {
    return { type: 'inconclusive', reason: `Net has ${P} places, siphon enumeration skipped` };
  }

  const siphons = findMinimalSiphons(flatNet, SIPHON_SEARCH_BUDGET);
  if (siphons === null) {
    return { type: 'inconclusive', reason: `siphon search exceeded ${SIPHON_SEARCH_BUDGET} nodes` };
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
 * Finds all minimal siphons (indices into `flatNet.places`). Exponential in the
 * worst case. Pass `budget` to cap the search; past `budget` search nodes it
 * returns `null`.
 *
 * A siphon is a place set `S` such that every transition with an output in `S`
 * has at least one input in `S`. The search grows `S` from each start place;
 * where a producer into `S` has no input in `S`, it branches on each of that
 * producer's inputs. Every minimal siphon containing the start place is reached
 * by the branch that always picks an input inside it, so the search is complete.
 * Committing to one input instead (the first, or all of them at once) is not:
 * it can miss exactly the unmarked siphon that makes the net dead.
 */
export function findMinimalSiphons(flatNet: FlatNet): ReadonlySet<number>[];
export function findMinimalSiphons(flatNet: FlatNet, budget: number): ReadonlySet<number>[] | null;
export function findMinimalSiphons(
  flatNet: FlatNet, budget = Number.POSITIVE_INFINITY,
): ReadonlySet<number>[] | null {
  const P = flatNet.places.length;
  const found: Set<number>[] = [];
  let nodes = 0;

  const grow = (siphon: Set<number>): boolean => {
    if (++nodes > budget) return false;
    // A superset of a siphon already found cannot lead to a new minimal one.
    if (found.some(f => isSubsetOf(f, siphon))) return true;

    const violating = flatNet.transitions.find(ft => {
      let outputsToSiphon = false;
      let hasInputInSiphon = false;
      for (const p of siphon) {
        if (ft.postVector[p]! > 0) outputsToSiphon = true;
        if (ft.preVector[p]! > 0) hasInputInSiphon = true;
      }
      return outputsToSiphon && !hasInputInSiphon;
    });

    if (violating === undefined) {
      found.push(siphon);
      return true;
    }
    // A producer with no inputs keeps any set holding its output marked: no siphon
    // on this branch. Otherwise branch on each input.
    for (let q = 0; q < P; q++) {
      if (violating.preVector[q]! > 0 && !grow(new Set([...siphon, q]))) return false;
    }
    return true;
  };

  for (let start = 0; start < P; start++) {
    if (!grow(new Set([start]))) return null;
  }

  return found.filter((s, i) => !found.some((other, j) => j !== i && isSubsetOf(other, s)));
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

function isSubsetOf(sub: ReadonlySet<number>, sup: ReadonlySet<number>): boolean {
  if (sub.size > sup.size) return false;
  for (const v of sub) {
    if (!sup.has(v)) return false;
  }
  return true;
}
