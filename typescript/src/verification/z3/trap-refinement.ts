/**
 * @module trap-refinement
 *
 * Trap refinement for the state-equation phase (VER-018), after Esparza,
 * Ledesma-Garza, Majumdar, Meyer and Niksic, "An SMT-based approach to coverability
 * analysis" (CAV 2014).
 *
 * A **trap** is a set of places `Q` such that every transition that removes a token
 * from `Q` also puts one into `Q`. A trap marked at `M0` stays marked in every
 * reachable marking, so a candidate that leaves an initially marked trap empty is not
 * reachable, and `Σ_{q∈Q} m_q ≥ 1` refutes it.
 *
 * "Removes a token" is generalised to the arcs the ordinary definition does not know:
 * a consume-all input or a reset arc on a place of `Q` removes tokens from `Q` whatever
 * its weight, so that transition must also put one into `Q`. Read and inhibitor arcs
 * remove nothing, and environment injection only adds tokens. No solver is involved.
 */
import type { FlatNet } from '../encoding/flat-net.js';
import type { FlatTransition } from '../encoding/flat-transition.js';
import type { MarkingInequality } from './state-equation-query.js';

/**
 * An initially marked trap the candidate leaves empty, as the inequality
 * `Σ_{q∈Q} m_q ≥ 1`, or `null` when there is none. The trap is shrunk to a locally
 * minimal one: a smaller trap is a stronger constraint on the next candidate.
 */
export function refutingTrap(
  flatNet: FlatNet,
  initial: readonly number[],
  candidate: readonly number[],
): MarkingInequality | null {
  const drains = flatNet.transitions.map(drainedPlaces);
  const feeds = flatNet.transitions.map(fedPlaces);
  const empty = new Set<number>();
  for (let p = 0; p < candidate.length; p++) if (candidate[p] === 0) empty.add(p);
  let trap = maximalTrap(empty, drains, feeds);
  if (!markedIn(trap, initial)) return null;
  for (const p of [...trap].sort((a, b) => a - b)) {
    // A snapshot of the trap we started from, while `trap` shrinks underneath: a place an
    // earlier round already dropped is no longer a candidate for dropping.
    if (!trap.has(p)) continue;
    const without = new Set(trap);
    without.delete(p);
    const smaller = maximalTrap(without, drains, feeds);
    if (markedIn(smaller, initial)) trap = smaller;
  }
  const weights = new Array<bigint>(flatNet.places.length).fill(0n);
  for (const p of trap) weights[p] = -1n;
  return { weights, constant: -1n, origin: 'trap' };
}

/**
 * The largest trap inside `within` (possibly empty): repeatedly drop the places a
 * transition drains when it feeds nothing back into what is left. Traps are closed
 * under union, so the result contains every trap inside `within`.
 */
function maximalTrap(
  within: ReadonlySet<number>,
  drains: readonly (readonly number[])[],
  feeds: readonly (readonly number[])[],
): Set<number> {
  const trap = new Set(within);
  let changed = true;
  while (changed) {
    changed = false;
    for (let t = 0; t < drains.length; t++) {
      if (!drains[t]!.some((p) => trap.has(p))) continue;
      if (feeds[t]!.some((p) => trap.has(p))) continue;
      for (const p of drains[t]!) if (trap.delete(p)) changed = true;
    }
  }
  return trap;
}

/** The places a firing of `ft` can take tokens from: its inputs, consume-all places and reset places. */
function drainedPlaces(ft: FlatTransition): number[] {
  const out = new Set<number>(ft.resetPlaces);
  for (let p = 0; p < ft.preVector.length; p++) {
    if (ft.preVector[p]! > 0 || ft.consumeAll[p]) out.add(p);
  }
  return [...out].sort((a, b) => a - b);
}

/** The places a firing of `ft` puts at least one token into. */
function fedPlaces(ft: FlatTransition): number[] {
  const out: number[] = [];
  for (let p = 0; p < ft.postVector.length; p++) if (ft.postVector[p]! > 0) out.push(p);
  return out;
}

function markedIn(places: ReadonlySet<number>, marking: readonly number[]): boolean {
  for (const p of places) if (marking[p]! > 0) return true;
  return false;
}
