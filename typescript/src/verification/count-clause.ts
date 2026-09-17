/**
 * @module count-clause
 *
 * A token count across places, shared by [VER-002]'s `QuiescentCount` and the open-net
 * contract of [VER-022]: how it is counted, which bound a marking breaks, and how it reads
 * in a report. Internal: `verification/index.ts` does not re-export this module.
 */
import type { Place } from '../core/place.js';
import type { MarkingState } from './marking-state.js';

/** `exactly 1`, `at most 1`, `at least 2`, `between 1 and 3`, `any number`. */
export function countPhrase(min: number, max: number): string {
  if (min === max) return `exactly ${min}`;
  if (max === Infinity) return min === 0 ? 'any number' : `at least ${min}`;
  if (min === 0) return `at most ${max}`;
  return `between ${min} and ${max}`;
}

/** `exactly 1 across {a, b}`: the one phrasing of a count clause, for reports and both open-net routes. */
export function countAcross(min: number, max: number, places: Iterable<Place<any>>): string {
  return `${countPhrase(min, max)} across {${[...places].map(p => p.name).join(', ')}}`;
}

/** The tokens `m` holds across `places`, each place counted once. */
export function tokensAcross(m: MarkingState, places: Iterable<Place<any>>): number {
  const seen = new Set<string>();
  let count = 0;
  for (const p of places) {
    if (seen.has(p.name)) continue;
    seen.add(p.name);
    count += m.tokens(p);
  }
  return count;
}

/**
 * Which bound of a count `m` breaks: `upper` above `max` across `places`, `lower` below `min`
 * while no `waivedBy` place is marked, else `null`. Shared by [VER-002]'s `QuiescentCount` on
 * the graph routes and by the open-net contract of [VER-022].
 */
export function countViolation(
  m: MarkingState,
  places: Iterable<Place<any>>,
  min: number,
  max: number,
  waivedBy: Iterable<Place<any>>,
): 'lower' | 'upper' | null {
  const count = tokensAcross(m, places);
  if (count > max) return 'upper';
  if (count < min && !m.hasTokensInAny(waivedBy)) return 'lower';
  return null;
}
