import type { EnvironmentPlace, Place } from '../place.js';

/**
 * The names of `places`, as a set to test membership against.
 *
 * A TypeScript place is identified by its name: `place('p')` called twice gives two objects that
 * are one place (the [MOD-024] note). A `Set<Place>` compares objects, so code that asks whether
 * a place belongs to a group of places asks through the names instead. Rust compares places by
 * name and Java by record equality, so this keeps the TypeScript answer the same as theirs.
 */
export function placeNames(places: Iterable<Place<any>>): Set<string> {
  const names = new Set<string>();
  for (const p of places) names.add(p.name);
  return names;
}

/** The names of the places `environmentPlaces` wrap ({@link placeNames}). */
export function environmentPlaceNames(environmentPlaces: Iterable<EnvironmentPlace<any>>): Set<string> {
  const names = new Set<string>();
  for (const ep of environmentPlaces) names.add(ep.place.name);
  return names;
}
