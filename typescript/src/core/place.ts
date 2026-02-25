/**
 * A typed place in the Petri Net that holds tokens of a specific type.
 *
 * Places are the "state containers" of a Petri net. They hold tokens that
 * represent data or resources flowing through the net.
 *
 * Places use name-based equality (matching Java record semantics).
 * Internally use `Map<string, ...>` keyed by `place.name` for O(1) lookups.
 */
export interface Place<T> {
  readonly name: string;
  /** Phantom field to carry the type parameter. Never set at runtime. */
  readonly _phantom?: T;
}

/**
 * An environment place that accepts external token injection.
 * Wraps a regular Place and marks it for external event injection.
 */
export interface EnvironmentPlace<T> {
  readonly place: Place<T>;
}

/** Creates a typed place. */
export function place<T>(name: string): Place<T> {
  return { name };
}

/** Creates an environment place (external event injection point). */
export function environmentPlace<T>(name: string): EnvironmentPlace<T> {
  return { place: place<T>(name) };
}
