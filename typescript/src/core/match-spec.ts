/**
 * ν-net join correlation ([[MatchSpec]]).
 *
 * A {@link MatchSpec} declares that a subset of a transition's **input** places
 * must be correlated by **name equality**: the transition is enabled only when
 * there exists a single {@link NameId} `n` such that every correlated input
 * supplies (at least) its required token count whose projected name equals `n`.
 * On firing, exactly those name-matched tokens are consumed (spec NU-020).
 *
 * This is the single *decidable* predicate — equality of opaque names — and is
 * deliberately NOT a general input predicate: it correlates the name dimension
 * *across* places (composition-structural, like cardinality) rather than
 * evaluating an arbitrary boolean per token. Input specifications themselves
 * remain purely structural (IO-006); name correlation is the only per-token
 * filter the enablement check ever applies (NU-021).
 */
import type { Place } from './place.js';
import type { NameId } from './name.js';

/**
 * A name projection: maps a token's value to its {@link NameId}. A projection
 * that yields no name (returns `null`/`undefined` at runtime) is treated as
 * "no name" — that token never correlates — mirroring the Java/Rust `KeyFn`
 * contract; the binding selector handles a nullish result defensively.
 */
export type KeyFn<T = any> = (value: T) => NameId;

/** One correlated input: the place plus its name projection. */
export interface MatchKey<T = any> {
  readonly place: Place<T>;
  readonly key: KeyFn<T>;
}

/** Correlated fork/join match specification (ν-net join side). */
export interface MatchSpec {
  readonly keys: readonly MatchKey[];
}

/** Builds one correlated input for a {@link MatchSpec}. */
export function matchKey<T>(place: Place<T>, key: KeyFn<T>): MatchKey<T> {
  return { place, key };
}

/**
 * Builds a {@link MatchSpec} from two or more correlated inputs.
 *
 * @example
 *   Transition.builder('join')
 *     .inputs(one(branchA), one(branchB))
 *     .match(matchSpec(
 *       matchKey(branchA, (m: Msg) => nameId(m.correlationId)),
 *       matchKey(branchB, (m: Msg) => nameId(m.correlationId)),
 *     ))
 *
 * @throws if fewer than two inputs are correlated (a match over a single place
 *   correlates nothing).
 */
export function matchSpec(...keys: MatchKey[]): MatchSpec {
  if (keys.length < 2) {
    throw new Error(`MatchSpec must correlate at least 2 input places, got ${keys.length}`);
  }
  return { keys };
}

/** Returns the name projection for `placeName`, or `undefined` if not correlated. */
export function keyForPlace(spec: MatchSpec, placeName: string): KeyFn | undefined {
  for (const k of spec.keys) {
    if (k.place.name === placeName) return k.key;
  }
  return undefined;
}

/** True when `placeName` is one of the correlated inputs. */
export function matchCorrelates(spec: MatchSpec, placeName: string): boolean {
  return spec.keys.some(k => k.place.name === placeName);
}
