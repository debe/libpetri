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

/**
 * A relay target of a join (NU-054): an **output** place onto which the join writes the name
 * it matched, with the projection that reads a produced token's name. Built by
 * {@link relayKey}; told apart from a {@link MatchKey} by its `relay` tag.
 */
export interface RelayKey<T = any> extends MatchKey<T> {
  readonly relay: true;
}

/** Correlated fork/join match specification (ν-net join side). */
export interface MatchSpec {
  readonly keys: readonly MatchKey[];
  /**
   * Relay targets (NU-054): output places onto which the join writes the matched name. Empty
   * for a join that drains the name. Each must be an output of the transition and appear once
   * (checked when the transition is built); a relay target may also be one of the `keys` (a
   * correlated self-loop). The executor checks every token a firing writes into one against the
   * matched name, as part of output validation (IO-015).
   */
  readonly relays: readonly MatchKey[];
}

/** Builds one correlated input for a {@link MatchSpec}. */
export function matchKey<T>(place: Place<T>, key: KeyFn<T>): MatchKey<T> {
  return { place, key };
}

/**
 * Builds one relay target for a {@link MatchSpec} (NU-054): the join writes the name it matched
 * onto `place`, an output of the transition, and `key` projects a produced token's name. A relay
 * target does not count towards the two correlated inputs {@link matchSpec} requires.
 *
 * @example
 *   Transition.builder('e')
 *     .inputs(one(c1), one(d1))
 *     .outputs(outPlace(p5))
 *     .match(matchSpec(matchKey(c1, byCase), matchKey(d1, byCase), relayKey(p5, byCase)))
 */
export function relayKey<T>(place: Place<T>, key: KeyFn<T>): RelayKey<T> {
  return { place, key, relay: true };
}

function isRelay(k: MatchKey): k is RelayKey {
  return (k as Partial<RelayKey>).relay === true;
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
 * {@link relayKey} entries may be mixed in anywhere; they become {@link MatchSpec.relays} and
 * do not count as correlated inputs.
 *
 * @throws if fewer than two inputs are correlated (a match over a single place
 *   correlates nothing).
 */
export function matchSpec(...entries: MatchKey[]): MatchSpec {
  const keys: MatchKey[] = [];
  const relays: MatchKey[] = [];
  for (const e of entries) {
    if (isRelay(e)) relays.push({ place: e.place, key: e.key });
    else keys.push(e);
  }
  if (keys.length < 2) {
    throw new Error(`MatchSpec must correlate at least 2 input places, got ${keys.length}`);
  }
  return { keys, relays };
}

/** Returns the relay projection for `placeName`, or `undefined` if it is not a relay target. */
export function relayKeyForPlace(spec: MatchSpec, placeName: string): KeyFn | undefined {
  for (const r of spec.relays) {
    if (r.place.name === placeName) return r.key;
  }
  return undefined;
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
