/**
 * ν-net token identities ([[NameId]]).
 *
 * A {@link NameId} is an **opaque correlation identity** carried by a token so
 * that a fork can mint a fresh name and a later join can re-merge exactly the
 * siblings that share it (see {@link import('./match-spec.js').MatchSpec}). The
 * only operation defined on names is **equality** (`===`); names also have a
 * lexicographic order used purely for the deterministic match tie-break
 * (NU-020).
 *
 * Identity is a *projection* of the token payload, not a field on
 * {@link import('./token.js').Token}: a `MatchSpec` declares the
 * `value → NameId` key, and the fork mints a fresh name into the payload via
 * `ctx.freshName()`. This keeps `Token` (and the event/archive formats)
 * unchanged while still giving the analyzer a name-symmetric uninterpreted sort
 * to reason about (spec NU-001).
 */

/** An opaque correlation identity for ν-net fork/join (a branded string). */
export type NameId = string & { readonly __nameIdBrand: unique symbol };

/** Creates a {@link NameId} from a string. */
export function nameId(value: string): NameId {
  return value as NameId;
}
