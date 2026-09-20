/**
 * Prototype-less marking records.
 *
 * The UI keys markings by **place name**, and a place name is arbitrary host text: `__proto__`,
 * `constructor` and `toString` are all legal, and the server keeps such a place on every marking
 * it sends. On an ordinary `{}` they collide with `Object.prototype`:
 *
 * - `marking['__proto__'] = tokens`, and `Object.assign(marking, wire)`, go through `[[Set]]` and
 *   hit the inherited `__proto__` setter — no own key is created and the token array becomes
 *   the marking's prototype, so the place vanishes from `Object.keys` and the marking starts
 *   answering to `length`;
 * - `marking['constructor']` on a marking without that place reads the inherited member and
 *   returns a function where the caller expects a token array or `undefined`.
 *
 * A record built on `Object.create(null)` inherits nothing, so every name is an ordinary own
 * key under plain `[]` reads and writes — which is what lets the rest of the UI keep its
 * `Record<string, …>` types and its `Object.keys` / `Object.entries` walks unchanged. Every
 * marking the UI *creates or re-keys* comes from here; the same choice the server makes in
 * `mapToRecord` / `convertMarking`.
 *
 * Note for callers: object spread and `structuredClone` both keep an own `__proto__` key but
 * hand back an ordinary object, so a later write of a *new* colliding name is lost again. Wrap
 * them in {@link copyMarking}.
 */

/** A new, empty marking record with no prototype. */
export function emptyMarking<T>(): Record<string, T> {
  return Object.create(null) as Record<string, T>;
}

/**
 * A prototype-less shallow copy of `source`: every own enumerable key, in order, and nothing
 * inherited. `source` may be an ordinary object (a `JSON.parse` result defines `__proto__` as an
 * own key, so it is read back correctly here) or another record; `null`/`undefined` copy to an
 * empty record. Token arrays are shared, not cloned.
 */
export function copyMarking<T>(source: Readonly<Record<string, T>> | null | undefined): Record<string, T> {
  const out = emptyMarking<T>();
  if (source === null || source === undefined) return out;
  for (const name of Object.keys(source)) {
    out[name] = source[name]!;
  }
  return out;
}
