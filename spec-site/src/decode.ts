/**
 * Tiny typed JSON decoders. A `Decoder<T>` checks an `unknown` value and returns it as `T`, or
 * throws a `DecodeError` naming the JSON path. Objects are exact: a missing key and an unknown
 * key both fail, so the generator's output and the model cannot drift apart silently.
 *
 * Used by the app to read the embedded `SiteData` once (`decode-site.ts`) and by generator
 * input modules to read JSON inputs (situations, Lean replay results, requirements.json).
 * No Node or DOM APIs here: it compiles under both tsconfigs.
 */

export type Decoder<T> = (value: unknown, path: string) => T;
export type DecodedOf<D> = D extends Decoder<infer T> ? T : never;
type Primitive = string | number | boolean | null;

export class DecodeError extends Error {
  readonly path: string;
  constructor(path: string, message: string) {
    super(`${path || '$'}: ${message}`);
    this.name = 'DecodeError';
    this.path = path;
  }
}

function describe(value: unknown): string {
  if (value === null) return 'null';
  if (Array.isArray(value)) return 'array';
  return typeof value;
}

/** Runs a decoder from the root, `$`. */
export function decode<T>(decoder: Decoder<T>, value: unknown): T {
  return decoder(value, '$');
}

export const str: Decoder<string> = (v, p) => {
  if (typeof v !== 'string') throw new DecodeError(p, `expected string, got ${describe(v)}`);
  return v;
};

export const num: Decoder<number> = (v, p) => {
  if (typeof v !== 'number' || !Number.isFinite(v)) throw new DecodeError(p, `expected finite number, got ${describe(v)}`);
  return v;
};

export const int: Decoder<number> = (v, p) => {
  if (typeof v !== 'number' || !Number.isSafeInteger(v)) throw new DecodeError(p, `expected integer, got ${describe(v)}`);
  return v;
};

export const bool: Decoder<boolean> = (v, p) => {
  if (typeof v !== 'boolean') throw new DecodeError(p, `expected boolean, got ${describe(v)}`);
  return v;
};

/** Exactly one of the listed primitive values. */
export function oneOf<const T extends readonly Primitive[]>(values: T): Decoder<T[number]> {
  return (v, p) => {
    for (const allowed of values) if (v === allowed) return allowed;
    throw new DecodeError(p, `expected one of ${JSON.stringify(values)}, got ${JSON.stringify(v)}`);
  };
}

/** Exactly this primitive value. */
export function lit<const T extends Primitive>(value: T): Decoder<T> {
  return (v, p) => {
    if (v !== value) throw new DecodeError(p, `expected ${JSON.stringify(value)}, got ${JSON.stringify(v)}`);
    return value;
  };
}

export function nullable<T>(decoder: Decoder<T>): Decoder<T | null> {
  return (v, p) => (v === null ? null : decoder(v, p));
}

export function arr<T>(decoder: Decoder<T>): Decoder<readonly T[]> {
  return (v, p) => {
    if (!Array.isArray(v)) throw new DecodeError(p, `expected array, got ${describe(v)}`);
    return v.map((item: unknown, i) => decoder(item, `${p}[${i}]`));
  };
}

function isPlainObject(v: unknown): v is Record<string, unknown> {
  return typeof v === 'object' && v !== null && !Array.isArray(v);
}

/** A string-keyed map whose values all decode with `decoder`. */
export function rec<T>(decoder: Decoder<T>): Decoder<Readonly<Record<string, T>>> {
  return (v, p) => {
    if (!isPlainObject(v)) throw new DecodeError(p, `expected object, got ${describe(v)}`);
    const out: Record<string, T> = {};
    for (const key of Object.keys(v)) out[key] = decoder(v[key], `${p}.${key}`);
    return out;
  };
}

type Shape = { readonly [key: string]: Decoder<unknown> };
type ShapeOut<S extends Shape> = { readonly [K in keyof S]: DecodedOf<S[K]> };

/** An object with exactly the keys of `shape`. */
export function obj<S extends Shape>(shape: S): Decoder<ShapeOut<S>> {
  const keys = Object.keys(shape);
  return (v, p) => {
    if (!isPlainObject(v)) throw new DecodeError(p, `expected object, got ${describe(v)}`);
    for (const key of Object.keys(v)) {
      if (!Object.hasOwn(shape, key)) throw new DecodeError(`${p}.${key}`, 'unknown key');
    }
    const out: Record<string, unknown> = {};
    for (const key of keys) {
      if (!Object.hasOwn(v, key)) throw new DecodeError(`${p}.${key}`, 'missing key');
      const field = shape[key];
      if (field === undefined) continue;
      out[key] = field(v[key], `${p}.${key}`);
    }
    return out as ShapeOut<S>;
  };
}

/**
 * A discriminated union: reads `value[key]`, picks the member decoder registered for that tag,
 * and decodes the whole object with it (the member decoder checks the tag again with `lit`).
 */
export function tagged<K extends string, M extends { readonly [tag: string]: Decoder<unknown> }>(
  key: K,
  members: M,
): Decoder<DecodedOf<M[keyof M]>> {
  return (v, p) => {
    if (!isPlainObject(v)) throw new DecodeError(p, `expected object, got ${describe(v)}`);
    const tag = v[key];
    if (typeof tag !== 'string' || !Object.hasOwn(members, tag)) {
      throw new DecodeError(`${p}.${key}`, `unknown tag ${JSON.stringify(tag)}; expected one of ${JSON.stringify(Object.keys(members))}`);
    }
    const member = members[tag];
    if (member === undefined) throw new DecodeError(`${p}.${key}`, 'no decoder');
    return member(v, p) as DecodedOf<M[keyof M]>;
  };
}

/** Defers building a decoder, for recursive types. Annotate the recursive constant's type. */
export function lazy<T>(make: () => Decoder<T>): Decoder<T> {
  let cached: Decoder<T> | undefined;
  return (v, p) => {
    cached ??= make();
    return cached(v, p);
  };
}

/** Post-checks a decoded value; `check` returns an error message or null. */
export function refine<T>(decoder: Decoder<T>, check: (value: T) => string | null): Decoder<T> {
  return (v, p) => {
    const out = decoder(v, p);
    const problem = check(out);
    if (problem !== null) throw new DecodeError(p, problem);
    return out;
  };
}
