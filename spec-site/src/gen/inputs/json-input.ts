/**
 * Decoding helpers for the JSON inputs (requirements.json, situations, replay files). They reuse
 * the exact decoders of `decode.ts` and add what an authored file needs: optional keys.
 */
import { type DecodedOf, type Decoder, DecodeError } from '../../decode.js';

type Shape = { readonly [key: string]: Decoder<unknown> };
type Required<S extends Shape> = { readonly [K in keyof S]: DecodedOf<S[K]> };
type Optional<S extends Shape> = { readonly [K in keyof S]: DecodedOf<S[K]> | undefined };

function isPlainObject(v: unknown): v is Record<string, unknown> {
  return typeof v === 'object' && v !== null && !Array.isArray(v);
}

/**
 * An object whose `required` keys must be present and whose `optional` keys may be; any other
 * key fails. An absent optional key decodes to `undefined` (the caller fills the default).
 */
export function objWith<R extends Shape, O extends Shape>(required: R, optional: O): Decoder<Required<R> & Optional<O>> {
  return (v, p) => {
    if (!isPlainObject(v)) throw new DecodeError(p, `expected object, got ${Array.isArray(v) ? 'array' : v === null ? 'null' : typeof v}`);
    for (const key of Object.keys(v)) {
      if (!Object.hasOwn(required, key) && !Object.hasOwn(optional, key)) throw new DecodeError(`${p}.${key}`, 'unknown key');
    }
    const out: Record<string, unknown> = {};
    for (const [key, decoder] of Object.entries(required)) {
      if (!Object.hasOwn(v, key)) throw new DecodeError(`${p}.${key}`, 'missing key');
      out[key] = decoder(v[key], `${p}.${key}`);
    }
    for (const [key, decoder] of Object.entries(optional)) {
      out[key] = Object.hasOwn(v, key) ? decoder(v[key], `${p}.${key}`) : undefined;
    }
    // Every key of R and O was written above with its decoder's output type.
    return out as Required<R> & Optional<O>;
  };
}

/** Parses JSON text; a syntax error names the file. */
export function parseJson(text: string, file: string): unknown {
  try {
    return JSON.parse(text) as unknown;
  } catch (error) {
    throw new Error(`${file}: not valid JSON (${error instanceof Error ? error.message : String(error)})`);
  }
}

/** Runs a decoder on a file's JSON; a decode error is prefixed with the file name. */
export function decodeFile<T>(decoder: Decoder<T>, value: unknown, file: string): T {
  try {
    return decoder(value, '$');
  } catch (error) {
    if (error instanceof DecodeError) throw new Error(`${file}: ${error.message}`);
    throw error;
  }
}
