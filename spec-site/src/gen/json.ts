/**
 * Deterministic JSON for the page: object keys sorted (code-unit order), arrays kept in order,
 * no whitespace. `undefined`, functions, non-finite numbers and non-plain objects are refused
 * rather than silently dropped, so the model's "no optional properties" rule holds in the output.
 */

export function stableStringify(value: unknown): string {
  return write(value, '$');
}

function write(value: unknown, path: string): string {
  if (value === null) return 'null';
  switch (typeof value) {
    case 'string':
      return JSON.stringify(value);
    case 'boolean':
      return value ? 'true' : 'false';
    case 'number':
      if (!Number.isFinite(value)) throw new Error(`${path}: non-finite number`);
      return JSON.stringify(value);
    case 'object': {
      if (Array.isArray(value)) return `[${value.map((v: unknown, i) => write(v, `${path}[${i}]`)).join(',')}]`;
      const proto: unknown = Object.getPrototypeOf(value);
      if (proto !== Object.prototype && proto !== null) throw new Error(`${path}: not a plain object`);
      const record = value as Readonly<Record<string, unknown>>;
      const keys = Object.keys(record).sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
      return `{${keys.map((k) => `${JSON.stringify(k)}:${write(record[k], `${path}.${k}`)}`).join(',')}}`;
    }
    default:
      throw new Error(`${path}: cannot serialise ${typeof value}`);
  }
}

/**
 * Makes JSON safe inside `<script type="application/json">`: every `<` becomes the six characters `\u003c`
 * (so no `</script`, `<!--` or `<script` can appear), and U+2028 / U+2029 are escaped too.
 * JSON.parse reads the result back unchanged.
 */
export function escapeJsonForScript(json: string): string {
  return json.replace(/</g, '\\u003c').replace(/\u2028/g, '\\u2028').replace(/\u2029/g, '\\u2029');
}
