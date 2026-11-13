/**
 * Pure text helpers the generator input modules share (no Node APIs, so `site.ts` and the
 * happy-dom tests that build site data can import them).
 */

/** An error naming the input and, when known, its 1-based line: `spec/01-core-model.md:12: ...`. */
export function inputError(file: string, line: number | null, message: string): Error {
  return new Error(`${file}${line === null ? '' : `:${line}`}: ${message}`);
}

/** A requirement ID such as `CORE-031`. */
export const REQ_ID_RE = /^[A-Z]+-\d+$/;

/** Python's `str.splitlines()`: every line boundary Python knows, no trailing empty line. */
export function splitLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split(/\r\n|[\n\r\v\f\x1c\x1d\x1e\x85\u2028\u2029]/);
  if (/(?:\r\n|[\n\r\v\f\x1c\x1d\x1e\x85\u2028\u2029])$/.test(text)) lines.pop();
  return lines;
}

/** Keeps the first occurrence of each value, in order. */
export function unique<T>(values: Iterable<T>): T[] {
  return [...new Set(values)];
}

/** Code-unit string order, the same in every locale. */
export function byString(a: string, b: string): number {
  return a < b ? -1 : a > b ? 1 : 0;
}

/** Sorted (code-unit order) and without repeats. */
export function sortedUnique(values: Iterable<string>): string[] {
  return unique(values).sort(byString);
}
