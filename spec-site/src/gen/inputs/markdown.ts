/**
 * Cuts Markdown lines into chunks (paragraphs, lists, tables, fenced code) and joins a chunk
 * back into one Markdown string the app renders: wrapped prose lines are joined with a space,
 * list items, table rows and fenced code keep their own lines.
 */
import { type ScannedLine, THEMATIC_RE } from './alignment.js';

/** A run of lines without a blank line between them (a fence may hold blank lines). */
export interface Chunk {
  /** 1-based file line of the chunk's first line. */
  readonly line: number;
  readonly lines: readonly ScannedLine[];
}

const LIST_ITEM_RE = /^(?:\d{1,9}[.)]|[-*+])(?:\s|$)/;

function indentOf(text: string): number {
  return text.length - text.trimStart().length;
}

/**
 * Splits scanned lines into chunks at blank lines and thematic breaks (`---`). A line matching
 * `startsChunk` (a `**Label:**` line) always opens a new chunk.
 * `firstLine` is the 1-based file line of `lines[0]`.
 */
export function toChunks(lines: readonly ScannedLine[], firstLine: number, startsChunk: RegExp | null = null): Chunk[] {
  const out: Chunk[] = [];
  let cur: { line: number; lines: ScannedLine[] } | null = null;
  for (const [i, l] of lines.entries()) {
    if (l.fence) {
      cur ??= { line: firstLine + i, lines: [] };
      cur.lines.push(l);
      continue;
    }
    if (l.text.trim() === '' || THEMATIC_RE.test(l.text)) {
      if (cur !== null) out.push(cur);
      cur = null;
      continue;
    }
    if (cur !== null && startsChunk !== null && startsChunk.test(l.text)) {
      out.push(cur);
      cur = null;
    }
    cur ??= { line: firstLine + i, lines: [] };
    cur.lines.push(l);
  }
  if (cur !== null) out.push(cur);
  return out;
}

/** Joins the lines of one chunk into Markdown (see the module comment). */
export function joinMarkdown(lines: readonly ScannedLine[]): string {
  const prose = lines.filter((l) => !l.fence && l.text.trim() !== '');
  const base = prose.length === 0 ? 0 : Math.min(...prose.map((l) => indentOf(l.text)));
  const dedent = (text: string): string => text.slice(Math.min(base, indentOf(text)));
  const out: string[] = [];
  let lastWasFence = false;
  let inList = false;
  for (const l of lines) {
    if (l.fence) {
      out.push(dedent(l.text).trimEnd());
      lastWasFence = true;
      continue;
    }
    const trimmed = l.text.trim();
    const last = out.length - 1;
    const item = LIST_ITEM_RE.test(trimmed);
    // A list right after a prose line gets a blank line first, so it reads as a list in any renderer.
    if (item && !inList && out.length > 0 && !lastWasFence) out.push('');
    const startsLine = out.length === 0 || lastWasFence || item || trimmed.startsWith('|');
    if (startsLine) out.push(dedent(l.text).trimEnd());
    else out[last] = `${out[last] ?? ''} ${trimmed}`;
    if (item) inList = true;
    lastWasFence = false;
  }
  return out.join('\n');
}

/**
 * Splits a chunk where a list starts right after prose lines (no blank line between them), so
 * the paragraph and the list become two chunks. Other chunks come back whole.
 */
export function splitProseAndList(chunk: Chunk): Chunk[] {
  const at = chunk.lines.findIndex((l, i) => i > 0 && !l.fence && LIST_ITEM_RE.test(l.text.trim()) && indentOf(l.text) <= 3);
  if (at <= 0 || chunk.lines.slice(0, at).some((l) => l.fence || LIST_ITEM_RE.test(l.text.trim()))) return [chunk];
  return [
    { line: chunk.line, lines: chunk.lines.slice(0, at) },
    { line: chunk.line + at, lines: chunk.lines.slice(at) },
  ];
}

/** True when the chunk is a fenced code block (its first line opens a fence). */
export function isFenced(chunk: Chunk): boolean {
  return chunk.lines[0]?.fence === true;
}
