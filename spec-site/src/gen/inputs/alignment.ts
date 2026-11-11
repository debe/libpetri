/**
 * A port of the section rules of `scripts/spec-lean-alignment.py`: how a spec file is cut into
 * `#### ID:` sections, how a section body is cut into units (paragraphs, list bullets, table
 * rows) and sentences, and when a Lean quote is a whole sentence run of its section.
 *
 * `spec.ts` uses the same line scan and heading rules, so the site and the CI gate agree on
 * which IDs exist and where each block ends. `site.ts` uses `matchQuote` to check that every
 * verbatim Lean quote the reader shows is text of its block. `tests/gen-parity.test.ts` runs
 * the Python script's own functions and compares the results with this port.
 *
 * Keep it a faithful port: the regular expressions and branch order follow the Python source.
 */

/** `^ {0,3}(#{1,6})(?:\s|$)`: an ATX heading; group 1 is the run of `#`. */
export const HEADING_RE = /^ {0,3}(#{1,6})(?:\s|$)/;
/** The canonical requirement heading that opens a section. */
export const CANON_HEADING_RE = /^#### ([A-Z]+-\d+):/;
const FENCE_OPEN_RE = /^( {0,3})(`{3,}|~{3,})(.*)$/;
const LIST_RE = /^(\s*)(\d{1,9}[.)]|[-*+])(?:\s+|$)(.*)$/;
export const THEMATIC_RE = /^ {0,3}([-*_])(?:\s*\1){2,}\s*$/;
const STRIKE_RE = /~~.*?~~/g;
const SENTENCE_SPLIT_RE = /(?:(?<=[.!?])|(?<=[.!?]["')\]]))\s+(?=[A-Z0-9"'`([])/;
export const SHALL_RE = /\bshall\b/i;
const AC_HEAD_RE = /^acceptance criteria:?$/i;

/** Python's `str.splitlines()`: every line boundary Python knows, no trailing empty line. */
export function splitLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split(/\r\n|[\n\r\v\f\x1c\x1d\x1e\x85\u2028\u2029]/);
  if (/(?:\r\n|[\n\r\v\f\x1c\x1d\x1e\x85\u2028\u2029])$/.test(text)) lines.pop();
  return lines;
}

/** Drops markdown emphasis markers (`*`, `_`) and collapses whitespace. */
export function norm(s: string): string {
  return s.replace(/[*_]/g, '').replace(/\s+/g, ' ').trim();
}

/** Splits normalised text into sentences. */
export function sentences(text: string): string[] {
  return text.split(SENTENCE_SPLIT_RE).filter((s) => s !== '');
}

/** Python's `str.expandtabs(4)`. */
function expandTabs(line: string): string {
  let out = '';
  for (const ch of line) {
    if (ch === '\t') out += ' '.repeat(4 - (out.length % 4));
    else out += ch;
  }
  return out;
}

function leadingSpaces(s: string): number {
  return s.length - s.replace(/^ +/, '').length;
}

function escapeRegExp(s: string): string {
  return s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

/** One line after the comment and fence scan. */
export interface ScannedLine {
  /** The line with HTML comments removed (the raw line when `fence` is true). */
  readonly text: string;
  /** True for a fence's opening line, its content and its closing line. */
  readonly fence: boolean;
}

/**
 * The first half of the Python `strip_markdown`: finds fenced code (CommonMark: indented at most
 * three spaces, closed by a fence of the same character at least as long, an unclosed fence runs
 * to the end) and removes HTML comments outside fences. One entry per input line.
 */
export function scanLines(lines: readonly string[]): ScannedLine[] {
  const out: ScannedLine[] = [];
  let inComment = false;
  let fence: RegExp | null = null; // the closing-fence pattern while inside a fence
  for (const line of lines) {
    if (fence !== null) {
      if (fence.test(line)) fence = null;
      out.push({ text: line, fence: true });
      continue;
    }
    if (!inComment) {
      const m = FENCE_OPEN_RE.exec(line);
      const run = m?.[2];
      const info = m?.[3] ?? '';
      if (run !== undefined && !(run[0] === '`' && info.includes('`'))) {
        fence = new RegExp(`^ {0,3}${escapeRegExp(run[0] ?? '`')}{${run.length},}\\s*$`);
        out.push({ text: line, fence: true });
        continue;
      }
    }
    let kept = '';
    let rest = line;
    while (rest !== '') {
      if (inComment) {
        const end = rest.indexOf('-->');
        if (end < 0) rest = '';
        else {
          rest = rest.slice(end + 3);
          inComment = false;
        }
      } else {
        const start = rest.indexOf('<!--');
        if (start < 0) {
          kept += rest;
          rest = '';
        } else {
          kept += rest.slice(0, start);
          rest = rest.slice(start + 4);
          inComment = true;
        }
      }
    }
    out.push({ text: kept, fence: false });
  }
  return out;
}

/** Python `strip_markdown`: comments and fenced code blanked, `~~strikethrough~~` dropped. */
export function stripMarkdown(lines: readonly string[]): string[] {
  return scanLines(lines).map((l) => (l.fence ? '' : l.text.replace(STRIKE_RE, '')));
}

/** True when the stripped line is a heading of level 1 to 4 (the lines that end a section). */
export function isSectionBreak(stripped: string): boolean {
  const m = HEADING_RE.exec(stripped);
  return m !== null && (m[1]?.length ?? 0) <= 4;
}

/** A paragraph, list bullet or table row of a section body, as normalised sentences. */
export interface SpecUnit {
  readonly sents: readonly string[];
  /** The number of a top-level Acceptance Criteria bullet, else null. */
  readonly ac: number | null;
}

type RawUnit = { kind: 'item' | 'para' | 'other'; lines: string[]; num: number | null; indent: number };

/** Python `units`: cuts stripped section body lines into units; drops indented code blocks. */
export function units(body: readonly string[]): SpecUnit[] {
  const raw: RawUnit[] = [];
  let cur: RawUnit | null = null;
  let inList = false;
  const flush = (unit: RawUnit | null): null => {
    if (unit !== null) raw.push(unit);
    return null;
  };

  for (const line of body) {
    if (line.trim() === '') {
      cur = flush(cur);
      continue;
    }
    const exp = expandTabs(line);
    const indent = leadingSpaces(exp);
    if (indent >= 4 && cur === null && !inList) continue;
    if (THEMATIC_RE.test(exp)) {
      cur = flush(cur);
      inList = false;
      continue;
    }
    const m = LIST_RE.exec(exp);
    if (m !== null && (indent < 4 || inList)) {
      cur = flush(cur);
      const marker = m[2] ?? '';
      const num = /^\d/.test(marker) ? Number.parseInt(marker.slice(0, -1), 10) : null;
      cur = { kind: 'item', lines: [m[3] ?? ''], num, indent };
      inList = true;
      continue;
    }
    if (HEADING_RE.test(exp) || exp.trimStart().startsWith('|')) {
      cur = flush(cur);
      raw.push({ kind: 'other', lines: [exp.trim().replace(/^#+/, '')], num: null, indent });
      inList = false;
      continue;
    }
    if (cur !== null) {
      cur.lines.push(exp.trim());
      continue;
    }
    if (!(inList && indent >= 2)) inList = false;
    cur = { kind: 'para', lines: [exp.trim()], num: null, indent };
  }
  cur = flush(cur);

  const result: SpecUnit[] = [];
  let acIndent: number | null = null;
  let inAc = false;
  for (const { kind, lines, num, indent } of raw) {
    const text = norm(lines.join(' '));
    if (text === '') continue;
    let ac: number | null = null;
    if (kind === 'para' && AC_HEAD_RE.test(text)) {
      inAc = true;
      acIndent = null;
    } else if (kind === 'item' && inAc) {
      if (num !== null && (acIndent === null || indent === acIndent)) {
        acIndent = indent;
        ac = num;
      }
    } else if (inAc && !(kind === 'para' && acIndent !== null && indent > acIndent)) {
      inAc = false;
    }
    result.push({ sents: sentences(text), ac });
  }
  return result;
}

/** A `#### ID:` section of one file. */
export interface AlignmentSection {
  readonly id: string;
  readonly file: string;
  /** 1-based line of the heading. */
  readonly line: number;
  /** Index of the first line after the section (0-based, exclusive). */
  readonly end: number;
  readonly units: readonly SpecUnit[];
}

/**
 * The `#### ID:` sections of one file, in line order, as the Python `spec_sections` finds them.
 * A duplicate heading inside the file is returned too; the caller decides (`spec.ts` fails).
 */
export function fileSections(file: string, lines: readonly string[]): AlignmentSection[] {
  const stripped = stripMarkdown(lines);
  const breaks = stripped.map(isSectionBreak);
  const out: AlignmentSection[] = [];
  for (let i = 0; i < stripped.length; i++) {
    if (breaks[i] !== true) continue;
    const m = CANON_HEADING_RE.exec(stripped[i] ?? '');
    const id = m?.[1];
    if (id === undefined) continue;
    let j = i + 1;
    while (j < stripped.length && breaks[j] !== true) j++;
    out.push({ id, file, line: i + 1, end: j, units: units(stripped.slice(i + 1, j)) });
  }
  return out;
}

/** Positions `[unit, sentence]` covered by every whole-sentence run equal to `q` (normalised). */
export function matchQuote(q: string, sectionUnits: readonly SpecUnit[]): Array<readonly [number, number]> {
  const hits: Array<readonly [number, number]> = [];
  sectionUnits.forEach((u, ui) => {
    for (let a = 0; a < u.sents.length; a++) {
      let run = '';
      for (let b = a; b < u.sents.length; b++) {
        const s = u.sents[b] ?? '';
        run = b === a ? s : `${run} ${s}`;
        if (run.length > q.length) break;
        if (run === q) {
          for (let k = a; k <= b; k++) hits.push([ui, k]);
          break;
        }
      }
    }
  });
  return hits;
}

/** True when the Lean quote is a whole sentence, sentence run or bullet of the section. */
export function quotePresent(quote: string, sectionUnits: readonly SpecUnit[]): boolean {
  const q = norm(quote);
  return q !== '' && matchQuote(q, sectionUnits).length > 0;
}
