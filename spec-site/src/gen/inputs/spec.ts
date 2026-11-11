/**
 * Input: the numbered spec files `spec/NN-*.md` and the registry `spec/00-index.md`.
 *
 * Sections follow the rules of `scripts/spec-lean-alignment.py` (ported in `alignment.ts`): a
 * block opens at a canonical `#### ID:` heading outside comments and fenced code and ends at the
 * next heading of level 1 to 4. Active IDs and tombstones come from the index's Alphabetical
 * Cross-Reference tables, as both Python checkers read them; the parsed blocks must match them.
 *
 * Inside a block, chunks (paragraphs, lists, tables, fenced code; a `**Label:**` line always
 * opens a chunk) are sorted into fields:
 * - `**Priority:**`, `**Kind:**`, `**Status:**`, `**Depends on:**`: metadata.
 * - `**Acceptance Criteria:**` (or `**Acceptance criteria (MAY):**`): its list items; a list
 *   chunk right after it continues the list, an indented chunk continues the last item.
 * - `**Test derivation:**`: the test derivation; later unlabelled chunks continue it.
 * - Any other label (`**Note:**`, `**Implementation notes:**`, ...): a note; later unlabelled
 *   chunks continue it unless they hold a *shall* sentence, which is body text.
 * - Every other chunk is a body paragraph: `shall` when it holds the word *shall*, else `prose`.
 */
import { readdirSync } from 'node:fs';
import type { BlockNote, BodyParagraph, GlossaryTerm, Priority, ReqId, ReqKind, SpecBlock, SpecFile, SpecSection } from '../../model.js';
import { PRIORITIES, REQ_KINDS } from '../../model.js';
import { type AlignmentSection, fileSections, HEADING_RE, type ScannedLine, scanLines, SHALL_RE, type SpecUnit, splitLines, stripMarkdown } from './alignment.js';
import { type Chunk, isFenced, joinMarkdown, splitProseAndList, toChunks } from './markdown.js';
import { readSource } from './source.js';
import { bracketIds, byString, inputError, REQ_ID_RE, sortedUnique, unique } from './text.js';
import { repoPath } from '../paths.js';

export interface SpecInput {
  readonly files: readonly SpecFile[];
  readonly blocks: readonly SpecBlock[];
  /**
   * The alignment units of every block (Python `units`), for the Lean quote check in `site.ts`.
   * `readSpec` always fills it; hand-built test fixtures leave it out, and then `buildSiteData`
   * skips its cross-input checks (see `checkSiteInputs` in `site.ts`).
   */
  readonly units?: ReadonlyMap<ReqId, readonly SpecUnit[]>;
}

export const SPEC_DIR = 'spec';
export const SPEC_INDEX_FILE = 'spec/00-index.md';
/** Numbered spec files: `01-core-model.md` ... (the index `00-` is not one). */
export const SPEC_FILE_RE = /^(\d{2})-[a-z0-9-]+\.md$/;

// ---------------------------------------------------------------------------------------------
// spec/00-index.md
// ---------------------------------------------------------------------------------------------

export interface IndexFileRow {
  readonly file: string;
  readonly prefix: string;
  readonly count: number;
}

export interface SpecIndex {
  readonly active: ReadonlySet<ReqId>;
  readonly tombstones: ReadonlySet<ReqId>;
  /** Rows of the Spec Files table. */
  readonly files: readonly IndexFileRow[];
}

const TOMB_CELL_RE = /^~~\s*([A-Z]+-\d+)\s*~~/;
const ID_CELL_RE = /^([A-Z]+-\d+)$/;
const FILE_ROW_RE = /^\|\s*\[(\d{2}-[a-z0-9-]+\.md)\]\([^)]*\)\s*\|\s*([A-Z]+)\s*\|.*\|\s*(\d+)\s*\|\s*$/;

/** Port of `active_ids` (spec-lean-alignment.py / spec-coverage-matrix.py) plus the Spec Files table. */
export function parseSpecIndex(text: string, file: string = SPEC_INDEX_FILE): SpecIndex {
  const files: IndexFileRow[] = [];
  for (const line of splitLines(text)) {
    const m = FILE_ROW_RE.exec(line);
    if (m !== null) files.push({ file: m[1] ?? '', prefix: m[2] ?? '', count: Number(m[3]) });
  }
  const start = text.indexOf('## Alphabetical Cross-Reference Index');
  if (start < 0) throw inputError(file, null, "'## Alphabetical Cross-Reference Index' heading not found");
  const rest = text.slice(start);
  const end = /\n## (?!#)/.exec(rest.slice(1));
  const section = end === null ? rest : rest.slice(0, end.index + 1);

  const active = new Set<ReqId>();
  const tombstones = new Set<ReqId>();
  let prefix: string | null = null;
  for (const line of splitLines(section)) {
    const h = /^### ([A-Z]+) — /.exec(line);
    if (h !== null) {
      prefix = h[1] ?? null;
      continue;
    }
    if (prefix === null || !line.startsWith('|')) continue;
    const cells = line
      .trim()
      .replace(/^\|+|\|+$/g, '')
      .split('|')
      .map((c) => c.trim());
    if (cells.length < 3) continue;
    const first = cells[0] ?? '';
    if (first === 'ID' || first === '' || /^[- ]+$/.test(first)) continue;
    const tomb = TOMB_CELL_RE.exec(first);
    if (tomb?.[1] !== undefined) {
      tombstones.add(tomb[1]);
      continue;
    }
    const id = ID_CELL_RE.exec(first)?.[1];
    if (id !== undefined) active.add(id);
  }
  if (active.size === 0) throw inputError(file, null, 'no active IDs in the cross-reference index');
  if (files.length === 0) throw inputError(file, null, 'no rows in the Spec Files table');
  return { active, tombstones, files };
}

// ---------------------------------------------------------------------------------------------
// Glossary terms in block text
// ---------------------------------------------------------------------------------------------

export interface TermMatcher {
  readonly slug: string;
  readonly re: RegExp;
}

/** A case-insensitive whole-word matcher for each term, allowing a plural `s` / `es`. */
export function termMatchers(glossary: readonly GlossaryTerm[]): TermMatcher[] {
  return glossary.map((g) => {
    const words = g.term
      .trim()
      .split(/\s+/)
      .map((w) => w.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'))
      .join('\\s+');
    return { slug: g.slug, re: new RegExp(`(?<![\\p{L}\\p{N}_-])${words}(?:s|es)?(?![\\p{L}\\p{N}_-])`, 'iu') };
  });
}

/** Slugs of the terms that occur in the text, outside code spans, link targets and IDs. Sorted. */
export function termsIn(text: string, matchers: readonly TermMatcher[]): string[] {
  const plain = text
    .replace(/`[^`]*`/g, ' ')
    .replace(/\]\([^)]*\)/g, '] ')
    .replace(/\[[A-Z]+-\d+\]/g, ' ');
  return sortedUnique(matchers.filter((m) => m.re.test(plain)).map((m) => m.slug));
}

// ---------------------------------------------------------------------------------------------
// One block
// ---------------------------------------------------------------------------------------------

const LABEL_RE = /^\*\*([^*]+?):\*\*\s*(.*)$/;
const LIST_MARKER_RE = /^(\s*)(?:\d{1,9}[.)]|[-*+])(?:\s+|$)/;

type Field = { kind: 'body' } | { kind: 'meta' } | { kind: 'ac' } | { kind: 'test' } | { kind: 'note'; index: number };

interface BlockFields {
  priority: Priority | null;
  kind: ReqKind | null;
  status: 'proposed' | 'removed' | null;
  dependsOn: ReqId[];
  body: BodyParagraph[];
  acceptance: string[];
  notes: BlockNote[];
  testDerivation: string | null;
  /** Text of every chunk except Depends on lines, for `mentions`. */
  cited: string[];
}

function indentOf(text: string): number {
  return text.length - text.trimStart().length;
}

/** Cuts list lines into items without their markers; nested lines are dedented to the item. */
function listItems(lines: readonly ScannedLine[], where: () => Error): string[] {
  const items: ScannedLine[][] = [];
  let column = 0;
  for (const l of lines) {
    const marker = l.fence ? null : LIST_MARKER_RE.exec(l.text);
    // A marker opens a new item when it sits left of the current item's content column; further
    // right it is a nested list, part of the item.
    if (marker !== null && indentOf(l.text) < (items.length === 0 ? 4 : column)) {
      column = marker[0].length;
      items.push([{ text: l.text.slice(column), fence: false }]);
      continue;
    }
    const item = items[items.length - 1];
    if (item === undefined) throw where();
    item.push({ text: l.text.slice(Math.min(column, indentOf(l.text))), fence: l.fence });
  }
  return items.map(joinMarkdown);
}

const FENCE_LINE_RE = /^ {0,3}(?:`{3,}|~{3,})/;

/** Cuts a chunk where fenced code starts or ends, so prose and code become separate chunks. */
function splitFences(chunk: Chunk): Chunk[] {
  const out: Chunk[] = [];
  let start = 0;
  for (let i = 1; i < chunk.lines.length; i++) {
    if (chunk.lines[i]?.fence !== chunk.lines[i - 1]?.fence) {
      out.push({ line: chunk.line + start, lines: chunk.lines.slice(start, i) });
      start = i;
    }
  }
  out.push({ line: chunk.line + start, lines: chunk.lines.slice(start) });
  return out;
}

/** A body chunk: fenced code keeps its lines without the fences; other text is shall or prose. */
function bodyParagraph(chunk: Chunk): BodyParagraph {
  if (isFenced(chunk)) {
    const lines = chunk.lines.map((l) => l.text.trimEnd());
    const last = lines[lines.length - 1];
    const closed = lines.length > 1 && last !== undefined && FENCE_LINE_RE.test(last);
    return { kind: 'code', text: lines.slice(1, closed ? -1 : undefined).join('\n') };
  }
  const text = joinMarkdown(chunk.lines);
  return SHALL_RE.test(text) ? { kind: 'shall', text } : { kind: 'prose', text };
}

function parseFields(file: string, chunks: readonly Chunk[]): BlockFields {
  const f: BlockFields = {
    priority: null,
    kind: null,
    status: null,
    dependsOn: [],
    body: [],
    acceptance: [],
    notes: [],
    testDerivation: null,
    cited: [],
  };
  let field: Field = { kind: 'body' };

  for (const chunk of chunks) {
    const first = chunk.lines[0];
    const label = first === undefined || first.fence ? null : LABEL_RE.exec(first.text);
    const at = (message: string): Error => inputError(file, chunk.line, message);

    if (label === null) {
      const text = joinMarkdown(chunk.lines);
      f.cited.push(text);
      if (field.kind === 'ac') {
        if (first !== undefined && !first.fence && LIST_MARKER_RE.test(first.text) && indentOf(first.text) < 2) {
          f.acceptance.push(...listItems(chunk.lines, () => at('list item expected')));
          continue;
        }
        const last = f.acceptance.length - 1;
        if (first !== undefined && indentOf(first.text) >= 2 && last >= 0) {
          f.acceptance[last] = `${f.acceptance[last] ?? ''}\n\n${text}`;
          continue;
        }
      } else if (field.kind === 'test') {
        f.testDerivation = `${f.testDerivation ?? ''}\n\n${text}`;
        continue;
      } else if (field.kind === 'note' && !SHALL_RE.test(text)) {
        const note = f.notes[field.index];
        if (note !== undefined) f.notes[field.index] = { label: note.label, text: `${note.text}\n\n${text}` };
        continue;
      }
      f.body.push(...splitFences(chunk).flatMap(splitProseAndList).map(bodyParagraph));
      field = { kind: 'body' };
      continue;
    }

    const name = (label[1] ?? '').trim();
    const rest: ScannedLine[] = [{ text: label[2] ?? '', fence: false }, ...chunk.lines.slice(1)].filter(
      (l, i) => i > 0 || l.text.trim() !== '',
    );
    const value = joinMarkdown(rest);
    const key = name.toLowerCase();

    if (key === 'priority') {
      if (f.priority !== null) throw at('second **Priority:** line');
      const p = PRIORITIES.find((x) => x === value);
      if (p === undefined) throw at(`priority "${value}" is not one of ${PRIORITIES.join(', ')}`);
      f.priority = p;
      field = { kind: 'meta' };
    } else if (key === 'kind') {
      if (f.kind !== null) throw at('second **Kind:** line');
      const k = REQ_KINDS.find((x) => x === value);
      if (k === undefined) throw at(`kind "${value}" is not one of ${REQ_KINDS.join(', ')}`);
      f.kind = k;
      field = { kind: 'meta' };
    } else if (key === 'status') {
      if (f.status !== null) throw at('second **Status:** line');
      if (/^removed\.?$/i.test(value)) f.status = 'removed';
      else if (/^proposed\.?$/i.test(value)) f.status = 'proposed';
      else throw at(`status "${value}" is neither Removed nor Proposed`);
      field = { kind: 'meta' };
    } else if (key === 'depends on') {
      const ids = bracketIds(value);
      if (ids.length === 0) throw at('**Depends on:** names no [ID]');
      f.dependsOn.push(...ids.filter((id) => !f.dependsOn.includes(id)));
      field = { kind: 'meta' };
    } else if (key.startsWith('acceptance criteria')) {
      f.cited.push(value);
      f.acceptance.push(...listItems(rest, () => at('text before the first acceptance criterion')));
      field = { kind: 'ac' };
    } else if (key === 'test derivation') {
      if (f.testDerivation !== null) throw at('second **Test derivation:** line');
      f.cited.push(value);
      f.testDerivation = value;
      field = { kind: 'test' };
    } else {
      f.cited.push(value);
      f.notes.push({ label: name, text: value });
      field = { kind: 'note', index: f.notes.length - 1 };
    }
  }
  return f;
}

/** `CONC-012: ~~Concurrent Action Limit~~ (Removed)` -> `Concurrent Action Limit`. */
function blockTitle(heading: string, id: string): string {
  return heading
    .replace(new RegExp(`^ {0,3}#### ${id}:\\s*`), '')
    .replace(/\s*\(Removed\)\s*$/, '')
    .replace(/~~/g, '')
    .trim();
}

// ---------------------------------------------------------------------------------------------
// One file
// ---------------------------------------------------------------------------------------------

export interface ParsedFile {
  readonly file: SpecFile;
  readonly blocks: readonly SpecBlock[];
  readonly units: ReadonlyArray<readonly [ReqId, readonly SpecUnit[]]>;
}

/**
 * Parses one numbered spec file. `index` decides active, removed and proposed; `matchers` find
 * glossary terms. IDs cited in the text are checked by `readSpec`, which knows every file.
 */
export function parseSpecFile(fileName: string, text: string, index: SpecIndex, matchers: readonly TermMatcher[]): ParsedFile {
  const where = `${SPEC_DIR}/${fileName}`;
  const number = SPEC_FILE_RE.exec(fileName)?.[1];
  if (number === undefined) throw inputError(where, null, 'not a numbered spec file name');
  const lines = splitLines(text);
  const scanned = scanLines(lines);
  const stripped = stripMarkdown(lines);

  let title: string | null = null;
  const h2 = new Map<number, string>();
  for (const [i, line] of stripped.entries()) {
    const level = HEADING_RE.exec(line)?.[1]?.length;
    const heading = line.trim().replace(/^#+\s*/, '').trim();
    if (level === 1 && title === null) title = heading.replace(/^\d{2}\s*[—–-]\s*/, '');
    if (level === 2) h2.set(i, heading);
  }
  if (title === null) throw inputError(where, null, 'no "# NN — Title" heading');

  const sectionAt = (lineIndex: number): { title: string; at: number } | null => {
    let found: { title: string; at: number } | null = null;
    for (const [at, t] of h2) if (at < lineIndex && (found === null || at > found.at)) found = { title: t, at };
    return found;
  };

  const blocks: SpecBlock[] = [];
  const unitsOut: Array<readonly [ReqId, readonly SpecUnit[]]> = [];
  const sections: Array<{ title: string; at: number; ids: ReqId[] }> = [];
  const seen = new Map<ReqId, number>();

  for (const sec of fileSections(where, lines)) {
    const prev = seen.get(sec.id);
    if (prev !== undefined) throw inputError(where, sec.line, `second '#### ${sec.id}:' heading (first at line ${prev})`);
    seen.set(sec.id, sec.line);
    const block = parseBlock(where, fileName, sec, lines, scanned, index, matchers, sectionAt(sec.line - 1)?.title ?? null);
    blocks.push(block);
    unitsOut.push([sec.id, sec.units]);

    const s = sectionAt(sec.line - 1) ?? { title, at: -1 };
    const last = sections[sections.length - 1];
    if (last !== undefined && last.at === s.at) last.ids.push(sec.id);
    else sections.push({ title: s.title, at: s.at, ids: [sec.id] });
  }
  if (blocks.length === 0) throw inputError(where, null, "no '#### ID:' blocks");

  return {
    file: {
      file: fileName,
      number,
      title,
      prefixes: unique(blocks.map((b) => b.id.replace(/-\d+$/, ''))),
      sections: sections.map((s): SpecSection => ({ title: s.title, ids: s.ids })),
    },
    blocks,
    units: unitsOut,
  };
}

function parseBlock(
  where: string,
  fileName: string,
  sec: AlignmentSection,
  lines: readonly string[],
  scanned: readonly ScannedLine[],
  index: SpecIndex,
  matchers: readonly TermMatcher[],
  section: string | null,
): SpecBlock {
  const id = sec.id;
  const chunks = toChunks(scanned.slice(sec.line, sec.end), sec.line + 1, LABEL_RE);
  const f = parseFields(where, chunks);
  const removed = index.tombstones.has(id);
  if (!removed && !index.active.has(id)) throw inputError(where, sec.line, `${id} is not listed in ${SPEC_INDEX_FILE}`);
  if (removed !== (f.status === 'removed')) {
    throw inputError(where, sec.line, removed ? `${id} is a tombstone in the index but has no **Status:** Removed` : `${id} says Removed but the index lists it as active`);
  }
  const dependsOn = f.dependsOn;
  // Only IDs with a spec prefix: `[RV-08]` is a bibliography entry, not a requirement.
  const prefixes = new Set(index.files.map((r) => r.prefix));
  const mentions = sortedUnique(f.cited.flatMap(bracketIds))
    .filter((x) => prefixes.has(x.replace(/-\d+$/, '')))
    .filter((x) => x !== id && !dependsOn.includes(x));
  return {
    id,
    title: blockTitle(lines[sec.line - 1] ?? '', id),
    file: fileName,
    line: sec.line,
    section,
    priority: f.priority,
    kind: f.kind,
    status: { state: f.status === 'removed' ? 'removed' : f.status === 'proposed' ? 'proposed' : 'active' },
    body: f.body,
    acceptance: f.acceptance,
    notes: f.notes,
    dependsOn,
    mentions,
    testDerivation: f.testDerivation,
    terms: termsIn(f.body.filter((p) => p.kind !== 'code').map((p) => p.text).join('\n'), matchers),
  };
}

// ---------------------------------------------------------------------------------------------
// All files
// ---------------------------------------------------------------------------------------------

/** Numbered spec file names, sorted. */
export function specFileNames(root: string): string[] {
  return readdirSync(repoPath(root, SPEC_DIR))
    .filter((n) => SPEC_FILE_RE.test(n) && !n.startsWith('00-'))
    .sort(byString);
}

/** Checks the parsed files against the index: same IDs, same per-file counts, known citations. */
function checkAgainstIndex(parsed: readonly ParsedFile[], index: SpecIndex): void {
  const ids = new Set(parsed.flatMap((p) => p.blocks.map((b) => b.id)));
  for (const id of [...index.active, ...index.tombstones].sort(byString)) {
    if (!ids.has(id)) throw inputError(SPEC_INDEX_FILE, null, `${id} is listed but no spec file has a '#### ${id}:' heading`);
  }
  for (const row of index.files) {
    const p = parsed.find((x) => x.file.file === row.file);
    if (p === undefined) throw inputError(SPEC_INDEX_FILE, null, `${row.file} is in the Spec Files table but not in spec/`);
    const n = p.blocks.filter((b) => b.status.state !== 'removed' && b.id.startsWith(`${row.prefix}-`)).length;
    if (n !== row.count) throw inputError(SPEC_INDEX_FILE, null, `${row.file} declares ${row.count} ${row.prefix} requirements, the file has ${n}`);
  }
  for (const p of parsed) {
    if (!index.files.some((r) => r.file === p.file.file)) throw inputError(`${SPEC_DIR}/${p.file.file}`, null, 'missing from the Spec Files table of the index');
    for (const b of p.blocks) {
      for (const cited of [...b.dependsOn, ...b.mentions]) {
        if (!REQ_ID_RE.test(cited) || !ids.has(cited)) throw inputError(`${SPEC_DIR}/${b.file}`, b.line, `${b.id} cites [${cited}], which is not a requirement`);
      }
    }
  }
}

export function readSpec(root: string, glossary: readonly GlossaryTerm[]): SpecInput {
  const index = parseSpecIndex(readSource(root, SPEC_INDEX_FILE));
  const matchers = termMatchers(glossary);
  const parsed = specFileNames(root).map((name) => parseSpecFile(name, readSource(root, `${SPEC_DIR}/${name}`), index, matchers));
  checkAgainstIndex(parsed, index);
  return {
    files: parsed.map((p) => p.file),
    blocks: parsed.flatMap((p) => p.blocks),
    units: new Map(parsed.flatMap((p) => p.units)),
  };
}
