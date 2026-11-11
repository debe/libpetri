/**
 * Input: `spec/runtime-defects.md`, the ledger table and the `### RD-NN. Title` entries with
 * their Requirements / Runtimes / Defect / Lean evidence / Status items.
 *
 * - Requirements: the IDs the item names, in order; they must equal the table row's IDs.
 * - Runtimes: names map to `Runtime` ("TypeScript" -> "typescript", "Python through Rust" ->
 *   "python", "all" -> every runtime), in `RUNTIMES` order; an unknown name fails the build.
 * - Lean evidence: the backticked names, or none when the item starts with "none".
 * - Status: `open` or `fixed in <version>`, matching the table row.
 * Entries in ledger order.
 */
import type { Defect, DefectStatus, ReqId, Runtime } from '../../model.js';
import { RUNTIMES } from '../../model.js';
import { scanLines, splitLines } from './alignment.js';
import { joinMarkdown } from './markdown.js';
import { readSource } from './source.js';
import { inputError, unique } from './text.js';

export const DEFECTS_FILE = 'spec/runtime-defects.md';

const ENTRY_RE = /^### (RD-\d+)\.\s+(.+?)\s*$/;
const ITEM_RE = /^- \*\*([^*]+?):\*\*\s*(.*)$/;
const ID_RE = /\b[A-Z]{2,6}-\d{3}\b/g;
const ITEMS = ['Requirements', 'Runtimes', 'Defect', 'Lean evidence', 'Status'] as const;
type Item = (typeof ITEMS)[number];

interface TableRow {
  readonly requirements: readonly ReqId[];
  readonly status: string;
}

/** `Rust, Java, TypeScript, and Python through Rust.` -> `['java', 'typescript', 'rust', 'python']`. */
export function parseRuntimes(text: string): Runtime[] | null {
  const plain = text.replace(/\.$/, '').trim();
  if (/^all$/i.test(plain)) return [...RUNTIMES];
  const found = new Set<Runtime>();
  for (const part of plain.split(/,|\band\b/)) {
    const word = part.trim().split(/\s+/)[0]?.toLowerCase() ?? '';
    if (word === '') continue;
    const runtime = RUNTIMES.find((r) => r === word);
    if (runtime === undefined) return null;
    found.add(runtime);
  }
  return RUNTIMES.filter((r) => found.has(r));
}

/** `open.` or `fixed in 12.0.1.`; anything else is null. */
export function parseDefectStatus(text: string): DefectStatus | null {
  const plain = text.trim().replace(/\.$/, '');
  if (plain === 'open') return { state: 'open' };
  const m = /^fixed in (\S+)$/.exec(plain);
  return m?.[1] === undefined ? null : { state: 'fixed', version: m[1] };
}

/** Backticked names of the Lean evidence item; none when it starts with "none". */
export function evidenceNames(text: string): string[] {
  if (/^none\b/i.test(text.trim())) return [];
  return unique([...text.matchAll(/`([A-Za-z_][\w.']*)`/g)].map((m) => m[1] ?? ''));
}

function parseTable(lines: readonly string[]): Map<string, TableRow> {
  const rows = new Map<string, TableRow>();
  for (const line of lines) {
    const m = /^\|\s*(RD-\d+)\s*\|([^|]*)\|([^|]*)\|([^|]*)\|\s*$/.exec(line);
    if (m?.[1] === undefined) continue;
    rows.set(m[1], { requirements: [...(m[2] ?? '').matchAll(ID_RE)].map((x) => x[0]), status: (m[4] ?? '').trim() });
  }
  return rows;
}

export function parseDefects(text: string, file: string = DEFECTS_FILE): Defect[] {
  const lines = splitLines(text);
  const scanned = scanLines(lines);
  const table = parseTable(lines);
  const defects: Defect[] = [];

  const starts: number[] = [];
  scanned.forEach((l, i) => {
    if (!l.fence && ENTRY_RE.test(l.text)) starts.push(i);
  });
  for (const [k, start] of starts.entries()) {
    const end = starts[k + 1] ?? scanned.length;
    const head = ENTRY_RE.exec(scanned[start]?.text ?? '');
    const id = head?.[1] ?? '';
    const title = head?.[2] ?? '';
    const at = (message: string): Error => inputError(file, start + 1, `${id}: ${message}`);

    const items = new Map<Item, string>();
    let current: { item: Item; lines: Array<{ text: string; fence: boolean }> } | null = null;
    const flush = (): void => {
      if (current !== null) items.set(current.item, joinMarkdown(current.lines));
      current = null;
    };
    for (const l of scanned.slice(start + 1, end)) {
      const m = l.fence ? null : ITEM_RE.exec(l.text);
      if (m !== null) {
        flush();
        const item = ITEMS.find((x) => x === m[1]);
        if (item === undefined) throw at(`unknown item "${m[1] ?? ''}"`);
        if (items.has(item)) throw at(`second "${item}" item`);
        current = { item, lines: [{ text: m[2] ?? '', fence: false }] };
      } else if (current !== null && (l.fence || /^\s+\S/.test(l.text))) {
        current.lines.push({ text: l.text, fence: l.fence });
      } else {
        flush();
      }
    }
    flush();
    const get = (item: Item): string => {
      const v = items.get(item);
      if (v === undefined || v === '') throw at(`no "${item}" item`);
      return v;
    };

    const requirements = unique([...get('Requirements').matchAll(ID_RE)].map((m) => m[0]));
    const runtimes = parseRuntimes(get('Runtimes'));
    if (runtimes === null || runtimes.length === 0) throw at(`unknown runtime in "${get('Runtimes')}"; use Java, TypeScript, Rust, Python or all`);
    const status = parseDefectStatus(get('Status'));
    if (status === null) throw at(`status "${get('Status')}" is neither "open" nor "fixed in <version>"`);

    const row = table.get(id);
    if (row === undefined) throw at('missing from the ledger table');
    if (row.requirements.join(',') !== requirements.join(',')) {
      throw at(`the table names ${row.requirements.join(', ')}, the entry ${requirements.join(', ')}`);
    }
    const tableStatus = parseDefectStatus(row.status);
    if (tableStatus === null || JSON.stringify(tableStatus) !== JSON.stringify(status)) throw at(`the table says "${row.status}", the entry "${get('Status')}"`);

    const evidenceText = get('Lean evidence');
    defects.push({ id, title, requirements, runtimes, text: get('Defect'), evidence: evidenceNames(evidenceText), evidenceText, status });
  }
  const ids = new Set(defects.map((d) => d.id));
  for (const id of table.keys()) if (!ids.has(id)) throw inputError(file, null, `${id} is in the table but has no "### ${id}." entry`);
  if (ids.size !== defects.length) throw inputError(file, null, 'a defect ID appears twice');
  return defects;
}

export function readDefects(root: string): readonly Defect[] {
  return parseDefects(readSource(root, DEFECTS_FILE));
}
