/**
 * Input: `spec/coverage-matrix.md` (written by `scripts/spec-coverage-matrix.py`), the theorem
 * map `lean/report/proof-coverage.json`, and the test files the matrix script greps.
 *
 * - A runtime is `tested` exactly when the matrix ticks its column. Its `refs` are the test files
 *   that cite the ID, found with the matrix script's own globs and ID pattern; the matrix tick and
 *   the files found must agree, so a stale matrix fails the build instead of showing two answers.
 * - `leanRef` is the matrix's Lean ref column.
 * - `leanProofs` are the proof-coverage entries of the ID in the matrix's order (module, name,
 *   fragment), each named by its full theorem name from the citations of requirements.json.
 */
import { type Dirent, readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { arr, str } from '../../decode.js';
import type { Citation, CoverageRow, LeanProof, ReqId, Runtime, TestCoverage } from '../../model.js';
import { RUNTIMES } from '../../model.js';
import { repoPath } from '../paths.js';
import { splitLines } from './alignment.js';
import { decodeFile, objWith, parseJson } from './json-input.js';
import { readLean } from './lean.js';
import { readSource } from './source.js';
import { byString, inputError, REQ_ID_RE } from './text.js';

export const COVERAGE_MATRIX_FILE = 'spec/coverage-matrix.md';
export const PROOF_COVERAGE_FILE = 'lean/report/proof-coverage.json';

// ---------------------------------------------------------------------------------------------
// spec/coverage-matrix.md
// ---------------------------------------------------------------------------------------------

export interface MatrixRow {
  readonly id: ReqId;
  /** The Lean proof cell names at least one theorem. */
  readonly proved: boolean;
  readonly leanRef: boolean;
  readonly tested: { readonly [R in Runtime]: boolean };
}

/** The header of the Lean proof column; the matrix also has Kind and Lean form columns before it. */
const LEAN_PROOF = 'Lean proof (theorem + fragment)';
const CHECK = '✓';
const DASH = '—';

/** Cells of a Markdown table row; `\|` inside a cell is not a separator. */
function cells(line: string): string[] {
  return line
    .trim()
    .replace(/^\||\|$/g, '')
    .split(/(?<!\\)\|/)
    .map((c) => c.trim());
}

function tick(cell: string | undefined, where: () => Error): boolean {
  if (cell === CHECK) return true;
  if (cell === DASH) return false;
  throw where();
}

export function parseCoverageMatrix(text: string, file: string = COVERAGE_MATRIX_FILE): MatrixRow[] {
  const rows: MatrixRow[] = [];
  let columns: Map<string, number> | null = null;
  for (const [i, line] of splitLines(text).entries()) {
    if (!line.startsWith('|')) {
      columns = null;
      continue;
    }
    const c = cells(line);
    if (c[0] === 'ID') {
      columns = new Map(c.map((name, k) => [name, k]));
      for (const name of [LEAN_PROOF, 'Lean ref', ...RUNTIMES]) {
        if (!columns.has(name)) throw inputError(file, i + 1, `table header has no "${name}" column`);
      }
      continue;
    }
    const id = c[0] ?? '';
    if (columns === null || !REQ_ID_RE.test(id)) continue;
    const col = (name: string): string | undefined => c[columns?.get(name) ?? -1];
    const where = (name: string) => (): Error => inputError(file, i + 1, `${id}: "${name}" cell is neither ${CHECK} nor ${DASH}`);
    const proofCell = col(LEAN_PROOF) ?? DASH;
    rows.push({
      id,
      proved: proofCell !== DASH,
      leanRef: tick(col('Lean ref'), where('Lean ref')),
      tested: {
        java: tick(col('java'), where('java')),
        typescript: tick(col('typescript'), where('typescript')),
        rust: tick(col('rust'), where('rust')),
        python: tick(col('python'), where('python')),
      },
    });
  }
  if (rows.length === 0) throw inputError(file, null, 'no requirement rows');
  return rows;
}

// ---------------------------------------------------------------------------------------------
// lean/report/proof-coverage.json
// ---------------------------------------------------------------------------------------------

const proofCoverage = objWith(
  { theorems: arr(objWith({ name: str, module: str, specIds: arr(objWith({ id: str, fragment: str }, {})) }, {})) },
  { $comment: str },
);

/** `Libpetri/Spec/Req/VER_002.lean` -> `Libpetri.Spec.Req.VER_002`. */
function moduleOfPath(path: string): string {
  return path.replace(/\.lean$/, '').replace(/\//g, '.');
}

/**
 * Lean proofs per ID, sorted as the matrix script sorts them, each resolved to the full theorem
 * name of its citation (same id, module, short name and fragment).
 */
export function parseProofCoverage(text: string, citations: readonly Citation[], file: string = PROOF_COVERAGE_FILE): Map<ReqId, LeanProof[]> {
  const data = decodeFile(proofCoverage, parseJson(text, file), file);
  const entries: Array<{ id: ReqId; module: string; name: string; fragment: string }> = [];
  for (const t of data.theorems) {
    for (const s of t.specIds) entries.push({ id: s.id, module: t.module, name: t.name, fragment: s.fragment.trim() });
  }
  entries.sort((a, b) => byString(a.module, b.module) || byString(a.name, b.name) || byString(a.fragment, b.fragment));
  const out = new Map<ReqId, LeanProof[]>();
  for (const e of entries) {
    const matches = citations.filter(
      (c) =>
        c.id === e.id &&
        c.module === moduleOfPath(e.module) &&
        c.fragment.trim() === e.fragment &&
        (c.theorem === e.name || c.theorem.endsWith(`.${e.name}`)),
    );
    const only = matches[0];
    if (only === undefined || matches.length > 1) {
      throw inputError(file, null, `${e.name} (${e.module}) for ${e.id}: ${matches.length} matching citations in requirements.json, expected 1`);
    }
    const list = out.get(e.id) ?? [];
    list.push({ theorem: only.theorem, fragment: e.fragment });
    out.set(e.id, list);
  }
  return out;
}

// ---------------------------------------------------------------------------------------------
// Test files (the globs of spec-coverage-matrix.py `collect_test_mentions`)
// ---------------------------------------------------------------------------------------------

const EXCLUDED_DIRS = new Set(['target', 'node_modules', '.lake', '.venv', 'dist']);
const SPEC_ID_RE = /\b([A-Z]{2,6}-\d{3})\b/g;
const RUST_CFG_TEST_RE = /#!?\[cfg\(test\)\]/;

/** Repo-relative paths (with `/`) of the files under `dir` ending in `suffix`, sorted. */
function walk(root: string, dir: string, suffix: string): string[] {
  const out: string[] = [];
  const visit = (relative: string): void => {
    let entries: Dirent[];
    try {
      entries = readdirSync(join(root, relative), { withFileTypes: true });
    } catch {
      return;
    }
    for (const e of entries) {
      const path = `${relative}/${e.name}`;
      if (e.isDirectory()) {
        if (!EXCLUDED_DIRS.has(e.name)) visit(path);
      } else if (e.isFile() && e.name.endsWith(suffix)) {
        out.push(path);
      }
    }
  };
  visit(dir);
  return out.sort(byString);
}

/** The test files of each runtime, as the matrix script selects them. */
export function testFiles(root: string): { readonly [R in Runtime]: readonly string[] } {
  const rust = walk(root, 'rust', '.rs').filter((p) => {
    const parts = p.split('/');
    if (parts.includes('tests')) return true;
    return parts.includes('src') && RUST_CFG_TEST_RE.test(readFileSync(join(root, p), 'utf8'));
  });
  const files = {
    java: walk(root, 'java/src/test', '.java'),
    typescript: walk(root, 'typescript/tests', '.ts'),
    rust,
    python: walk(root, 'python/tests', '.py'),
  };
  for (const r of RUNTIMES) if (files[r].length === 0) throw new Error(`no ${r} test files found; check the test globs in src/gen/inputs/coverage.ts`);
  return files;
}

/** For each ID, the files (sorted) whose text contains it. */
export function citingFiles(root: string, files: readonly string[]): Map<ReqId, string[]> {
  const out = new Map<ReqId, string[]>();
  for (const f of files) {
    const text = readFileSync(repoPath(root, f), 'utf8');
    for (const id of new Set([...text.matchAll(SPEC_ID_RE)].map((m) => m[1] ?? ''))) {
      const list = out.get(id) ?? [];
      list.push(f);
      out.set(id, list);
    }
  }
  return out;
}

// ---------------------------------------------------------------------------------------------

/** Joins the three sources into one row per matrix ID; any disagreement fails the build. */
export function coverageRows(
  matrix: readonly MatrixRow[],
  proofs: ReadonlyMap<ReqId, readonly LeanProof[]>,
  refs: { readonly [R in Runtime]: ReadonlyMap<ReqId, readonly string[]> },
): Record<ReqId, CoverageRow> {
  const stale = `${COVERAGE_MATRIX_FILE} is stale; run python3 scripts/spec-coverage-matrix.py --update`;
  const out: Record<ReqId, CoverageRow> = {};
  for (const row of matrix) {
    if (out[row.id] !== undefined) throw inputError(COVERAGE_MATRIX_FILE, null, `${row.id} has two rows`);
    const leanProofs = proofs.get(row.id) ?? [];
    if (row.proved !== leanProofs.length > 0) throw new Error(`${row.id}: Lean proof column disagrees with ${PROOF_COVERAGE_FILE}; ${stale}`);
    const test = (r: Runtime): TestCoverage => {
      const files = refs[r].get(row.id) ?? [];
      if (row.tested[r] !== files.length > 0) {
        throw new Error(`${row.id}: the ${r} column says ${row.tested[r] ? 'tested' : 'untested'} but ${files.length} test files cite it; ${stale}`);
      }
      return row.tested[r] ? { state: 'tested', refs: files } : { state: 'untested' };
    };
    out[row.id] = {
      id: row.id,
      leanProofs,
      leanRef: row.leanRef,
      tests: { java: test('java'), typescript: test('typescript'), rust: test('rust'), python: test('python') },
    };
  }
  return out;
}

export function readCoverage(root: string): Readonly<Record<ReqId, CoverageRow>> {
  const matrix = parseCoverageMatrix(readSource(root, COVERAGE_MATRIX_FILE));
  const proofs = parseProofCoverage(readSource(root, PROOF_COVERAGE_FILE), readLean(root).citations);
  const files = testFiles(root);
  const refs = {
    java: citingFiles(root, files.java),
    typescript: citingFiles(root, files.typescript),
    rust: citingFiles(root, files.rust),
    python: citingFiles(root, files.python),
  };
  return coverageRows(matrix, proofs, refs);
}
