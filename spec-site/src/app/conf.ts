/**
 * Conformance matrix (`#/conf`, design 6): every active requirement against Lean, Java,
 * TypeScript, Rust and Python. Rows are grouped in collapsible bands per spec file; a cell is
 * tested, untested or an open defect (Lean: block, cited, mentioned or none). Filters live in
 * the route query (`f`, `kind`, `q`) and update the address bar silently; a cell opens a drawer.
 *
 * The derivations (rows, filters, summaries, grid moves) are pure and exported for the tests;
 * the view below only draws them.
 *
 * Owner: conf + graph agent.
 */
import { REQ_KINDS, RUNTIMES } from '../model.js';
import type { Defect, ReqKind, Runtime, SiteData, SpecBlock } from '../model.js';
import type { AppContext, ViewResult } from './context.js';
import { type Child, h, listen, replaceChildren } from './dom.js';
import { openDrawer } from './drawer.js';
import { blocks as mdBlocks } from './md.js';
import { href, type QueryParams, queryList, R, reqGraph, type RouteOf } from './router.js';
import {
  LEAN_META,
  type LeanState,
  leanState,
  openDefects,
  ROLE_META,
  ROLE_ORDER,
  RUNTIME_LABEL,
  type StatusMeta,
  TEST_META,
  TESTED_MEANS,
  type TestState,
  testState,
  type Tone,
} from './status.js';
import { idLink, statusBadge, viewFrame } from './ui.js';

// ---------------------------------------------------------------------------------------------
// Columns
// ---------------------------------------------------------------------------------------------

export type ConfColumn = 'lean' | Runtime;

export const CONF_COLUMNS: readonly ConfColumn[] = ['lean', ...RUNTIMES];

export const COLUMN_LABEL: { readonly [C in ConfColumn]: string } = { lean: 'Lean', ...RUNTIME_LABEL };

/** Short headers for the 400px matrix (design 6), shown as `<abbr>`. */
export const COLUMN_ABBR: { readonly [C in ConfColumn]: string } = { lean: 'L', java: 'J', typescript: 'TS', rust: 'Rs', python: 'Py' };

export const PYTHON_NOTE = 'Python binds the Rust runtime.';

export function isConfColumn(value: string): value is ConfColumn {
  return value === 'lean' || (RUNTIMES as readonly string[]).includes(value);
}

/** Kind letters with their words (design 3.2). */
export const KIND_WORD: { readonly [K in ReqKind]: string } = {
  A: 'Assumption',
  B: 'Behaviour',
  F: 'Function',
  T: 'Timing',
  Q: 'Quality (tested, not proven)',
  N: 'Configuration',
};

// ---------------------------------------------------------------------------------------------
// Rows and bands
// ---------------------------------------------------------------------------------------------

export interface ConfRow {
  readonly block: SpecBlock;
  readonly lean: LeanState;
  readonly tests: { readonly [R in Runtime]: TestState };
  /** Open defects naming this ID, any runtime, ledger order. */
  readonly defects: readonly Defect[];
  /** No test file in any runtime cites the ID (the coverage data, as the "untested" count uses). */
  readonly untested: boolean;
  /** Per runtime: a test file cites the ID (true even where an open defect hides it in `tests`). */
  readonly cited: { readonly [R in Runtime]: boolean };
}

export interface ConfBand {
  /** Spec file name, e.g. `01-core-model.md`. */
  readonly file: string;
  /** "01 Core Model". */
  readonly title: string;
  /** "CORE" (prefixes joined with ", "). */
  readonly prefixes: string;
  /** Rows of this file that pass the filters, in display order. */
  readonly rows: readonly ConfRow[];
  /** Rows of this file before filtering. */
  readonly total: number;
}

const rowCache = new WeakMap<SiteData, readonly ConfRow[]>();

/** One row per active requirement, spec order (file, then line). Cached per data object. */
export function buildConfRows(ctx: AppContext): readonly ConfRow[] {
  const cached = rowCache.get(ctx.data);
  if (cached !== undefined) return cached;
  const rows = ctx.index.activeBlocks.map((block): ConfRow => {
    const id = block.id;
    const cov = ctx.data.coverage[id];
    return {
      block,
      lean: leanState(ctx, id),
      tests: {
        java: testState(ctx, id, 'java'),
        typescript: testState(ctx, id, 'typescript'),
        rust: testState(ctx, id, 'rust'),
        python: testState(ctx, id, 'python'),
      },
      defects: openDefects(ctx, id),
      untested: cov === undefined || RUNTIMES.every((r) => cov.tests[r].state === 'untested'),
      cited: {
        java: cov?.tests.java.state === 'tested',
        typescript: cov?.tests.typescript.state === 'tested',
        rust: cov?.tests.rust.state === 'tested',
        python: cov?.tests.python.state === 'tested',
      },
    };
  });
  rowCache.set(ctx.data, rows);
  return rows;
}

// ---------------------------------------------------------------------------------------------
// Filters (route query: f, kind, q)
// ---------------------------------------------------------------------------------------------

export interface ConfFilters {
  readonly q: string;
  /** `f=defects`: rows with an open defect first inside each band. */
  readonly defectsFirst: boolean;
  /** `f=untested`: only rows no test file cites in any language. */
  readonly untested: boolean;
  /** `f=nolean`: only rows without a Lean block. */
  readonly noLean: boolean;
  /** `gap=python`: only rows no test file of this language cites. */
  readonly gap: Runtime | null;
  /** `kind=B,F`: only these kinds; empty = all. */
  readonly kinds: readonly ReqKind[];
}

export const NO_FILTERS: ConfFilters = { q: '', defectsFirst: false, untested: false, noLean: false, gap: null, kinds: [] };

function isReqKind(value: string): value is ReqKind {
  return (REQ_KINDS as readonly string[]).includes(value);
}

/** Reads the filters from the route query; unknown values are ignored. */
export function parseConfFilters(query: QueryParams): ConfFilters {
  const f = queryList(query, 'f');
  const kinds = new Set(queryList(query, 'kind').map((k) => k.toUpperCase()).filter(isReqKind));
  return {
    q: query['q'] ?? '',
    defectsFirst: f.includes('defects'),
    untested: f.includes('untested'),
    noLean: f.includes('nolean'),
    gap: RUNTIMES.find((r) => r === query['gap']) ?? null,
    kinds: REQ_KINDS.filter((k) => kinds.has(k)),
  };
}

/** The route query of a filter state; default values are left out. */
export function confQuery(filters: ConfFilters): QueryParams {
  const f = [filters.defectsFirst && 'defects', filters.noLean && 'nolean', filters.untested && 'untested'].filter(
    (v): v is string => typeof v === 'string',
  );
  const out: Record<string, string> = {};
  if (f.length > 0) out['f'] = f.join(',');
  if (filters.gap !== null) out['gap'] = filters.gap;
  if (filters.kinds.length > 0) out['kind'] = filters.kinds.join(',');
  if (filters.q.trim() !== '') out['q'] = filters.q;
  return out;
}

/** True when any filter narrows the rows (sorting alone does not). */
export function narrows(filters: ConfFilters): boolean {
  return filters.q.trim() !== '' || filters.untested || filters.noLean || filters.gap !== null || filters.kinds.length > 0;
}

const squash = (text: string): string => text.toLowerCase().replace(/[\s_-]+/g, '');

/**
 * Text filter: the ID ignoring case, spaces and hyphens (`core031` finds CORE-031), or every
 * word of the query in the title.
 */
export function matchesText(block: SpecBlock, q: string): boolean {
  const query = q.trim().toLowerCase();
  if (query === '') return true;
  if (squash(block.id).includes(squash(query))) return true;
  const title = block.title.toLowerCase();
  return query.split(/\s+/).every((word) => title.includes(word));
}

export function rowPasses(row: ConfRow, filters: ConfFilters): boolean {
  if (filters.untested && !row.untested) return false;
  if (filters.noLean && row.lean === 'block') return false;
  if (filters.gap !== null && row.cited[filters.gap]) return false;
  if (filters.kinds.length > 0 && (row.block.kind === null || !filters.kinds.includes(row.block.kind))) return false;
  return matchesText(row.block, filters.q);
}

/**
 * Rows grouped by spec file in `data.files` order (unknown files after, by name). Bands keep
 * spec order; "defects first" moves rows with an open defect to the top of their band.
 * Bands with no passing row are kept (with empty `rows`) so the counts stay visible.
 */
export function confBands(data: SiteData, rows: readonly ConfRow[], filters: ConfFilters): readonly ConfBand[] {
  const byFile = new Map<string, ConfRow[]>();
  for (const row of rows) {
    const list = byFile.get(row.block.file);
    if (list === undefined) byFile.set(row.block.file, [row]);
    else list.push(row);
  }
  const known = data.files.map((f) => f.file).filter((f) => byFile.has(f));
  const unknown = [...byFile.keys()].filter((f) => !known.includes(f)).sort();
  return [...known, ...unknown].map((file): ConfBand => {
    const all = byFile.get(file) ?? [];
    const meta = data.files.find((f) => f.file === file);
    const passing = all.filter((r) => rowPasses(r, filters));
    const ordered = filters.defectsFirst
      ? [...passing.filter((r) => r.defects.length > 0), ...passing.filter((r) => r.defects.length === 0)]
      : passing;
    return {
      file,
      title: meta === undefined ? file : `${meta.number} ${meta.title}`,
      prefixes: meta === undefined ? '' : meta.prefixes.join(', '),
      rows: ordered,
      total: all.length,
    };
  });
}

// ---------------------------------------------------------------------------------------------
// Cells and column summaries
// ---------------------------------------------------------------------------------------------

export interface CellDisplay {
  readonly glyph: string;
  /**
   * For a defect cell, the test glyph under the defect (tested ✓ or untested ○), so "tested but
   * broken" and "untested and broken" look different; '' otherwise.
   */
  readonly under: string;
  /** Visible text after the glyph (defect IDs), '' for plain glyph cells. */
  readonly text: string;
  /** Screen-reader word, e.g. "tested", "open defect RD-07". */
  readonly word: string;
  readonly tone: Tone;
  readonly meta: StatusMeta;
}

export function cellDisplay(row: ConfRow, column: ConfColumn): CellDisplay {
  if (column === 'lean') {
    const meta = LEAN_META[row.lean];
    return { glyph: meta.glyph, under: '', text: '', word: meta.word, tone: meta.tone, meta };
  }
  const state = row.tests[column];
  const meta = TEST_META[state.state];
  if (state.state === 'defect') {
    const ids = state.defects.map((d) => d.id);
    const first = ids[0] ?? '';
    const text = ids.length === 1 ? first : String(ids.length);
    const cited = row.cited[column];
    const tests = cited ? 'a test file cites the rule' : 'no test file cites the rule';
    return {
      glyph: meta.glyph,
      under: cited ? TEST_META.tested.glyph : TEST_META.untested.glyph,
      text,
      word: `${ids.length === 1 ? 'open defect' : 'open defects'} ${ids.join(', ')}; ${tests}`,
      tone: meta.tone,
      meta,
    };
  }
  return { glyph: meta.glyph, under: '', text: '', word: meta.word, tone: meta.tone, meta };
}

export interface SummarySegment {
  readonly tone: Tone;
  readonly count: number;
  /** "115 tested". */
  readonly label: string;
}

export interface ColumnSummary {
  readonly column: ConfColumn;
  readonly total: number;
  /** Non-empty segments in display order; counts sum to `total`. */
  readonly segments: readonly SummarySegment[];
  /** The text line, every part of it from the data: "115 tested · 6 open defects · 103 untested". */
  readonly text: string;
}

const plural = (n: number, one: string, many: string): string => `${n} ${n === 1 ? one : many}`;

export function columnSummary(rows: readonly ConfRow[], column: ConfColumn): ColumnSummary {
  const count = (pred: (r: ConfRow) => boolean): number => rows.filter(pred).length;
  let parts: readonly SummarySegment[];
  if (column === 'lean') {
    const block = count((r) => r.lean === 'block');
    const cited = count((r) => r.lean === 'cited');
    const mention = count((r) => r.lean === 'mention');
    const none = count((r) => r.lean === 'none');
    parts = [
      // IDs, not blocks: one ID can have companion blocks (the header counts blocks).
      { tone: 'ok', count: block, label: `${block} with a Lean block` },
      { tone: 'consistent', count: cited, label: `${cited} cited` },
      // "mentioned" is shown only when it occurs; the other three always show.
      ...(mention > 0 ? [{ tone: 'none' as const, count: mention, label: `${mention} mentioned` }] : []),
      { tone: 'none', count: none, label: `${none} none` },
    ];
  } else {
    const tested = count((r) => r.tests[column].state === 'tested');
    const defect = count((r) => r.tests[column].state === 'defect');
    const untested = count((r) => r.tests[column].state === 'untested');
    parts = [
      { tone: 'ok', count: tested, label: `${tested} tested` },
      { tone: 'defect', count: defect, label: plural(defect, 'open defect', 'open defects') },
      { tone: 'none', count: untested, label: `${untested} untested` },
    ];
  }
  return {
    column,
    total: rows.length,
    segments: parts.filter((p) => p.count > 0),
    text: parts.map((p) => p.label).join(' · '),
  };
}

// ---------------------------------------------------------------------------------------------
// Roving focus over the matrix (one tab stop; arrows, Home/End, Ctrl Home/End, PageUp/Down)
// ---------------------------------------------------------------------------------------------

export interface GridPos {
  readonly row: number;
  readonly col: number;
}

/** How many rows PageUp / PageDown move. */
export const PAGE_ROWS = 10;

/**
 * The next focus position for a key, or null when the key does not move. `widths[r]` is the
 * number of focusable items in navigable row r (band rows have one); `wantCol` is the column
 * vertical moves aim for, so moving through a one-item band row keeps the column.
 */
export function moveInGrid(widths: readonly number[], pos: GridPos, key: string, ctrl: boolean, wantCol: number): GridPos | null {
  const last = widths.length - 1;
  if (last < 0) return null;
  const width = (r: number): number => Math.max(1, widths[r] ?? 1);
  const vertical = (row: number): GridPos => {
    const r = Math.min(last, Math.max(0, row));
    return { row: r, col: Math.min(wantCol, width(r) - 1) };
  };
  switch (key) {
    case 'ArrowRight':
      return { row: pos.row, col: Math.min(width(pos.row) - 1, pos.col + 1) };
    case 'ArrowLeft':
      return { row: pos.row, col: Math.max(0, pos.col - 1) };
    case 'ArrowDown':
      return vertical(pos.row + 1);
    case 'ArrowUp':
      return vertical(pos.row - 1);
    case 'PageDown':
      return vertical(pos.row + PAGE_ROWS);
    case 'PageUp':
      return vertical(pos.row - PAGE_ROWS);
    case 'Home':
      return ctrl ? { row: 0, col: 0 } : { row: pos.row, col: 0 };
    case 'End':
      return ctrl ? { row: last, col: width(last) - 1 } : { row: pos.row, col: width(pos.row) - 1 };
    default:
      return null;
  }
}

// ---------------------------------------------------------------------------------------------
// View
// ---------------------------------------------------------------------------------------------

/** Kind letter in a small square, with the word for screen readers (design 3.2). */
export function kindBadge(kind: ReqKind | null, block: 'conf' | 'graph' = 'conf'): HTMLElement | null {
  if (kind === null) return null;
  return h('span', { class: `${block}__kind`, title: KIND_WORD[kind] },
    h('span', { 'aria-hidden': 'true' }, kind),
    h('span', { class: 'sr-only' }, KIND_WORD[kind]),
  );
}

function chip(label: Child, pressed: boolean, onClick: () => void, extra: Child = null): HTMLButtonElement {
  return h('button', { type: 'button', class: 'conf__chip', 'aria-pressed': pressed ? 'true' : 'false', on: { click: onClick } },
    h('span', { class: 'conf__chip-check', 'aria-hidden': 'true' }, '✓'),
    label,
    extra,
  );
}

function summaryCard(summary: ColumnSummary): HTMLElement {
  const note = summary.column === 'python' ? h('p', { class: 'conf__summary-note' }, PYTHON_NOTE) : null;
  return h('li', { class: 'conf__summary' },
    h('h2', { class: 'conf__summary-name' }, COLUMN_LABEL[summary.column]),
    h('p', { class: 'conf__summary-text' }, summary.text),
    miniBar(summary, 'conf__bar'),
    note,
  );
}

function miniBar(summary: ColumnSummary, cls: string): HTMLElement {
  return h('div', { class: cls, 'aria-hidden': 'true' },
    summary.segments.map((seg) => h('span', {
      class: ['conf__seg', `conf__seg--${seg.tone}`],
      title: seg.label,
      style: { 'flex-grow': String(seg.count) },
    })),
  );
}

function headerCell(column: ConfColumn, summary: ColumnSummary): HTMLTableCellElement {
  const note = column === 'python'
    ? h('span', { class: 'conf__note', title: PYTHON_NOTE },
        h('span', { 'aria-hidden': 'true' }, '*'),
        h('span', { class: 'sr-only' }, ` (${PYTHON_NOTE})`))
    : null;
  return h('th', { scope: 'col', class: ['conf__col', `conf__col--${column}`] },
    h('span', { class: 'conf__col-full' }, COLUMN_LABEL[column]),
    h('abbr', { class: 'conf__col-abbr', title: COLUMN_LABEL[column] }, COLUMN_ABBR[column]),
    note,
    miniBar(summary, 'conf__col-bar'),
  );
}

function cellButton(row: ConfRow, column: ConfColumn): HTMLTableCellElement {
  const d = cellDisplay(row, column);
  const id = row.block.id;
  return h('td', { class: ['conf__cell', `conf__cell--${d.tone}`] },
    h('button', {
      type: 'button',
      class: 'conf__cell-btn',
      tabindex: -1,
      title: `${id} in ${COLUMN_LABEL[column]}: ${d.word}. Open details.`,
      'data-nav': '',
      'data-id': id,
      'data-col': column,
    },
      h('span', { class: 'conf__glyph', 'aria-hidden': 'true' }, d.glyph),
      d.text === '' ? null : h('span', { class: 'conf__cell-text', 'aria-hidden': 'true' }, d.text),
      d.under === '' ? null : h('span', { class: 'conf__cell-under', 'aria-hidden': 'true' }, d.under),
      h('span', { class: 'sr-only' }, d.word),
    ),
  );
}

function dataRow(ctx: AppContext, row: ConfRow): HTMLTableRowElement {
  const link = idLink(ctx, row.block.id);
  link.tabIndex = -1;
  link.setAttribute('data-nav', '');
  link.setAttribute('data-col', 'id');
  return h('tr', { class: ['conf__row', row.defects.length > 0 && 'conf__row--defect'], 'data-row': '', 'data-id': row.block.id },
    h('th', { scope: 'row', class: 'conf__id' },
      link,
      h('span', { class: 'conf__subtitle' }, row.block.title),
    ),
    h('td', { class: 'conf__title' }, row.block.title, ' ', kindBadge(row.block.kind)),
    CONF_COLUMNS.map((c) => cellButton(row, c)),
  );
}

/** Drawer body for one cell (design 6 "Cell drawer"). */
export function cellDetails(ctx: AppContext, row: ConfRow, column: ConfColumn): HTMLElement {
  const id = row.block.id;
  const d = cellDisplay(row, column);
  const label = COLUMN_LABEL[column];
  const parts: Child[] = [
    h('p', { class: 'conf__d-rule' }, idLink(ctx, id), ' ', row.block.title),
    h('p', { class: 'conf__d-state' }, statusBadge(d.meta, d.text === '' ? d.meta.word : `${d.meta.word} ${d.text}`)),
    h('p', null, d.meta.explain, '.'),
  ];
  if (column === 'lean') {
    parts.push(leanDetails(ctx, row));
  } else {
    const cov = ctx.data.coverage[id]?.tests[column];
    const tested = cov?.state === 'tested';
    const refs = cov?.state === 'tested' ? cov.refs : [];
    parts.push(h('h3', { class: 'conf__d-head' }, 'Test files'));
    if (!tested) parts.push(h('p', null, `No ${label} test file cites this ID.`));
    else if (refs.length === 0) parts.push(h('p', null, `A ${label} test file cites this ID.`));
    else {
      parts.push(h('ul', { class: 'conf__d-list' },
        refs.map((ref) => h('li', null, h('a', { href: `${ctx.data.links.blob}${ref}`, rel: 'noopener', class: 'conf__d-path' }, ref))),
      ));
    }
    const defects = openDefects(ctx, id, column);
    if (defects.length > 0) {
      parts.push(h('h3', { class: 'conf__d-head' }, 'Open defects'));
      parts.push(h('ul', { class: 'conf__d-defects' }, defects.map((def) => defectItem(ctx, def))));
    }
    if (column === 'python') parts.push(h('p', { class: 'conf__d-note' }, PYTHON_NOTE));
    parts.push(h('p', { class: 'conf__d-honest' }, TESTED_MEANS));
  }
  parts.push(h('p', { class: 'conf__d-links' },
    h('a', { href: href(R.req(id)) }, 'Open rule ›'),
    h('a', { href: href(reqGraph(id)) }, 'Open in graph ›'),
  ));
  return h('div', { class: 'conf__details' }, parts);
}

function defectItem(ctx: AppContext, def: Defect): HTMLElement {
  return h('li', { class: 'conf__d-defect' },
    h('p', null,
      statusBadge(TEST_META.defect, def.id),
      ' ',
      h('a', { href: href(R.graph({ kind: 'defect', id: def.id })) }, def.title),
    ),
    h('p', { class: 'conf__d-meta' }, def.runtimes.map((r) => RUNTIME_LABEL[r]).join(', ')),
    h('div', { class: 'conf__d-text' }, mdBlocks(ctx, def.text)),
  );
}

function leanDetails(ctx: AppContext, row: ConfRow): HTMLElement {
  const id = row.block.id;
  const blocks = ctx.index.lean(id);
  const cites = ctx.index.citationsByReq.get(id) ?? [];
  const proof = (name: string): HTMLElement =>
    h('a', { href: `${ctx.data.links.proofGraph}#${name}`, rel: 'noopener', class: 'conf__d-thm', title: name }, `${shortTheorem(name)} ↗`);
  const out: Child[] = [];
  if (blocks.length > 0) {
    out.push(h('h3', { class: 'conf__d-head' }, blocks.length === 1 ? 'Lean block' : `Lean blocks (${blocks.length})`));
    out.push(h('ul', { class: 'conf__d-list' }, blocks.map((b) => {
      const roles = ROLE_ORDER.map((role) => [role, b.evidence.filter((e) => e.role === role).length] as const).filter(([, n]) => n > 0);
      return h('li', null,
        h('code', { class: 'conf__d-decl' }, b.decl),
        h('p', { class: 'conf__d-meta' },
          b.signoff.state === 'signed' ? `Signed ${b.signoff.date}` : 'Not signed',
          roles.length > 0 ? ' · ' : '',
          roles.map(([role, n]) => `${ROLE_META[role].glyph} ${ROLE_META[role].word} ${n}`).join(' · '),
        ),
      );
    })));
  } else if (cites.length === 0) {
    out.push(h('p', null, row.lean === 'mention' ? 'Mentioned in Lean comments only.' : 'Lean does not mention this rule.'));
  }
  if (cites.length > 0) {
    out.push(h('h3', { class: 'conf__d-head' }, `Cited by ${plural(cites.length, 'theorem', 'theorems')}`));
    out.push(h('ul', { class: 'conf__d-list' }, cites.map((c) => h('li', null, proof(c.theorem), h('p', { class: 'conf__d-meta' }, c.fragment)))));
  }
  return h('div', null, out);
}

export function shortTheorem(name: string): string {
  return name.startsWith('Libpetri.Spec.') ? name.slice('Libpetri.Spec.'.length) : name;
}

export function renderConf(ctx: AppContext, route: RouteOf<'conf'>): ViewResult {
  let filters = parseConfFilters(route.query);
  const rows = buildConfRows(ctx);
  const summaries = CONF_COLUMNS.map((c) => columnSummary(rows, c));
  const collapsed = new Set<string>();
  let focusKey: string | null = null;
  let wantCol = 0;

  const counts = {
    defects: rows.filter((r) => r.defects.length > 0).length,
    untested: rows.filter((r) => r.untested).length,
    noLean: rows.filter((r) => r.lean !== 'block').length,
  };
  const kindCount = (k: ReqKind): number => rows.filter((r) => r.block.kind === k).length;
  const kindsShown = REQ_KINDS.filter((k) => kindCount(k) > 0);

  const status = h('p', { class: 'conf__status', role: 'status' });
  const host = h('div', { class: 'conf__host' });
  const input = h('input', {
    class: 'conf__filter',
    type: 'search',
    id: 'conf-filter',
    value: filters.q,
    placeholder: 'Filter by ID or title',
    autocomplete: 'off',
    spellcheck: false,
  });
  const chipCount = (n: number): HTMLElement => h('span', { class: 'conf__chip-count' }, String(n));
  const chips = {
    // Counts rules, not ledger entries: one entry can name several rules and languages.
    defects: chip('Defects first', filters.defectsFirst, () => set({ defectsFirst: !filters.defectsFirst }),
      h('span', { class: 'conf__chip-count' }, `${counts.defects} rules`)),
    untested: chip('Untested only', filters.untested, () => set({ untested: !filters.untested }), chipCount(counts.untested)),
    noLean: chip('No Lean block', filters.noLean, () => set({ noLean: !filters.noLean }), chipCount(counts.noLean)),
  };
  const kindChips = new Map(kindsShown.map((k) => [k, chip(
    h('span', null, h('span', { class: 'conf__kind-letter', 'aria-hidden': 'true' }, k), ' ', KIND_WORD[k]),
    filters.kinds.includes(k),
    () => set({ kinds: filters.kinds.includes(k) ? filters.kinds.filter((x) => x !== k) : REQ_KINDS.filter((x) => x === k || filters.kinds.includes(x)) }),
    chipCount(kindCount(k)),
  )] as const));
  const kinds = h('div', { class: 'conf__kinds', role: 'group', 'aria-labelledby': 'conf-kind-label' },
    h('span', { class: 'conf__kinds-label', id: 'conf-kind-label' }, 'Kind'),
    [...kindChips.values()],
  );
  chips.defects.title = `${plural(counts.defects, 'rule has', 'rules have')} an open defect. The header counts ledger entries; one entry can name several rules and languages.`;
  const gapSelect = h('select', { class: 'conf__gap', id: 'conf-gap' },
    h('option', { value: '' }, 'Any language'),
    RUNTIMES.map((r) => h('option', { value: r }, `${COLUMN_LABEL[r]} (${rows.filter((row) => !row.cited[r]).length})`)),
  );
  gapSelect.value = filters.gap ?? '';
  gapSelect.addEventListener('change', () => set({ gap: RUNTIMES.find((r) => r === gapSelect.value) ?? null }));
  const gap = h('div', { class: 'conf__gap-field' }, h('label', { for: 'conf-gap', class: 'conf__gap-label' }, 'Untested in'), gapSelect);
  const clear = h('button', { type: 'button', class: 'conf__clear', on: { click: () => set(NO_FILTERS, true) } }, 'Clear filters');

  function set(change: Partial<ConfFilters>, refocus = false): void {
    filters = { ...filters, ...change };
    if (input.value !== filters.q) input.value = filters.q;
    ctx.navigate(R.conf(confQuery(filters)), { silent: true });
    redraw();
    if (refocus) input.focus();
  }

  input.addEventListener('input', () => set({ q: input.value }));

  function navItems(table: HTMLElement): HTMLElement[][] {
    return Array.from(table.querySelectorAll<HTMLTableRowElement>('tr[data-row], tr[data-band]'))
      .filter((tr) => !tr.hidden)
      .map((tr) => Array.from(tr.querySelectorAll<HTMLElement>('[data-nav]')));
  }

  /** A stable key of a focusable item, so the tab stop survives a redraw. */
  const keyOf = (el: HTMLElement): string => el.dataset['band'] ?? `${el.closest('tr')?.dataset['id'] ?? ''}|${el.dataset['col'] ?? ''}`;

  function setStop(table: HTMLElement, target: HTMLElement | null): void {
    for (const el of table.querySelectorAll<HTMLElement>('[data-nav]')) el.tabIndex = -1;
    const stop = target ?? table.querySelector<HTMLElement>('tr:not([hidden]) [data-nav]');
    if (stop) {
      stop.tabIndex = 0;
      focusKey = keyOf(stop);
    }
  }

  function onKey(table: HTMLElement, e: KeyboardEvent): void {
    const current = e.target instanceof HTMLElement ? e.target.closest<HTMLElement>('[data-nav]') : null;
    if (current === null || e.altKey || e.metaKey) return;
    const grid = navItems(table);
    const row = grid.findIndex((items) => items.includes(current));
    if (row < 0) return;
    const col = grid[row]?.indexOf(current) ?? 0;
    const next = moveInGrid(grid.map((items) => items.length), { row, col }, e.key, e.ctrlKey, wantCol);
    if (next === null) return;
    e.preventDefault();
    if (e.key === 'ArrowLeft' || e.key === 'ArrowRight' || e.key === 'Home' || e.key === 'End') wantCol = next.col;
    const target = grid[next.row]?.[next.col];
    if (target) {
      setStop(table, target);
      target.focus();
    }
  }

  function onClick(e: MouseEvent): void {
    const btn = e.target instanceof Element ? e.target.closest<HTMLElement>('button[data-col]') : null;
    const band = e.target instanceof Element ? e.target.closest<HTMLElement>('button[data-band]') : null;
    if (band !== null) {
      const file = band.dataset['band'] ?? '';
      const open = collapsed.has(file);
      if (open) collapsed.delete(file);
      else collapsed.add(file);
      band.setAttribute('aria-expanded', String(open));
      for (const tr of band.closest('tbody')?.querySelectorAll<HTMLTableRowElement>('tr[data-row]') ?? []) tr.hidden = !open;
      const table = band.closest('table');
      if (table) setStop(table, band);
      return;
    }
    if (btn === null) return;
    const id = btn.dataset['id'] ?? '';
    const col = btn.dataset['col'] ?? '';
    const row = rows.find((r) => r.block.id === id);
    if (row === undefined || !isConfColumn(col)) return;
    const table = btn.closest('table');
    if (table) setStop(table, btn);
    openDrawer({ title: `${id} in ${COLUMN_LABEL[col]}`, content: cellDetails(ctx, row, col) });
  }

  function redraw(): void {
    const bands = confBands(ctx.data, rows, filters);
    const shown = bands.reduce((n, b) => n + b.rows.length, 0);
    status.textContent = `Showing ${shown} of ${plural(rows.length, 'rule', 'rules')}`;
    chips.defects.setAttribute('aria-pressed', String(filters.defectsFirst));
    chips.untested.setAttribute('aria-pressed', String(filters.untested));
    chips.noLean.setAttribute('aria-pressed', String(filters.noLean));
    for (const [k, el] of kindChips) el.setAttribute('aria-pressed', String(filters.kinds.includes(k)));
    gapSelect.value = filters.gap ?? '';
    clear.hidden = !narrows(filters) && !filters.defectsFirst;

    if (shown === 0) {
      replaceChildren(host, h('div', { class: 'conf__empty' },
        h('p', null, 'No rules match these filters.'),
        h('button', { type: 'button', class: 'conf__clear', on: { click: () => set(NO_FILTERS, true) } }, 'Clear filters'),
      ));
      return;
    }
    const table = h('table', { class: 'conf__table' },
      h('caption', { class: 'sr-only' },
        'Conformance of each rule in Lean, Java, TypeScript, Rust and Python. Arrow keys move between cells; Enter opens the details of a cell.'),
      h('thead', null, h('tr', null,
        h('th', { scope: 'col', class: 'conf__col conf__col--id' }, 'ID'),
        h('th', { scope: 'col', class: 'conf__col conf__col--title' }, 'Title'),
        CONF_COLUMNS.map((c, i) => headerCell(c, summaries[i] ?? columnSummary(rows, c))),
      )),
      bands.filter((b) => b.rows.length > 0).map((band) => {
        const open = !collapsed.has(band.file);
        const countText = band.rows.length === band.total ? String(band.total) : `${band.rows.length} of ${band.total}`;
        return h('tbody', { class: 'conf__band' },
          h('tr', { class: 'conf__band-row', 'data-band': band.file },
            h('th', { scope: 'rowgroup', colspan: 2 + CONF_COLUMNS.length, class: 'conf__band-head' },
              h('button', { type: 'button', class: 'conf__band-btn', tabindex: -1, 'aria-expanded': String(open), 'data-band': band.file, 'data-nav': '' },
                h('span', { class: 'conf__band-caret', 'aria-hidden': 'true' }, '▸'),
                h('span', { class: 'conf__band-title' }, band.title),
                band.prefixes === '' ? null : h('span', { class: 'conf__band-meta' }, ` · ${band.prefixes}`),
                h('span', { class: 'conf__band-meta' }, ` · ${countText}`),
              ),
            ),
          ),
          band.rows.map((r) => {
            const tr = dataRow(ctx, r);
            tr.hidden = !open;
            return tr;
          }),
        );
      }),
    );
    table.addEventListener('keydown', (e) => onKey(table, e));
    table.addEventListener('click', onClick);
    replaceChildren(host,
      h('div', { class: 'conf__scroll' }, table),
      h('p', { class: 'conf__honest' }, TESTED_MEANS),
    );
    const restore = Array.from(table.querySelectorAll<HTMLElement>('[data-nav]'))
      .find((el) => focusKey !== null && keyOf(el) === focusKey && el.closest('tr')?.hidden !== true) ?? null;
    setStop(table, restore);
  }

  redraw();

  const stopEscape = listen(input, 'keydown', (e) => {
    if (e.key === 'Escape' && input.value !== '') {
      e.preventDefault();
      set({ q: '' });
    }
  });

  return {
    title: 'Conformance',
    node: viewFrame('conf', 'Conformance',
      h('p', { class: 'view__lede' },
        'Which rules each implementation is checked against. Lean states and proves; the test columns show whether a test file cites the rule.'),
      h('ul', { class: 'conf__summaries', 'aria-label': 'Column summaries' }, summaries.map(summaryCard)),
      h('div', { class: 'conf__toolbar' },
        h('label', { class: 'sr-only', for: 'conf-filter' }, 'Filter by ID or title'),
        input,
        h('div', { class: 'conf__chips', role: 'group', 'aria-label': 'Filters' }, chips.defects, chips.untested, chips.noLean, gap),
        clear,
        status,
        kindsShown.length > 0 ? kinds : null,
      ),
      host,
    ),
    dispose: stopEscape,
  };
}
