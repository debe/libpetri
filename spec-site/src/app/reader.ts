/**
 * Rules reader (`#/req`, `#/req/<ID>`, design 5): file navigation with filters on the left; in the
 * centre the spec sentences beside "What Lean checks" (quote matched to reading, assumptions,
 * the Lean statement, evidence by role, signoff and hash), then acceptance criteria, test
 * derivation and the situations that use the rule; on the right depends-on / used-by, defects and
 * tests per language. Tombstoned IDs get a tombstone page; unknown IDs the design 3.8 copy.
 *
 * Filters live in the route query (contracts 6.2): `kind` (ReqKind letters), `lean`
 * (`block`, `cited`, `none`), `f` (`signed`, `defect`, `untested`), `q` (text). Changing one
 * updates the address with a silent navigation and redraws the list in place.
 *
 * Owner: reader + md + search agent.
 */
import { REQ_KINDS, RUNTIMES } from '../model.js';
import type { BodyParagraph, Defect, Evidence, EvidenceRole, LeanBlock, ReqId, ReqKind, Signoff, SpecBlock, SpecFile } from '../model.js';
import type { AppContext, ViewResult } from './context.js';
import { thumbnailDiagram } from './data.js';
import { h, listen, replaceChildren, type Child } from './dom.js';
import { openDrawer } from './drawer.js';
import { KIND_WORD, openHelp } from './help.js';
import { viewKeys } from './keyboard.js';
import { blocks, inline, plainText } from './md.js';
import { href, type QueryParams, queryList, R, reqGraph, type RouteOf } from './router.js';
import { impactOf } from './graph.js';
import { openSearch, shortTheorem } from './search.js';
import {
  LEAN_META,
  leanState,
  openDefects,
  ROLE_META,
  ROLE_ORDER,
  RUNTIME_LABEL,
  type StatusMeta,
  TEST_META,
  TESTED_MEANS,
  testState,
} from './status.js';
import { idLink, statusBadge, viewFrame } from './ui.js';

// ---------------------------------------------------------------------------------------------
// Words
// ---------------------------------------------------------------------------------------------

/** Design 3.2 kind badge: one letter in a square, the word as tooltip and for screen readers. */
export function kindBadge(kind: ReqKind): HTMLElement {
  return h('span', { class: 'kind-badge', title: `Kind: ${KIND_WORD[kind]}` },
    h('span', { 'aria-hidden': 'true' }, kind),
    h('span', { class: 'sr-only' }, `Kind: ${KIND_WORD[kind]}`),
  );
}

/** Design 3.5 signoff badge. */
export function signoffBadge(signoff: Signoff): HTMLElement {
  if (signoff.state === 'pending') {
    return statusBadge({ glyph: '○', word: 'Not signed', tone: 'open', explain: "No reviewer has signed this block's statement yet." });
  }
  return h('span', { class: 'reader__signed' },
    statusBadge({ glyph: '●', word: `Signed ${signoff.date}`, tone: 'ok', explain: 'A reviewer signed this exact statement. The build fails if the statement changes.' }),
    ' ',
    h('code', { class: 'reader__hash', title: signoff.hash }, signoff.hash.slice(0, 9)),
  );
}

// ---------------------------------------------------------------------------------------------
// Filters (pure)
// ---------------------------------------------------------------------------------------------

export const LEAN_FILTERS = ['block', 'cited', 'mention', 'none'] as const;
export type LeanFilter = (typeof LEAN_FILTERS)[number];
export const FLAG_FILTERS = ['signed', 'defect', 'untested'] as const;
export type FlagFilter = (typeof FLAG_FILTERS)[number];

export interface ReaderFilters {
  readonly kinds: readonly ReqKind[];
  readonly lean: readonly LeanFilter[];
  readonly flags: readonly FlagFilter[];
  readonly q: string;
}

function pick<T extends string>(values: readonly string[], allowed: readonly T[]): readonly T[] {
  return allowed.filter((a) => values.includes(a));
}

/** Filters from the route query; unknown values are ignored. Pure. */
export function parseFilters(query: QueryParams): ReaderFilters {
  return {
    kinds: pick(queryList(query, 'kind'), REQ_KINDS),
    lean: pick(queryList(query, 'lean'), LEAN_FILTERS),
    flags: pick(queryList(query, 'f'), FLAG_FILTERS),
    q: (query['q'] ?? '').trim(),
  };
}

/** The query for a set of filters; defaults are left out. Pure. */
export function filtersToQuery(f: ReaderFilters): QueryParams {
  const out: Record<string, string> = {};
  if (f.kinds.length > 0) out['kind'] = f.kinds.join(',');
  if (f.lean.length > 0) out['lean'] = f.lean.join(',');
  if (f.flags.length > 0) out['f'] = f.flags.join(',');
  if (f.q !== '') out['q'] = f.q;
  return out;
}

export function filtersActive(f: ReaderFilters): boolean {
  return f.kinds.length > 0 || f.lean.length > 0 || f.flags.length > 0 || f.q !== '';
}

export const NO_FILTERS: ReaderFilters = { kinds: [], lean: [], flags: [], q: '' };

/** Toggles one value of a list, keeping the canonical order of `all`. Pure. */
export function toggle<T extends string>(list: readonly T[], value: T, all: readonly T[]): readonly T[] {
  return list.includes(value) ? list.filter((v) => v !== value) : all.filter((v) => v === value || list.includes(v));
}

function leanFilterOf(ctx: AppContext, id: ReqId): LeanFilter {
  return leanState(ctx, id);
}

function hasFlag(ctx: AppContext, block: SpecBlock, flag: FlagFilter): boolean {
  switch (flag) {
    case 'signed':
      return ctx.index.lean(block.id).some((b) => b.signoff.state === 'signed');
    case 'defect':
      return openDefects(ctx, block.id).length > 0;
    case 'untested': {
      const row = ctx.data.coverage[block.id];
      return row !== undefined && RUNTIMES.every((r) => row.tests[r].state === 'untested');
    }
  }
}

/**
 * True when a block passes the filters: values of one filter are alternatives (kind B or F),
 * different filters must all hold. Tombstones pass only when no filter is on.
 */
export function matchesFilters(ctx: AppContext, block: SpecBlock, f: ReaderFilters): boolean {
  if (block.status.state === 'removed') return !filtersActive(f);
  if (f.kinds.length > 0 && (block.kind === null || !f.kinds.includes(block.kind))) return false;
  if (f.lean.length > 0 && !f.lean.includes(leanFilterOf(ctx, block.id))) return false;
  if (!f.flags.every((flag) => hasFlag(ctx, block, flag))) return false;
  if (f.q !== '') {
    const q = f.q.toLowerCase();
    const compactQ = q.replace(/[^a-z0-9]/g, '');
    const idHit = compactQ !== '' && block.id.toLowerCase().replace(/[^a-z0-9]/g, '').includes(compactQ);
    if (!idHit && !block.title.toLowerCase().includes(q)) return false;
  }
  return true;
}

/** The ID `j` (+1) or `k` (-1) moves to in the filtered list, or null at the end. Pure. */
export function neighbour(order: readonly ReqId[], visible: readonly ReqId[], current: ReqId, step: 1 | -1): ReqId | null {
  const at = visible.indexOf(current);
  if (at >= 0) return visible[at + step] ?? null;
  // The current rule is filtered out: move to the nearest visible one in spec order.
  const pos = order.indexOf(current);
  const rank = (id: ReqId): number => order.indexOf(id);
  if (step === 1) return visible.find((id) => rank(id) > pos) ?? null;
  return [...visible].reverse().find((id) => rank(id) < pos) ?? null;
}

/** How a Lean block's quotes and reading lines are laid out (design 5.3). */
export interface QuoteLayout {
  /** Leading reading lines that set the scene ("For every executor R:", "Let Build be ..."). */
  readonly preamble: readonly string[];
  /**
   * True when the quotes and the reading lines after the preamble are equal in number. Only
   * then does line i read quote i, and only then are they shown side by side with a number.
   */
  readonly paired: boolean;
  readonly quotes: readonly string[];
  readonly lines: readonly string[];
}

/** A reading line that introduces the others rather than reading one quote. */
function isPreambleLine(line: string): boolean {
  return line.trimEnd().endsWith(':') || /^Let\s/.test(line);
}

/**
 * Splits off the preamble and decides whether quotes and reading lines pair by position. The
 * Lean data carries no quote-to-line mapping, so unequal counts are shown as two lists rather
 * than a table that would suggest a correspondence. Pure.
 */
export function quoteLayout(quotes: readonly string[], reading: readonly string[]): QuoteLayout {
  let n = 0;
  while (n < reading.length - 1 && isPreambleLine(reading[n] ?? '')) n += 1;
  const lines = reading.slice(n);
  return { preamble: reading.slice(0, n), paired: quotes.length > 0 && quotes.length === lines.length, quotes, lines };
}

/** Evidence grouped by role in the design 3.3 order, empty groups left out. Pure. */
export function groupEvidence(evidence: readonly Evidence[]): readonly { readonly role: EvidenceRole; readonly items: readonly Evidence[] }[] {
  return ROLE_ORDER.map((role) => ({ role, items: evidence.filter((e) => e.role === role) })).filter((g) => g.items.length > 0);
}

/** Groups shown open: holds, nonvacuous and conflict always, others when short. */
export function groupOpen(role: EvidenceRole, size: number): boolean {
  return role === 'holds' || role === 'nonvacuous' || role === 'conflict' || size <= 4;
}

/** The label of a Lean block among its ID's blocks: the ID, or the title's companion suffix. Pure. */
export function blockLabel(block: LeanBlock, index: number): string {
  if (index === 0) return block.id;
  const suffix = /\(([^)]+)\)\s*$/.exec(block.title)?.[1];
  return suffix === undefined ? `${block.id} · ${shortTheorem(block.decl)}` : `${block.id} (${suffix})`;
}

/** Lean statement keywords and connectives, for highlighting. */
export const LEAN_TOKEN = /\b(?:on|shall|when|while|never|until|after|occurs)\b|at-most-once|[∀∃¬∧∨→↔]/gu;

/** Splits a Lean statement into plain, keyword and symbol runs. Pure. */
export function leanRuns(statement: string): readonly { readonly kind: 'text' | 'kw' | 'sym'; readonly text: string }[] {
  const out: { kind: 'text' | 'kw' | 'sym'; text: string }[] = [];
  let last = 0;
  const re = new RegExp(LEAN_TOKEN.source, LEAN_TOKEN.flags);
  for (let m = re.exec(statement); m !== null; m = re.exec(statement)) {
    if (m.index > last) out.push({ kind: 'text', text: statement.slice(last, m.index) });
    out.push({ kind: /^[a-z-]+$/.test(m[0]) ? 'kw' : 'sym', text: m[0] });
    last = m.index + m[0].length;
  }
  if (last < statement.length) out.push({ kind: 'text', text: statement.slice(last) });
  return out;
}

// ---------------------------------------------------------------------------------------------
// Small pieces
// ---------------------------------------------------------------------------------------------

/** Timers and listeners a view starts, stopped in its dispose. */
class Disposer {
  private readonly stops: (() => void)[] = [];
  add(stop: () => void): void {
    this.stops.push(stop);
  }
  timeout(fn: () => void, ms: number): void {
    const t = window.setTimeout(fn, ms);
    this.add(() => clearTimeout(t));
  }
  dispose(): void {
    for (const s of this.stops.splice(0)) s();
  }
}

/** A Copy button: writes `text` to the clipboard, says "Copied" for 1.5 s. */
function copyButton(d: Disposer, label: string, text: () => string, accessible: string): HTMLElement {
  const button = h('button', { type: 'button', class: 'reader__copy', 'aria-label': accessible }, label);
  listen(button, 'click', () => {
    const done = (): void => {
      button.textContent = 'Copied';
      d.timeout(() => {
        button.textContent = label;
      }, 1500);
    };
    try {
      const clip = navigator.clipboard as Clipboard | undefined; // absent on file:// in some browsers
      if (clip === undefined) return;
      clip.writeText(text()).then(done, () => {});
    } catch {
      // No clipboard: the text is on screen to select.
    }
  });
  return button;
}

function section(cls: string, title: string, ...children: readonly Child[]): HTMLElement {
  const id = `reader-${cls}`;
  return h('section', { class: ['reader__section', `reader__section--${cls}`], 'aria-labelledby': id },
    h('h2', { class: 'reader__h2', id }, title),
    ...children,
  );
}

function proofGraphHref(ctx: AppContext, theorem: string): string {
  return `${ctx.data.links.proofGraph}#${encodeURI(theorem)}`;
}

function fileHref(ctx: AppContext, block: SpecBlock): string {
  return `${ctx.data.links.blob}spec/${block.file}#L${block.line}`;
}

// ---------------------------------------------------------------------------------------------
// Defect drawer
// ---------------------------------------------------------------------------------------------

/** Opens a ledger entry in the drawer (design 3.7). */
export function openDefectDrawer(ctx: AppContext, defect: Defect): void {
  const status: StatusMeta = defect.status.state === 'open'
    ? { glyph: '⚠', word: 'Open', tone: 'defect', explain: 'The runtime breaks the rule; ledger entry open' }
    : { glyph: '✓', word: `Fixed in ${defect.status.version}`, tone: 'ok', explain: 'Fixed; kept in the ledger as history' };
  openDrawer({
    title: `${defect.id} ${defect.title}`,
    content: h('div', { class: 'defect-card' },
      h('p', null, statusBadge(status)),
      h('dl', { class: 'defect-card__facts' },
        h('dt', null, 'Rules'), h('dd', null, defect.requirements.map((id) => [idLink(ctx, id), ' '])),
        h('dt', null, 'Runtimes'), h('dd', null, defect.runtimes.map((r) => RUNTIME_LABEL[r]).join(', ') || 'None named'),
      ),
      h('h3', { class: 'defect-card__h' }, 'Defect'),
      h('div', { class: 'defect-card__text' }, blocks(ctx, defect.text)),
      h('h3', { class: 'defect-card__h' }, 'Lean evidence'),
      defect.evidence.length > 0
        ? h('ul', { class: 'defect-card__thms' }, defect.evidence.map((t) => h('li', null,
            h('code', { title: t }, shortTheorem(t)), ' ', h('a', { href: proofGraphHref(ctx, t) }, 'Proof graph ↗'))))
        : h('div', { class: 'defect-card__text' }, blocks(ctx, defect.evidenceText)),
      h('p', null, h('a', { href: href(R.graph({ kind: 'defect', id: defect.id })) }, 'Open in graph')),
    ),
  });
}

function defectBadge(ctx: AppContext, defect: Defect): HTMLElement {
  return h('button', {
    type: 'button',
    class: ['badge', 'badge--defect', 'reader__defect-badge'],
    title: `Open ${defect.id}: ${defect.title}`,
    'aria-haspopup': 'dialog',
    on: { click: () => openDefectDrawer(ctx, defect) },
  }, h('span', { 'aria-hidden': 'true' }, '⚠'), ` ${defect.id}`);
}

// ---------------------------------------------------------------------------------------------
// Left navigation
// ---------------------------------------------------------------------------------------------

interface NavState {
  filters: ReaderFilters;
}

function chip(label: string, count: number, pressed: boolean, onToggle: () => void, title?: string): HTMLElement {
  return h('button', {
    type: 'button',
    class: 'filter-chip',
    'aria-pressed': String(pressed),
    ...(title === undefined ? {} : { title }),
    on: { click: onToggle },
  }, h('span', { class: 'filter-chip__check', 'aria-hidden': 'true' }, '✓'), `${label} `, h('span', { class: 'filter-chip__count' }, count));
}

function visibleIds(ctx: AppContext, f: ReaderFilters): readonly ReqId[] {
  return ctx.data.blocks.filter((b) => b.status.state !== 'removed' && matchesFilters(ctx, b, f)).map((b) => b.id);
}

function fileLabel(file: SpecFile): string {
  return `${file.number} ${file.title}`;
}

function navRow(ctx: AppContext, block: SpecBlock, currentId: ReqId | null, query: QueryParams): HTMLElement {
  const removed = block.status.state === 'removed';
  const lean = LEAN_META[leanState(ctx, block.id)];
  return h('li', null,
    h('a', {
      class: ['reader__row', removed && 'reader__row--removed'],
      href: href(R.req(block.id, query)),
      title: `${block.id} ${block.title}`,
      'aria-current': block.id === currentId ? 'page' : null,
    },
      h('span', { class: 'reader__row-id' }, block.id),
      h('span', { class: 'reader__row-title' }, block.title, removed ? h('span', { class: 'sr-only' }, ' (removed)') : null),
      removed
        ? null
        : h('span', { class: `reader__row-lean reader__row-lean--${lean.tone}`, title: lean.explain },
            h('span', { 'aria-hidden': 'true' }, lean.glyph), h('span', { class: 'sr-only' }, `, ${lean.word}`)),
    ),
  );
}

function buildNav(ctx: AppContext, currentId: ReqId | null, state: NavState, onChange: () => void): { readonly node: HTMLElement; readonly current: () => HTMLElement | null } {
  const files = h('div', { class: 'reader__files' });
  const empty = h('div', { class: 'reader__empty', hidden: true });
  const currentFile = currentId === null ? null : ctx.index.blocks.get(currentId)?.file ?? null;
  const qInput = h('input', {
    class: 'reader__q',
    type: 'search',
    value: state.filters.q,
    placeholder: 'Filter by ID or title',
    'aria-label': 'Filter by ID or title',
    autocomplete: 'off',
    spellcheck: false,
  });
  const set = (next: ReaderFilters): void => {
    state.filters = next;
    onChange();
    drawList();
  };
  const clearButton = (): HTMLElement => h('button', {
    type: 'button',
    class: 'reader__clear',
    on: {
      click: () => {
        qInput.value = '';
        set(NO_FILTERS);
        for (const c of chips) c.el.setAttribute('aria-pressed', 'false');
      },
    },
  }, 'Clear filters');

  const active = ctx.index.activeBlocks;
  const countOf = (one: ReaderFilters): number => active.filter((b) => matchesFilters(ctx, b, one)).length;
  const chips: { readonly el: HTMLElement; readonly on: () => boolean }[] = [];
  const addChip = (label: string, count: number, on: () => boolean, flip: () => ReaderFilters, title?: string): HTMLElement => {
    const el = chip(label, count, on(), () => {
      set(flip());
      el.setAttribute('aria-pressed', String(on()));
    }, title);
    chips.push({ el, on });
    return el;
  };
  const kindChips = REQ_KINDS.map((k) => {
    const n = countOf({ ...NO_FILTERS, kinds: [k] });
    return n === 0 && !state.filters.kinds.includes(k)
      ? null
      : addChip(k, n, () => state.filters.kinds.includes(k), () => ({ ...state.filters, kinds: toggle(state.filters.kinds, k, REQ_KINDS) }), KIND_WORD[k]);
  });
  // The same four Lean states as the Conformance matrix (block, cited, mentioned, none).
  const leanLabels: { readonly [L in LeanFilter]: string } = { block: 'Has block', cited: 'Cited', mention: 'Mentioned', none: 'None' };
  const leanChips = LEAN_FILTERS.map((l) => addChip(leanLabels[l], countOf({ ...NO_FILTERS, lean: [l] }),
    () => state.filters.lean.includes(l), () => ({ ...state.filters, lean: toggle(state.filters.lean, l, LEAN_FILTERS) }), LEAN_META[l].explain));
  const flagLabels: { readonly [F in FlagFilter]: string } = { signed: 'Signed', defect: 'Has open defect', untested: 'Untested anywhere' };
  const flagTitles: { readonly [F in FlagFilter]: string } = {
    signed: 'Rules with a Lean block a reviewer signed',
    defect: 'Rules named by an open entry of the defect ledger. One entry can name several rules, so this counts rules, not entries.',
    untested: 'Rules no test file in any language cites',
  };
  const flagChips = FLAG_FILTERS.map((fl) => addChip(flagLabels[fl], countOf({ ...NO_FILTERS, flags: [fl] }),
    () => state.filters.flags.includes(fl), () => ({ ...state.filters, flags: toggle(state.filters.flags, fl, FLAG_FILTERS) }), flagTitles[fl]));

  const clearSlot = h('div', { class: 'reader__clear-slot' });
  // Open on very wide screens or while a filter is on; otherwise one summary to tab past.
  const filtersOpen = filtersActive(state.filters) || (typeof matchMedia === 'function' && matchMedia('(min-width: 1400px)').matches);
  const filterBlock = h('details', { class: 'reader__filters', open: filtersOpen },
    h('summary', { class: 'reader__filters-summary' }, 'Filters'),
    h('div', { class: 'reader__chip-group', role: 'group', 'aria-label': 'Kind' }, h('span', { class: 'reader__chip-label', 'aria-hidden': 'true' }, 'Kind'), kindChips),
    h('div', { class: 'reader__chip-group', role: 'group', 'aria-label': 'Lean' }, h('span', { class: 'reader__chip-label', 'aria-hidden': 'true' }, 'Lean'), leanChips),
    h('div', { class: 'reader__chip-group', role: 'group', 'aria-label': 'Status' }, h('span', { class: 'reader__chip-label', 'aria-hidden': 'true' }, 'Status'), flagChips),
    clearSlot,
  );

  let currentRow: HTMLElement | null = null;
  // The rows are one tab stop (roving tabindex): arrow keys, Home and End move between the rows
  // of open files, so Tab leaves the list in one step.
  const openRows = (): HTMLElement[] => Array.from(files.querySelectorAll<HTMLElement>('details[open] .reader__row'));
  const setStop = (row: HTMLElement | null): void => {
    for (const r of files.querySelectorAll<HTMLElement>('.reader__row')) r.tabIndex = -1;
    const target = row ?? openRows()[0] ?? null;
    if (target !== null) target.tabIndex = 0;
  };
  const keepStopVisible = (): void => {
    const stop = files.querySelector<HTMLElement>('.reader__row[tabindex="0"]');
    if (stop === null || !openRows().includes(stop)) setStop(currentRow !== null && openRows().includes(currentRow) ? currentRow : null);
  };
  listen(files, 'keydown', (event) => {
    const target = event.target;
    if (!(target instanceof HTMLElement) || !target.classList.contains('reader__row')) return;
    const rows = openRows();
    const at = rows.indexOf(target);
    const next = event.key === 'ArrowDown' ? rows[at + 1]
      : event.key === 'ArrowUp' ? rows[at - 1]
      : event.key === 'Home' ? rows[0]
      : event.key === 'End' ? rows[rows.length - 1]
      : undefined;
    if (next === undefined) return;
    event.preventDefault();
    setStop(next);
    next.focus();
  });
  listen(files, 'focusin', (event) => {
    if (event.target instanceof HTMLElement && event.target.classList.contains('reader__row')) setStop(event.target);
  });
  const drawList = (): void => {
    const f = state.filters;
    const query = filtersToQuery(f);
    const filtering = filtersActive(f);
    currentRow = null;
    let shown = 0;
    const groups = ctx.data.files.map((file) => {
      const fileBlocks = ctx.data.blocks.filter((b) => b.file === file.file && matchesFilters(ctx, b, f));
      if (fileBlocks.length === 0) return null;
      const live = fileBlocks.filter((b) => b.status.state !== 'removed').length;
      shown += live;
      const list = h('ul', { class: 'reader__rows' }, fileBlocks.map((b) => navRow(ctx, b, currentId, query)));
      const row = list.querySelector<HTMLElement>('[aria-current="page"]');
      if (row !== null) currentRow = row;
      const group = h('details', { class: 'reader__file', open: filtering || file.file === currentFile || currentFile === null },
        h('summary', { class: 'reader__file-summary' },
          h('span', { class: 'reader__file-name' }, fileLabel(file)),
          h('span', { class: 'reader__file-meta' }, ` · ${file.prefixes.join(', ')} · `, h('span', { class: 'reader__file-count' }, live)),
        ),
        list,
      );
      listen(group, 'toggle', keepStopVisible);
      return group;
    });
    replaceChildren(files, groups);
    setStop(currentRow);
    empty.hidden = shown > 0;
    replaceChildren(empty, h('p', null, 'No rules match these filters.'), clearButton());
    replaceChildren(clearSlot, filtering ? clearButton() : null);
  };

  listen(qInput, 'input', () => set({ ...state.filters, q: qInput.value.trim() }));
  drawList();

  const toggleButton = h('button', { type: 'button', class: 'reader__nav-toggle', 'aria-expanded': 'false', 'aria-controls': 'reader-nav-body' }, 'Files and filters');
  const navBody = h('div', { class: 'reader__nav-body', id: 'reader-nav-body' }, filterBlock, qInput, empty,
    h('p', { class: 'sr-only', id: 'reader-rows-hint' }, 'Arrow keys move between rules.'), files);
  // "Skip to content" lands before this list; this second skip link jumps over it to the rule.
  const skip = h('a', { class: 'reader__skip', href: href(R.req(currentId)) }, 'Skip to the rule text');
  listen(skip, 'click', (event) => {
    event.preventDefault();
    document.getElementById('view-title-req')?.focus();
  });
  const node = h('nav', { class: 'reader__nav', 'aria-label': 'Requirements' }, currentId === null ? null : skip, toggleButton, navBody);
  listen(toggleButton, 'click', () => {
    const open = toggleButton.getAttribute('aria-expanded') !== 'true';
    toggleButton.setAttribute('aria-expanded', String(open));
    node.classList.toggle('reader__nav--open', open);
  });
  return { node, current: () => currentRow };
}

// ---------------------------------------------------------------------------------------------
// Lean column
// ---------------------------------------------------------------------------------------------

function quotePairs(ctx: AppContext, block: LeanBlock): HTMLElement {
  const layout = quoteLayout(block.quotes, block.reading);
  const preamble = layout.preamble.map((line) => h('p', { class: 'reader__preamble' }, inline(ctx, line, { ears: false })));
  if (layout.paired) {
    return h('div', { class: 'reader__pairs' },
      preamble,
      h('div', { class: 'reader__pairs-head', 'aria-hidden': 'true' }, h('span', null, 'Quote'), h('span', null, 'Reading')),
      h('ol', { class: 'reader__pair-list' }, layout.quotes.map((quote, i) => h('li', { class: 'reader__pair' },
        h('span', { class: 'reader__pair-n', 'aria-hidden': 'true' }, String(i + 1)),
        h('blockquote', { class: 'reader__pair-quote' }, h('span', { class: 'sr-only' }, `Quote ${i + 1}: `), inline(ctx, quote)),
        h('p', { class: 'reader__pair-reading' }, h('span', { class: 'sr-only' }, `Reading ${i + 1}: `), inline(ctx, layout.lines[i] ?? '', { ears: false })),
      ))),
    );
  }
  // Unequal counts: two plain lists, so nothing suggests that line i reads quote i.
  return h('div', { class: ['reader__pairs', 'reader__pairs--lists'] },
    h('h4', { class: 'reader__list-title' }, 'Quote'),
    layout.quotes.length === 0
      ? h('p', { class: 'reader__muted' }, 'No spec sentence is quoted.')
      : h('ul', { class: 'reader__quote-list' }, layout.quotes.map((q) => h('li', null, h('blockquote', { class: 'reader__pair-quote' }, inline(ctx, q))))),
    h('h4', { class: 'reader__list-title' }, 'Reading'),
    preamble,
    h('ul', { class: 'reader__reading-list' }, layout.lines.map((line) => h('li', { class: 'reader__pair-reading' }, inline(ctx, line, { ears: false })))),
  );
}

const STATEMENT_FOLD_LINES = 18;

function statement(ctx: AppContext, d: Disposer, block: LeanBlock): HTMLElement {
  const lines = block.statement.split('\n').length;
  const pre = h('pre', { class: ['reader__stmt', lines > STATEMENT_FOLD_LINES && 'reader__stmt--folded'], tabindex: 0, 'aria-label': `Lean statement of ${block.decl}` },
    h('code', null, leanRuns(block.statement).map((r) => (r.kind === 'text' ? r.text : h('span', { class: `lean-${r.kind}` }, r.text)))),
  );
  const more = lines > STATEMENT_FOLD_LINES
    ? h('button', { type: 'button', class: 'reader__link-button', 'aria-expanded': 'false' }, `Show all ${lines} lines`)
    : null;
  if (more !== null) {
    listen(more, 'click', () => {
      const open = pre.classList.toggle('reader__stmt--folded') === false;
      more.setAttribute('aria-expanded', String(open));
      more.textContent = open ? 'Show less' : `Show all ${lines} lines`;
    });
  }
  return h('details', { class: 'reader__details reader__details--stmt', open: wide() },
    h('summary', null, 'Lean statement'),
    h('div', { class: 'reader__stmt-head' },
      h('code', { class: 'reader__decl', title: block.decl }, block.decl),
      copyButton(d, 'Copy', () => block.statement, `Copy the Lean statement of ${block.decl}`),
    ),
    pre,
    h('p', { class: 'reader__stmt-foot' },
      more,
      h('button', { type: 'button', class: 'reader__link-button', on: { click: () => openHelp(ctx, 'lean') } }, 'How to read Lean statements'),
    ),
  );
}

/** The label of a theorem's docstring disclosure: what the docstring holds for its role. */
export function docLabel(role: EvidenceRole): string {
  switch (role) {
    case 'forbids':
    case 'violated':
      return 'Counterexample';
    case 'nonvacuous':
    case 'allows':
    case 'consistent':
      return 'Witness';
    case 'mutant':
      return 'The wrong reading';
    case 'conflict':
      return 'The conflict';
    default:
      return 'What it says';
  }
}

/** True on wide screens, where the Lean statement and the first counterexample start open. */
function wide(): boolean {
  return typeof matchMedia === 'function' && matchMedia('(min-width: 1100px)').matches;
}

function evidenceRow(ctx: AppContext, e: Evidence, open: boolean): HTMLElement {
  const short = shortTheorem(e.theorem);
  return h('li', { class: 'reader__thm' },
    h('div', { class: 'reader__thm-line' },
      h('a', { class: 'reader__thm-name', href: href(R.graph({ kind: 'theorem', name: e.theorem })), title: e.theorem }, short),
      h('a', { class: 'reader__thm-pg', href: proofGraphHref(ctx, e.theorem), 'aria-label': `Proof graph of ${short}` }, 'Proof graph ↗'),
    ),
    h('span', { class: 'reader__thm-module' }, e.module),
    e.doc === null
      ? null
      : h('details', { class: 'reader__example', open }, h('summary', null, docLabel(e.role)), h('div', { class: 'reader__doc' }, blocks(ctx, e.doc, { ears: false }))),
  );
}

function evidence(ctx: AppContext, block: LeanBlock, headingId: string): HTMLElement {
  const groups = groupEvidence(block.evidence);
  // The first counterexample opens by itself on wide screens: it shows what the rule rules out.
  const firstForbids = wide();
  return h('section', { class: 'reader__evidence', 'aria-labelledby': headingId },
    h('h4', { class: 'reader__h4', id: headingId }, 'Evidence'),
    groups.length === 0
      ? h('p', { class: 'reader__muted' }, 'No evidence theorems listed.')
      : groups.map((g) => {
          const meta = ROLE_META[g.role];
          return h('details', { class: ['reader__role', `reader__role--${meta.tone}`], open: groupOpen(g.role, g.items.length) || (g.role === 'forbids' && firstForbids) },
            h('summary', { class: 'reader__role-summary', title: meta.explain },
              h('span', { class: `reader__role-glyph tone--${meta.tone}`, 'aria-hidden': 'true' }, meta.glyph === '✗m' ? ['✗', h('small', null, 'm')] : meta.glyph),
              ` ${meta.word} · ${g.items.length}`,
            ),
            h('ul', { class: 'reader__thms' }, g.items.map((e, i) => evidenceRow(ctx, e, i === 0 && g.role === 'forbids' && firstForbids))),
          );
        }),
  );
}

function leanBlockCard(ctx: AppContext, d: Disposer, block: LeanBlock, index: number, total: number): HTMLElement {
  const label = blockLabel(block, index);
  const base = `lean-${block.decl.replace(/[^A-Za-z0-9]/g, '-')}`;
  const sourceBadge = block.source === 'verbatim'
    ? statusBadge({ glyph: '“', word: 'verbatim', tone: 'none', explain: 'The quotes are the spec text, word for word' })
    : statusBadge({ glyph: '?', word: block.source, tone: 'open', explain: 'New text, not yet in the spec' });
  return h('article', { class: 'reader__lean-block', 'aria-labelledby': `${base}-h` },
    total > 1 ? h('h3', { class: 'reader__h3', id: `${base}-h` }, label) : h('h3', { class: 'sr-only', id: `${base}-h` }, `Lean block ${label}`),
    h('p', { class: 'reader__scope' }, `Scope: ${block.scope}`, ' ', sourceBadge),
    quotePairs(ctx, block),
    block.assumes.length === 0
      ? null
      : h('details', { class: 'reader__details' },
          h('summary', null, 'What the model assumes'),
          h('ul', { class: 'reader__assumes' }, block.assumes.map((a) => h('li', null, inline(ctx, a, { ears: false })))),
        ),
    statement(ctx, d, block),
    evidence(ctx, block, `${base}-ev`),
    h('footer', { class: 'reader__lean-foot' },
      signoffBadge(block.signoff),
      h('span', { class: 'reader__hash-line' }, 'Statement hash ', h('code', { class: 'reader__hash', title: block.hash }, block.hash.slice(0, 9))),
    ),
  );
}

/**
 * A requirement's Lean blocks: one card, or for companion blocks a `tablist` above one panel per
 * block (design 5.3). Arrow keys, Home and End move the selection and the focus.
 */
function leanBlocks(ctx: AppContext, d: Disposer, lean: readonly LeanBlock[]): Child {
  const [only] = lean;
  if (lean.length === 1 && only !== undefined) return leanBlockCard(ctx, d, only, 0, 1);
  const base = (b: LeanBlock): string => `lean-tab-${b.decl.replace(/[^A-Za-z0-9]/g, '-')}`;
  const tabs = lean.map((b, i) => h('button', {
    type: 'button',
    role: 'tab',
    class: 'reader__tab',
    id: `${base(b)}-tab`,
    'aria-controls': `${base(b)}-panel`,
    'aria-selected': String(i === 0),
    tabindex: i === 0 ? 0 : -1,
  }, blockLabel(b, i)));
  const panels = lean.map((b, i) => h('div', {
    role: 'tabpanel',
    class: 'reader__tabpanel',
    id: `${base(b)}-panel`,
    'aria-labelledby': `${base(b)}-tab`,
    hidden: i !== 0,
  }, leanBlockCard(ctx, d, b, i, lean.length)));
  const select = (index: number, focus: boolean): void => {
    tabs.forEach((tab, i) => {
      tab.setAttribute('aria-selected', String(i === index));
      tab.tabIndex = i === index ? 0 : -1;
    });
    panels.forEach((panel, i) => {
      panel.hidden = i !== index;
    });
    if (focus) tabs[index]?.focus();
  };
  const list = h('div', { role: 'tablist', class: 'reader__tabs', 'aria-label': 'Lean blocks of this rule' }, tabs);
  tabs.forEach((tab, i) => d.add(listen(tab, 'click', () => select(i, false))));
  d.add(listen(list, 'keydown', (event) => {
    const current = tabs.findIndex((t) => t.getAttribute('aria-selected') === 'true');
    const last = tabs.length - 1;
    const next = event.key === 'ArrowRight' ? (current + 1) % tabs.length
      : event.key === 'ArrowLeft' ? (current + last) % tabs.length
      : event.key === 'Home' ? 0
      : event.key === 'End' ? last
      : null;
    if (next === null) return;
    event.preventDefault();
    select(next, true);
  }));
  return [list, panels];
}

function noLeanCard(ctx: AppContext, id: ReqId): HTMLElement {
  const cites = ctx.index.citationsByReq.get(id) ?? [];
  const state = leanState(ctx, id);
  return h('div', { class: 'reader__no-lean' },
    h('p', { class: 'reader__no-lean-title' }, 'No Lean block yet.'),
    cites.length > 0
      ? [
          h('p', null, `Cited by ${cites.length} ${cites.length === 1 ? 'theorem' : 'theorems'}`),
          h('ul', { class: 'reader__thms' }, cites.map((c) => h('li', { class: 'reader__thm' },
            h('div', { class: 'reader__thm-line' },
              h('span', { class: 'reader__role-glyph tone--none', 'aria-hidden': 'true' }, '↗'),
              h('span', { class: 'sr-only' }, 'cites: '),
              h('a', { class: 'reader__thm-name', href: href(R.graph({ kind: 'theorem', name: c.theorem })), title: c.theorem }, shortTheorem(c.theorem)),
              h('a', { class: 'reader__thm-pg', href: proofGraphHref(ctx, c.theorem), 'aria-label': `Proof graph of ${shortTheorem(c.theorem)}` }, 'Proof graph ↗'),
            ),
            h('p', { class: 'reader__fragment' }, inline(ctx, c.fragment, { ears: false })),
          ))),
        ]
      : h('p', { class: 'reader__muted' }, state === 'mention' ? 'Mentioned in Lean comments only.' : 'Lean does not mention this rule.'),
  );
}

// ---------------------------------------------------------------------------------------------
// Side column
// ---------------------------------------------------------------------------------------------

function chips(ctx: AppContext, ids: readonly ReqId[]): Child {
  return ids.length === 0 ? h('p', { class: 'reader__muted' }, 'None') : h('ul', { class: 'reader__chips' }, ids.map((id) => h('li', null, idLink(ctx, id))));
}

/** A repository path with a line-break opportunity after each `/` and nowhere else. */
function pathNode(path: string): Child[] {
  return path.split(/(?<=\/)/).flatMap((part, i) => (i === 0 ? [part] : [h('wbr'), part]));
}

/** A language's test files: a count behind a disclosure, basenames with the full path as title. */
function refList(ctx: AppContext, refs: readonly string[]): HTMLElement {
  return h('details', { class: 'reader__refs' },
    h('summary', null, refs.length === 1 ? '1 file' : `${refs.length} files`),
    h('ul', null, refs.map((ref) => h('li', null,
      h('a', { href: `${ctx.data.links.blob}${ref}`, rel: 'noopener', title: ref }, h('code', null, pathNode(ref)))))),
  );
}

/** Rules that depend on `id` directly or through others (the impact view's closure). */
export function transitiveUsers(ctx: AppContext, id: ReqId): number {
  return impactOf(ctx.index, { kind: 'req', id }, { hops: Number.POSITIVE_INFINITY }).layers.flat().filter((hit) => hit.node.kind === 'req').length;
}

function defectEntry(ctx: AppContext, d: Defect): HTMLElement {
  return h('li', { class: 'reader__defect' },
    defectBadge(ctx, d),
    h('span', { class: 'reader__defect-runtimes' }, d.runtimes.map((r) => RUNTIME_LABEL[r]).join(', ')),
    h('span', { class: 'reader__defect-title' }, d.title),
    h('details', { class: 'reader__defect-more' },
      h('summary', null, 'What breaks'),
      h('div', { class: 'reader__doc' }, blocks(ctx, d.text, { ears: false })),
      d.evidence.length > 0
        ? h('p', { class: 'reader__defect-ev' }, 'Lean evidence: ', d.evidence.map((t, i) => [i > 0 ? ', ' : null,
            h('a', { href: href(R.graph({ kind: 'theorem', name: t })), title: t }, h('code', null, shortTheorem(t)))]))
        : null,
    ),
  );
}

function sideColumn(ctx: AppContext, block: SpecBlock): HTMLElement {
  const id = block.id;
  const usedBy = ctx.index.usedBy.get(id) ?? [];
  const reach = transitiveUsers(ctx, id);
  const all = ctx.index.defectsByReq.get(id) ?? [];
  const open = all.filter((d) => d.status.state === 'open');
  const fixed = all.filter((d) => d.status.state === 'fixed');
  const lean = LEAN_META[leanState(ctx, id)];
  const cited = (ctx.index.citationsByReq.get(id) ?? []).length;
  const shown = ctx.index.situationsByReq.get(id) ?? [];
  const replayed = shown.filter((s) => s.result !== null).length;
  const runtimeRow = (r: (typeof RUNTIMES)[number]): HTMLElement => {
    const st = testState(ctx, id, r);
    const meta = TEST_META[st.state];
    const refs = st.state === 'tested' ? st.refs : [];
    return h('li', { class: 'reader__test' },
      h('span', { class: 'reader__test-name' }, RUNTIME_LABEL[r], r === 'python' ? h('span', { class: 'reader__note-mark', title: 'Python binds the Rust runtime.' }, ' ⓘ') : null),
      st.state === 'defect'
        ? h('span', { class: 'reader__test-state' }, st.defects.map((d) => defectBadge(ctx, d)))
        : h('span', { class: `reader__test-state tone--${meta.tone}`, title: meta.explain }, h('span', { 'aria-hidden': 'true' }, meta.glyph), ` ${meta.word}`),
      refs.length > 0 ? refList(ctx, refs) : null,
    );
  };
  return h('aside', { class: 'reader__side', 'aria-label': 'Rule details' },
    h('section', { class: 'reader__panel', 'aria-labelledby': 'reader-conn' },
      h('h2', { class: 'reader__panel-title', id: 'reader-conn' }, 'Connections'),
      h('h3', { class: 'reader__h3 reader__h3--small' }, `Depends on (${block.dependsOn.length})`),
      chips(ctx, block.dependsOn),
      h('h3', { class: 'reader__h3 reader__h3--small' }, `Used by (${usedBy.length})`),
      chips(ctx, usedBy),
      reach > usedBy.length
        ? h('p', { class: 'reader__reach' }, `${reach} rules depend on it directly or through others. `,
            h('a', { href: href(reqGraph(id, 'impact')) }, 'See the impact'))
        : null,
      h('p', { class: 'reader__panel-links' },
        h('a', { href: href(reqGraph(id)) }, 'Open graph'), ' · ', h('a', { href: href(reqGraph(id, 'impact')) }, 'Open impact')),
    ),
    h('section', { class: 'reader__panel', 'aria-labelledby': 'reader-defects' },
      h('h2', { class: 'reader__panel-title', id: 'reader-defects' }, 'Open defects'),
      open.length === 0
        ? h('p', { class: 'reader__muted' }, 'No open defects for this rule.')
        : h('ul', { class: 'reader__defects' }, open.map((d) => defectEntry(ctx, d))),
      fixed.length === 0
        ? null
        : h('details', { class: 'reader__details' }, h('summary', null, 'History'),
            h('ul', { class: 'reader__defects' }, fixed.map((d) => h('li', { class: 'reader__defect' },
              h('button', { type: 'button', class: 'reader__link-button', 'aria-haspopup': 'dialog', on: { click: () => openDefectDrawer(ctx, d) } }, d.id),
              ' ',
              statusBadge({ glyph: '✓', word: d.status.state === 'fixed' ? `fixed in ${d.status.version}` : 'fixed', tone: 'ok', explain: 'Fixed; kept in the ledger as history' }),
              h('span', { class: 'reader__defect-title' }, d.title),
            )))),
    ),
    h('section', { class: 'reader__panel', 'aria-labelledby': 'reader-tests' },
      h('h2', { class: 'reader__panel-title', id: 'reader-tests' }, 'Tests per language'),
      h('ul', { class: 'reader__tests' },
        h('li', { class: 'reader__test' },
          h('span', { class: 'reader__test-name' }, 'Lean'),
          h('span', { class: `reader__test-state tone--${lean.tone}`, title: lean.explain }, h('span', { 'aria-hidden': 'true' }, lean.glyph), ` ${lean.word}`,
            cited > 0 && lean !== LEAN_META.cited ? h('span', { class: 'reader__muted' }, ` · cited by ${cited}`) : null),
        ),
        RUNTIMES.map(runtimeRow),
      ),
      h('p', { class: 'reader__honest' }, TESTED_MEANS),
      shown.length === 0
        ? null
        : h('p', { class: 'reader__honest' },
            `Also shown in ${shown.length === 1 ? 'one situation' : `${shown.length} situations`}`,
            replayed === 0 ? '.' : replayed === shown.length ? ', replayed by Lean.' : `, ${replayed} replayed by Lean.`),
    ),
  );
}

// ---------------------------------------------------------------------------------------------
// Centre
// ---------------------------------------------------------------------------------------------

/**
 * One body paragraph: fenced code as a code block, a paragraph with list lines through the block
 * renderer (so items become a list), anything else as one paragraph.
 */
export function bodyNode(ctx: AppContext, p: BodyParagraph, terms: readonly string[], seen: Set<string>): HTMLElement {
  if (p.kind === 'code') return h('pre', { class: 'md-pre reader__code' }, h('code', null, p.text));
  const cls = p.kind === 'shall' ? 'reader__shall' : 'reader__prose';
  return p.text.includes('\n')
    ? h('div', { class: [cls, 'reader__para'] }, blocks(ctx, p.text, { terms, seen }))
    : h('p', { class: cls }, inline(ctx, p.text, { terms, seen }));
}

function specBody(ctx: AppContext, block: SpecBlock, seen: Set<string>): Child[] {
  return [
    block.body.map((p) => bodyNode(ctx, p, block.terms, seen)),
    block.notes.map((n) => h('aside', { class: 'reader__note', 'aria-label': n.label },
      h('p', { class: 'reader__note-label' }, n.label),
      blocks(ctx, n.text, { terms: block.terms, seen }),
    )),
  ];
}

function situationsUsing(ctx: AppContext, id: ReqId): HTMLElement {
  const list = ctx.index.situationsByReq.get(id) ?? [];
  return section('situations', 'Situations that use this rule',
    list.length === 0
      ? h('p', { class: 'reader__muted' }, 'No situation shows this rule yet.')
      : h('ul', { class: 'reader__sits' }, list.map((s) => {
          const svg = s.diagram ? thumbnailDiagram(s.slug, 170) : null;
          return h('li', null, h('a', { class: 'reader__sit', href: href(R.situation(s.slug)) },
            h('span', { class: 'reader__sit-canvas' }, svg),
            h('span', { class: 'reader__sit-title' }, s.title),
            h('span', { class: 'reader__sit-group' }, s.group),
          ));
        })),
  );
}

function header(ctx: AppContext, d: Disposer, block: SpecBlock, lean: readonly LeanBlock[]): HTMLElement {
  const id = block.id;
  const usedBy = (ctx.index.usedBy.get(id) ?? []).length;
  const signed = lean.filter((b) => b.signoff.state === 'signed').length;
  const leanMeta = LEAN_META[leanState(ctx, id)];
  const sign: Child = lean.length === 0
    ? null
    : signed === lean.length && lean[0] !== undefined
      ? signoffBadge(lean[0].signoff)
      : signed === 0
        ? signoffBadge({ state: 'pending' })
        : statusBadge({ glyph: '◐', word: `${signed} of ${lean.length} signed`, tone: 'open', explain: 'Some Lean blocks of this rule are signed, some are not' });
  return h('header', { class: 'reader__head' },
    h('div', { class: 'reader__head-main' },
      h('p', { class: 'reader__id' }, id),
      h('h1', { class: 'view__title reader__title', id: 'view-title-req', tabindex: -1 }, block.title),
      h('div', { class: 'reader__meta' },
        block.kind === null ? null : kindBadge(block.kind),
        block.priority === null ? null : h('span', { class: 'reader__priority' }, block.priority),
        block.status.state === 'proposed' ? statusBadge({ glyph: '◌', word: 'Proposed', tone: 'open', explain: 'Some implementation has not built it yet' }) : null,
        h('a', { class: 'reader__file-link', href: fileHref(ctx, block), rel: 'noopener' }, block.file),
        statusBadge(leanMeta),
        sign,
        openDefects(ctx, id).map((x) => defectBadge(ctx, x)),
        h('span', { class: 'reader__conn' },
          h('a', { href: href(reqGraph(id)) }, `Depends on ${block.dependsOn.length}`),
          ' · ',
          h('a', { href: href(reqGraph(id)) }, `Used by ${usedBy}`),
        ),
      ),
    ),
    h('div', { class: 'reader__actions' },
      h('a', { class: 'reader__action', href: href(reqGraph(id)), title: 'Graph (g g)' }, 'Graph'),
      h('a', { class: 'reader__action', href: href(reqGraph(id, 'impact')) }, 'Impact'),
      copyButton(d, 'Copy link', () => location.href, 'Copy link to this rule'),
    ),
  );
}

// ---------------------------------------------------------------------------------------------
// Views
// ---------------------------------------------------------------------------------------------

function renderIndex(ctx: AppContext): ViewResult {
  const c = ctx.data.counts;
  const files = ctx.data.files
    .map((file) => ({ file, live: ctx.index.activeBlocks.filter((b) => b.file === file.file) }))
    .filter((x) => x.live.length > 0);
  const node = viewFrame('req', 'Rules',
    h('p', { class: 'view__lede' },
      `${c.activeIds} active requirements in ${files.length} files. Each one has acceptance criteria; ${c.leanIds} have a Lean block.`),
    files.length === 0
      ? h('p', { class: 'reader__muted' }, 'The page holds no spec files.')
      : h('ul', { class: 'reader__index' }, files.map(({ file, live }) => {
          const first = live[0];
          const leanIds = live.filter((b) => ctx.index.lean(b.id).length > 0).length;
          const untested = live.filter((b) => hasFlag(ctx, b, 'untested')).length;
          const defects = live.filter((b) => openDefects(ctx, b.id).length > 0).length;
          return h('li', null, h('a', { class: 'reader__file-card', href: first === undefined ? href(R.req()) : href(R.req(first.id)) },
            h('h2', { class: 'reader__file-card-title' }, h('span', { class: 'reader__file-num' }, file.number), ` ${file.title}`),
            h('p', { class: 'reader__file-prefix' }, file.prefixes.join(' · ')),
            h('p', { class: 'reader__file-stats' },
              `${live.length} ${live.length === 1 ? 'rule' : 'rules'} · ${leanIds} with a Lean block · ${untested} untested · ${defects} with open defects`),
          ));
        })),
  );
  return { title: 'Rules', node };
}

function renderUnknown(ctx: AppContext, id: string): ViewResult {
  const title = `No requirement ${id}`;
  return {
    title,
    node: viewFrame('req', title,
      h('p', null, 'Removed requirements stay listed as tombstones; this ID was never used.'),
      h('p', null,
        h('button', { type: 'button', class: 'reader__action', on: { click: () => openSearch(ctx, id) } }, 'Search'),
        ' ',
        h('a', { href: href(R.req()) }, 'All rules'),
      ),
    ),
  };
}

function resolveId(ctx: AppContext, raw: string): SpecBlock | undefined {
  const exact = ctx.index.blocks.get(raw);
  if (exact !== undefined) return exact;
  const up = raw.toUpperCase();
  const direct = ctx.index.blocks.get(up);
  if (direct !== undefined) return direct;
  // `core031` -> CORE-031
  const m = /^([A-Z]+)-?(\d+)$/.exec(up);
  return m === null ? undefined : ctx.index.blocks.get(`${m[1] ?? ''}-${m[2] ?? ''}`);
}

export function renderReader(ctx: AppContext, route: RouteOf<'req'>): ViewResult {
  if (route.id === null) return renderIndex(ctx);
  const block = resolveId(ctx, route.id);
  if (block === undefined) return renderUnknown(ctx, route.id);

  const d = new Disposer();
  const state: NavState = { filters: parseFilters(route.query) };
  const nav = buildNav(ctx, block.id, state, () => ctx.navigate(R.req(block.id, filtersToQuery(state.filters)), { silent: true }));
  const removed = block.status.state === 'removed';
  const lean = ctx.index.lean(block.id);
  const seen = new Set<string>();

  let main: HTMLElement;
  if (removed) {
    main = h('div', { class: 'reader__centre' },
      h('header', { class: 'reader__head' },
        h('div', { class: 'reader__head-main' },
          h('p', { class: 'reader__id' }, block.id),
          h('h1', { class: 'view__title reader__title reader__title--removed', id: 'view-title-req', tabindex: -1 }, block.title),
          h('div', { class: 'reader__meta' }, statusBadge({ glyph: '–', word: 'Removed', tone: 'none', explain: 'Kept as a tombstone for traceability' })),
        ),
      ),
      h('div', { class: 'reader__tombstone' },
        h('p', null, 'This requirement was removed and is kept for traceability.'),
        specBody(ctx, block, seen),
        block.mentions.length > 0 ? h('p', null, 'See also: ', block.mentions.map((id, i) => [i > 0 ? ', ' : null, idLink(ctx, id)])) : null,
      ),
    );
  } else {
    main = h('div', { class: 'reader__centre' },
      header(ctx, d, block, lean),
      h('div', { class: 'reader__cols' },
        h('section', { class: 'reader__spec', 'aria-labelledby': 'reader-spec' },
          h('h2', { class: 'reader__col-title', id: 'reader-spec' }, 'Spec text'),
          specBody(ctx, block, seen),
        ),
        h('section', { class: 'reader__lean', 'aria-labelledby': 'reader-lean' },
          h('h2', { class: 'reader__col-title', id: 'reader-lean' }, 'What Lean checks'),
          lean.length === 0 ? noLeanCard(ctx, block.id) : leanBlocks(ctx, d, lean),
        ),
      ),
      section('acceptance', 'Acceptance criteria',
        block.acceptance.length === 0
          ? h('p', { class: 'reader__muted' }, 'This block lists no acceptance criteria.')
          : h('ol', { class: 'reader__acceptance' }, block.acceptance.map((a) => h('li', null,
              a.includes('\n') ? blocks(ctx, a, { terms: block.terms, seen }) : inline(ctx, a, { terms: block.terms, seen })))),
      ),
      block.testDerivation === null ? null : section('derivation', 'Test derivation', h('p', null, inline(ctx, block.testDerivation, { ears: false }))),
      situationsUsing(ctx, block.id),
    );
  }

  const node = h('section', { class: ['view', 'view--req', 'reader', removed && 'reader--removed'], 'aria-labelledby': 'view-title-req' },
    nav.node,
    main,
    removed ? null : sideColumn(ctx, block),
  );

  // j / k: next / previous rule in the filtered list, keeping the filters.
  const order = ctx.index.activeBlocks.map((b) => b.id);
  const go = (step: 1 | -1): void => {
    const next = neighbour(order, visibleIds(ctx, state.filters), block.id, step);
    if (next !== null) ctx.navigate(R.req(next, filtersToQuery(state.filters)));
  };
  d.add(viewKeys({ j: () => go(1), k: () => go(-1) }));

  // Bring the current row into the nav's own scroll area once the view is in the document.
  const raf = typeof requestAnimationFrame === 'function'
    ? requestAnimationFrame(() => {
        const row = nav.current();
        const scroller = nav.node.querySelector<HTMLElement>('.reader__nav-body');
        if (row === null || scroller === null || !row.isConnected) return;
        const top = row.getBoundingClientRect().top - scroller.getBoundingClientRect().top + scroller.scrollTop;
        scroller.scrollTop = Math.max(0, top - scroller.clientHeight / 3);
      })
    : 0;
  d.add(() => {
    if (typeof cancelAnimationFrame === 'function') cancelAnimationFrame(raf);
  });

  return {
    title: `${block.id} ${block.title}`,
    node,
    dispose: () => d.dispose(),
  };
}

/** Plain text of a block's first `shall` sentence (previews). */
export function firstShall(block: SpecBlock): string {
  const p = block.body.find((x) => x.kind === 'shall') ?? block.body[0];
  return p === undefined ? '' : plainText(p.text);
}
