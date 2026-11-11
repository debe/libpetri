/**
 * Search overlay (design 8.1; keys `/`, Ctrl K, Cmd K): rules, terms, situations, theorems and
 * defects, grouped, ranked, keyboard driven. Never changes the route; opening a result does.
 *
 * Ranking (higher first): exact ID > ID prefix > title phrase > title words > term name >
 * theorem name > body text. Case, hyphens and spaces do not matter for IDs (`core031` finds
 * CORE-031); `nu` finds `ν`.
 *
 * Owner: reader + md + search agent.
 */
import type { SiteData } from '../model.js';
import type { AppContext } from './context.js';
import { h, listen, replaceChildren, type Child } from './dom.js';
import { plainText } from './md.js';
import { type OverlayHandle, openOverlay } from './overlay.js';
import { formatRoute, parseHash, R, reqGraph, type Route } from './router.js';
import { LEAN_META, leanState, openDefects } from './status.js';

export type SearchHitKind = 'req' | 'term' | 'situation' | 'theorem' | 'defect';

export interface SearchHit {
  readonly kind: SearchHitKind;
  /** ID, slug or theorem name. */
  readonly key: string;
  readonly title: string;
  /** Plain-text context around the match. */
  readonly snippet: string;
  readonly route: Route;
  /** Higher is better; ties keep data order. */
  readonly score: number;
}

/** Display order of result groups, with their headings. */
export const GROUPS: readonly { readonly kind: SearchHitKind; readonly label: string; readonly noun: string }[] = [
  { kind: 'req', label: 'Rules', noun: 'rules' },
  { kind: 'term', label: 'Terms', noun: 'terms' },
  { kind: 'situation', label: 'Situations', noun: 'situations' },
  { kind: 'theorem', label: 'Theorems', noun: 'theorems' },
  { kind: 'defect', label: 'Defects', noun: 'defects' },
];

/** Results per group before "Show all". */
export const GROUP_LIMIT = 8;

const KIND_GLYPH: { readonly [K in SearchHitKind]: string } = {
  req: '§',
  term: 'Aa',
  situation: '▶',
  theorem: '⊢',
  defect: '⚠',
};

// ---------------------------------------------------------------------------------------------
// Normalisation and scoring (pure)
// ---------------------------------------------------------------------------------------------

/** Lower case, `ν` read as `nu`. */
export function norm(text: string): string {
  return text.toLowerCase().replace(/ν/g, 'nu');
}

/** Letters and digits only: `CORE-031` and `core 031` both give `core031`. */
export function compact(text: string): string {
  return norm(text).replace(/[^a-z0-9]/g, '');
}

/** Query words (lower case, `ν` as `nu`). */
export function words(query: string): readonly string[] {
  return norm(query).split(/[\s,]+/).filter((w) => w !== '');
}

interface Entry {
  readonly kind: SearchHitKind;
  readonly key: string;
  readonly title: string;
  /** Requirement and defect IDs, matched exactly or by prefix. */
  readonly ids: readonly string[];
  /** Name fields (term names, theorem names). */
  readonly names: readonly string[];
  /** Sentences of body text. */
  readonly sentences: readonly string[];
  readonly route: Route;
  /** Added to the score: tombstones rank below live rules. */
  readonly bias: number;
  /** Shown when the match is not in the body. */
  readonly lead: string;
}

/** Splits text into sentences for snippets. Pure. */
export function sentences(text: string): readonly string[] {
  return text
    .split(/(?<=[.!?:;])\s+(?=[A-Z*`[(ν])|\n+/)
    .map((s) => s.replace(/^\s*(?:[-*+]|\d+[.)])\s+/, '').replace(/\s*\|\s*/g, ' · ').replace(/^ · | · $/g, '').trim())
    .filter((s) => s !== '' && /[\p{L}\p{N}]/u.test(s));
}

const SHORT_PREFIX = 'Libpetri.Spec.';

/** A theorem name without the common `Libpetri.Spec.` prefix. */
export function shortTheorem(name: string): string {
  return name.startsWith(SHORT_PREFIX) ? name.slice(SHORT_PREFIX.length) : name;
}

function buildEntries(data: SiteData): readonly Entry[] {
  const out: Entry[] = [];
  for (const b of data.blocks) {
    const body = [...b.body.map((p) => p.text), ...b.acceptance, ...b.notes.map((n) => n.text)].map(plainText).join('\n');
    const firstShall = b.body.find((p) => p.kind === 'shall') ?? b.body[0];
    out.push({
      kind: 'req',
      key: b.id,
      title: b.title,
      ids: [b.id],
      names: [],
      sentences: sentences(body),
      route: R.req(b.id),
      bias: b.status.state === 'removed' ? -60 : 0,
      lead: firstShall ? plainText(firstShall.text) : '',
    });
  }
  for (const t of data.glossary) {
    const text = plainText(t.text);
    out.push({
      kind: 'term',
      key: t.slug,
      title: t.term.replace(/`/g, ''),
      ids: [],
      names: [t.term.replace(/`/g, '')],
      sentences: sentences(text),
      route: R.graph({ kind: 'term', slug: t.slug }),
      bias: 0,
      lead: text,
    });
  }
  for (const s of data.situations) {
    const text = plainText(s.text);
    out.push({
      kind: 'situation',
      key: s.slug,
      title: s.title,
      ids: [],
      names: [s.slug],
      sentences: sentences(text),
      route: R.situation(s.slug),
      bias: 0,
      lead: text,
    });
  }
  const theorems = new Map<string, { roles: Set<string>; ids: Set<string>; doc: string }>();
  const addTheorem = (name: string, role: string, id: string, doc: string | null): void => {
    let t = theorems.get(name);
    if (t === undefined) {
      t = { roles: new Set(), ids: new Set(), doc: '' };
      theorems.set(name, t);
    }
    t.roles.add(role);
    t.ids.add(id);
    if (t.doc === '' && doc !== null) t.doc = doc;
  };
  for (const id of Object.keys(data.lean).sort()) {
    for (const block of data.lean[id] ?? []) for (const e of block.evidence) addTheorem(e.theorem, e.role, block.id, e.doc);
  }
  for (const c of data.citations) addTheorem(c.theorem, 'cites', c.id, c.fragment);
  for (const [name, t] of [...theorems].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))) {
    const short = shortTheorem(name);
    out.push({
      kind: 'theorem',
      key: name,
      title: short,
      ids: [],
      names: [name, short],
      sentences: sentences(plainText(t.doc)),
      route: R.graph({ kind: 'theorem', name }),
      bias: 0,
      lead: `${[...t.roles].sort().join(', ')} · ${[...t.ids].sort().join(', ')}`,
    });
  }
  for (const d of data.defects) {
    const text = plainText(d.text);
    out.push({
      kind: 'defect',
      key: d.id,
      title: d.title,
      ids: [d.id],
      names: [],
      sentences: sentences(text),
      route: R.graph({ kind: 'defect', id: d.id }),
      bias: d.status.state === 'open' ? 0 : -20,
      lead: text,
    });
  }
  return out;
}

const entryCache = new WeakMap<SiteData, readonly Entry[]>();

function entriesOf(data: SiteData): readonly Entry[] {
  let e = entryCache.get(data);
  if (e === undefined) {
    e = buildEntries(data);
    entryCache.set(data, e);
  }
  return e;
}

const hasAll = (text: string, ws: readonly string[]): boolean => {
  const n = norm(text);
  return ws.every((w) => n.includes(w));
};

function clip(text: string, max = 160): string {
  return text.length <= max ? text : `${text.slice(0, max - 1).trimEnd()}…`;
}

/** A snippet of `sentence` around the first query word, at most ~160 characters. Pure. */
export function snippetAround(sentence: string, ws: readonly string[], max = 160): string {
  if (sentence.length <= max) return sentence;
  const n = norm(sentence);
  const at = Math.min(...ws.map((w) => n.indexOf(w)).filter((i) => i >= 0), sentence.length);
  const start = Math.max(0, Math.min(at - 50, sentence.length - max));
  const body = sentence.slice(start, start + max).trim();
  return `${start > 0 ? '…' : ''}${body}${start + max < sentence.length ? '…' : ''}`;
}

function scoreEntry(e: Entry, q: string, ws: readonly string[]): { score: number; snippet: string } | null {
  const cq = compact(q);
  const nq = norm(q).trim();
  let score = 0;
  for (const id of e.ids) {
    const c = compact(id);
    if (c === cq) score = Math.max(score, 1000);
    else if (cq.length >= 2 && c.startsWith(cq)) score = Math.max(score, 900 - Math.min(99, c.length - cq.length));
  }
  const title = norm(e.title);
  if (score === 0) {
    if (title === nq) score = 760;
    else if (title.startsWith(nq)) score = 720;
    else if (title.includes(nq)) score = 700;
    else if (hasAll(e.title, ws)) score = 600;
  }
  if (score === 0) {
    for (const name of e.names) {
      const n = norm(name);
      if (n === nq) score = Math.max(score, 560);
      else if (n.includes(nq) || compact(name).includes(cq)) score = Math.max(score, e.kind === 'theorem' ? 450 : 500);
      else if (hasAll(name, ws)) score = Math.max(score, 420);
    }
  }
  const hit = e.sentences.find((s) => norm(s).includes(nq)) ?? e.sentences.find((s) => hasAll(s, ws));
  if (score === 0 && hit !== undefined) score = norm(hit).includes(nq) ? 300 : 200;
  if (score === 0) return null;
  const snippet = hit !== undefined ? snippetAround(hit, ws) : clip(e.lead);
  return { score: score + e.bias, snippet };
}

const KIND_RANK: { readonly [K in SearchHitKind]: number } = { req: 0, term: 1, situation: 2, theorem: 3, defect: 4 };

/** Ranked hits for a query (pure; the self-test and unit tests call it). */
export function searchSite(ctx: AppContext, query: string, limit = 50): readonly SearchHit[] {
  const ws = words(query);
  if (ws.length === 0 || compact(query) === '') return [];
  const hits: (SearchHit & { readonly order: number })[] = [];
  entriesOf(ctx.data).forEach((e, order) => {
    const s = scoreEntry(e, query, ws);
    if (s !== null) hits.push({ kind: e.kind, key: e.key, title: e.title, snippet: s.snippet, route: e.route, score: s.score, order });
  });
  hits.sort((a, b) => b.score - a.score || KIND_RANK[a.kind] - KIND_RANK[b.kind] || a.order - b.order);
  return hits.slice(0, limit).map(({ order: _order, ...hit }) => hit);
}

/** The graph route of a hit, for Ctrl Enter. */
export function graphRouteOf(hit: SearchHit): Route {
  switch (hit.kind) {
    case 'req':
      return reqGraph(hit.key);
    case 'situation':
      return R.graph({ kind: 'situation', slug: hit.key });
    default:
      return hit.route;
  }
}

/**
 * Text split into runs, with the runs that match a query word marked. Pure.
 * Longer words win where two overlap.
 */
export function highlightRuns(text: string, ws: readonly string[]): readonly { readonly mark: boolean; readonly text: string }[] {
  const n = norm(text);
  // `norm` keeps lengths except for ν -> nu; fall back to no marks if lengths differ.
  if (n.length !== text.length || ws.length === 0) return [{ mark: false, text }];
  const marked = new Array<boolean>(text.length).fill(false);
  for (const w of [...ws].sort((a, b) => b.length - a.length)) {
    for (let i = n.indexOf(w); i >= 0; i = n.indexOf(w, i + w.length)) marked.fill(true, i, i + w.length);
  }
  const out: { mark: boolean; text: string }[] = [];
  for (let i = 0; i < text.length; i++) {
    const m = marked[i] ?? false;
    const last = out[out.length - 1];
    if (last !== undefined && last.mark === m) last.text += text[i];
    else out.push({ mark: m, text: text[i] ?? '' });
  }
  return out;
}

// ---------------------------------------------------------------------------------------------
// Recent results (per viewer; storage may be missing)
// ---------------------------------------------------------------------------------------------

const RECENT_KEY = 'libpetri-spec.search.recent';
const RECENT_MAX = 5;

interface Recent {
  readonly kind: SearchHitKind;
  readonly key: string;
  readonly title: string;
  readonly hash: string;
}

const KINDS: readonly string[] = GROUPS.map((g) => g.kind);

function isRecent(v: unknown): v is Recent {
  if (typeof v !== 'object' || v === null) return false;
  const r = v as Record<string, unknown>; // narrowing a parsed JSON object
  return typeof r['kind'] === 'string' && KINDS.includes(r['kind']) && typeof r['key'] === 'string' && typeof r['title'] === 'string' && typeof r['hash'] === 'string';
}

function readRecent(): readonly Recent[] {
  try {
    const raw: unknown = JSON.parse(localStorage.getItem(RECENT_KEY) ?? '[]');
    return Array.isArray(raw) ? raw.filter(isRecent).slice(0, RECENT_MAX) : [];
  } catch {
    return [];
  }
}

function rememberRecent(hit: SearchHit): void {
  try {
    const entry: Recent = { kind: hit.kind, key: hit.key, title: hit.title, hash: formatRoute(hit.route) };
    const next = [entry, ...readRecent().filter((r) => r.hash !== entry.hash)].slice(0, RECENT_MAX);
    localStorage.setItem(RECENT_KEY, JSON.stringify(next));
  } catch {
    // No storage (private window, file:// in some browsers): recent results are a convenience.
  }
}

// ---------------------------------------------------------------------------------------------
// Panel
// ---------------------------------------------------------------------------------------------

const TRY: readonly string[] = ['CORE-031', 'inhibitor', 'timeout', 'ν join'];
const LIST_ID = 'search-list';

function marked(text: string, ws: readonly string[]): Child[] {
  return highlightRuns(text, ws).map((r) => (r.mark ? h('mark', null, r.text) : r.text));
}

function statusGlyphs(ctx: AppContext, hit: SearchHit): Child {
  if (hit.kind !== 'req') return null;
  const lean = LEAN_META[leanState(ctx, hit.key)];
  const defects = openDefects(ctx, hit.key).length;
  return h('span', { class: 'search__status' },
    h('span', { class: `search__lean search__lean--${lean.tone}`, title: lean.explain }, lean.glyph, h('span', { class: 'sr-only' }, ` ${lean.word}`)),
    defects > 0 ? h('span', { class: 'search__defect', title: `${defects} open ${defects === 1 ? 'defect' : 'defects'}` }, '⚠', h('span', { class: 'sr-only' }, ` ${defects} open`)) : null,
  );
}

/** One selectable row: a result, a "Show all" row, a recent entry. */
interface Row {
  readonly el: HTMLElement;
  readonly open: (inGraph: boolean) => void;
}

/**
 * The overlay's content for a query, detached (the self-test renders it). With `onClose`, a
 * Cancel button closes the overlay (the only way out on a touch screen).
 */
export function renderSearchPanel(ctx: AppContext, query: string, onClose?: () => void): HTMLElement {
  const input = h('input', {
    class: 'search__input',
    type: 'text',
    value: query,
    placeholder: 'Search rules, terms, theorems, situations, defects',
    autocomplete: 'off',
    spellcheck: false,
    role: 'combobox',
    'aria-label': 'Search',
    'aria-expanded': 'false',
    'aria-controls': LIST_ID,
    'aria-autocomplete': 'list',
  });
  const status = h('p', { class: 'sr-only', role: 'status' });
  // Focusable so keyboard users can scroll a long list (the options themselves are reached through the input).
  const body = h('div', { class: 'search__body', tabindex: 0 });
  const root = h('div', { class: 'search__inner' },
    h('div', { class: 'search__field' },
      h('span', { class: 'search__icon', 'aria-hidden': 'true' }, '⌕'),
      input,
      onClose === undefined ? null : h('button', { type: 'button', class: 'search__close', on: { click: onClose } }, 'Cancel'),
    ),
    status,
    body,
    h('p', { class: 'search__hint', 'aria-hidden': 'true' },
      h('kbd', null, '↑'), h('kbd', null, '↓'), ' move · ', h('kbd', null, 'Enter'), ' open · ', h('kbd', null, 'Ctrl'), h('kbd', null, 'Enter'), ' graph · ', h('kbd', null, 'Esc'), ' close'),
  );

  let rows: Row[] = [];
  let activeIndex = -1;
  const expanded = new Set<SearchHitKind>();

  const setActive = (i: number): void => {
    rows.forEach((r, j) => r.el.setAttribute('aria-selected', String(j === i)));
    activeIndex = i;
    const row = rows[i];
    if (row === undefined) {
      input.removeAttribute('aria-activedescendant');
      return;
    }
    input.setAttribute('aria-activedescendant', row.el.id);
    if (typeof row.el.scrollIntoView === 'function') row.el.scrollIntoView({ block: 'nearest' });
  };

  const optionRow = (id: number, content: Child, open: (inGraph: boolean) => void, cls: string): HTMLElement => {
    const el = h('div', { id: `search-opt-${id}`, class: ['search__option', cls], role: 'option', 'aria-selected': 'false' }, content);
    const index = rows.length;
    rows.push({ el, open });
    el.addEventListener('mousemove', () => {
      if (activeIndex !== index) setActive(index);
    });
    el.addEventListener('click', (e) => open(e.ctrlKey || e.metaKey));
    return el;
  };

  const openHit = (hit: SearchHit, inGraph: boolean): void => {
    rememberRecent(hit);
    ctx.navigate(inGraph ? graphRouteOf(hit) : hit.route);
  };

  const render = (): void => {
    const q = input.value;
    const ws = words(q);
    rows = [];
    activeIndex = -1;
    input.removeAttribute('aria-activedescendant');
    if (ws.length === 0) {
      const recent = readRecent();
      const list = h('div', { id: LIST_ID, role: 'listbox', class: 'search__list', 'aria-label': 'Recent', hidden: recent.length === 0 },
        recent.length > 0
          ? h('div', { role: 'group', 'aria-labelledby': 'search-g-recent', class: 'search__group' },
              h('div', { id: 'search-g-recent', class: 'search__group-title', role: 'presentation' }, 'Recent'),
              recent.map((r, i) => optionRow(i, [
                h('span', { class: 'search__glyph', 'aria-hidden': 'true' }, KIND_GLYPH[r.kind]),
                h('span', { class: ['search__key', (r.kind === 'req' || r.kind === 'theorem') && 'search__key--mono'] }, r.kind === 'req' || r.kind === 'defect' ? r.key : r.title),
                r.kind === 'req' || r.kind === 'defect' ? h('span', { class: 'search__title' }, r.title) : null,
              ], () => ctx.navigate(parseHash(r.hash)), 'search__option--recent')),
            )
          : null,
      );
      replaceChildren(body,
        list,
        h('p', { class: 'search__try' }, 'Try: ',
          TRY.map((t, i) => [i > 0 ? ' · ' : null, h('button', { type: 'button', class: 'search__try-btn', on: { click: () => { input.value = t; render(); input.focus(); } } }, t)]),
        ),
      );
      input.setAttribute('aria-expanded', String(recent.length > 0));
      status.textContent = '';
      return;
    }

    const hits = searchSite(ctx, q, Number.POSITIVE_INFINITY);
    if (hits.length === 0) {
      replaceChildren(body, h('div', { id: LIST_ID, role: 'listbox', class: 'search__list', 'aria-label': 'Results', hidden: true }),
        h('p', { class: 'search__empty' }, `No matches for "${q.trim()}". Try an ID like CORE-031, a term like inhibitor arc, or a theorem name.`));
      input.setAttribute('aria-expanded', 'false');
      status.textContent = 'No results';
      return;
    }
    let n = 0;
    const groups = GROUPS.map((g) => {
      const all = hits.filter((hit) => hit.kind === g.kind);
      if (all.length === 0) return null;
      const shown = expanded.has(g.kind) ? all : all.slice(0, GROUP_LIMIT);
      const headId = `search-g-${g.kind}`;
      return h('div', { role: 'group', 'aria-labelledby': headId, class: 'search__group' },
        h('div', { id: headId, class: 'search__group-title', role: 'presentation' }, g.label, h('span', { class: 'search__count' }, ` ${all.length}`)),
        shown.map((hit) => optionRow(n++, [
          h('span', { class: 'search__glyph', 'aria-hidden': 'true' }, KIND_GLYPH[hit.kind]),
          h('span', { class: 'search__main' },
            h('span', { class: 'search__line' },
              hit.kind === 'req' || hit.kind === 'defect'
                ? [h('span', { class: 'search__key search__key--mono' }, marked(hit.key, ws)), ' ', h('span', { class: 'search__title' }, marked(hit.title, ws))]
                : h('span', { class: ['search__key', hit.kind === 'theorem' && 'search__key--mono'] }, marked(hit.title, ws)),
            ),
            hit.snippet !== '' ? h('span', { class: 'search__snippet' }, marked(hit.snippet, ws)) : null,
          ),
          statusGlyphs(ctx, hit),
        ], (inGraph) => openHit(hit, inGraph), `search__option--${hit.kind}`)),
        shown.length < all.length
          ? optionRow(n++, `Show all ${all.length} ${g.noun}`, () => {
              expanded.add(g.kind);
              render();
              input.focus();
            }, 'search__option--more')
          : null,
      );
    });
    replaceChildren(body, h('div', { id: LIST_ID, role: 'listbox', class: 'search__list', 'aria-label': 'Results' }, groups));
    input.setAttribute('aria-expanded', 'true');
    status.textContent = `${hits.length} ${hits.length === 1 ? 'result' : 'results'}`;
    setActive(0);
  };

  listen(input, 'input', () => {
    expanded.clear();
    render();
  });
  listen(input, 'keydown', (e) => {
    const count = rows.length;
    switch (e.key) {
      case 'ArrowDown':
        e.preventDefault();
        if (count > 0) setActive((activeIndex + 1) % count);
        break;
      case 'ArrowUp':
        e.preventDefault();
        if (count > 0) setActive((activeIndex - 1 + count) % count);
        break;
      case 'Enter': {
        const row = rows[activeIndex] ?? rows[0];
        if (row !== undefined) {
          e.preventDefault();
          row.open(e.ctrlKey || e.metaKey);
        }
        break;
      }
      case 'Escape':
        // First Esc clears a query; the second reaches the overlay, which closes.
        if (input.value !== '') {
          e.preventDefault();
          e.stopPropagation();
          input.value = '';
          expanded.clear();
          render();
        }
        break;
      default:
        break;
    }
  });
  render();
  return root;
}

export function openSearch(ctx: AppContext, query = ''): OverlayHandle {
  let handle: OverlayHandle | null = null;
  const content = renderSearchPanel(ctx, query, () => handle?.close());
  const input = content.querySelector('input');
  const opened = openOverlay({ label: 'Search', block: 'search', content, ...(input ? { initialFocus: input } : {}) });
  handle = opened;
  input?.select();
  return opened;
}
