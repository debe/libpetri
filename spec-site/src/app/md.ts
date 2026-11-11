/**
 * The Markdown subset of the spec, rendered to DOM nodes (never to an HTML string):
 * `code`, *emphasis*, **strong**, [ID] requirement links, [text](url) links, EARS keywords
 * (When, While, Where, If, then, shall) highlighted, glossary terms marked with a hover card
 * when asked.
 *
 * Parsing is pure (`parseInline`, `parseBlocks`: text in, a small tree out) so it is unit tested
 * without a DOM; `inline` and `blocks` turn the tree into nodes with `h()`. Text only ever
 * becomes text nodes; a link only gets an `href` that `safeHref` accepts.
 *
 * Owner: reader + md + search agent.
 */
import type { GlossaryTerm } from '../model.js';
import type { AppContext } from './context.js';
import { frag, h, type Child } from './dom.js';
import { openDrawer } from './drawer.js';
import { attachHoverCard, hideHoverCard } from './hovercard.js';
import { href, R } from './router.js';
import { idLink } from './ui.js';

// ---------------------------------------------------------------------------------------------
// Inline tree
// ---------------------------------------------------------------------------------------------

export type InlineNode =
  | { readonly t: 'text'; readonly v: string }
  | { readonly t: 'code'; readonly v: string }
  | { readonly t: 'em'; readonly c: readonly InlineNode[] }
  | { readonly t: 'strong'; readonly c: readonly InlineNode[] }
  | { readonly t: 'link'; readonly href: string; readonly c: readonly InlineNode[] }
  | { readonly t: 'req'; readonly id: string };

const REQ_REF = /^\[([A-Z]+-\d+)\]/;
const MD_LINK = /^\[([^\]\n]+)\]\(([^)\s]+)\)/;

/**
 * The closing `*` of an emphasis run that opens before `from`, skipping code spans and nested
 * `**strong**` runs; the run must not end on a space. -1 when there is none.
 */
function findEmClose(text: string, from: number): number {
  for (let i = from; i < text.length; i++) {
    const ch = text[i];
    if (ch === '`') {
      const end = text.indexOf('`', i + 1);
      if (end < 0) return -1;
      i = end;
    } else if (ch === '\\') {
      i += 1;
    } else if (ch === '*') {
      if (text[i + 1] === '*') {
        const end = text.indexOf('**', i + 2);
        if (end < 0) return -1;
        i = end + 1;
      } else if (text[i - 1] !== ' ') {
        return i;
      }
    }
  }
  return -1;
}

/** Parses one paragraph's inline Markdown. Pure. */
export function parseInline(text: string): readonly InlineNode[] {
  const out: InlineNode[] = [];
  let buf = '';
  const flush = (): void => {
    if (buf !== '') out.push({ t: 'text', v: buf });
    buf = '';
  };
  let i = 0;
  while (i < text.length) {
    const ch = text[i] ?? '';
    const rest = text.slice(i);
    if (ch === '\\' && i + 1 < text.length && /[\\`*_[\]()#|-]/.test(text[i + 1] ?? '')) {
      buf += text[i + 1];
      i += 2;
      continue;
    }
    if (ch === '`') {
      const end = text.indexOf('`', i + 1);
      if (end > i + 1) {
        flush();
        out.push({ t: 'code', v: text.slice(i + 1, end) });
        i = end + 1;
        continue;
      }
    }
    if (rest.startsWith('**')) {
      const end = text.indexOf('**', i + 2);
      if (end > i + 2) {
        flush();
        out.push({ t: 'strong', c: parseInline(text.slice(i + 2, end)) });
        i = end + 2;
        continue;
      }
    }
    if (ch === '*' && text[i + 1] !== ' ' && text[i + 1] !== '*' && text[i + 1] !== undefined) {
      const end = findEmClose(text, i + 1);
      if (end > i + 1) {
        flush();
        out.push({ t: 'em', c: parseInline(text.slice(i + 1, end)) });
        i = end + 1;
        continue;
      }
    }
    if (ch === '[') {
      const req = REQ_REF.exec(rest);
      if (req?.[1] !== undefined) {
        flush();
        out.push({ t: 'req', id: req[1] });
        i += req[0].length;
        continue;
      }
      const link = MD_LINK.exec(rest);
      if (link?.[1] !== undefined && link[2] !== undefined) {
        flush();
        out.push({ t: 'link', href: link[2], c: parseInline(link[1]) });
        i += link[0].length;
        continue;
      }
    }
    buf += ch;
    i += 1;
  }
  flush();
  return out;
}

/** The plain text of inline Markdown (search, previews, titles). Pure. */
export function plainText(text: string): string {
  const walk = (nodes: readonly InlineNode[]): string =>
    nodes
      .map((n) => {
        switch (n.t) {
          case 'text':
          case 'code':
            return n.v;
          case 'req':
            return n.id;
          case 'em':
          case 'strong':
          case 'link':
            return walk(n.c);
        }
      })
      .join('');
  return walk(parseInline(text));
}

/**
 * A link target the page may follow, by allowlist: http(s), a hash (route or anchor), or a
 * relative path (`./`, `../`, or a path that starts with a letter, digit, `_` or `-` and has no
 * scheme). A URL holding any control character or space gives null: browsers strip leading
 * control characters, so `\x01javascript:` would otherwise run as a script. Pure.
 */
export function safeHref(url: string): string | null {
  const u = url.trim();
  if (u === '' || /[\u0000-\u0020\u007f]/.test(u)) return null;
  if (/^https?:\/\//i.test(u)) return u;
  if (u.startsWith('#') || u.startsWith('./') || u.startsWith('../')) return u;
  return /^[A-Za-z0-9_-][^:]*$/.test(u.split(/[?#]/)[0] ?? '') ? u : null;
}

// ---------------------------------------------------------------------------------------------
// Block tree
// ---------------------------------------------------------------------------------------------

export type BlockNode =
  | { readonly t: 'p'; readonly text: string }
  | { readonly t: 'ul'; readonly items: readonly string[] }
  | { readonly t: 'ol'; readonly items: readonly string[]; readonly start: number }
  | { readonly t: 'quote'; readonly text: string }
  | { readonly t: 'pre'; readonly text: string }
  | { readonly t: 'heading'; readonly text: string };

const UL_ITEM = /^\s*[-*+]\s+(.*)$/;
const OL_ITEM = /^\s*(\d+)[.)]\s+(.*)$/;

/**
 * Splits block Markdown into paragraphs, lists, quotes, fenced code and headings. Soft line
 * breaks inside a paragraph or list item join with a space; a table keeps its lines (`pre`).
 * Pure.
 */
export function parseBlocks(text: string): readonly BlockNode[] {
  const lines = text.replace(/\r\n?/g, '\n').split('\n');
  const out: BlockNode[] = [];
  let i = 0;
  while (i < lines.length) {
    const line = lines[i] ?? '';
    if (line.trim() === '') {
      i += 1;
      continue;
    }
    if (/^\s*```/.test(line)) {
      const body: string[] = [];
      i += 1;
      while (i < lines.length && !/^\s*```/.test(lines[i] ?? '')) body.push(lines[i++] ?? '');
      i += 1;
      out.push({ t: 'pre', text: body.join('\n') });
      continue;
    }
    if (/^#{1,6}\s/.test(line)) {
      out.push({ t: 'heading', text: line.replace(/^#{1,6}\s+/, '') });
      i += 1;
      continue;
    }
    if (/^\s*\|/.test(line)) {
      const body: string[] = [];
      while (i < lines.length && /^\s*\|/.test(lines[i] ?? '')) body.push((lines[i++] ?? '').trim());
      out.push({ t: 'pre', text: body.join('\n') });
      continue;
    }
    if (/^\s*>/.test(line)) {
      const body: string[] = [];
      while (i < lines.length && /^\s*>/.test(lines[i] ?? '')) body.push((lines[i++] ?? '').replace(/^\s*>\s?/, ''));
      out.push({ t: 'quote', text: body.join(' ').trim() });
      continue;
    }
    const ul = UL_ITEM.test(line);
    const ol = OL_ITEM.exec(line);
    if (ul || ol) {
      const items: string[] = [];
      const pattern = ul ? UL_ITEM : OL_ITEM;
      while (i < lines.length) {
        const l = lines[i] ?? '';
        if (l.trim() === '') break;
        const m = pattern.exec(l);
        if (m) items.push((ul ? m[1] : m[2]) ?? '');
        else if (/^\s+\S/.test(l) && items.length > 0) items[items.length - 1] += ` ${l.trim()}`;
        else break;
        i += 1;
      }
      out.push(ul ? { t: 'ul', items } : { t: 'ol', items, start: Number(ol?.[1] ?? '1') });
      continue;
    }
    const body: string[] = [];
    while (i < lines.length) {
      const l = lines[i] ?? '';
      if (l.trim() === '' || /^\s*```/.test(l) || (body.length > 0 && (UL_ITEM.test(l) || OL_ITEM.test(l) || /^\s*>/.test(l)))) break;
      body.push(l.trim());
      i += 1;
    }
    out.push({ t: 'p', text: body.join(' ') });
  }
  return out;
}

// ---------------------------------------------------------------------------------------------
// EARS
// ---------------------------------------------------------------------------------------------

const EARS_TRIGGERS = new Set(['when', 'while', 'if', 'then', 'where']);
const EARS_MODALS = new Set(['shall', 'shall not', 'never', 'must', 'must not']);

/** The EARS role of an emphasised phrase, or null. Pure. */
export function earsRole(phrase: string): 'trigger' | 'modal' | null {
  const p = phrase.trim().toLowerCase();
  if (EARS_TRIGGERS.has(p)) return 'trigger';
  if (EARS_MODALS.has(p)) return 'modal';
  return null;
}

/** Bare `shall` / `shall not` in running text. */
const BARE_SHALL = /\bshall(?: not)?\b/g;

// ---------------------------------------------------------------------------------------------
// Glossary terms
// ---------------------------------------------------------------------------------------------

export interface MdOptions {
  /**
   * Mark glossary terms with a hover card. `true` considers every term; a list of slugs
   * (a block's `terms`) only those. Default false.
   */
  readonly terms?: boolean | readonly string[];
  /** Highlight EARS keywords. Default true. */
  readonly ears?: boolean;
  /**
   * Slugs already marked. Pass one set to every call for one requirement so only the first
   * occurrence of a term is marked (design 3.6); it is filled as terms are marked.
   */
  readonly seen?: Set<string>;
  /**
   * Attach the rule preview card to `[ID]` links. Default true; content that is itself in a
   * hover card passes false, so one card never opens another.
   */
  readonly previews?: boolean;
}

function escapeRegExp(text: string): string {
  return text.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

/** The forms a term is matched in: the name without backticks or a trailing `()`. Pure. */
export function termPattern(names: readonly string[]): RegExp | null {
  const forms = names
    .map((n) => n.replace(/`/g, '').replace(/\(\)$/, '').trim())
    .filter((n) => n.length >= 3)
    .sort((a, b) => b.length - a.length || (a < b ? -1 : 1))
    .map(escapeRegExp);
  if (forms.length === 0) return null;
  return new RegExp(`(?<![\\p{L}\\p{N}_-])(?:${forms.join('|')})(?:e?s)?(?![\\p{L}\\p{N}_])`, 'giu');
}

interface TermMatcher {
  readonly pattern: RegExp;
  /** Lower-cased matchable form -> slug. */
  readonly bySlugForm: ReadonlyMap<string, string>;
}

const matcherCache = new WeakMap<object, Map<string, TermMatcher | null>>();

function termMatcher(ctx: AppContext, slugs: readonly string[] | null): TermMatcher | null {
  let cache = matcherCache.get(ctx.data);
  if (cache === undefined) {
    cache = new Map();
    matcherCache.set(ctx.data, cache);
  }
  const key = slugs === null ? '*' : [...slugs].sort().join(',');
  const hit = cache.get(key);
  if (hit !== undefined) return hit;
  const terms: GlossaryTerm[] = [];
  if (slugs === null) terms.push(...ctx.data.glossary);
  else for (const s of slugs) {
    const t = ctx.index.terms.get(s);
    if (t !== undefined) terms.push(t);
  }
  const bySlugForm = new Map<string, string>();
  for (const t of terms) bySlugForm.set(t.term.replace(/`/g, '').replace(/\(\)$/, '').trim().toLowerCase(), t.slug);
  const pattern = termPattern(terms.map((t) => t.term));
  const matcher = pattern === null ? null : { pattern, bySlugForm };
  cache.set(key, matcher);
  return matcher;
}

/** The slug a matched word belongs to (`places` -> `place`). */
function slugOfMatch(matcher: TermMatcher, word: string): string | undefined {
  const w = word.toLowerCase();
  return matcher.bySlugForm.get(w) ?? matcher.bySlugForm.get(w.replace(/es$/, '')) ?? matcher.bySlugForm.get(w.replace(/s$/, ''));
}

/** The hover card / drawer body of a glossary term. */
export function termCard(ctx: AppContext, term: GlossaryTerm, full: boolean): HTMLElement {
  return h('div', { class: ['term-card', full && 'term-card--full'] },
    full ? null : h('p', { class: 'term-card__title' }, term.term),
    h('p', { class: 'term-card__group' }, term.group.replace(/^Glossary:\s*/i, '')),
    h('div', { class: 'term-card__text' }, blocks(ctx, term.text, { ears: false, previews: full })),
    term.refs.length > 0
      ? h('p', { class: 'term-card__refs' }, term.refs.map((id) => [h('a', { class: 'req-id', href: href(R.req(id)) }, id), ' ']))
      : null,
    h('p', { class: 'term-card__foot' }, h('a', { href: href(R.graph({ kind: 'term', slug: term.slug })) }, 'Open in graph')),
  );
}

/** Opens a glossary term in the drawer (a pinned hover card). */
export function openTermDrawer(ctx: AppContext, slug: string): void {
  const term = ctx.index.terms.get(slug);
  if (term === undefined) return;
  openDrawer({ title: term.term, content: termCard(ctx, term, true) });
}

function termButton(ctx: AppContext, term: GlossaryTerm, text: string): HTMLElement {
  // Click or Enter pins the card: it becomes the term drawer (design 3.6).
  const button = h('button', {
    type: 'button',
    class: 'term',
    'data-term': term.slug,
    on: {
      click: () => {
        hideHoverCard();
        openTermDrawer(ctx, term.slug);
      },
    },
  }, text);
  attachHoverCard(button, () => termCard(ctx, term, false), { focusDelayMs: 0 });
  return button;
}

// ---------------------------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------------------------

interface RenderState {
  readonly ctx: AppContext;
  readonly ears: boolean;
  readonly matcher: TermMatcher | null;
  readonly seen: Set<string>;
  readonly previews: boolean;
}

function modal(text: string): HTMLElement {
  return h('strong', { class: 'ears-modal' }, text);
}

/** Plain text with bare `shall` highlighted and the first occurrence of each term marked. */
function renderText(st: RenderState, text: string): Child[] {
  const out: Child[] = [];
  const shallParts = st.ears ? splitBy(text, BARE_SHALL) : [{ match: false, text }];
  for (const part of shallParts) {
    if (part.match) {
      out.push(modal(part.text));
      continue;
    }
    if (st.matcher === null) {
      out.push(part.text);
      continue;
    }
    let last = 0;
    const re = new RegExp(st.matcher.pattern.source, st.matcher.pattern.flags);
    for (let m = re.exec(part.text); m !== null; m = re.exec(part.text)) {
      const slug = slugOfMatch(st.matcher, m[0]);
      const term = slug === undefined ? undefined : st.ctx.index.terms.get(slug);
      if (slug === undefined || term === undefined || st.seen.has(slug)) continue;
      st.seen.add(slug);
      const end = m.index + m[0].length;
      // Punctuation right after a term stays on its line: a button is an atomic inline, and
      // the browser may otherwise break between it and a following full stop.
      const tail = /^[.,;:!?)\]’”'"]+/.exec(part.text.slice(end))?.[0] ?? '';
      const button = termButton(st.ctx, term, m[0]);
      out.push(part.text.slice(last, m.index), tail === '' ? button : h('span', { class: 'term-wrap' }, button, tail));
      last = end + tail.length;
    }
    out.push(part.text.slice(last));
  }
  return out;
}

/** Splits text into matching and non-matching runs of a global pattern. Pure. */
export function splitBy(text: string, pattern: RegExp): readonly { readonly match: boolean; readonly text: string }[] {
  const re = new RegExp(pattern.source, pattern.flags.includes('g') ? pattern.flags : `${pattern.flags}g`);
  const out: { match: boolean; text: string }[] = [];
  let last = 0;
  for (let m = re.exec(text); m !== null; m = re.exec(text)) {
    if (m[0] === '') {
      re.lastIndex += 1;
      continue;
    }
    if (m.index > last) out.push({ match: false, text: text.slice(last, m.index) });
    out.push({ match: true, text: m[0] });
    last = m.index + m[0].length;
  }
  if (last < text.length) out.push({ match: false, text: text.slice(last) });
  return out;
}

function renderNodes(st: RenderState, nodes: readonly InlineNode[]): Child[] {
  return nodes.map((n): Child => {
    switch (n.t) {
      case 'text':
        return renderText(st, n.v);
      case 'code':
        return h('code', null, n.v);
      case 'req':
        return st.previews ? idLink(st.ctx, n.id) : h('a', { class: 'req-id', href: href(R.req(n.id)) }, n.id);
      case 'strong':
        return h('strong', null, renderNodes(st, n.c));
      case 'em': {
        const role = st.ears && n.c.length === 1 && n.c[0]?.t === 'text' ? earsRole(n.c[0].v) : null;
        const text = n.c[0]?.t === 'text' ? n.c[0].v : '';
        if (role === 'trigger') return h('span', { class: 'ears-trigger' }, text);
        if (role === 'modal') return modal(text);
        return h('em', null, renderNodes(st, n.c));
      }
      case 'link': {
        const url = safeHref(n.href);
        const label = renderNodes({ ...st, matcher: null }, n.c);
        if (url === null) return h('span', null, label);
        const external = /^https?:/i.test(url);
        return h('a', { href: url, ...(external ? { rel: 'noopener' } : {}) }, label);
      }
    }
  });
}

function state(ctx: AppContext, options: MdOptions): RenderState {
  const t = options.terms ?? false;
  return {
    ctx,
    ears: options.ears ?? true,
    matcher: t === false ? null : termMatcher(ctx, t === true ? null : t),
    seen: options.seen ?? new Set<string>(),
    previews: options.previews ?? true,
  };
}

/** One paragraph's inline Markdown. */
export function inline(ctx: AppContext, text: string, options: MdOptions = {}): DocumentFragment {
  return frag(renderNodes(state(ctx, options), parseInline(text)));
}

/** Block Markdown: paragraphs, lists, quotes, fenced code and tables (as preformatted text). */
export function blocks(ctx: AppContext, text: string, options: MdOptions = {}): DocumentFragment {
  const st = state(ctx, options);
  const line = (t: string): Child[] => renderNodes(st, parseInline(t));
  return frag(
    parseBlocks(text).map((b): Child => {
      switch (b.t) {
        case 'p':
          return h('p', null, line(b.text));
        case 'heading':
          return h('p', { class: 'md-heading' }, h('strong', null, line(b.text)));
        case 'quote':
          return h('blockquote', null, h('p', null, line(b.text)));
        case 'pre':
          return h('pre', { class: 'md-pre' }, b.text);
        case 'ul':
          return h('ul', null, b.items.map((item) => h('li', null, line(item))));
        case 'ol':
          return h('ol', b.start === 1 ? null : { attrs: { start: b.start } }, b.items.map((item) => h('li', null, line(item))));
      }
    }),
  );
}
