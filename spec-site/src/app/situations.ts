/**
 * Situations (design 4): the home grid of example runs (`#/`) and one situation page
 * (`#/situation/<slug>?step=N`). Keys `[` and `]` go to the previous / next situation.
 *
 * The derivations (grouping, rule counts, status strip, neighbours, the key
 * *shall* sentence) are small pure functions exported for `tests/situations.test.ts`; the
 * render functions only arrange their results. The situation page mounts the player
 * (`player.ts` `mountPlayer`: canvas, controls, steps list and the Lean verdict box) and one
 * rule card per entry of `entry.rules`.
 */
import type {
  Defect,
  EvidenceRole,
  LeanBlock,
  NotReplayed,
  ReqId,
  ReqKind,
  Runtime,
  RuleLink,
  SituationEntry,
  SituationGroup,
  SituationRule,
  SpecBlock,
} from '../model.js';
import { RUNTIMES, SITUATION_GROUPS } from '../model.js';
import type { AppContext, ViewResult } from './context.js';
import { thumbnailDiagram } from './data.js';
import { h, listen } from './dom.js';
import { KIND_WORD } from './help.js';
import { viewKeys } from './keyboard.js';
import { blocks as mdBlocks, inline } from './md.js';
import { mountPlayer } from './player.js';
import { href, R, type QueryParams, type RouteOf } from './router.js';
import {
  LEAN_META,
  leanState,
  openDefects,
  provedInLean,
  ROLE_META,
  ROLE_ORDER,
  RUNTIME_LABEL,
  TEST_META,
  testState,
} from './status.js';
import { idLink, statusBadge, viewFrame } from './ui.js';

// ---------------------------------------------------------------------------------------------
// Copy
// ---------------------------------------------------------------------------------------------

/** One line under each home group heading (app copy, not data; contracts 4.3). */
export const GROUP_INTRO: { readonly [G in SituationGroup]: string } = {
  Firing: 'When a transition may fire, and what a firing takes and leaves.',
  Outputs: 'Where a firing puts its tokens: one place, several places, or one branch of a choice.',
  Time: 'Delays, deadlines and windows that decide when a transition fires.',
  Running: 'How an executor runs a net: order, priority, actions and stopping.',
  Correlation: 'Joining tokens that belong together by their identity (ν-nets).',
  Composition: 'One net built from smaller nets that share places.',
  Verification: 'What the verifier proves about a net before it runs.',
  Export: 'How a net becomes a diagram.',
};

/** Why a situation is not replayed, as the card's short word (the player writes the sentence). */
export const NOT_REPLAYED_SHORT: { readonly [N in NotReplayed]: string } = {
  timed: 'timed',
  environment: 'environment',
  'nu-net': 'ν-net',
  composition: 'composition',
  export: 'export',
  verification: 'verification',
};

// ---------------------------------------------------------------------------------------------
// Pure derivations
// ---------------------------------------------------------------------------------------------

export interface SituationGroupView {
  readonly group: SituationGroup;
  readonly intro: string;
  readonly entries: readonly SituationEntry[];
}

/** Situations grouped in the fixed group order; empty groups are left out, entry order kept. */
export function groupSituations(entries: readonly SituationEntry[]): readonly SituationGroupView[] {
  return SITUATION_GROUPS.map((group) => ({ group, intro: GROUP_INTRO[group], entries: entries.filter((e) => e.group === group) }))
    .filter((g) => g.entries.length > 0);
}

/** The situations before and after `slug` in home order (the order of `data.situations`). */
export function neighbours(
  entries: readonly SituationEntry[],
  slug: string,
): { readonly prev: SituationEntry | null; readonly next: SituationEntry | null } {
  const i = entries.findIndex((e) => e.slug === slug);
  if (i < 0) return { prev: null, next: null };
  return { prev: entries[i - 1] ?? null, next: entries[i + 1] ?? null };
}

/** The `?step=` query as a player step: an integer in 0..max, else 0. */
export function parseStep(query: QueryParams, max: number): number {
  const raw = query['step'];
  if (raw === undefined || !/^\d+$/.test(raw)) return 0;
  return Math.min(max, Number.parseInt(raw, 10));
}

export interface RuleStats {
  readonly rules: number;
  /** Rules with a Lean block that has a holds theorem (design 12: "proved in Lean"). */
  readonly proved: number;
  /** Open defects of any linked rule, unique, sorted by ID. */
  readonly defects: readonly Defect[];
}

export function ruleStats(ctx: AppContext, entry: SituationEntry): RuleStats {
  const defects = new Map<string, Defect>();
  for (const r of entry.rules) for (const d of openDefects(ctx, r.id)) defects.set(d.id, d);
  return {
    rules: entry.rules.length,
    proved: entry.rules.filter((r) => provedInLean(ctx, r.id)).length,
    defects: [...defects.values()].sort((a, b) => (a.id < b.id ? -1 : a.id > b.id ? 1 : 0)),
  };
}

/** "6 rules · 4 proved in Lean". */
export function ruleCountText(stats: RuleStats): string {
  return `${plural(stats.rules, 'rule')} · ${stats.proved} proved in Lean`;
}

export type StripKey = 'lean' | Runtime;

/** One segment of a card's status strip (design 4.1). */
export interface StripColumn {
  readonly key: StripKey;
  readonly label: string;
  /** Short header, shown in an `abbr` with `label` as its title. */
  readonly short: string;
  /** Lean: rules with a Lean block. Runtimes: rules a test file cites, without an open defect here. */
  readonly ok: number;
  /** Rules with an open defect in this runtime (always 0 for Lean). */
  readonly defect: number;
  readonly total: number;
}

const STRIP_SHORT: { readonly [K in StripKey]: string } = { lean: 'Lean', java: 'J', typescript: 'TS', rust: 'Rs', python: 'Py' };

export function statusStrip(ctx: AppContext, ids: readonly ReqId[]): readonly StripColumn[] {
  const lean: StripColumn = {
    key: 'lean',
    label: 'Lean',
    short: STRIP_SHORT.lean,
    ok: ids.filter((id) => leanState(ctx, id) === 'block').length,
    defect: 0,
    total: ids.length,
  };
  const runtimes = RUNTIMES.map((rt): StripColumn => {
    const states = ids.map((id) => testState(ctx, id, rt).state);
    return {
      key: rt,
      label: RUNTIME_LABEL[rt],
      short: STRIP_SHORT[rt],
      ok: states.filter((s) => s === 'tested').length,
      defect: states.filter((s) => s === 'defect').length,
      total: ids.length,
    };
  });
  return [lean, ...runtimes];
}

/** Text equivalent of the strip: "Lean block for 4 of 6. Java tested 5 of 6, 1 open defect. …" */
export function stripSentence(columns: readonly StripColumn[]): string {
  return columns.map((c) => {
    const head = c.key === 'lean' ? `Lean block for ${c.ok} of ${c.total}` : `${c.label} tested ${c.ok} of ${c.total}`;
    return c.defect > 0 ? `${head}, ${plural(c.defect, 'open defect')}.` : `${head}.`;
  }).join(' ');
}

/** Percent widths of the strip's ok and defect parts. */
export function stripShares(c: StripColumn): { readonly ok: number; readonly defect: number } {
  if (c.total === 0) return { ok: 0, defect: 0 };
  return { ok: (100 * c.ok) / c.total, defect: (100 * c.defect) / c.total };
}

/** The first sentence of the first *shall* paragraph, or null when the block has none. */
export function keyShallSentence(block: SpecBlock): string | null {
  const para = block.body.find((p) => p.kind === 'shall');
  if (para === undefined) return null;
  const sentences = para.text.split(/(?<=[.!?])\s+(?=[A-Z[`*_(])/);
  return sentences.find((s) => /\bshall\b/i.test(s))?.trim() ?? para.text.trim();
}

export interface RoleCount {
  readonly role: EvidenceRole;
  readonly count: number;
}

/** Evidence of all Lean blocks of a rule, counted per role, in the reader's role order. */
export function evidenceCounts(blocks: readonly LeanBlock[]): readonly RoleCount[] {
  const counts = new Map<EvidenceRole, number>();
  for (const b of blocks) for (const e of b.evidence) counts.set(e.role, (counts.get(e.role) ?? 0) + 1);
  return ROLE_ORDER.flatMap((role) => {
    const count = counts.get(role) ?? 0;
    return count > 0 ? [{ role, count }] : [];
  });
}

/** "Why here" phrases of a rule card (design 4.6). */
export function whyHere(links: readonly RuleLink[]): readonly string[] {
  return links.map((l) => {
    switch (l.kind) {
      case 'cited':
        return 'cited by this situation';
      case 'step':
        return `cited by step ${l.index + 1}`;
      case 'exercised':
        return 'the net uses a feature it governs';
    }
  });
}

export type RuleFilter = 'all' | 'cited' | 'exercised';

/** Cited: listed by the situation or named by a blocked step. Exercised: the net uses its feature. */
export function filterRules(rules: readonly SituationRule[], filter: RuleFilter): readonly SituationRule[] {
  switch (filter) {
    case 'all':
      return rules;
    case 'cited':
      return rules.filter((r) => r.links.some((l) => l.kind !== 'exercised'));
    case 'exercised':
      return rules.filter((r) => r.links.some((l) => l.kind === 'exercised'));
  }
}

/** Filter chips earn their place only when some filter keeps part of the list, not none or all. */
export function showFilters(rules: readonly SituationRule[]): boolean {
  return (['cited', 'exercised'] as const).some((f) => {
    const n = filterRules(rules, f).length;
    return n > 0 && n < rules.length;
  });
}

/** The newest signoff date among a rule's Lean blocks, or null when none is signed. */
export function signedDate(blocks: readonly LeanBlock[]): string | null {
  const dates = blocks.flatMap((b) => (b.signoff.state === 'signed' ? [b.signoff.date] : [])).sort();
  return dates[dates.length - 1] ?? null;
}

function plural(n: number, word: string): string {
  return `${n} ${word}${n === 1 ? '' : 's'}`;
}

// ---------------------------------------------------------------------------------------------
// Components
// ---------------------------------------------------------------------------------------------

/** Design 3.2 kind badge: a letter in a square, the word as tooltip and for screen readers. */
function kindBadge(kind: ReqKind): HTMLElement {
  return h('span', { class: 'kind-badge', title: KIND_WORD[kind] },
    h('span', { 'aria-hidden': 'true' }, kind),
    h('span', { class: 'sr-only' }, KIND_WORD[kind]),
  );
}

/** The exported diagram on its paper canvas, decorative, or a quiet placeholder without one. */
function miniDiagram(entry: SituationEntry): HTMLElement {
  // About 300px wide on a card; labels stay near 9px, a tall net shows its top part.
  const svg = entry.diagram ? thumbnailDiagram(entry.slug, 300) : null;
  if (svg !== null) return h('div', { class: 'sit-card__figure' }, svg);
  const net = entry.net;
  return h('div', { class: ['sit-card__figure', 'sit-card__figure--empty'], 'aria-hidden': 'true' },
    `${plural(net.places.length, 'place')} · ${plural(net.transitions.length, 'transition')}`,
  );
}

function strip(columns: readonly StripColumn[], sentenceId: string): HTMLElement {
  return h('div', { class: 'sit-strip' },
    h('div', { class: 'sit-strip__cols', 'aria-hidden': 'true' }, columns.map((c) => {
      const share = stripShares(c);
      return h('span', { class: 'sit-strip__col', title: `${c.label}: ${c.ok} of ${c.total}${c.defect > 0 ? `, ${plural(c.defect, 'open defect')}` : ''}` },
        h('span', { class: 'sit-strip__label' }, c.short),
        h('span', {
          class: 'sit-strip__bar',
          style: { '--strip-ok': `${share.ok.toFixed(2)}%`, '--strip-defect': `${(share.ok + share.defect).toFixed(2)}%` },
        }),
      );
    })),
    h('span', { class: 'sr-only', id: sentenceId }, stripSentence(columns)),
  );
}

function replayLine(entry: SituationEntry): HTMLElement {
  if (entry.result === null) {
    const short = entry.notReplayed === null ? 'not untimed' : NOT_REPLAYED_SHORT[entry.notReplayed];
    return h('p', { class: ['sit-card__replay', 'sit-card__replay--none'] }, `Not replayed (${short})`);
  }
  return h('p', { class: 'sit-card__replay' },
    h('span', { class: 'sit-card__replay-glyph', 'aria-hidden': 'true' }, '▶ '),
    `Replayed by Lean · ${plural(entry.steps.length, 'step')}`,
  );
}

/** A card for the home grid: mini diagram, title, rule count, status strip, replay line. */
export function situationCard(ctx: AppContext, entry: SituationEntry): HTMLElement {
  const stats = ruleStats(ctx, entry);
  const columns = statusStrip(ctx, entry.rules.map((r) => r.id));
  const defects = stats.defects.length;
  // The title is the link (its name is the title alone); CSS stretches its hit area over the
  // whole card, and the rule count and status strip describe it.
  const key = `sit-card-${entry.slug}`;
  return h('article', { class: 'sit-card', 'data-slug': entry.slug },
    h('div', { class: 'sit-card__media' },
      miniDiagram(entry),
      defects > 0 ? h('span', { class: ['badge', 'badge--defect', 'sit-card__defects'] },
        h('span', { 'aria-hidden': 'true' }, '⚠'), ` ${plural(defects, 'open defect')}`) : null,
    ),
    h('div', { class: 'sit-card__body' },
      h('div', { class: 'sit-card__head' },
        h('h3', { class: 'sit-card__title' },
          h('a', { class: 'sit-card__link', href: href(R.situation(entry.slug)), 'aria-describedby': `${key}-meta ${key}-strip` }, entry.title)),
        h('span', { class: 'sit-card__group' }, entry.group),
      ),
      h('p', { class: 'sit-card__summary' }, inline(ctx, entry.text, { terms: false, ears: false, previews: false })),
      h('p', { class: 'sit-card__count', id: `${key}-meta` }, ruleCountText(stats)),
      strip(columns, `${key}-strip`),
      replayLine(entry),
    ),
  );
}

function statLink(value: string, label: string, target: string, title: string, onClick: ((e: MouseEvent) => void) | null = null): HTMLElement {
  return h('li', { class: 'sit-stat' },
    h('a', { class: 'sit-stat__box', href: target, title, ...(onClick === null ? {} : { on: { click: onClick } }) },
      h('span', { class: 'sit-stat__value' }, value), h('span', { class: 'sit-stat__label' }, label)),
  );
}

// ---------------------------------------------------------------------------------------------
// Home `#/`
// ---------------------------------------------------------------------------------------------

export function renderSituations(ctx: AppContext, route: RouteOf<'situations'>): ViewResult {
  void route;
  const c = ctx.data.counts;
  const entries = ctx.data.situations;
  const groups = groupSituations(entries);
  const first = entries[0];

  // Four stats, every one a link (design 4.1); blocks and signoffs ride on the Lean stat.
  const stats = h('ul', { class: 'sit-stats', 'aria-label': 'Spec at a glance' },
    statLink(String(c.activeIds), 'rules', href(R.req()), 'Active requirements in the spec'),
    statLink(`${c.leanIds} of ${c.activeIds}`, `with a Lean block · ${c.leanBlocks} blocks, ${c.signedBlocks} signed`, href(R.req(null, { lean: 'block' })),
      'Requirement IDs with at least one Lean block; blocks count companion blocks; signed blocks have a reviewer signoff'),
    statLink(String(c.openDefects), 'open defects', href(R.conf({ f: 'defects' })), 'Open entries of the runtime defect ledger; one entry can name several rules'),
    // The page uses the hash for routes, so this link scrolls to the first group by hand.
    statLink(String(c.situations), `situations · ${c.replayed} replayed`, href(R.situations()),
      `Example runs; ${c.replayed} replayed by the Lean reference`, (e) => {
        const heading = first === undefined ? null : document.getElementById(`sit-group-${first.group.toLowerCase()}`);
        if (heading === null) return;
        e.preventDefault();
        heading.setAttribute('tabindex', '-1');
        heading.scrollIntoView({ block: 'start' });
        heading.focus({ preventScroll: true });
      }),
  );

  const body = groups.length === 0
    ? h('p', { class: 'view__note' }, 'No situations yet.')
    : h('div', { class: 'situations__groups' }, groups.map((g) => {
      const headingId = `sit-group-${g.group.toLowerCase()}`;
      return h('section', { class: 'situations__group', 'aria-labelledby': headingId },
        h('div', { class: 'situations__group-head' },
          h('h2', { class: 'situations__group-title', id: headingId }, g.group),
          h('span', { class: 'situations__group-count' }, plural(g.entries.length, 'situation')),
        ),
        h('p', { class: 'situations__group-intro' }, g.intro),
        h('ul', { class: 'situations__grid' }, g.entries.map((e) => h('li', { class: 'situations__cell' }, situationCard(ctx, e)))),
      );
    }));

  const node = viewFrame('situations', 'See the rules run',
    h('p', { class: ['view__lede', 'situations__lede'] },
      'Each situation is a small net and a run of it. The Lean reference replays every untimed run; the rules on each page say why a step fires or is blocked.'),
    stats,
    first === undefined ? null : h('p', { class: 'situations__start' },
      'New here? Start with ', h('a', { href: href(R.situation(first.slug)) }, first.title), '.'),
    body,
  );
  return { title: 'libpetri spec', node };
}

// ---------------------------------------------------------------------------------------------
// Situation page `#/situation/<slug>`
// ---------------------------------------------------------------------------------------------

function leanSummary(ctx: AppContext, id: ReqId, blocks: readonly LeanBlock[]): HTMLElement {
  if (blocks.length === 0) {
    const state = leanState(ctx, id);
    const cites = (ctx.index.citationsByReq.get(id) ?? []).length;
    const rest = state === 'cited' ? `Cited by ${plural(cites, 'theorem')}.`
      : state === 'mention' ? 'Mentioned in Lean comments only.'
        : 'Lean does not mention this rule.';
    return h('p', { class: 'rule-card__evidence' }, h('span', { class: 'rule-card__label' }, 'Evidence: '), `No Lean block yet. ${rest}`);
  }
  const counts = evidenceCounts(blocks);
  return h('p', { class: 'rule-card__evidence' },
    h('span', { class: 'rule-card__label' }, 'Evidence: '),
    counts.length === 0 ? 'none recorded' : counts.map((c, i) => {
      const meta = ROLE_META[c.role];
      return [
        i > 0 ? h('span', { class: 'rule-card__sep', 'aria-hidden': 'true' }, ' · ') : null,
        h('span', { class: ['rule-card__role', `tone--${meta.tone}`], title: meta.explain },
          h('span', { class: 'rule-card__glyph', 'aria-hidden': 'true' }, meta.glyph),
          ` ${meta.word}${c.count > 1 ? ` ${c.count}` : ''}`,
          i < counts.length - 1 ? h('span', { class: 'sr-only' }, ',') : null,
        ),
      ];
    }),
  );
}

function testsLine(ctx: AppContext, id: ReqId): HTMLElement {
  const defects = openDefects(ctx, id);
  return h('div', { class: 'rule-card__tests' },
    h('span', { class: 'rule-card__label' }, 'Tests: '),
    h('ul', { class: 'rule-card__runtimes' }, RUNTIMES.map((rt) => {
      const state = testState(ctx, id, rt);
      const meta = TEST_META[state.state];
      const note = rt === 'python' ? ' Python binds the Rust runtime.' : '';
      return h('li', { class: 'rule-card__runtime', title: `${RUNTIME_LABEL[rt]}: ${meta.explain}.${note}` },
        `${RUNTIME_LABEL[rt]} `,
        h('span', { class: ['rule-card__glyph', `tone--${meta.tone}`], 'aria-hidden': 'true' }, meta.glyph),
        h('span', { class: 'sr-only' }, ` ${meta.word}`),
      );
    })),
    defects.length === 0 ? null : h('span', { class: 'rule-card__defects' }, defects.map((d) =>
      h('a', { class: ['badge', 'badge--defect'], href: href(R.graph({ kind: 'defect', id: d.id })), title: d.title },
        h('span', { 'aria-hidden': 'true' }, '⚠'), ` ${d.id}`))),
  );
}

/** Design 4.6: one linked requirement on a situation page. */
export function ruleCard(ctx: AppContext, rule: SituationRule): HTMLElement {
  const block = ctx.index.blocks.get(rule.id);
  const why = h('p', { class: 'rule-card__why' }, h('span', { class: 'rule-card__label' }, 'Why here: '), whyHere(rule.links).join(' · '));
  const whyWithLink = h('p', { class: ['rule-card__why', 'rule-card__why--link'] },
    h('span', null, h('span', { class: 'rule-card__label' }, 'Why here: '), whyHere(rule.links).join(' · ')),
    h('a', { href: href(R.req(rule.id)), class: 'rule-card__open-link' },
      'Open rule', h('span', { class: 'sr-only' }, ` ${rule.id}`), h('span', { 'aria-hidden': 'true' }, ' ›')));
  if (block === undefined) {
    return h('li', { class: ['rule-card', 'rule-card--unknown'] },
      h('div', { class: 'rule-card__head' }, idLink(ctx, rule.id), h('h3', { class: 'rule-card__title' }, 'Unknown requirement')),
      h('p', null, `No requirement ${rule.id}. Removed requirements stay listed as tombstones; this ID was never used.`),
      why,
    );
  }
  if (block.status.state === 'removed') {
    return h('li', { class: ['rule-card', 'rule-card--removed'] },
      h('div', { class: 'rule-card__head' }, idLink(ctx, rule.id), h('h3', { class: 'rule-card__title' }, block.title)),
      h('p', null, 'Removed. Kept as a tombstone.'),
      why,
    );
  }
  const lean = ctx.index.lean(rule.id);
  const state = leanState(ctx, rule.id);
  const signed = signedDate(lean);
  const shall = keyShallSentence(block);
  return h('li', { class: 'rule-card', 'data-rule': rule.id },
    h('div', { class: 'rule-card__head' },
      idLink(ctx, rule.id),
      h('h3', { class: 'rule-card__title' }, block.title),
      h('span', { class: 'rule-card__meta' },
        block.kind === null ? null : kindBadge(block.kind),
        block.priority === null ? null : h('span', { class: 'rule-card__priority' }, block.priority),
        statusBadge(LEAN_META[state]),
        lean.length === 0 ? null
          : signed === null ? h('span', { class: ['badge', 'badge--open'], title: "No reviewer has signed this block's statement yet." },
            h('span', { 'aria-hidden': 'true' }, '○'), ' Not signed')
            : h('span', { class: ['badge', 'badge--ok'], title: 'A reviewer signed this exact statement. The build fails if the statement changes.' },
              h('span', { 'aria-hidden': 'true' }, '●'), ` Signed ${signed}`),
      ),
    ),
    shall === null ? null : h('p', { class: 'rule-card__shall' }, inline(ctx, shall, { terms: false, ears: true })),
    leanSummary(ctx, rule.id, lean),
    testsLine(ctx, rule.id),
    whyWithLink,
  );
}

const FILTERS: readonly { readonly filter: RuleFilter; readonly label: string }[] = [
  { filter: 'all', label: 'All' },
  { filter: 'cited', label: 'Cited' },
  { filter: 'exercised', label: 'Exercised' },
];

function rulesSection(ctx: AppContext, entry: SituationEntry): HTMLElement {
  let current: RuleFilter = 'all';
  const list = h('ul', { class: 'rule-cards' });
  const empty = h('p', { class: 'view__note', hidden: true }, 'No rules match this filter.');
  const chips = FILTERS.map((f) => h('button', {
    type: 'button',
    class: 'filter-chip',
    'aria-pressed': String(f.filter === current),
    'data-filter': f.filter,
  }, f.label, ' ', h('span', { class: 'filter-chip__count' }, String(filterRules(entry.rules, f.filter).length))));
  const show = (): void => {
    const rules = filterRules(entry.rules, current);
    list.replaceChildren(...rules.map((r) => ruleCard(ctx, r)));
    empty.hidden = rules.length > 0;
    for (const chip of chips) chip.setAttribute('aria-pressed', String(chip.dataset['filter'] === current));
  };
  for (const chip of chips) {
    listen(chip, 'click', () => {
      const f = FILTERS.find((x) => x.filter === chip.dataset['filter']);
      if (f === undefined || f.filter === current) return;
      current = f.filter;
      show();
    });
  }
  show();
  return h('section', { class: 'sit-rules', 'aria-labelledby': 'sit-rules-title' },
    h('div', { class: 'sit-rules__head' },
      h('h2', { class: 'sit-rules__title', id: 'sit-rules-title' }, `Rules in this situation (${entry.rules.length})`),
      showFilters(entry.rules) ? h('div', { class: 'sit-rules__filters', role: 'group', 'aria-label': 'Show rules' }, chips) : null,
    ),
    entry.rules.length === 0 ? h('p', { class: 'view__note' }, 'No rules are linked to this situation.') : null,
    list,
    empty,
  );
}

function notFound(route: RouteOf<'situation'>): ViewResult {
  const node = viewFrame('situation', 'Nothing here',
    h('p', null, `The address #/situation/${route.slug} does not match a page.`),
    h('p', null, h('a', { href: href(R.situations()) }, 'Situations'), ' · ', h('a', { href: href(R.req()) }, 'Rules')),
  );
  return { title: 'Nothing here', node };
}

export function renderSituation(ctx: AppContext, route: RouteOf<'situation'>): ViewResult {
  const entry = ctx.index.situations.get(route.slug);
  if (entry === undefined) return notFound(route);

  const { prev, next } = neighbours(ctx.data.situations, entry.slug);
  const steps = entry.result?.steps.length ?? 0;
  const player = mountPlayer(ctx, entry, {
    initialStep: parseStep(route.query, steps),
    onStep: (step) => ctx.navigate(R.situation(entry.slug, step === 0 ? null : step), { silent: true }),
  });

  const pager = h('nav', { class: 'sit-page__pager', 'aria-label': 'Other situations' },
    prev === null
      ? h('span', { class: ['sit-page__pager-link', 'sit-page__pager-link--off'], 'aria-hidden': 'true' }, '◀ Previous')
      : h('a', { class: 'sit-page__pager-link', href: href(R.situation(prev.slug)), title: `Previous: ${prev.title} ([)`, rel: 'prev' },
        h('span', { 'aria-hidden': 'true' }, '◀'), 'Previous', h('span', { class: 'sr-only' }, `: ${prev.title}`)),
    next === null
      ? h('span', { class: ['sit-page__pager-link', 'sit-page__pager-link--off'], 'aria-hidden': 'true' }, 'Next ▶')
      : h('a', { class: 'sit-page__pager-link', href: href(R.situation(next.slug)), title: `Next: ${next.title} (])`, rel: 'next' },
        'Next', h('span', { class: 'sr-only' }, `: ${next.title}`), h('span', { 'aria-hidden': 'true' }, '▶')),
  );

  const node = viewFrame('situation', entry.title,
    h('nav', { class: 'sit-page__crumbs', 'aria-label': 'Breadcrumb' },
      h('ol', null,
        h('li', null, h('a', { href: href(R.situations()) }, 'Situations')),
        h('li', null, h('span', { 'aria-current': 'page' }, entry.group)),
      ),
    ),
    pager,
    h('div', { class: ['view__lede', 'sit-page__lede'] }, mdBlocks(ctx, entry.text, { terms: false, ears: false })),
    // The player brings its own canvas, steps list and Lean verdict box (design 4.3, 4.4).
    h('div', { class: 'sit-page__stage' }, player.node),
    rulesSection(ctx, entry),
  );

  const stopKeys = viewKeys({
    '[': () => { if (prev !== null) ctx.navigate(R.situation(prev.slug)); },
    ']': () => { if (next !== null) ctx.navigate(R.situation(next.slug)); },
  });

  return {
    title: entry.title,
    node,
    dispose: () => {
      stopKeys();
      player.dispose();
    },
  };
}
