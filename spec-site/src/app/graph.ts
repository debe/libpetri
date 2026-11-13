/**
 * Graph (design 7): `#/graph` picker, `#/graph/<node>` neighbourhood as columns of chips (for a
 * rule: depends on · the rule · used by · Lean and terms · mentions and situations; only
 * depends-on edges count as dependencies, so the counts match the rule page), and
 * `#/graph/impact/<node>` impact as columns by distance (a BFS over incoming edges, 3 hops),
 * with a copy-as-Markdown button. Key `i` toggles the two modes.
 *
 * An edge `from -> to` always reads "from depends on to" (a rule on the rules it names, a rule
 * on its evidence theorems and terms, a theorem on the rule it cites, a situation on the rules
 * it shows, a defect on the rule it breaks), so the incoming edges of a node are what a change
 * to it reaches.
 *
 * Owner: conf + graph agent.
 */
import { edgeEnds, nodeKey } from '../model.js';
import type { Edge, EdgeKind, EvidenceRole, GraphNode, GraphNodeKey, ReqId, SiteData } from '../model.js';
import { kindBadge, shortTheorem } from './conf.js';
import type { AppContext, ViewResult } from './context.js';
import { type Child, h, replaceChildren } from './dom.js';
import type { SiteIndex } from './indexes.js';
import { viewKeys } from './keyboard.js';
import { blocks as mdBlocks } from './md.js';
import { href, R, type RouteOf } from './router.js';
import { openSearch } from './search.js';
import { defectStatusWord, LEAN_META, leanState, openDefects, ROLE_META, ROLE_ORDER, RUNTIME_LABEL, TEST_META } from './status.js';
import { statusBadge, viewFrame } from './ui.js';

// ---------------------------------------------------------------------------------------------
// Requirement-only impact (kept for callers that want rule IDs only)
// ---------------------------------------------------------------------------------------------

/**
 * Requirements that depend on `id`, directly or not, by distance: layer 0 is `[id]`, layer k
 * the blocks first reached after k depends-on edges walked backwards. Sorted per layer.
 */
export function impactLayers(index: SiteIndex, id: ReqId): readonly (readonly ReqId[])[] {
  const layers: ReqId[][] = [[id]];
  const seen = new Set<ReqId>([id]);
  for (;;) {
    const last = layers[layers.length - 1] ?? [];
    const next: ReqId[] = [];
    for (const r of last) {
      for (const user of index.usedBy.get(r) ?? []) {
        if (!seen.has(user)) {
          seen.add(user);
          next.push(user);
        }
      }
    }
    if (next.length === 0) return layers;
    layers.push(next.sort());
  }
}

// ---------------------------------------------------------------------------------------------
// Nodes: labels, existence, order
// ---------------------------------------------------------------------------------------------

/** Edge kinds in the order groups appear. */
export const EDGE_ORDER: readonly EdgeKind[] = ['depends-on', 'mentions', 'evidence', 'cites', 'uses-term', 'exercises', 'breaks'];

/** Group heading for edges leaving the node ("this node ... them"). */
export const OUT_LABEL: { readonly [K in EdgeKind]: string } = {
  'depends-on': 'Depends on',
  mentions: 'Mentions',
  evidence: 'Evidence',
  cites: 'Cites',
  'uses-term': 'Uses terms',
  exercises: 'Shows rules',
  breaks: 'Breaks',
};

/** Group heading for edges arriving at the node ("they ... this node"). */
export const IN_LABEL: { readonly [K in EdgeKind]: string } = {
  'depends-on': 'Used by',
  mentions: 'Mentioned by',
  evidence: 'Evidence for',
  cites: 'Cited by',
  'uses-term': 'Used by rules',
  exercises: 'Shown in situations',
  breaks: 'Defects',
};

/** How a node one hop away reaches the start, for the impact chips ("depends on it"). */
export const VIA_LABEL: { readonly [K in EdgeKind]: string } = {
  'depends-on': 'depends on it',
  mentions: 'mentions it',
  evidence: 'uses it as evidence',
  cites: 'cites it',
  'uses-term': 'uses this term',
  exercises: 'shows it',
  breaks: 'breaks it',
};

const KIND_WORD: { readonly [K in GraphNode['kind']]: string } = {
  req: 'Rule',
  theorem: 'Theorem',
  term: 'Glossary term',
  situation: 'Situation',
  defect: 'Defect',
};

const KIND_RANK: { readonly [K in GraphNode['kind']]: number } = { req: 0, theorem: 1, term: 2, situation: 3, defect: 4 };

export interface NodeInfo {
  readonly node: GraphNode;
  readonly key: GraphNodeKey;
  /** Short label: the ID, term, short theorem name or situation title. */
  readonly label: string;
  /** A longer line: the rule or defect title, the full theorem name, the term group. */
  readonly title: string;
  /** False when the data has no such node (the view then shows the not-found card). */
  readonly exists: boolean;
}

export function nodeInfo(ctx: AppContext, node: GraphNode): NodeInfo {
  const key = nodeKey(node);
  switch (node.kind) {
    case 'req': {
      const block = ctx.index.blocks.get(node.id);
      return { node, key, label: node.id, title: block?.title ?? '', exists: block !== undefined };
    }
    case 'defect': {
      const d = ctx.index.defects.get(node.id);
      return { node, key, label: node.id, title: d?.title ?? '', exists: d !== undefined };
    }
    case 'term': {
      const t = ctx.index.terms.get(node.slug);
      return { node, key, label: t?.term ?? node.slug, title: t?.group ?? '', exists: t !== undefined };
    }
    case 'theorem':
      return {
        node,
        key,
        label: shortTheorem(node.name),
        title: node.name,
        exists: ctx.index.edgesFrom.has(key) || ctx.index.edgesTo.has(key),
      };
    case 'situation': {
      const s = ctx.index.situations.get(node.slug);
      return { node, key, label: s?.title ?? node.slug, title: s?.group ?? '', exists: s !== undefined };
    }
  }
}

const orderCache = new WeakMap<SiteData, ReadonlyMap<ReqId, number>>();

function specOrder(data: SiteData): ReadonlyMap<ReqId, number> {
  let map = orderCache.get(data);
  if (map === undefined) {
    map = new Map(data.blocks.map((b, i) => [b.id, i] as const));
    orderCache.set(data, map);
  }
  return map;
}

const byString = (a: string, b: string): number => (a < b ? -1 : a > b ? 1 : 0);

/** Display order of nodes: rules in spec order, then theorems, terms, situations, defects by key. */
export function nodeComparator(data: SiteData): (a: GraphNode, b: GraphNode) => number {
  const order = specOrder(data);
  return (a, b) => {
    const k = KIND_RANK[a.kind] - KIND_RANK[b.kind];
    if (k !== 0) return k;
    if (a.kind === 'req' && b.kind === 'req') {
      const ra = order.get(a.id) ?? Number.MAX_SAFE_INTEGER;
      const rb = order.get(b.id) ?? Number.MAX_SAFE_INTEGER;
      if (ra !== rb) return ra - rb;
    }
    return byString(nodeKey(a), nodeKey(b));
  };
}

// ---------------------------------------------------------------------------------------------
// Neighbourhood
// ---------------------------------------------------------------------------------------------

export interface Neighbour {
  readonly node: GraphNode;
  readonly key: GraphNodeKey;
  /** Every edge of this group between the focus and this node (evidence may carry several roles). */
  readonly edges: readonly Edge[];
}

export interface EdgeGroup {
  readonly kind: EdgeKind;
  readonly dir: 'in' | 'out';
  readonly label: string;
  readonly items: readonly Neighbour[];
}

/** The focus node's edges in one direction, grouped by edge kind (EDGE_ORDER), each group sorted. */
export function neighbourGroups(
  index: SiteIndex,
  key: GraphNodeKey,
  dir: 'in' | 'out',
  compare: (a: GraphNode, b: GraphNode) => number,
): readonly EdgeGroup[] {
  const edges = (dir === 'in' ? index.edgesTo : index.edgesFrom).get(key) ?? [];
  const groups: EdgeGroup[] = [];
  for (const kind of EDGE_ORDER) {
    const byKey = new Map<GraphNodeKey, { node: GraphNode; edges: Edge[] }>();
    for (const e of edges) {
      if (e.kind !== kind) continue;
      const ends = edgeEnds(e);
      const other = dir === 'in' ? ends.from : ends.to;
      const k = nodeKey(other);
      const entry = byKey.get(k);
      if (entry === undefined) byKey.set(k, { node: other, edges: [e] });
      else entry.edges.push(e);
    }
    if (byKey.size === 0) continue;
    const items = [...byKey.entries()]
      .map(([k, v]): Neighbour => ({ node: v.node, key: k, edges: v.edges }))
      .sort((a, b) => compare(a.node, b.node));
    groups.push({ kind, dir, label: (dir === 'in' ? IN_LABEL : OUT_LABEL)[kind], items });
  }
  return groups;
}

// ---------------------------------------------------------------------------------------------
// Impact: BFS over incoming edges
// ---------------------------------------------------------------------------------------------

/** How many hops the impact view shows. */
export const IMPACT_HOPS = 3;

export interface ImpactHit {
  readonly node: GraphNode;
  readonly key: GraphNodeKey;
  /** The node one hop closer to the start through which this one was first reached. */
  readonly via: GraphNode;
  readonly viaKey: GraphNodeKey;
  /** The kind of that edge. */
  readonly edge: EdgeKind;
}

export interface Impact {
  /** `layers[k]` holds the nodes first reached after k + 1 hops, at most `hops` layers. */
  readonly layers: readonly (readonly ImpactHit[])[];
  /** Nodes that depend on the start but are more than `hops` hops away. */
  readonly beyond: number;
  /** How many hops the whole closure spans (layers shown or not). */
  readonly depth: number;
}

export interface ImpactOptions {
  /** Layers to return (default `IMPACT_HOPS`). */
  readonly hops?: number;
  /** Walk `mentions` edges too (default false: a mention is a reference, not a dependency). */
  readonly mentions?: boolean;
  /** Order inside a layer (default by node key). */
  readonly compare?: (a: GraphNode, b: GraphNode) => number;
}

/**
 * Breadth-first search from `start` over incoming edges. Each node appears once, at its
 * shortest distance; `via` is the first node of the previous layer (in layer order) that
 * reaches it, so the result is deterministic.
 */
export function impactOf(index: SiteIndex, start: GraphNode, options: ImpactOptions = {}): Impact {
  const hops = options.hops ?? IMPACT_HOPS;
  const compare = options.compare ?? ((a: GraphNode, b: GraphNode) => byString(nodeKey(a), nodeKey(b)));
  const startKey = nodeKey(start);
  const seen = new Set<GraphNodeKey>([startKey]);
  const layers: ImpactHit[][] = [];
  let frontier: readonly (readonly [GraphNodeKey, GraphNode])[] = [[startKey, start]];
  while (frontier.length > 0) {
    const next: ImpactHit[] = [];
    for (const [key, via] of frontier) {
      for (const e of index.edgesTo.get(key) ?? []) {
        if (e.kind === 'mentions' && options.mentions !== true) continue;
        const from = edgeEnds(e).from;
        const k = nodeKey(from);
        if (seen.has(k)) continue;
        seen.add(k);
        next.push({ node: from, key: k, via, viaKey: key, edge: e.kind });
      }
    }
    if (next.length === 0) break;
    next.sort((a, b) => compare(a.node, b.node));
    layers.push(next);
    frontier = next.map((hit) => [hit.key, hit.node] as const);
  }
  return {
    layers: layers.slice(0, Math.max(0, hops)),
    beyond: layers.slice(Math.max(0, hops)).reduce((n, layer) => n + layer.length, 0),
    depth: layers.length,
  };
}

/** "210 more nodes are 4 to 9 steps away." */
export function beyondText(impact: Impact): string {
  const from = impact.layers.length + 1;
  const range = from === impact.depth ? `${from} steps` : `${from} to ${impact.depth} steps`;
  return `${plural(impact.beyond, 'more node is', 'more nodes are')} ${range} away.`;
}

/** Display groups of one impact layer: rules first, then theorems, terms, situations, defects. */
export function layerGroups(layer: readonly ImpactHit[]): readonly { readonly kind: GraphNode['kind']; readonly hits: readonly ImpactHit[] }[] {
  const kinds: readonly GraphNode['kind'][] = ['req', 'theorem', 'term', 'situation', 'defect'];
  return kinds.map((kind) => ({ kind, hits: layer.filter((hit) => hit.node.kind === kind) })).filter((g) => g.hits.length > 0);
}

const GROUP_TITLE: { readonly [K in GraphNode['kind']]: string } = {
  req: 'Rules',
  theorem: 'Theorems',
  term: 'Terms',
  situation: 'Situations',
  defect: 'Defects',
};

/** "Directly", "2 steps", "3 steps" ... for layer index k (0-based). */
export function hopLabel(k: number): string {
  return k === 0 ? 'Directly' : `${k + 1} steps`;
}

const plural = (n: number, one: string, many: string): string => `${n} ${n === 1 ? one : many}`;

/**
 * "Within 3 steps: 24 rules, 3 theorems, 5 situations, 2 open defects." (or "In all: ..." when
 * every layer is shown). Kinds with no node are left out.
 */
export function impactTotals(ctx: AppContext, impact: Impact): string {
  const hits = impact.layers.flat();
  const count = (kind: GraphNode['kind']): number => hits.filter((hit) => hit.node.kind === kind).length;
  const defects = hits.flatMap((hit) => (hit.node.kind === 'defect' ? [ctx.index.defects.get(hit.node.id)] : []));
  const open = defects.filter((d) => d?.status.state === 'open').length;
  const parts = [
    plural(count('req'), 'rule', 'rules'),
    count('theorem') > 0 ? plural(count('theorem'), 'theorem', 'theorems') : null,
    count('term') > 0 ? plural(count('term'), 'term', 'terms') : null,
    count('situation') > 0 ? plural(count('situation'), 'situation', 'situations') : null,
    open > 0 ? plural(open, 'open defect', 'open defects') : null,
    defects.length - open > 0 ? plural(defects.length - open, 'fixed defect', 'fixed defects') : null,
  ].filter((p): p is string => p !== null);
  const lead = impact.beyond === 0 ? 'In all' : `Within ${impact.layers.length} ${impact.layers.length === 1 ? 'step' : 'steps'}`;
  return `${lead}: ${parts.join(', ')}.`;
}

/** The impact as Markdown, for the copy button (deterministic: same data, same text). */
export function impactMarkdown(ctx: AppContext, start: GraphNode, impact: Impact): string {
  const focus = nodeInfo(ctx, start);
  const line = (hit: ImpactHit): string => {
    const info = nodeInfo(ctx, hit.node);
    const name = hit.node.kind === 'theorem' ? `\`${info.label}\`` : info.label;
    const title = hit.node.kind === 'req' || hit.node.kind === 'defect' ? ` ${info.title}` : '';
    const kind = hit.node.kind === 'req' ? '' : ` (${KIND_WORD[hit.node.kind].toLowerCase()})`;
    const via = hit.viaKey === focus.key ? VIA_LABEL[hit.edge] : `via ${nodeInfo(ctx, hit.via).label}`;
    return `- ${name}${title}${kind}: ${via}`;
  };
  const out = [`## Impact of ${focus.label}${focus.node.kind === 'req' && focus.title !== '' ? ` ${focus.title}` : ''}`, ''];
  if (impact.layers.length === 0) {
    out.push(`Nothing depends on ${focus.label}.`);
    return `${out.join('\n')}\n`;
  }
  out.push(`If ${focus.label} changes, these depend on it, directly or through others.`, '');
  impact.layers.forEach((layer, k) => {
    out.push(`### ${hopLabel(k)} (${layer.length})`, '', ...layer.map(line), '');
  });
  out.push(impactTotals(ctx, impact));
  if (impact.beyond > 0) out.push('', beyondText(impact));
  return `${out.join('\n')}\n`;
}

// ---------------------------------------------------------------------------------------------
// Theorem facts (for the theorem focus card)
// ---------------------------------------------------------------------------------------------

interface TheoremFacts {
  readonly module: string | null;
  readonly doc: string | null;
  readonly roles: readonly EvidenceRole[];
}

const theoremCache = new WeakMap<SiteData, ReadonlyMap<string, TheoremFacts>>();

function theoremFacts(data: SiteData, name: string): TheoremFacts | undefined {
  let map = theoremCache.get(data);
  if (map === undefined) {
    const build = new Map<string, { module: string | null; doc: string | null; roles: Set<EvidenceRole> }>();
    const entry = (theorem: string): { module: string | null; doc: string | null; roles: Set<EvidenceRole> } => {
      let e = build.get(theorem);
      if (e === undefined) {
        e = { module: null, doc: null, roles: new Set() };
        build.set(theorem, e);
      }
      return e;
    };
    for (const blocks of Object.values(data.lean)) {
      for (const b of blocks) {
        for (const ev of b.evidence) {
          const e = entry(ev.theorem);
          e.module ??= ev.module;
          e.doc ??= ev.doc;
          e.roles.add(ev.role);
        }
      }
    }
    for (const c of data.citations) entry(c.theorem).module ??= c.module;
    map = new Map([...build].map(([k, v]) => [k, { module: v.module, doc: v.doc, roles: ROLE_ORDER.filter((r) => v.roles.has(r)) }] as const));
    theoremCache.set(data, map);
  }
  return map.get(name);
}

// ---------------------------------------------------------------------------------------------
// Components
// ---------------------------------------------------------------------------------------------

/** Chips shown before "Show N more". */
export const CHIP_LIMIT = 12;

function roleTag(role: EvidenceRole): HTMLElement {
  const meta = ROLE_META[role];
  return h('span', { class: ['graph__tag', `graph__tag--${meta.tone}`], title: meta.explain },
    h('span', { 'aria-hidden': 'true' }, meta.glyph), ' ', meta.word);
}

/** A long Lean name with line-break opportunities after each `_` and `.`. */
function breakable(name: string): Child[] {
  return name.split(/(?<=[_.])/).flatMap((part, i) => (i === 0 ? [part] : [h('wbr'), part]));
}

function nodeChip(ctx: AppContext, node: GraphNode, meta: Child = null): HTMLElement {
  const info = nodeInfo(ctx, node);
  const removed = node.kind === 'req' && ctx.index.blocks.get(node.id)?.status.state === 'removed';
  const mono = node.kind === 'req' || node.kind === 'defect' || node.kind === 'theorem';
  const second = node.kind === 'req' || node.kind === 'defect' ? info.title : '';
  return h('div', {
    class: ['graph__chip', `graph__chip--${node.kind}`, removed && 'graph__chip--removed', !info.exists && 'graph__chip--missing'],
    attrs: { title: node.kind === 'theorem' ? info.title : null },
  },
    h('a', { class: 'graph__chip-main', href: href(R.graph(node)), 'data-nav': '' },
      h('span', { class: ['graph__chip-key', mono && 'graph__chip-key--mono'] }, node.kind === 'theorem' ? breakable(info.label) : info.label),
      second === '' ? null : h('span', { class: 'graph__chip-title' }, second),
    ),
    meta === null ? null : h('span', { class: 'graph__chip-meta' }, meta),
    node.kind === 'req' && info.exists
      ? h('a', { class: 'graph__chip-rule', href: href(R.req(node.id)), 'aria-label': `Open rule ${node.id}` }, 'rule ›')
      : null,
  );
}

/** A list of chips; past `CHIP_LIMIT` the rest hide behind "Show N more". */
function chipList(items: readonly HTMLElement[]): HTMLElement {
  const lis = items.map((chip, i) => h('li', { hidden: i >= CHIP_LIMIT }, chip));
  const list = h('ul', { class: 'graph__chips' }, lis);
  if (items.length <= CHIP_LIMIT) return list;
  const more = h('button', { type: 'button', class: 'graph__more' }, `Show ${items.length - CHIP_LIMIT} more`);
  more.addEventListener('click', () => {
    for (const li of lis) li.hidden = false;
    more.remove();
    lis[CHIP_LIMIT]?.querySelector<HTMLElement>('a')?.focus();
  });
  return h('div', null, list, more);
}

function neighbourMeta(n: Neighbour): Child {
  const roles = n.edges.flatMap((e) => (e.kind === 'evidence' ? [e.role] : []));
  if (roles.length > 0) return ROLE_ORDER.filter((r) => roles.includes(r)).map(roleTag);
  return null;
}

function defectMeta(ctx: AppContext, node: GraphNode): Child {
  if (node.kind !== 'defect') return null;
  const d = ctx.index.defects.get(node.id);
  if (d === undefined) return null;
  return d.status.state === 'open'
    ? h('span', { class: 'graph__tag graph__tag--defect' }, h('span', { 'aria-hidden': 'true' }, '⚠'), ' open')
    : h('span', { class: 'graph__tag graph__tag--ok' }, defectStatusWord(d.status));
}

/** The neighbourhood columns (design 7). Only depends-on edges count as dependencies. */
export type ColumnKey = 'depends' | 'usedby' | 'lean' | 'other';

export const COLUMN_TITLE: { readonly [K in ColumnKey]: string } = {
  depends: 'Depends on',
  usedby: 'Used by',
  lean: 'Lean and terms',
  other: 'Mentions and situations',
};

/** The column an edge group belongs to: depends-on edges are dependencies, the rest are links. */
export function columnOf(kind: EdgeKind, dir: 'in' | 'out'): ColumnKey {
  switch (kind) {
    case 'depends-on':
      return dir === 'out' ? 'depends' : 'usedby';
    case 'evidence':
    case 'cites':
    case 'uses-term':
      return 'lean';
    case 'mentions':
    case 'exercises':
    case 'breaks':
      return 'other';
  }
}

/**
 * The focus node's edge groups sorted into columns. A requirement gets all four; any other node
 * has no depends-on edges, so it gets one "Connections" column with every group.
 */
export function neighbourColumns(index: SiteIndex, info: NodeInfo, compare: (a: GraphNode, b: GraphNode) => number): readonly { readonly key: ColumnKey | 'all'; readonly title: string; readonly groups: readonly EdgeGroup[] }[] {
  const groups = [...neighbourGroups(index, info.key, 'out', compare), ...neighbourGroups(index, info.key, 'in', compare)];
  if (info.node.kind !== 'req') return [{ key: 'all', title: 'Connections', groups }];
  const keys: readonly ColumnKey[] = ['depends', 'usedby', 'lean', 'other'];
  return keys.map((key) => ({ key, title: COLUMN_TITLE[key], groups: groups.filter((g) => columnOf(g.kind, g.dir) === key) }));
}

function neighbourColumn(ctx: AppContext, info: NodeInfo, column: { readonly key: ColumnKey | 'all'; readonly title: string; readonly groups: readonly EdgeGroup[] }): HTMLElement {
  const total = column.groups.reduce((n, g) => n + g.items.length, 0);
  const id = `graph-col-${column.key}`;
  const empty = column.key === 'usedby' ? `No rule depends on ${info.label}.`
    : column.key === 'depends' ? `${info.label} depends on no other rule.`
      : 'None.';
  // A single group needs no sub-heading: the column title already names it.
  const single = column.groups.length === 1 && (column.key === 'depends' || column.key === 'usedby');
  return h('section', { class: ['graph__col', `graph__col--${column.key}`], 'aria-labelledby': id },
    h('h2', { class: 'graph__col-title', id }, column.title, ' ', h('span', { class: 'graph__count' }, `(${total})`)),
    column.groups.length === 0
      ? h('p', { class: 'graph__empty' }, empty)
      : single
        ? column.groups.map((g) => chipList(g.items.map((n) => nodeChip(ctx, n.node, neighbourMeta(n) ?? defectMeta(ctx, n.node)))))
        : column.groups.map((g) => h('details', { class: 'graph__group', open: true },
            h('summary', { class: 'graph__group-summary' },
              h('h3', { class: 'graph__group-title' }, g.label, ' ', h('span', { class: 'graph__count' }, `(${g.items.length})`))),
            chipList(g.items.map((n) => nodeChip(ctx, n.node, neighbourMeta(n) ?? defectMeta(ctx, n.node)))),
          )),
  );
}

function actions(...children: readonly Child[]): HTMLElement {
  return h('p', { class: 'graph__actions' }, children);
}

function modeLink(info: NodeInfo, mode: 'node' | 'impact'): HTMLElement {
  return mode === 'impact'
    ? h('a', { class: 'graph__button', href: href(R.impact(info.node)), 'aria-keyshortcuts': 'i' }, 'Impact')
    : h('a', { class: 'graph__button', href: href(R.graph(info.node)), 'aria-keyshortcuts': 'i' }, 'Neighbourhood');
}

/** Design 3.8 copy for a node the data does not have. */
function missingCard(ctx: AppContext, info: NodeInfo): HTMLElement {
  const text = info.node.kind === 'req'
    ? `No requirement ${info.label}. Removed requirements stay listed as tombstones; this ID was never used.`
    : `No ${KIND_WORD[info.node.kind].toLowerCase()} ${info.label} in this spec.`;
  const search = h('button', { type: 'button', class: 'graph__button', on: { click: () => openSearch(ctx, info.label) } }, 'Search');
  return h('article', { class: ['graph__focus', 'graph__focus--missing'] },
    h('p', { class: 'graph__kicker' }, KIND_WORD[info.node.kind]),
    h('h2', { class: 'graph__focus-title' }, 'Not found'),
    h('p', null, text),
    actions(search, h('a', { class: 'graph__button', href: href(R.graph()) }, 'Graph start')),
  );
}

function focusCard(ctx: AppContext, info: NodeInfo, mode: 'node' | 'impact'): HTMLElement {
  if (!info.exists) return missingCard(ctx, info);
  const node = info.node;
  const frame = (kicker: Child, title: string, ...body: readonly Child[]): HTMLElement =>
    h('article', { class: ['graph__focus', `graph__focus--${node.kind}`], 'aria-labelledby': 'graph-focus-title' },
      h('p', { class: 'graph__kicker' }, kicker),
      h('h2', { class: 'graph__focus-title', id: 'graph-focus-title' }, title),
      ...body,
    );
  const other = modeLink(info, mode === 'node' ? 'impact' : 'node');
  switch (node.kind) {
    case 'req': {
      const block = ctx.index.blocks.get(node.id);
      if (block === undefined) return missingCard(ctx, info);
      const removed = block.status.state === 'removed';
      const lean = LEAN_META[leanState(ctx, node.id)];
      return frame(
        [h('span', { class: 'graph__mono' }, node.id), ` · ${block.file}`],
        block.title,
        h('p', { class: 'graph__meta' },
          kindBadge(block.kind, 'graph'),
          block.priority === null ? null : h('span', { class: 'graph__priority' }, block.priority),
          removed ? statusBadge({ glyph: '–', word: 'Removed', tone: 'none', explain: 'Removed. Kept as a tombstone.' }) : statusBadge(lean),
          openDefects(ctx, node.id).map((d) => h('a', { class: 'graph__defect-link', href: href(R.graph({ kind: 'defect', id: d.id })) }, statusBadge(TEST_META.defect, d.id))),
        ),
        actions(h('a', { class: ['graph__button', 'graph__button--primary'], href: href(R.req(node.id)) }, 'Open rule'), other),
      );
    }
    case 'defect': {
      const d = ctx.index.defects.get(node.id);
      if (d === undefined) return missingCard(ctx, info);
      return frame(
        [h('span', { class: 'graph__mono' }, d.id), ' · Defect'],
        d.title,
        h('p', { class: 'graph__meta' },
          d.status.state === 'open'
            ? statusBadge(TEST_META.defect, 'open')
            : statusBadge({ glyph: '✓', word: defectStatusWord(d.status), tone: 'ok', explain: 'The ledger entry is closed.' }),
          ' ',
          d.runtimes.map((r) => RUNTIME_LABEL[r]).join(', '),
        ),
        h('div', { class: 'graph__prose' }, mdBlocks(ctx, d.text)),
        actions(other),
      );
    }
    case 'term': {
      const t = ctx.index.terms.get(node.slug);
      if (t === undefined) return missingCard(ctx, info);
      return frame(`Glossary term · ${t.group}`, t.term, h('div', { class: 'graph__prose' }, mdBlocks(ctx, t.text)), actions(other));
    }
    case 'theorem': {
      const facts = theoremFacts(ctx.data, node.name);
      const doc = facts?.doc ?? null;
      return frame(
        'Theorem',
        info.label,
        h('p', { class: 'graph__fullname' }, h('code', null, node.name)),
        facts?.module ? h('p', { class: 'graph__meta' }, 'Module ', h('code', null, facts.module)) : null,
        facts && facts.roles.length > 0 ? h('p', { class: 'graph__meta' }, facts.roles.map(roleTag)) : null,
        doc === null ? null : h('details', { class: 'graph__doc' }, h('summary', null, 'Example'), h('div', { class: 'graph__prose' }, mdBlocks(ctx, doc))),
        actions(h('a', { class: 'graph__button', href: `${ctx.data.links.proofGraph}#${node.name}`, rel: 'noopener' }, 'Proof graph ↗'), other),
      );
    }
    case 'situation': {
      const s = ctx.index.situations.get(node.slug);
      if (s === undefined) return missingCard(ctx, info);
      return frame(
        `Situation · ${s.group}`,
        s.title,
        h('div', { class: 'graph__prose' }, mdBlocks(ctx, s.text)),
        actions(h('a', { class: ['graph__button', 'graph__button--primary'], href: href(R.situation(s.slug)) }, 'Open situation'), other),
      );
    }
  }
}

// ---------------------------------------------------------------------------------------------
// Views
// ---------------------------------------------------------------------------------------------

/** Picker candidates: every node a reader can start from. */
function candidates(ctx: AppContext): readonly GraphNode[] {
  const theorems = new Set<string>();
  for (const e of ctx.data.edges) {
    if (e.kind === 'evidence') theorems.add(e.to);
    if (e.kind === 'cites') theorems.add(e.from);
  }
  return [
    ...ctx.data.blocks.map((b): GraphNode => ({ kind: 'req', id: b.id })),
    ...[...theorems].sort().map((name): GraphNode => ({ kind: 'theorem', name })),
    ...ctx.data.glossary.map((t): GraphNode => ({ kind: 'term', slug: t.slug })),
    ...ctx.data.situations.map((s): GraphNode => ({ kind: 'situation', slug: s.slug })),
    ...ctx.data.defects.map((d): GraphNode => ({ kind: 'defect', id: d.id })),
  ];
}

const squash = (text: string): string => text.toLowerCase().replace(/[\s_.-]+/g, '');

/** Picker matches: the key or label ignoring case, spaces, dots and hyphens, or every word in the title. */
export function pickerMatches(ctx: AppContext, query: string, limit = 20): readonly GraphNode[] {
  const q = query.trim().toLowerCase();
  if (q === '') return [];
  const flat = squash(q);
  const words = q.split(/\s+/);
  const scored: { node: GraphNode; score: number; i: number }[] = [];
  candidates(ctx).forEach((node, i) => {
    const info = nodeInfo(ctx, node);
    const key = squash(info.label);
    const score = key === flat ? 0 : key.startsWith(flat) ? 1 : key.includes(flat) ? 2
      : words.every((w) => `${info.label} ${info.title}`.toLowerCase().includes(w)) ? 3 : -1;
    if (score >= 0) scored.push({ node, score, i });
  });
  return scored.sort((a, b) => a.score - b.score || a.i - b.i).slice(0, limit).map((s) => s.node);
}

/** The `n` active rules with the most edges, ties in spec order. */
export function mostConnected(ctx: AppContext, n = 10): readonly ReqId[] {
  const degree = (id: ReqId): number => (ctx.index.edgesFrom.get(id)?.length ?? 0) + (ctx.index.edgesTo.get(id)?.length ?? 0);
  return ctx.index.activeBlocks
    .map((b, i) => ({ id: b.id, d: degree(b.id), i }))
    .filter((x) => x.d > 0)
    .sort((a, b) => b.d - a.d || a.i - b.i)
    .slice(0, n)
    .map((x) => x.id);
}

function renderPicker(ctx: AppContext): ViewResult {
  const input = h('input', {
    id: 'graph-picker',
    class: 'graph__picker-input',
    type: 'search',
    placeholder: 'CORE-031, inhibitor, a theorem name',
    autocomplete: 'off',
    spellcheck: false,
  });
  const heading = h('h2', { class: 'graph__col-title', id: 'graph-picker-list' });
  const status = h('p', { class: 'sr-only', role: 'status' });
  const host = h('div');
  const draw = (): void => {
    const q = input.value;
    const nodes = q.trim() === '' ? mostConnected(ctx).map((id): GraphNode => ({ kind: 'req', id })) : pickerMatches(ctx, q);
    replaceChildren(heading, q.trim() === '' ? 'Most used rules' : `Matches (${nodes.length})`);
    status.textContent = q.trim() === '' ? '' : plural(nodes.length, 'match', 'matches');
    replaceChildren(host, nodes.length === 0
      ? h('p', { class: 'graph__empty' }, q.trim() === '' ? 'The graph is empty.' : `No matches for "${q.trim()}". Try an ID like CORE-031, a term like inhibitor arc, or a theorem name.`)
      : h('ul', { class: 'graph__chips graph__chips--picker', 'aria-labelledby': 'graph-picker-list' }, nodes.map((n) => h('li', null, nodeChip(ctx, n, defectMeta(ctx, n))))));
  };
  input.addEventListener('input', draw);
  draw();
  return {
    title: 'Graph',
    node: viewFrame('graph', 'Graph',
      h('p', { class: 'view__lede' }, 'Every rule, theorem, glossary term, situation and defect, with what it depends on and what depends on it.'),
      h('div', { class: 'graph__picker' },
        h('label', { class: 'graph__picker-label', for: 'graph-picker' }, 'Start from a rule, term or theorem'),
        input,
      ),
      status,
      h('section', { class: 'graph__picker-results', 'aria-labelledby': 'graph-picker-list' }, heading, host),
    ),
  };
}

function renderNeighbourhood(ctx: AppContext, info: NodeInfo): ViewResult {
  const title = `Graph: ${info.label}`;
  const columns = neighbourColumns(ctx.index, info, nodeComparator(ctx.data));
  const body = info.exists
    ? h('div', { class: ['graph__grid', info.node.kind === 'req' ? 'graph__grid--req' : 'graph__grid--node'] },
        h('div', { class: 'graph__centre' }, focusCard(ctx, info, 'node')),
        columns.map((c) => neighbourColumn(ctx, info, c)),
      )
    : h('div', { class: 'graph__grid graph__grid--missing' }, h('div', { class: 'graph__centre' }, focusCard(ctx, info, 'node')));
  return { title, node: viewFrame('graph', title, body) };
}

function renderImpact(ctx: AppContext, info: NodeInfo): ViewResult {
  const title = `Impact of ${info.label}`;
  if (!info.exists) return { title: `Impact: ${info.label}`, node: viewFrame('graph', title, focusCard(ctx, info, 'impact')) };

  let mentions = false;
  let allSteps = false;
  let timer = 0;
  const compare = nodeComparator(ctx.data);
  const host = h('div', { class: 'graph__impact' });
  const status = h('span', { class: 'graph__copy-status', role: 'status' });
  const fallback = h('textarea', { class: 'graph__copy-text', attrs: { readonly: true }, 'aria-label': 'Impact as Markdown', hidden: true });
  const toggle = h('button', { type: 'button', class: 'graph__toggle', 'aria-pressed': 'false' },
    h('span', { class: 'graph__toggle-check', 'aria-hidden': 'true' }, '✓'), 'Include mentions');
  const copy = h('button', { type: 'button', class: 'graph__button' }, 'Copy as Markdown');

  const compute = (): Impact => impactOf(ctx.index, info.node, { mentions, compare, hops: allSteps ? Number.POSITIVE_INFINITY : IMPACT_HOPS });
  const showAll = h('button', { type: 'button', class: 'graph__button' }, 'Show all steps');
  showAll.addEventListener('click', () => {
    allSteps = true;
    draw();
    host.querySelector<HTMLElement>(`#graph-hop-${IMPACT_HOPS + 1}`)?.focus();
  });

  const draw = (): void => {
    const impact = compute();
    toggle.setAttribute('aria-pressed', String(mentions));
    if (impact.layers.length === 0) {
      replaceChildren(host, h('p', { class: 'graph__empty' }, `Nothing depends on ${info.label}.`));
      return;
    }
    replaceChildren(host,
      h('div', { class: 'graph__hops' }, impact.layers.map((layer, k) => {
        const id = `graph-hop-${k + 1}`;
        const groups = layerGroups(layer);
        const rules = layer.filter((hit) => hit.node.kind === 'req').length;
        const chipsOf = (hits: readonly ImpactHit[]): HTMLElement => chipList(hits.map((hit) => nodeChip(ctx, hit.node, h('span', { class: 'graph__via' },
          k === 0 ? VIA_LABEL[hit.edge] : `via ${nodeInfo(ctx, hit.via).label}`))));
        // The heading counts rules only; theorems, situations and defects get their own groups.
        return h('section', { class: 'graph__hop', 'aria-labelledby': id },
          h('h2', { class: 'graph__col-title', id, tabindex: -1 }, hopLabel(k), ' ', h('span', { class: 'graph__count' }, `(${plural(rules, 'rule', 'rules')})`)),
          groups.length === 1 && groups[0]?.kind === 'req'
            ? chipsOf(layer)
            : groups.map((g) => h('div', { class: 'graph__hop-group' },
                h('h3', { class: 'graph__group-title' }, `${GROUP_TITLE[g.kind]} `,
                  h('span', { class: 'graph__count' }, `(${g.hits.length})`)),
                chipsOf(g.hits),
              )),
        );
      })),
      h('p', { class: 'graph__total' }, impactTotals(ctx, impact)),
      impact.beyond > 0 ? h('p', { class: 'graph__beyond' }, beyondText(impact), ' ', showAll) : null,
    );
  };

  toggle.addEventListener('click', () => {
    mentions = !mentions;
    draw();
  });
  copy.addEventListener('click', () => {
    const text = impactMarkdown(ctx, info.node, compute());
    const done = (message: string): void => {
      status.textContent = message;
      clearTimeout(timer);
      timer = window.setTimeout(() => {
        status.textContent = '';
      }, 1500);
    };
    const showFallback = (): void => {
      fallback.value = text;
      fallback.hidden = false;
      fallback.focus();
      fallback.select();
      status.textContent = 'Select the text below and copy it.';
    };
    const clip = typeof navigator === 'undefined' ? undefined : navigator.clipboard;
    if (clip === undefined) showFallback();
    else clip.writeText(text).then(() => done('Copied'), showFallback);
  });

  draw();
  const lede = `If ${info.label} changes, everything below depends on it, directly or through others. Column headings count rules; theorems, situations and defects are listed under them. Mentions are left out unless you include them.`;
  return {
    title: `Impact: ${info.label}`,
    node: viewFrame('graph', title,
      h('p', { class: 'view__lede' }, lede),
      h('div', { class: 'graph__impact-head' },
        focusCard(ctx, info, 'impact'),
        h('div', { class: 'graph__toolbar' }, toggle, copy, status),
      ),
      fallback,
      host,
    ),
    dispose: () => clearTimeout(timer),
  };
}

export function renderGraph(ctx: AppContext, route: RouteOf<'graph'>): ViewResult {
  if (route.node === null) return renderPicker(ctx);
  const info = nodeInfo(ctx, route.node);
  const view = route.mode === 'impact' ? renderImpact(ctx, info) : renderNeighbourhood(ctx, info);
  const node = route.node;
  const stopKeys = viewKeys({ i: () => ctx.navigate(route.mode === 'impact' ? R.graph(node) : R.impact(node)) });
  return {
    ...view,
    dispose: () => {
      stopKeys();
      view.dispose?.();
    },
  };
}
