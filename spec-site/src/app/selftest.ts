/**
 * Self-test (`#/selftest`, design 9). Renders every view of the page in memory (every situation
 * at every step, every rule, tombstones included, the graph of every node and the impact of every
 * rule), the search and help panels, and checks the embedded data for broken references. CI opens
 * the page and requires 0 errors through
 * `#selftest-result[data-selftest-errors][data-selftest-done="true"]`.
 *
 * The checks run in slices on timers, so the page stays responsive and shows progress; leaving
 * the view cancels the run. `runSelftest` runs the same checks in one go (unit tests use it).
 *
 * Owner: CI + tests agent.
 */
import type {
  GraphNode,
  Marking,
  NetTransition,
  NodeName,
  OutputSpec,
  SiteData,
  SituationEntry,
} from '../model.js';
import { nodeKey } from '../model.js';
import { cloneDiagram } from './data.js';
import type { AppContext, ViewResult } from './context.js';
import { h } from './dom.js';
import { renderHelpPanel, type HelpSection } from './help.js';
import { formatRoute, parseHash, R, reqGraph, type Route, type RouteOf } from './router.js';
import { renderSearchPanel, searchSite } from './search.js';
import { viewFrame } from './ui.js';

/** Result groups, in the order the page lists them. */
export const SELFTEST_GROUPS = [
  'Situations',
  'Situation pages',
  'Rules',
  'Conformance',
  'Graph',
  'Impact',
  'Unknown addresses',
  'Search',
  'Help',
  'Data invariants',
] as const;
export type SelftestGroup = (typeof SELFTEST_GROUPS)[number];

export interface SelftestCheck {
  readonly group: SelftestGroup;
  readonly name: string;
  /** null when the check passed. */
  readonly error: string | null;
}

export interface SelftestReport {
  readonly checks: readonly SelftestCheck[];
  readonly errors: number;
}

/** A check not run yet. `sandbox` is a hidden element in the document to mount views into. */
interface PlannedCheck {
  readonly group: SelftestGroup;
  readonly name: string;
  readonly run: (sandbox: HTMLElement) => void;
}

const HELP_SECTIONS: readonly HelpSection[] = ['keyboard', 'reading', 'replays', 'lean'];
const SEARCH_QUERIES: readonly string[] = ['', 'CORE-031', 'core-031', 'inhibitor', 'timeout', 'xor', 'RD-0', 'zzzz-no-match'];

// ---------------------------------------------------------------------------------------------
// Routes
// ---------------------------------------------------------------------------------------------

/** Every theorem name the page knows: evidence, citations and defect evidence. */
function theoremNames(data: SiteData): ReadonlySet<string> {
  const names = new Set<string>();
  for (const id of Object.keys(data.lean).sort()) {
    for (const block of data.lean[id] ?? []) for (const e of block.evidence) names.add(e.theorem);
  }
  for (const c of data.citations) names.add(c.theorem);
  for (const d of data.defects) for (const t of d.evidence) names.add(t);
  return names;
}

/** Every graph node: rules (tombstones too), defects, terms, theorems, situations. */
export function graphNodes(data: SiteData): readonly GraphNode[] {
  const nodes: GraphNode[] = [];
  for (const b of data.blocks) nodes.push({ kind: 'req', id: b.id });
  for (const d of data.defects) nodes.push({ kind: 'defect', id: d.id });
  for (const t of data.glossary) nodes.push({ kind: 'term', slug: t.slug });
  for (const s of data.situations) nodes.push({ kind: 'situation', slug: s.slug });
  for (const name of [...theoremNames(data)].sort()) nodes.push({ kind: 'theorem', name });
  return nodes;
}

/**
 * Routes the self-test renders: every view, every situation at every step, every block (with a
 * few filter combinations), the graph of every node and the impact of every block.
 */
export function sampleRoutes(data: SiteData): readonly (readonly [group: SelftestGroup, route: Route])[] {
  const out: (readonly [SelftestGroup, Route])[] = [['Situations', R.situations()]];
  for (const s of data.situations) {
    for (let step = 0; step <= s.steps.length; step++) out.push(['Situation pages', R.situation(s.slug, step)]);
  }
  out.push(
    ['Rules', R.req()],
    ['Rules', R.req(null, { kind: 'A,B' })],
    ['Rules', R.req(null, { lean: 'none' })],
    ['Rules', R.req(null, { f: 'signed,defect,untested' })],
    ['Rules', R.req(null, { q: 'inhibitor' })],
  );
  for (const b of data.blocks) out.push(['Rules', R.req(b.id)]);
  out.push(
    ['Conformance', R.conf()],
    ['Conformance', R.conf({ f: 'defects,untested' })],
    ['Conformance', R.conf({ f: 'nolean', kind: 'B' })],
    ['Conformance', R.conf({ q: 'timeout' })],
    ['Graph', R.graph()],
  );
  for (const node of graphNodes(data)) out.push(['Graph', R.graph(node)]);
  for (const b of data.blocks) out.push(['Impact', reqGraph(b.id, 'impact')]);
  return out;
}

/** Addresses that do not exist: each view must render its "not found" copy, not throw. */
function unknownRoutes(): readonly Route[] {
  return [
    R.req('NOPE-999'),
    R.situation('no-such-situation'),
    R.situation('no-such-situation', 3),
    reqGraph('NOPE-999'),
    reqGraph('NOPE-999', 'impact'),
    R.graph({ kind: 'term', slug: 'no-such-term' }),
    R.graph({ kind: 'theorem', name: 'Libpetri.NoSuchTheorem' }),
    R.graph({ kind: 'situation', slug: 'no-such-situation' }),
    R.graph({ kind: 'defect', id: 'RD-999' }),
    parseHash('#/no/such/page'),
  ];
}

// ---------------------------------------------------------------------------------------------
// DOM checks on a rendered view
// ---------------------------------------------------------------------------------------------

interface Known {
  readonly theorems: ReadonlySet<string>;
}

function nodeExists(ctx: AppContext, known: Known, node: GraphNode): boolean {
  switch (node.kind) {
    case 'req':
      return ctx.index.blocks.has(node.id);
    case 'defect':
      return ctx.index.defects.has(node.id);
    case 'term':
      return ctx.index.terms.has(node.slug);
    case 'theorem':
      return known.theorems.has(node.name);
    case 'situation':
      return ctx.index.situations.has(node.slug);
  }
}

/** Why an in-page route would land on a "not found" page, or null when it resolves. */
function routeProblem(ctx: AppContext, known: Known, route: Route): string | null {
  switch (route.view) {
    case 'notfound':
      return 'no such page';
    case 'req':
      return route.id !== null && !ctx.index.blocks.has(route.id) ? 'unknown requirement' : null;
    case 'situation':
      return ctx.index.situations.has(route.slug) ? null : 'unknown situation';
    case 'graph':
      return route.node !== null && !nodeExists(ctx, known, route.node) ? 'unknown graph node' : null;
    case 'situations':
    case 'conf':
    case 'selftest':
      return null;
  }
}

function sample(list: readonly string[]): string {
  const unique = [...new Set(list)];
  const head = unique.slice(0, 4).join('; ');
  return unique.length > 4 ? `${head}; and ${unique.length - 4} more` : head;
}

/** Every `#/` link in `root` resolves. Links marked as deliberately unknown (`.req-id--unknown`) are skipped. */
function checkLinks(ctx: AppContext, known: Known, root: ParentNode): void {
  const dead: string[] = [];
  for (const a of root.querySelectorAll<HTMLAnchorElement>('a[href^="#/"]')) {
    if (a.classList.contains('req-id--unknown')) continue;
    const target = a.getAttribute('href') ?? '';
    const why = routeProblem(ctx, known, parseHash(target));
    if (why !== null) dead.push(`${target} (${why})`);
  }
  if (dead.length > 0) throw new Error(`dead links: ${sample(dead)}`);
}

/** No duplicate ids, and every aria-labelledby / aria-describedby / label `for` points inside the view. */
function checkIds(root: Element): void {
  const seen = new Set<string>();
  const dupes: string[] = [];
  for (const el of root.querySelectorAll('[id]')) {
    if (seen.has(el.id)) dupes.push(el.id);
    seen.add(el.id);
  }
  if (root.id !== '') seen.add(root.id);
  if (dupes.length > 0) throw new Error(`duplicate ids: ${sample(dupes)}`);
  const missing: string[] = [];
  for (const attr of ['aria-labelledby', 'aria-describedby']) {
    for (const el of root.querySelectorAll(`[${attr}]`)) {
      for (const ref of (el.getAttribute(attr) ?? '').split(/\s+/)) {
        if (ref !== '' && !seen.has(ref)) missing.push(`${attr}=${ref}`);
      }
    }
  }
  for (const label of root.querySelectorAll<HTMLLabelElement>('label[for]')) {
    if (!seen.has(label.htmlFor)) missing.push(`for=${label.htmlFor}`);
  }
  if (missing.length > 0) throw new Error(`references to missing ids: ${sample(missing)}`);
}

interface ViewCheckOptions {
  readonly links: boolean;
  readonly extra?: (root: Element) => void;
}

function checkView(ctx: AppContext, known: Known, route: Route, sandbox: HTMLElement, options: ViewCheckOptions): void {
  const view: ViewResult = ctx.render(route);
  try {
    if (view.title.trim() === '') throw new Error('empty title');
    sandbox.replaceChildren(view.node);
    const h1s = sandbox.querySelectorAll('h1');
    if (h1s.length !== 1) throw new Error(`a view needs exactly one h1, found ${h1s.length}`);
    const h1 = h1s[0];
    if (h1 === undefined || (h1.textContent ?? '').trim() === '') throw new Error('the h1 is empty');
    if (h1.tabIndex !== -1) throw new Error('the h1 needs tabindex="-1" so the shell can focus it');
    if (sandbox.querySelector('.view--error') !== null) throw new Error('the view shows an error card');
    checkIds(sandbox);
    if (options.links) checkLinks(ctx, known, sandbox);
    options.extra?.(sandbox);
  } finally {
    view.dispose?.();
    sandbox.replaceChildren();
  }
}

// ---------------------------------------------------------------------------------------------
// Data invariants
// ---------------------------------------------------------------------------------------------

function fail(problems: readonly string[]): void {
  if (problems.length > 0) throw new Error(sample(problems));
}

function outputPlaces(spec: OutputSpec | null, into: Set<NodeName>): void {
  if (spec === null) return;
  switch (spec.type) {
    case 'place':
      into.add(spec.place);
      return;
    case 'and':
    case 'xor':
      for (const c of spec.children) outputPlaces(c, into);
      return;
    case 'timeout':
      outputPlaces(spec.child, into);
      return;
    case 'forward':
      into.add(spec.from);
      into.add(spec.to);
      return;
  }
}

/** Places a transition touches through any arc. */
function arcPlaces(t: NetTransition, into: Set<NodeName>): void {
  for (const a of t.inputs) into.add(a.place);
  for (const p of [...t.inhibitors, ...t.reads, ...t.resets]) into.add(p);
  outputPlaces(t.output, into);
}

/** Places a situation's player needs to find in its diagram: every place an arc names or a marking holds. */
function playerPlaces(s: SituationEntry): readonly NodeName[] {
  const places = new Set<NodeName>(Object.keys(s.net.marking));
  for (const t of s.net.transitions) arcPlaces(t, places);
  if (s.result !== null) {
    for (const p of Object.keys(s.result.initial)) places.add(p);
    for (const step of s.result.steps) if (step.kind === 'fired') for (const p of Object.keys(step.marking)) places.add(p);
  }
  return [...places].sort();
}

function checkMarking(label: string, marking: Marking, places: ReadonlySet<NodeName>, problems: string[]): void {
  for (const [place, n] of Object.entries(marking)) {
    if (!places.has(place)) problems.push(`${label}: place ${place} is not in the net`);
    if (!Number.isInteger(n) || n <= 0) problems.push(`${label}: ${place} holds ${n}`);
  }
}

function checkSituationReplay(ctx: AppContext, s: SituationEntry): void {
  const problems: string[] = [];
  const names = new Set(s.net.transitions.map((t) => t.name));
  if (s.replay !== (s.result !== null)) problems.push(s.replay ? 'replay is on but there is no Lean result' : 'not replayed but has a Lean result');
  if (s.replay !== (s.notReplayed === null)) problems.push('notReplayed must be set exactly when replay is false');
  for (const [i, step] of s.steps.entries()) if (!names.has(step.fire)) problems.push(`step ${i + 1} fires unknown transition ${step.fire}`);
  const places = new Set<NodeName>([...s.net.places, ...playerPlaces(s)]);
  checkMarking('initial marking', s.net.marking, places, problems);
  const r = s.result;
  if (r !== null) {
    if (r.slug !== s.slug) problems.push(`result slug ${r.slug}`);
    checkMarking('Lean initial marking', r.initial, places, problems);
    if (r.steps.length > s.steps.length) problems.push('the replay has more steps than the situation');
    for (const [i, step] of r.steps.entries()) {
      const authored = s.steps[i];
      if (step.index !== i) problems.push(`replay step ${i + 1} has index ${step.index}`);
      if (authored === undefined || authored.fire !== step.fire) problems.push(`replay step ${i + 1} fires ${step.fire}, the situation says ${authored?.fire ?? 'nothing'}`);
      if (step.kind === 'fired') {
        if (!names.has(step.fire)) problems.push(`replay step ${i + 1} fired unknown transition ${step.fire}`);
        checkMarking(`marking after step ${i + 1}`, step.marking, places, problems);
      } else {
        if (i !== r.steps.length - 1) problems.push(`blocked step ${i + 1} is not the last replay step`);
        if (step.reason.kind === 'unknownTransition' ? names.has(step.fire) : !names.has(step.fire)) {
          problems.push(`blocked step ${i + 1}: ${step.reason.kind} does not fit transition ${step.fire}`);
        }
        if (!ctx.index.blocks.has(step.requirement)) problems.push(`blocked step ${i + 1} cites unknown ${step.requirement}`);
        if (step.message.trim() === '') problems.push(`blocked step ${i + 1} has no message`);
      }
    }
    const allFired = r.steps.length === s.steps.length && r.steps.every((st) => st.kind === 'fired');
    if (r.complete !== allFired) problems.push(`complete is ${r.complete}, but ${allFired ? 'every step fired' : 'not every step fired'}`);
  }
  for (const rule of s.rules) {
    if (!ctx.index.blocks.has(rule.id)) problems.push(`rule ${rule.id} is unknown`);
    if (rule.links.length === 0) problems.push(`rule ${rule.id} has no link`);
  }
  for (const id of s.cites) {
    const b = ctx.index.blocks.get(id);
    if (b === undefined || b.status.state === 'removed') problems.push(`cites ${id}, which is ${b === undefined ? 'unknown' : 'removed'}`);
  }
  fail(problems);
}

function cssString(text: string): string {
  return `"${text.replace(/\\/g, '\\\\').replace(/"/g, '\\"')}"`;
}

function checkSituationDiagram(s: SituationEntry): void {
  if (!s.diagram) throw new Error('no diagram was rendered for this situation');
  const svg = cloneDiagram(s.slug);
  if (svg === null) throw new Error(`the page has no diagram template for ${s.slug}`);
  const problems: string[] = [];
  if (svg.querySelector('[id]') !== null || svg.id !== '') problems.push('the SVG still carries id attributes');
  if (!svg.hasAttribute('viewBox')) problems.push('the SVG has no viewBox');
  for (const place of playerPlaces(s)) {
    if (svg.querySelector(`[data-kind="place"][data-name=${cssString(place)}]`) === null) problems.push(`no node for place ${place}`);
  }
  for (const t of s.net.transitions) {
    if (svg.querySelector(`[data-kind="transition"][data-name=${cssString(t.name)}]`) === null) problems.push(`no node for transition ${t.name}`);
  }
  for (const g of svg.querySelectorAll('g.node')) {
    const key = g.getAttribute('data-node') ?? '';
    const kind = g.getAttribute('data-kind') ?? '';
    if (key === '') problems.push('a node group has no data-node');
    if (kind === 'place' && !key.startsWith('p_')) problems.push(`place node ${key} lacks the p_ prefix`);
    if (kind === 'transition' && !key.startsWith('t_')) problems.push(`transition node ${key} lacks the t_ prefix`);
  }
  fail(problems);
}

function dataChecks(ctx: AppContext, known: Known): readonly PlannedCheck[] {
  const { data, index } = ctx;
  const out: PlannedCheck[] = [];
  const add = (name: string, run: () => void): void => {
    out.push({ group: 'Data invariants', name, run: () => run() });
  };
  const isActive = (id: string): boolean => {
    const b = index.blocks.get(id);
    return b !== undefined && b.status.state !== 'removed';
  };

  add('content hash is 12 hex digits', () => {
    if (!/^[0-9a-f]{12}$/.test(data.contentHash)) throw new Error(`content hash ${data.contentHash}`);
  });

  add('IDs, slugs and defect IDs are unique', () => {
    const problems: string[] = [];
    const dupes = (label: string, keys: readonly string[]): void => {
      const seen = new Set<string>();
      for (const k of keys) {
        if (seen.has(k)) problems.push(`${label} ${k} twice`);
        seen.add(k);
      }
    };
    dupes('requirement', data.blocks.map((b) => b.id));
    dupes('situation', data.situations.map((s) => s.slug));
    dupes('term', data.glossary.map((t) => t.slug));
    dupes('defect', data.defects.map((d) => d.id));
    fail(problems);
  });

  add('counts match the data', () => {
    const c = data.counts;
    const leanLists = Object.values(data.lean);
    const signed = leanLists.flat().filter((b) => b.signoff.state === 'signed').length;
    const expect: readonly (readonly [string, number, number])[] = [
      // Active means not removed: proposed blocks count as active (the 224 of spec/00-index.md).
      ['activeIds', c.activeIds, data.blocks.filter((b) => b.status.state !== 'removed').length],
      ['removedIds', c.removedIds, data.blocks.filter((b) => b.status.state === 'removed').length],
      ['proposedIds', c.proposedIds, data.blocks.filter((b) => b.status.state === 'proposed').length],
      ['leanBlocks', c.leanBlocks, leanLists.reduce((n, l) => n + l.length, 0)],
      ['leanIds', c.leanIds, leanLists.filter((l) => l.length > 0).length],
      ['signedBlocks', c.signedBlocks, signed],
      ['citedIds', c.citedIds, new Set(data.citations.map((x) => x.id)).size],
      ['openDefects', c.openDefects, data.defects.filter((d) => d.status.state === 'open').length],
      ['situations', c.situations, data.situations.length],
      ['replayed', c.replayed, data.situations.filter((s) => s.result !== null).length],
      ['glossaryTerms', c.glossaryTerms, data.glossary.length],
    ];
    fail(expect.filter(([, shown, actual]) => shown !== actual).map(([k, shown, actual]) => `${k} says ${shown}, the data has ${actual}`));
  });

  add('one coverage row per active requirement', () => {
    const problems: string[] = [];
    for (const b of index.activeBlocks) if (data.coverage[b.id] === undefined) problems.push(`${b.id} has no row`);
    for (const id of Object.keys(data.coverage)) {
      if (!isActive(id)) problems.push(`row ${id} is not an active requirement`);
      if (data.coverage[id]?.id !== id) problems.push(`row ${id} names ${data.coverage[id]?.id ?? 'nothing'}`);
    }
    fail(problems);
  });

  for (const b of data.blocks) {
    add(`${b.id}: every ID link and glossary term resolves`, () => {
      const problems: string[] = [];
      for (const id of b.dependsOn) if (!index.blocks.has(id)) problems.push(`depends on unknown ${id}`);
      for (const id of b.mentions) if (!index.blocks.has(id)) problems.push(`mentions unknown ${id}`);
      for (const slug of b.terms) if (!index.terms.has(slug)) problems.push(`uses term ${slug}, which has no glossary entry`);
      if (b.status.state !== 'removed' && b.title.trim() === '') problems.push('empty title');
      if (!index.files.has(b.file)) problems.push(`file ${b.file} is not a spec file`);
      fail(problems);
    });
  }

  add('glossary references resolve', () => {
    const problems: string[] = [];
    for (const t of data.glossary) for (const id of t.refs) if (!index.blocks.has(id)) problems.push(`${t.slug} refers to unknown ${id}`);
    fail(problems);
  });

  add('every Lean block belongs to a requirement and every evidence theorem has a proof graph link', () => {
    const problems: string[] = [];
    if (data.links.proofGraph === '') problems.push('links.proofGraph is empty');
    for (const id of Object.keys(data.lean).sort()) {
      if (!index.blocks.has(id)) problems.push(`Lean blocks for unknown ${id}`);
      for (const block of data.lean[id] ?? []) {
        if (block.id !== id) problems.push(`block ${block.decl} is filed under ${id} but names ${block.id}`);
        for (const e of block.evidence) {
          // The link is `${links.proofGraph}#${theorem}`: the name must be a usable fragment.
          if (!/^[^\s#]+$/.test(e.theorem)) problems.push(`theorem "${e.theorem}" cannot be a link fragment`);
        }
      }
    }
    fail(problems);
  });

  add('citations name active requirements', () => {
    fail(data.citations.filter((c) => !isActive(c.id)).map((c) => `${c.theorem} cites ${c.id}`));
  });

  add('defects name known requirements', () => {
    const problems: string[] = [];
    for (const d of data.defects) for (const id of d.requirements) if (!index.blocks.has(id)) problems.push(`${d.id} breaks unknown ${id}`);
    fail(problems);
  });

  add('every graph edge joins two known nodes', () => {
    const problems: string[] = [];
    for (const e of data.edges) {
      const node = (n: GraphNode): void => {
        if (!nodeExists(ctx, known, n)) problems.push(`${e.kind} edge to unknown ${nodeKey(n)}`);
      };
      switch (e.kind) {
        case 'depends-on':
        case 'mentions':
          node({ kind: 'req', id: e.from });
          node({ kind: 'req', id: e.to });
          break;
        case 'evidence':
          node({ kind: 'req', id: e.from });
          node({ kind: 'theorem', name: e.to });
          break;
        case 'cites':
          node({ kind: 'theorem', name: e.from });
          node({ kind: 'req', id: e.to });
          break;
        case 'uses-term':
          node({ kind: 'req', id: e.from });
          node({ kind: 'term', slug: e.to });
          break;
        case 'exercises':
          node({ kind: 'situation', slug: e.from });
          node({ kind: 'req', id: e.to });
          break;
        case 'breaks':
          node({ kind: 'defect', id: e.from });
          node({ kind: 'req', id: e.to });
          break;
      }
    }
    fail(problems);
  });

  for (const s of data.situations) {
    add(`${s.slug}: every replay step references an existing transition`, () => checkSituationReplay(ctx, s));
    add(`${s.slug}: diagram has a node for every place and transition the player needs`, () => checkSituationDiagram(s));
  }
  return out;
}

// ---------------------------------------------------------------------------------------------
// The plan
// ---------------------------------------------------------------------------------------------

/** Every check of the self-test, in page order. */
function planChecks(ctx: AppContext): readonly PlannedCheck[] {
  const known: Known = { theorems: theoremNames(ctx.data) };
  const plan: PlannedCheck[] = [];

  for (const [group, route] of sampleRoutes(ctx.data)) {
    const situation = route.view === 'situation' ? ctx.index.situations.get(route.slug) : undefined;
    const extra = situation?.diagram === true
      ? (root: Element): void => {
          if (root.querySelector('svg [data-kind="place"]') === null) throw new Error('the situation page shows no diagram');
        }
      : undefined;
    plan.push({
      group,
      name: formatRoute(route),
      run: (sandbox) => checkView(ctx, known, route, sandbox, { links: true, ...(extra === undefined ? {} : { extra }) }),
    });
  }

  for (const route of unknownRoutes()) {
    plan.push({ group: 'Unknown addresses', name: formatRoute(route), run: (sandbox) => checkView(ctx, known, route, sandbox, { links: false }) });
  }

  for (const q of SEARCH_QUERIES) {
    plan.push({
      group: 'Search',
      name: `search "${q}"`,
      run: (sandbox) => {
        const hits = searchSite(ctx, q);
        const dead = hits.map((hit) => [hit, routeProblem(ctx, known, hit.route)] as const).filter(([, why]) => why !== null);
        if (dead.length > 0) throw new Error(`hits lead nowhere: ${sample(dead.map(([hit, why]) => `${hit.key} (${why ?? ''})`))}`);
        sandbox.replaceChildren(renderSearchPanel(ctx, q));
        checkIds(sandbox);
        sandbox.replaceChildren();
      },
    });
  }
  const firstActive = ctx.index.activeBlocks[0];
  if (firstActive !== undefined) {
    plan.push({
      group: 'Search',
      name: `an exact ID query ranks that rule first (${firstActive.id})`,
      run: () => {
        for (const q of [firstActive.id, firstActive.id.toLowerCase()]) {
          const top = searchSite(ctx, q)[0];
          if (top === undefined || top.kind !== 'req' || top.key !== firstActive.id) {
            throw new Error(`"${q}" ranks ${top === undefined ? 'nothing' : `${top.kind} ${top.key}`} first`);
          }
        }
      },
    });
  }

  plan.push({
    group: 'Help',
    name: 'help panel has every section',
    run: (sandbox) => {
      sandbox.replaceChildren(renderHelpPanel(ctx));
      const missing = HELP_SECTIONS.filter((section) => sandbox.querySelector(`#help-${section}`) === null);
      checkIds(sandbox);
      sandbox.replaceChildren();
      if (missing.length > 0) throw new Error(`missing sections: ${missing.map((m) => `#help-${m}`).join(', ')}`);
    },
  });

  plan.push(...dataChecks(ctx, known));
  return plan;
}

function message(error: unknown): string {
  return error instanceof Error ? error.message : String(error);
}

function runOne(check: PlannedCheck, sandbox: HTMLElement): SelftestCheck {
  try {
    check.run(sandbox);
    return { group: check.group, name: check.name, error: null };
  } catch (error) {
    return { group: check.group, name: check.name, error: message(error) };
  }
}

function makeSandbox(): HTMLElement {
  // Mounted in the document (not in <main>) so layout-dependent code can run; hidden from
  // everyone, and inert so nothing in it takes focus.
  const sandbox = h('div', { class: 'selftest__sandbox', hidden: true, 'aria-hidden': 'true', attrs: { inert: true } });
  document.body.append(sandbox);
  return sandbox;
}

function report(checks: readonly SelftestCheck[]): SelftestReport {
  return { checks, errors: checks.filter((c) => c.error !== null).length };
}

/** Runs every check at once, or only the checks of the `only` groups. */
export function runSelftest(ctx: AppContext, only: ReadonlySet<SelftestGroup> | null = null): SelftestReport {
  const sandbox = makeSandbox();
  try {
    const plan = planChecks(ctx).filter((check) => only === null || only.has(check.group));
    return report(plan.map((check) => runOne(check, sandbox)));
  } finally {
    sandbox.remove();
  }
}

/** Time one slice may take before the runner yields to the browser. */
const SLICE_MS = 40;

/**
 * Runs the checks in slices on timers. Calls `onProgress(done, total)` after each slice and
 * `onDone` at the end. Returns a function that cancels the run.
 */
function startSelftest(
  ctx: AppContext,
  onProgress: (done: number, total: number) => void,
  onDone: (result: SelftestReport) => void,
): () => void {
  let timer: ReturnType<typeof setTimeout> | null = null;
  let sandbox: HTMLElement | null = null;
  let plan: readonly PlannedCheck[] = [];
  const results: SelftestCheck[] = [];
  let next = 0;
  const stop = (): void => {
    if (timer !== null) clearTimeout(timer);
    timer = null;
    sandbox?.remove();
    sandbox = null;
  };
  const slice = (): void => {
    timer = null;
    if (sandbox === null) {
      sandbox = makeSandbox();
      plan = planChecks(ctx);
    }
    const until = performance.now() + SLICE_MS;
    while (next < plan.length && performance.now() < until) {
      const check = plan[next];
      next++;
      if (check !== undefined) results.push(runOne(check, sandbox));
    }
    onProgress(next, plan.length);
    if (next < plan.length) {
      timer = setTimeout(slice, 0);
    } else {
      stop();
      onDone(report(results));
    }
  };
  timer = setTimeout(slice, 0);
  return stop;
}

// ---------------------------------------------------------------------------------------------
// The view
// ---------------------------------------------------------------------------------------------

function plural(n: number, one: string, many: string): string {
  return `${n} ${n === 1 ? one : many}`;
}

function renderGroups(result: SelftestReport): HTMLElement {
  const groups = SELFTEST_GROUPS.map((group) => [group, result.checks.filter((c) => c.group === group)] as const)
    .filter(([, checks]) => checks.length > 0);
  return h('div', { class: 'selftest__groups' },
    groups.map(([group, checks]) => {
      const failed = checks.filter((c) => c.error !== null);
      const passed = checks.filter((c) => c.error === null);
      return h('section', { class: 'selftest__group', 'data-group': group, 'data-errors': failed.length },
        h('h2', { class: 'selftest__group-title' },
          h('span', { class: ['selftest__glyph', failed.length === 0 ? 'selftest__glyph--ok' : 'selftest__glyph--bad'], 'aria-hidden': 'true' }, failed.length === 0 ? '✓' : '✗'),
          ` ${group}`,
          h('span', { class: 'selftest__group-count' }, ` ${plural(checks.length, 'check', 'checks')}, ${failed.length} failed`),
        ),
        failed.length === 0
          ? null
          : h('ul', { class: 'selftest__failures' },
              failed.map((f) => h('li', { class: 'selftest__failure' },
                h('span', { class: 'selftest__glyph selftest__glyph--bad', 'aria-hidden': 'true' }, '✗'),
                h('span', { class: 'sr-only' }, 'Failed: '),
                h('code', { class: 'selftest__name' }, f.name),
                h('span', { class: 'selftest__message' }, f.error ?? ''),
              )),
            ),
        passed.length === 0
          ? null
          : h('details', { class: 'selftest__passes' },
              h('summary', null,
                h('span', { class: 'selftest__glyph selftest__glyph--ok', 'aria-hidden': 'true' }, '✓'),
                ` ${passed.length} passed`,
              ),
              h('ul', { class: 'selftest__passed' }, passed.map((p) => h('li', null, h('code', { class: 'selftest__name' }, p.name)))),
            ),
      );
    }),
  );
}

export function renderSelftest(ctx: AppContext, route: RouteOf<'selftest'>): ViewResult {
  void route;
  const result = h('output', {
    id: 'selftest-result',
    class: 'selftest__result',
    'data-selftest-done': 'false',
  }, 'Running checks…');
  const progress = h('progress', { class: 'selftest__progress', 'aria-label': 'Self-test progress' });
  const groups = h('div', { class: 'selftest__body' });
  let cancel: (() => void) | null = null;

  const run = (): void => {
    cancel?.();
    result.dataset['selftestDone'] = 'false';
    delete result.dataset['selftestErrors'];
    result.className = 'selftest__result';
    result.textContent = 'Running checks…';
    progress.hidden = false;
    progress.removeAttribute('value');
    groups.replaceChildren();
    cancel = startSelftest(ctx,
      (done, total) => {
        progress.max = total;
        progress.value = done;
      },
      (report) => {
        cancel = null;
        const n = report.errors;
        progress.hidden = true;
        result.className = `selftest__result selftest__result--${n === 0 ? 'ok' : 'bad'}`;
        result.textContent = `${plural(n, 'error', 'errors')} in ${report.checks.length} checks`;
        result.dataset['selftestErrors'] = String(n);
        result.dataset['selftestDone'] = 'true';
        groups.replaceChildren(renderGroups(report));
      },
    );
  };

  const again = h('button', { class: 'selftest__again', type: 'button', on: { click: run } }, 'Run again');
  run();

  return {
    title: 'Self-test',
    node: viewFrame('selftest', 'Self-test',
      h('p', { class: 'view__lede' }, 'Renders every view of this page in memory and counts errors. CI opens it and expects 0.'),
      h('div', { class: 'selftest__status' }, result, again),
      progress,
      groups,
    ),
    dispose: () => {
      cancel?.();
      cancel = null;
    },
  };
}
