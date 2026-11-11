/**
 * Assembles `SiteData` from the parsed inputs: groups Lean blocks by ID, derives the situation
 * entries, the graph edges, the counts and the content hash. No file access: tests call it directly.
 *
 * Owner: generator-inputs agent (initial version by the skeleton).
 */
import { createHash } from 'node:crypto';
import type {
  CoverageRow,
  Defect,
  Edge,
  GlossaryTerm,
  LeanBlock,
  OutputSpec,
  ReplayResult,
  ReqId,
  RuleLink,
  SiteCounts,
  SiteData,
  SiteLinks,
  Situation,
  SituationEntry,
  SituationGroup,
  SituationRule,
  SpecBlock,
} from '../model.js';
import { SITUATION_GROUPS } from '../model.js';
import { quotePresent } from './inputs/alignment.js';
import type { SpecInput } from './inputs/spec.js';
import type { LeanInput } from './inputs/lean.js';
import type { SituationInput } from './inputs/situations.js';
import { byString } from './inputs/text.js';
import { stableStringify } from './json.js';

export interface SiteInputs {
  readonly spec: SpecInput;
  readonly glossary: readonly GlossaryTerm[];
  readonly lean: LeanInput;
  readonly coverage: Readonly<Record<ReqId, CoverageRow>>;
  readonly defects: readonly Defect[];
  readonly situations: readonly SituationInput[];
  /** Slugs that have a rendered diagram. */
  readonly diagrams: ReadonlySet<string>;
}

export const SITE_LINKS: SiteLinks = {
  repo: 'https://github.com/debe/libpetri',
  blob: 'https://github.com/debe/libpetri/blob/main/',
  proofGraph: '../proof-graph/',
  home: '../',
};


export function groupLean(blocks: readonly LeanBlock[]): Readonly<Record<ReqId, readonly LeanBlock[]>> {
  const out: Record<ReqId, LeanBlock[]> = {};
  for (const block of blocks) (out[block.id] ??= []).push(block);
  return out;
}

/** The output spec node types of a tree, depth first. */
function outputTypes(spec: OutputSpec): OutputSpec['type'][] {
  switch (spec.type) {
    case 'place':
    case 'forward':
      return [spec.type];
    case 'and':
    case 'xor':
      return [spec.type, ...spec.children.flatMap(outputTypes)];
    case 'timeout':
      return [spec.type, ...outputTypes(spec.child)];
  }
}

const INPUT_RULE = { one: 'IO-001', exactly: 'IO-002', all: 'IO-003', atLeast: 'IO-004' } as const;
const OUTPUT_RULES: Readonly<Record<OutputSpec['type'], readonly ReqId[]>> = {
  place: [],
  and: ['IO-011'],
  xor: ['IO-012', 'IO-016'],
  timeout: ['IO-013'],
  forward: ['IO-014'],
};

/**
 * Requirements a situation's net exercises, by the net features a reader sees in its diagram:
 * - an input arc -> IO-001..004 by its cardinality, and IO-007 for `all` / `atLeast`, where the
 *   consumed count differs from the required count;
 * - an inhibitor arc -> CORE-031, a read arc -> CORE-032, a reset arc -> CORE-034;
 * - an `and` node -> IO-011, `xor` -> IO-012 and IO-016, `timeout` -> IO-013, `forward` -> IO-014;
 * - two transitions with an input arc on one place -> CORE-022 (they compete for its tokens).
 * A plain `place` output and the input arc itself (CORE-030) are in nearly every net, so they
 * are not listed. Sorted; `situationRules` keeps only active IDs.
 */
export function exercisedRules(situation: Situation): readonly ReqId[] {
  const ids = new Set<ReqId>();
  const consumers = new Map<string, number>();
  for (const t of situation.net.transitions) {
    for (const arc of t.inputs) {
      ids.add(INPUT_RULE[arc.kind]);
      if (arc.kind === 'all' || arc.kind === 'atLeast') ids.add('IO-007');
      consumers.set(arc.place, (consumers.get(arc.place) ?? 0) + 1);
    }
    if (t.inhibitors.length > 0) ids.add('CORE-031');
    if (t.reads.length > 0) ids.add('CORE-032');
    if (t.resets.length > 0) ids.add('CORE-034');
    for (const type of t.output === null ? [] : outputTypes(t.output)) for (const id of OUTPUT_RULES[type]) ids.add(id);
  }
  if ([...consumers.values()].some((n) => n > 1)) ids.add('CORE-022');
  return [...ids].sort(byString);
}

/**
 * The linked rules of a situation in spec order, each with how it is linked. `specOrder` holds
 * the active IDs; an exercised rule outside it is left out.
 */
export function situationRules(situation: Situation, result: ReplayResult | null, specOrder: ReadonlyMap<ReqId, number>): readonly SituationRule[] {
  const links = new Map<ReqId, RuleLink[]>();
  const add = (id: ReqId, link: RuleLink): void => {
    const list = links.get(id);
    if (list === undefined) links.set(id, [link]);
    else if (!list.some((l) => l.kind === link.kind)) list.push(link);
  };
  for (const id of situation.cites) add(id, { kind: 'cited' });
  for (const step of result?.steps ?? []) if (step.kind === 'blocked') add(step.requirement, { kind: 'step', index: step.index });
  for (const id of exercisedRules(situation)) if (specOrder.has(id)) add(id, { kind: 'exercised' });
  const rank = (id: ReqId): number => specOrder.get(id) ?? Number.MAX_SAFE_INTEGER;
  return [...links.entries()]
    .sort(([a], [b]) => rank(a) - rank(b) || byString(a, b))
    .map(([id, l]) => ({ id, links: l }));
}

/** Situation entries in home order: group order of `SITUATION_GROUPS`, then slug. */
export function situationEntries(
  inputs: readonly SituationInput[],
  diagrams: ReadonlySet<string>,
  specOrder: ReadonlyMap<ReqId, number>,
): readonly SituationEntry[] {
  const groupRank = (g: SituationGroup): number => SITUATION_GROUPS.indexOf(g);
  return [...inputs]
    .sort((a, b) => groupRank(a.situation.group) - groupRank(b.situation.group) || byString(a.situation.slug, b.situation.slug))
    .map(({ situation, result }) => ({
      ...situation,
      rules: situationRules(situation, result, specOrder),
      result,
      diagram: diagrams.has(situation.slug),
    }));
}

function edgeKey(e: Edge): string {
  return `${e.kind}\u0000${e.from}\u0000${e.to}\u0000${e.kind === 'evidence' ? e.role : ''}`;
}

export function buildEdges(
  spec: SpecInput,
  lean: LeanInput,
  defects: readonly Defect[],
  situations: readonly SituationEntry[],
): readonly Edge[] {
  const edges: Edge[] = [];
  for (const b of spec.blocks) {
    for (const to of b.dependsOn) edges.push({ kind: 'depends-on', from: b.id, to });
    for (const to of b.mentions) edges.push({ kind: 'mentions', from: b.id, to });
    for (const to of b.terms) edges.push({ kind: 'uses-term', from: b.id, to });
  }
  for (const lb of lean.blocks) {
    for (const ev of lb.evidence) edges.push({ kind: 'evidence', from: lb.id, to: ev.theorem, role: ev.role });
  }
  for (const c of lean.citations) edges.push({ kind: 'cites', from: c.theorem, to: c.id });
  for (const s of situations) for (const r of s.rules) edges.push({ kind: 'exercises', from: s.slug, to: r.id });
  for (const d of defects) for (const to of d.requirements) edges.push({ kind: 'breaks', from: d.id, to });

  const seen = new Map<string, Edge>();
  for (const e of edges) seen.set(edgeKey(e), e);
  return [...seen.entries()].sort(([a], [b]) => byString(a, b)).map(([, e]) => e);
}

export function buildCounts(
  spec: SpecInput,
  glossary: readonly GlossaryTerm[],
  lean: LeanInput,
  coverage: Readonly<Record<ReqId, CoverageRow>>,
  defects: readonly Defect[],
  situations: readonly SituationEntry[],
): SiteCounts {
  const active = spec.blocks.filter((b) => b.status.state !== 'removed');
  const untested = active.filter((b) => {
    const row = coverage[b.id];
    return row === undefined || Object.values(row.tests).every((t) => t.state === 'untested');
  });
  return {
    specFiles: spec.files.length,
    activeIds: active.length,
    removedIds: spec.blocks.length - active.length,
    proposedIds: spec.blocks.filter((b) => b.status.state === 'proposed').length,
    leanBlocks: lean.blocks.length,
    leanIds: new Set(lean.blocks.map((b) => b.id)).size,
    signedBlocks: lean.blocks.filter((b) => b.signoff.state === 'signed').length,
    citedIds: new Set(lean.citations.map((c) => c.id)).size,
    openDefects: defects.filter((d) => d.status.state === 'open').length,
    situations: situations.length,
    replayed: situations.filter((s) => s.result !== null).length,
    glossaryTerms: glossary.length,
    untestedIds: untested.length,
  };
}

/** First 12 hex digits of SHA-256 over the JSON of the data without `contentHash`. */
export function contentHashOf(data: Omit<SiteData, 'contentHash'>): string {
  return createHash('sha256').update(stableStringify(data)).digest('hex').slice(0, 12);
}

// ---------------------------------------------------------------------------------------------
// Cross-input checks
// ---------------------------------------------------------------------------------------------

/**
 * The checks no single input can make, one line per problem (`checkSiteInputs` fails with all
 * of them). Every ID another input names must be a spec ID (`needActive`: an active one), the
 * coverage rows must be exactly the active IDs, and every verbatim Lean quote must be a whole
 * sentence run of its block (the rule of `scripts/spec-lean-alignment.py`).
 */
export function inputProblems(inputs: SiteInputs): string[] {
  const problems: string[] = [];
  const blocks = new Map<ReqId, SpecBlock>(inputs.spec.blocks.map((b) => [b.id, b]));
  const need = (id: ReqId, where: string, active: boolean): void => {
    const b = blocks.get(id);
    if (b === undefined) problems.push(`${where}: ${id} is not a requirement`);
    else if (active && b.status.state === 'removed') problems.push(`${where}: ${id} is removed`);
  };
  for (const g of inputs.glossary) for (const id of g.refs) need(id, `glossary term "${g.term}"`, false);
  for (const lb of inputs.lean.blocks) need(lb.id, `Lean block ${lb.decl}`, true);
  for (const c of inputs.lean.citations) need(c.id, `citation ${c.theorem}`, true);
  for (const d of inputs.defects) for (const id of d.requirements) need(id, `defect ${d.id}`, true);
  for (const { situation, result } of inputs.situations) {
    for (const id of situation.cites) need(id, `situation ${situation.slug}`, true);
    for (const step of result?.steps ?? []) if (step.kind === 'blocked') need(step.requirement, `situation ${situation.slug} step ${step.index + 1}`, true);
  }
  for (const b of inputs.spec.blocks) {
    if (b.status.state !== 'removed' && inputs.coverage[b.id] === undefined) problems.push(`coverage matrix: no row for ${b.id}`);
  }
  for (const id of Object.keys(inputs.coverage).sort(byString)) need(id, 'coverage matrix', true);
  const units = inputs.spec.units ?? new Map<ReqId, never>();
  for (const lb of inputs.lean.blocks) {
    if (lb.source !== 'verbatim') continue;
    const u = units.get(lb.id) ?? [];
    for (const q of lb.quotes) if (!quotePresent(q, u)) problems.push(`Lean block ${lb.decl}: quote is not text of ${lb.id}: ${JSON.stringify(q.slice(0, 80))}`);
  }
  return problems;
}

/**
 * Defect evidence names as the ledger writes them (`EXEC_021_forbids_validateTimeout`) become
 * full theorem names when exactly one evidence or cited theorem ends with that name; others
 * (a definition, an assumption) stay as written.
 */
export function resolveDefectEvidence(defects: readonly Defect[], lean: LeanInput): readonly Defect[] {
  const theorems = sortedTheorems(lean);
  const resolve = (name: string): string => {
    const hits = theorems.filter((t) => t === name || t.endsWith(`.${name}`));
    return hits.length === 1 ? (hits[0] ?? name) : name;
  };
  return defects.map((d) => ({ ...d, evidence: d.evidence.map(resolve) }));
}

function sortedTheorems(lean: LeanInput): string[] {
  const names = new Set<string>();
  for (const b of lean.blocks) for (const e of b.evidence) names.add(e.theorem);
  for (const c of lean.citations) names.add(c.theorem);
  return [...names].sort(byString);
}

/** Throws one error listing every problem of `inputProblems`. */
export function checkSiteInputs(inputs: SiteInputs): void {
  const problems = inputProblems(inputs);
  if (problems.length > 0) throw new Error(`the site inputs disagree:\n  ${problems.join('\n  ')}`);
}

/**
 * Assembles the page data. Inputs read from disk (`readSpec` sets `spec.units`) are checked
 * with `checkSiteInputs` first; hand-built test fixtures, which leave `units` out, are not.
 */
export function buildSiteData(inputs: SiteInputs): SiteData {
  if (inputs.spec.units !== undefined) checkSiteInputs(inputs);
  const specOrder = new Map(inputs.spec.blocks.filter((b) => b.status.state !== 'removed').map((b, i) => [b.id, i] as const));
  const situations = situationEntries(inputs.situations, inputs.diagrams, specOrder);
  const defects = resolveDefectEvidence(inputs.defects, inputs.lean);
  const data: Omit<SiteData, 'contentHash'> = {
    schema: 1,
    counts: buildCounts(inputs.spec, inputs.glossary, inputs.lean, inputs.coverage, defects, situations),
    links: SITE_LINKS,
    files: inputs.spec.files,
    blocks: inputs.spec.blocks,
    glossary: inputs.glossary,
    lean: groupLean(inputs.lean.blocks),
    citations: inputs.lean.citations,
    coverage: inputs.coverage,
    defects,
    situations,
    edges: buildEdges(inputs.spec, inputs.lean, defects, situations),
  };
  return { ...data, contentHash: contentHashOf(data) };
}
