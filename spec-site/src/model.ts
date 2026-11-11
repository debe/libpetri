/**
 * The data model of the spec site, shared by the generator (Node) and the app (browser).
 *
 * Rules every type here follows:
 * - Everything is `readonly`. The app never mutates `SiteData`.
 * - No optional properties: an absent value is `null`, an absent list is `[]`. The JSON the
 *   generator writes therefore has every key, which keeps it deterministic and lets the
 *   decoder in `decode-site.ts` reject unknown and missing keys alike.
 * - Variants are discriminated unions on a `kind` (or `state`, `type`) field.
 * - Maps keyed by an ID are `Readonly<Record<string, T>>`; with `noUncheckedIndexedAccess` a
 *   lookup is `T | undefined`, so a missing ID is handled at every use.
 *
 * Changing a type here is a contract change: update `src/decode-site.ts` in the same edit (the
 * compiler fails until the two agree) and the shape notes in the contracts file.
 */

// ---------------------------------------------------------------------------------------------
// Identifiers. Plain strings, named for documentation.
// ---------------------------------------------------------------------------------------------

/** A requirement ID such as `CORE-001`. */
export type ReqId = string;
/** A fully qualified Lean declaration name such as `Libpetri.Spec.CONC_001_reference`. */
export type TheoremName = string;
/** A runtime defect ID such as `RD-01`. */
export type DefectId = string;
/** A situation slug: the file name of `spec/situations/<slug>.json`, `[a-z0-9-]+`. */
export type SituationSlug = string;
/** A place or transition name inside a situation net. */
export type NodeName = string;

/** The four runtimes the conformance matrix tracks, in display order. */
export const RUNTIMES = ['java', 'typescript', 'rust', 'python'] as const;
export type Runtime = (typeof RUNTIMES)[number];

// ---------------------------------------------------------------------------------------------
// Spec files and blocks (spec/NN-*.md)
// ---------------------------------------------------------------------------------------------

export const PRIORITIES = ['MUST', 'SHOULD', 'MAY'] as const;
export type Priority = (typeof PRIORITIES)[number];

/**
 * Requirement kind, from a block's `**Kind:**` line and the Lean block's `kind` field:
 * A = assumption, B = behaviour, F = function, T = timing, Q = quality (tested, not proven),
 * N = configuration.
 * The legend text lives in the app; the letter is the data.
 */
export const REQ_KINDS = ['A', 'B', 'F', 'T', 'Q', 'N'] as const;
export type ReqKind = (typeof REQ_KINDS)[number];

/** One spec file such as `01-core-model.md`. */
export interface SpecFile {
  /** File name relative to `spec/`, e.g. `01-core-model.md`. */
  readonly file: string;
  /** Two-digit number, e.g. `01`. */
  readonly number: string;
  /** Title from the file's `#` heading without the number, e.g. `Core Model`. */
  readonly title: string;
  /** ID prefixes the file defines, e.g. `["CORE"]`. */
  readonly prefixes: readonly string[];
  /** `##` sections in file order, each with the IDs it holds (tombstones included). */
  readonly sections: readonly SpecSection[];
}

export interface SpecSection {
  readonly title: string;
  readonly ids: readonly ReqId[];
}

/** A block's lifecycle, from its `**Status:**` line and the index. */
export type BlockStatus =
  | { readonly state: 'active' }
  /** `**Status:** Proposed`: some implementation has not built it yet. */
  | { readonly state: 'proposed' }
  /** A struck-through tombstone in `spec/00-index.md` (`**Status:** Removed`). */
  | { readonly state: 'removed' };

/**
 * A paragraph of a block's normative body (the text between the metadata lines and the
 * acceptance criteria). Text is the raw Markdown of the paragraph: wrapped lines are joined,
 * list items keep one line each; `md.ts` renders it. A paragraph containing the word *shall* is
 * a `shall` paragraph: the statement the Lean block quotes. A fenced code block is `code`, its
 * text the lines between the fences (no backticks). Others are `prose` (definitions, context).
 */
export type BodyParagraph =
  | { readonly kind: 'prose'; readonly text: string }
  | { readonly kind: 'shall'; readonly text: string }
  | { readonly kind: 'code'; readonly text: string };

/** A free-form labelled note such as `**Note:**` or `**Implementation notes:**`. */
export interface BlockNote {
  /** The label without the colon, e.g. `Note`, `Implementation notes`, `Divergence`. */
  readonly label: string;
  /** Markdown text of the note (may span paragraphs, joined with `\n\n`). */
  readonly text: string;
}

/** One `#### ID: Title` block of a spec file. */
export interface SpecBlock {
  readonly id: ReqId;
  readonly title: string;
  /** File name relative to `spec/`. */
  readonly file: string;
  /** 1-based line of the `#### ID:` heading. */
  readonly line: number;
  /** The `##` section the block sits in, or null before the first section. */
  readonly section: string | null;
  readonly priority: Priority | null;
  /** Null when the block has no `**Kind:**` line. */
  readonly kind: ReqKind | null;
  readonly status: BlockStatus;
  readonly body: readonly BodyParagraph[];
  /** Acceptance criteria in order, Markdown, without the list numbers. */
  readonly acceptance: readonly string[];
  readonly notes: readonly BlockNote[];
  /** IDs from the `**Depends on:**` line, in order. */
  readonly dependsOn: readonly ReqId[];
  /** Every `[ID]` cited anywhere in the block other than in `dependsOn`, sorted, unique. */
  readonly mentions: readonly ReqId[];
  readonly testDerivation: string | null;
  /** Glossary term slugs whose term occurs in the body, sorted. */
  readonly terms: readonly string[];
}

// ---------------------------------------------------------------------------------------------
// Glossary (spec/glossary.md)
// ---------------------------------------------------------------------------------------------

export interface GlossaryTerm {
  /** The `### Term` heading text, e.g. `Token count`. */
  readonly term: string;
  /** Lower-case kebab slug, e.g. `token-count`. Unique. */
  readonly slug: string;
  /** The enclosing `#` or `##` heading, e.g. `Glossary: firing semantics`. */
  readonly group: string;
  /** Markdown definition. */
  readonly text: string;
  /** IDs cited in the definition, in order of first mention. */
  readonly refs: readonly ReqId[];
}

// ---------------------------------------------------------------------------------------------
// Lean requirement blocks (lean/report/requirements.json)
// ---------------------------------------------------------------------------------------------

/**
 * Evidence roles that `requirements.json` uses. A role the generator does not know fails the
 * build: add it here (and its label in the app) rather than dropping it.
 */
export const EVIDENCE_ROLES = [
  'holds',
  'forbids',
  'mutant',
  'consistent',
  'nonvacuous',
  'allows',
  'undecided',
  'total',
  // Roles the design has glyphs for; not used by requirements.json today.
  'violated',
  'conflict',
  'ambiguity',
] as const;
export type EvidenceRole = (typeof EVIDENCE_ROLES)[number];

export interface Evidence {
  readonly theorem: TheoremName;
  readonly role: EvidenceRole;
  /** Lean module, e.g. `Libpetri.Spec.Req.CONC_001`. */
  readonly module: string;
  /** The theorem's docstring (its worked example), or null when it has none. */
  readonly doc: string | null;
}

export type Signoff =
  | { readonly state: 'pending' }
  /** Parsed from `"2026-11-10 104625b4eefcf18b"`: date and the statement hash signed. */
  | { readonly state: 'signed'; readonly date: string; readonly hash: string };

/** One Lean requirement block. An ID may have several (companion blocks). */
export interface LeanBlock {
  readonly id: ReqId;
  readonly title: string;
  /** Declaration of the block, e.g. `Libpetri.Spec.CONC_001`. Unique across blocks. */
  readonly decl: TheoremName;
  readonly module: string;
  readonly kind: ReqKind;
  /** `spec/05-concurrency.md`. */
  readonly sourceRef: string;
  /** `verbatim` today; kept as text. */
  readonly source: string;
  readonly scope: string;
  /** Spec sentences the block formalises, verbatim. */
  readonly quotes: readonly string[];
  /** Plain-words reading of the Lean statement, line by line. */
  readonly reading: readonly string[];
  readonly assumes: readonly string[];
  /** Pretty-printed Lean statement. */
  readonly statement: string;
  readonly signoff: Signoff;
  /** 16-hex statement hash. */
  readonly hash: string;
  readonly evidence: readonly Evidence[];
}

/** A theorem tagged `@[evidence cites "ID" "fragment"]` (requirements.json `citations`). */
export interface Citation {
  readonly id: ReqId;
  readonly theorem: TheoremName;
  readonly module: string;
  /** The honest scope of the claim. */
  readonly fragment: string;
}

// ---------------------------------------------------------------------------------------------
// Coverage (spec/coverage-matrix.md, lean/report/proof-coverage.json)
// ---------------------------------------------------------------------------------------------

/** A Lean theorem proving a fragment of a requirement (the matrix's "Lean proof" column). */
export interface LeanProof {
  readonly theorem: TheoremName;
  readonly fragment: string;
}

export type TestCoverage =
  /** `refs`: test file paths relative to the repo root; may be empty when only the matrix tick is known. */
  | { readonly state: 'tested'; readonly refs: readonly string[] }
  | { readonly state: 'untested' };

export interface CoverageRow {
  readonly id: ReqId;
  readonly leanProofs: readonly LeanProof[];
  /** The ID appears in Lean comments (weaker than a proof). */
  readonly leanRef: boolean;
  readonly tests: { readonly [R in Runtime]: TestCoverage };
}

// ---------------------------------------------------------------------------------------------
// Runtime defects (spec/runtime-defects.md)
// ---------------------------------------------------------------------------------------------

export type DefectStatus =
  | { readonly state: 'open' }
  | { readonly state: 'fixed'; readonly version: string };

export interface Defect {
  /** `RD-01`. */
  readonly id: DefectId;
  /** The `### RD-01. <title>` heading text after the ID. */
  readonly title: string;
  readonly requirements: readonly ReqId[];
  readonly runtimes: readonly Runtime[];
  /** Markdown of the `**Defect:**` item. */
  readonly text: string;
  /** Lean theorem names from the `**Lean evidence:**` item; empty when it says none. */
  readonly evidence: readonly TheoremName[];
  /** Markdown of the `**Lean evidence:**` item as written (for the "none beyond" wording). */
  readonly evidenceText: string;
  readonly status: DefectStatus;
}

// ---------------------------------------------------------------------------------------------
// Situation nets: the conformance corpus net schema
// (spec/verification-fixtures/conformance/README.md), normalised: every optional field is
// present, absent = null.
// ---------------------------------------------------------------------------------------------

export type InputArc =
  | { readonly kind: 'one'; readonly place: NodeName }
  | { readonly kind: 'exactly'; readonly place: NodeName; readonly n: number }
  | { readonly kind: 'all'; readonly place: NodeName }
  | { readonly kind: 'atLeast'; readonly place: NodeName; readonly n: number };

export type OutputSpec =
  | { readonly type: 'place'; readonly place: NodeName }
  | { readonly type: 'and'; readonly children: readonly OutputSpec[] }
  | { readonly type: 'xor'; readonly children: readonly OutputSpec[] }
  | { readonly type: 'timeout'; readonly afterMs: number; readonly child: OutputSpec }
  | { readonly type: 'forward'; readonly from: NodeName; readonly to: NodeName };

/** Bounds a kind does not take are null. */
export interface Timing {
  readonly kind: 'immediate' | 'unconstrained' | 'deadline' | 'delayed' | 'window' | 'exact';
  readonly earliestMs: number | null;
  readonly latestMs: number | null;
}

export interface NetTransition {
  readonly name: NodeName;
  readonly inputs: readonly InputArc[];
  readonly inhibitors: readonly NodeName[];
  readonly reads: readonly NodeName[];
  readonly resets: readonly NodeName[];
  /** null = no output. */
  readonly output: OutputSpec | null;
  /** 0 when absent. */
  readonly priority: number;
  /** null = immediate. */
  readonly timing: Timing | null;
}

export type NetProperty =
  | { readonly type: 'deadlock-free'; readonly id: string; readonly sinks: readonly NodeName[] }
  | { readonly type: 'terminates-at-sink'; readonly id: string; readonly sinks: readonly NodeName[] }
  | { readonly type: 'place-bound'; readonly id: string; readonly place: NodeName; readonly bound: number }
  | { readonly type: 'mutual-exclusion'; readonly id: string; readonly places: readonly NodeName[] }
  | { readonly type: 'unreachable'; readonly id: string; readonly places: readonly NodeName[] }
  | {
      readonly type: 'quiescent-count';
      readonly id: string;
      readonly places: readonly NodeName[];
      readonly min: number;
      readonly max: number | null;
    };

/** Token counts per place. Only places with a count above zero, keys sorted. */
export type Marking = Readonly<Record<NodeName, number>>;

export interface CorpusNet {
  /** Declared places, in file order. Arcs may name places not listed (places by use). */
  readonly places: readonly NodeName[];
  readonly marking: Marking;
  readonly transitions: readonly NetTransition[];
  readonly properties: readonly NetProperty[];
}

// ---------------------------------------------------------------------------------------------
// Situations: `spec/situations/<slug>.json` (authored; schema in spec/situations/README.md) and
// `spec/situations/expected/<slug>.json` (written by `lake exe reference situations`, never by
// hand). The model below is the normalised form: optional keys filled with their defaults.
// ---------------------------------------------------------------------------------------------

/** Home page groups, in display order. The authored `group` value is one of these words. */
export const SITUATION_GROUPS = [
  'Firing',
  'Outputs',
  'Time',
  'Running',
  'Correlation',
  'Composition',
  'Verification',
  'Export',
] as const;
export type SituationGroup = (typeof SITUATION_GROUPS)[number];

/**
 * Why a situation is not replayed by Lean (`"replay": false`). Authored as the extra key
 * `"notReplayed"` in the situation file; the player's note names it ("this situation is timed").
 */
export const NOT_REPLAYED = ['timed', 'environment', 'nu-net', 'composition', 'export', 'verification'] as const;
export type NotReplayed = (typeof NOT_REPLAYED)[number];

export interface SituationStep {
  /** The transition to fire. */
  readonly fire: NodeName;
  /** Output branch, numbered as IO-016 enumerates them. Default 0. */
  readonly branch: number;
  /** True when the step ends with the timeout outcome (IO-013). Default false. */
  readonly timeout: boolean;
  /** Caption the player shows for the step, or null. */
  readonly text: string | null;
  /**
   * What the author says the step does: `fired` (default) or `blocked`. The generator fails
   * when the Lean replay of a step does not match, so the verdict box can say the replay agrees.
   */
  readonly expect: StepExpect;
}

export const STEP_EXPECTS = ['fired', 'blocked'] as const;
export type StepExpect = (typeof STEP_EXPECTS)[number];

/** A hand-written example run, as authored (normalised). */
export interface Situation {
  /** File name without `.json`. */
  readonly slug: SituationSlug;
  readonly title: string;
  /** Plain-words explanation (Markdown) shown above the player. */
  readonly text: string;
  readonly group: SituationGroup;
  /** Requirements the situation shows, as authored, in authored order. */
  readonly cites: readonly ReqId[];
  /** True (the default) when the Lean reference replays the steps. */
  readonly replay: boolean;
  /** Set exactly when `replay` is false. */
  readonly notReplayed: NotReplayed | null;
  readonly net: CorpusNet;
  readonly steps: readonly SituationStep[];
}

/** The arc of an `inputShort` reason, as in the net schema. `n` is null for `one` and `all`. */
export interface ReasonArc {
  readonly kind: InputArc['kind'];
  readonly n: number | null;
}

/** Why a step cannot fire (Lean's `Blocked`); kinds as the expected files spell them. */
export type BlockReason =
  | { readonly kind: 'unknownTransition' }
  | { readonly kind: 'inputShort'; readonly place: NodeName; readonly arc: ReasonArc; readonly need: number; readonly have: number }
  | { readonly kind: 'inhibitorMarked'; readonly place: NodeName; readonly count: number }
  | { readonly kind: 'readEmpty'; readonly place: NodeName }
  | { readonly kind: 'noSuchBranch'; readonly branch: number; readonly timeout: boolean };

export type ReplayStep =
  | {
      readonly kind: 'fired';
      /** 0-based index of the authored step. */
      readonly index: number;
      readonly fire: NodeName;
      readonly branch: number;
      readonly timeout: boolean;
      /** Marking after the step. */
      readonly marking: Marking;
    }
  | {
      readonly kind: 'blocked';
      readonly index: number;
      readonly fire: NodeName;
      readonly branch: number;
      readonly timeout: boolean;
      readonly reason: BlockReason;
      /** The requirement the reason cites (CORE-020, IO-001..004, CORE-031, CORE-032, IO-013, IO-016). */
      readonly requirement: ReqId;
      /** Lean's one-sentence message, e.g. "'take' is not enabled: inhibitor place 'lock' holds 1 token". */
      readonly message: string;
    };

export interface ReplayResult {
  readonly slug: SituationSlug;
  /** SHA-256 content hash of the Lean reference sources. */
  readonly reference: string;
  readonly initial: Marking;
  /** True when every step fired. */
  readonly complete: boolean;
  /** One entry per authored step up to and including the first blocked one. */
  readonly steps: readonly ReplayStep[];
}

/** How a rule is linked to a situation ("Why here" on the rule card). */
export type RuleLink =
  /** Listed in the situation's `cites`. */
  | { readonly kind: 'cited' }
  /** The requirement of the blocked step with this 0-based index. */
  | { readonly kind: 'step'; readonly index: number }
  /** The net uses a feature the requirement governs (see the contracts for the mapping). */
  | { readonly kind: 'exercised' };

export interface SituationRule {
  readonly id: ReqId;
  /** At least one link; order: cited, step, exercised. */
  readonly links: readonly RuleLink[];
}

/** A situation as the site shows it: the authored data plus what the generator derived. */
export interface SituationEntry extends Situation {
  /** Linked rules in spec order (file, then line). */
  readonly rules: readonly SituationRule[];
  /** The Lean replay, or null when `replay` is false. */
  readonly result: ReplayResult | null;
  /** True when the page holds the diagram `<template id="dia-<slug>">` (`diagramTemplateId`). */
  readonly diagram: boolean;
}

// ---------------------------------------------------------------------------------------------
// Graph edges
// ---------------------------------------------------------------------------------------------

export type Edge =
  /** Block `from` lists `to` on its Depends on line. */
  | { readonly kind: 'depends-on'; readonly from: ReqId; readonly to: ReqId }
  /** Block `from` cites `to` in its text (not a dependency). */
  | { readonly kind: 'mentions'; readonly from: ReqId; readonly to: ReqId }
  /** A Lean block of `from` lists theorem `to` as evidence with `role`. */
  | { readonly kind: 'evidence'; readonly from: ReqId; readonly to: TheoremName; readonly role: EvidenceRole }
  /** Theorem `from` carries `@[evidence cites "to"]`. */
  | { readonly kind: 'cites'; readonly from: TheoremName; readonly to: ReqId }
  /** Block `from` uses glossary term (slug) `to`. */
  | { readonly kind: 'uses-term'; readonly from: ReqId; readonly to: string }
  /** Situation `from` exercises requirement `to`. */
  | { readonly kind: 'exercises'; readonly from: SituationSlug; readonly to: ReqId }
  /** Defect `from` breaks requirement `to`. */
  | { readonly kind: 'breaks'; readonly from: DefectId; readonly to: ReqId };

export type EdgeKind = Edge['kind'];

/**
 * A node of the graph view, and its key in routes (`#/graph/<key>`) and in the app's edge index:
 *   requirement `CORE-031` · defect `RD-07` · term `term:<slug>` · theorem `thm:<full name>` ·
 *   situation `sit:<slug>`.
 */
export type GraphNode =
  | { readonly kind: 'req'; readonly id: ReqId }
  | { readonly kind: 'defect'; readonly id: DefectId }
  | { readonly kind: 'term'; readonly slug: string }
  | { readonly kind: 'theorem'; readonly name: TheoremName }
  | { readonly kind: 'situation'; readonly slug: SituationSlug };

export type GraphNodeKey = string;

const DEFECT_ID = /^RD-\d+$/;

export function nodeKey(node: GraphNode): GraphNodeKey {
  switch (node.kind) {
    case 'req':
    case 'defect':
      return node.id;
    case 'term':
      return `term:${node.slug}`;
    case 'theorem':
      return `thm:${node.name}`;
    case 'situation':
      return `sit:${node.slug}`;
  }
}

/** Inverse of `nodeKey`. Any other string is read as a requirement ID (the view checks it exists). */
export function parseNodeKey(key: GraphNodeKey): GraphNode {
  if (key.startsWith('term:')) return { kind: 'term', slug: key.slice(5) };
  if (key.startsWith('thm:')) return { kind: 'theorem', name: key.slice(4) };
  if (key.startsWith('sit:')) return { kind: 'situation', slug: key.slice(4) };
  if (DEFECT_ID.test(key)) return { kind: 'defect', id: key };
  return { kind: 'req', id: key };
}

/** The graph nodes an edge joins. */
export function edgeEnds(edge: Edge): { readonly from: GraphNode; readonly to: GraphNode } {
  switch (edge.kind) {
    case 'depends-on':
    case 'mentions':
      return { from: { kind: 'req', id: edge.from }, to: { kind: 'req', id: edge.to } };
    case 'evidence':
      return { from: { kind: 'req', id: edge.from }, to: { kind: 'theorem', name: edge.to } };
    case 'cites':
      return { from: { kind: 'theorem', name: edge.from }, to: { kind: 'req', id: edge.to } };
    case 'uses-term':
      return { from: { kind: 'req', id: edge.from }, to: { kind: 'term', slug: edge.to } };
    case 'exercises':
      return { from: { kind: 'situation', slug: edge.from }, to: { kind: 'req', id: edge.to } };
    case 'breaks':
      return { from: { kind: 'defect', id: edge.from }, to: { kind: 'req', id: edge.to } };
  }
}

// ---------------------------------------------------------------------------------------------
// The whole site
// ---------------------------------------------------------------------------------------------

export interface SiteCounts {
  /** Numbered spec files (13). */
  readonly specFiles: number;
  /** Active requirements, tombstones excluded (224). */
  readonly activeIds: number;
  readonly removedIds: number;
  readonly proposedIds: number;
  /** Lean requirement blocks (157). */
  readonly leanBlocks: number;
  /** Distinct IDs with a Lean block (138). */
  readonly leanIds: number;
  readonly signedBlocks: number;
  /** IDs with at least one validated `@[evidence cites]` theorem. */
  readonly citedIds: number;
  readonly openDefects: number;
  readonly situations: number;
  /** Situations with a Lean replay result. */
  readonly replayed: number;
  readonly glossaryTerms: number;
  /** Active IDs no test file in any runtime references. */
  readonly untestedIds: number;
}

export interface SiteLinks {
  /** `https://github.com/debe/libpetri`. */
  readonly repo: string;
  /** Prefix for a file view on main, e.g. `https://github.com/debe/libpetri/blob/main/`. */
  readonly blob: string;
  /** Proof graph page; a theorem links to `${proofGraph}#${theorem}`. */
  readonly proofGraph: string;
  /** Landing page, `/`. */
  readonly home: string;
}

export interface SiteData {
  /** Bumped when the shape changes incompatibly. */
  readonly schema: 1;
  /**
   * First 12 hex digits of the SHA-256 of this object's JSON without this field. Shown in the
   * footer. Not a git sha: the committed page must equal a rebuild at the same commit.
   */
  readonly contentHash: string;
  readonly counts: SiteCounts;
  readonly links: SiteLinks;
  readonly files: readonly SpecFile[];
  /** Every block, tombstones included, in file then line order. */
  readonly blocks: readonly SpecBlock[];
  readonly glossary: readonly GlossaryTerm[];
  /** Lean blocks grouped by requirement ID; each list in requirements.json order. */
  readonly lean: Readonly<Record<ReqId, readonly LeanBlock[]>>;
  /** Sorted by id, then theorem. */
  readonly citations: readonly Citation[];
  /** One row per active ID. */
  readonly coverage: Readonly<Record<ReqId, CoverageRow>>;
  readonly defects: readonly Defect[];
  /** In display order: group order of `SITUATION_GROUPS`, then file order within a group. */
  readonly situations: readonly SituationEntry[];
  /** Sorted by kind, from, to (deterministic). */
  readonly edges: readonly Edge[];
}

/** The id of the `<template>` that holds the pre-rendered SVG diagram of a situation. */
export function diagramTemplateId(slug: SituationSlug): string {
  return `dia-${slug}`;
}

/** The id of the `<script type="application/json">` element holding `SiteData`. */
export const SITE_DATA_ELEMENT_ID = 'site-data';

/** The id of the element the app mounts into. */
export const APP_ROOT_ID = 'app';
