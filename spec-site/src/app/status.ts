/**
 * Shared status derivations and their display metadata (design 3.3, 3.4), so every view shows
 * the same glyph, word and tone for the same fact. Pure functions over `AppContext`.
 *
 * Owner: skeleton (core). Views import; changes go through the integrator.
 */
import type { Defect, EvidenceRole, ReqId, Runtime } from '../model.js';
import type { AppContext } from './context.js';

/** Colour family of a status: a CSS token pair `--<tone>` / `--<tone>-bg`. */
export type Tone = 'ok' | 'bad' | 'mutant' | 'nonvac' | 'conflict' | 'consistent' | 'open' | 'defect' | 'none';

export interface StatusMeta {
  readonly glyph: string;
  /** The word shown next to the glyph. */
  readonly word: string;
  readonly tone: Tone;
  /** Tooltip and screen-reader sentence. */
  readonly explain: string;
}

/** Evidence roles in the reader's fixed order (design 3.3), with their display. */
export const ROLE_META: { readonly [R in EvidenceRole]: StatusMeta } = {
  holds: { glyph: '✓', word: 'holds', tone: 'ok', explain: 'Holds of the reference model' },
  nonvacuous: { glyph: '◉', word: 'nonvacuous', tone: 'nonvac', explain: 'The premises can be met: the model has a case it applies to' },
  allows: { glyph: '✓', word: 'allows', tone: 'ok', explain: 'The requirement permits this behaviour' },
  total: { glyph: '✓', word: 'total', tone: 'ok', explain: 'An outcome exists in every covered case' },
  consistent: { glyph: '⇄', word: 'consistent', tone: 'consistent', explain: 'These requirements can all hold together' },
  forbids: { glyph: '✗', word: 'forbids', tone: 'bad', explain: 'A concrete wrong semantics breaks the requirement' },
  violated: { glyph: '✗', word: 'violated', tone: 'bad', explain: 'The named model breaks the requirement' },
  mutant: { glyph: '✗m', word: 'mutant killed', tone: 'mutant', explain: 'A plausible wrong reading is told apart from the requirement' },
  conflict: { glyph: '⊥', word: 'conflict', tone: 'conflict', explain: 'These requirements cannot all hold together' },
  undecided: { glyph: '?', word: 'undecided', tone: 'open', explain: 'An open question the spec does not settle' },
  ambiguity: { glyph: '?', word: 'ambiguity', tone: 'open', explain: 'An open question the spec does not settle' },
};

/** The order role groups appear in (design 3.3), `ROLE_META`'s key order. */
export const ROLE_ORDER: readonly EvidenceRole[] = [
  'holds', 'nonvacuous', 'allows', 'total', 'consistent', 'forbids', 'violated', 'mutant', 'conflict', 'undecided', 'ambiguity',
];

export const RUNTIME_LABEL: { readonly [R in Runtime]: string } = {
  java: 'Java',
  typescript: 'TypeScript',
  rust: 'Rust',
  python: 'Python',
};

/** Lean column state of a requirement (design 3.4). */
export type LeanState = 'block' | 'cited' | 'mention' | 'none';

export const LEAN_META: { readonly [S in LeanState]: StatusMeta } = {
  block: { glyph: '◆', word: 'Lean block', tone: 'ok', explain: 'A Lean requirement block states it' },
  cited: { glyph: '◇', word: 'cited', tone: 'consistent', explain: 'Only theorem fragments cite it' },
  mention: { glyph: '·', word: 'mentioned', tone: 'none', explain: 'Lean comments mention the ID; nothing proved' },
  none: { glyph: '–', word: 'none', tone: 'none', explain: 'Lean does not mention this rule' },
};

export function leanState(ctx: AppContext, id: ReqId): LeanState {
  if (ctx.index.lean(id).length > 0) return 'block';
  if ((ctx.index.citationsByReq.get(id) ?? []).length > 0) return 'cited';
  if (ctx.data.coverage[id]?.leanRef === true) return 'mention';
  return 'none';
}

/** A runtime column state; an open defect overrides tested / untested. */
export type TestState =
  | { readonly state: 'defect'; readonly defects: readonly Defect[] }
  | { readonly state: 'tested'; readonly refs: readonly string[] }
  | { readonly state: 'untested' };

export const TEST_META: { readonly [S in TestState['state']]: StatusMeta } = {
  defect: { glyph: '⚠', word: 'open defect', tone: 'defect', explain: 'The runtime breaks the rule; ledger entry open' },
  tested: { glyph: '✓', word: 'tested', tone: 'ok', explain: 'At least one test file in this language cites the ID' },
  untested: { glyph: '○', word: 'untested', tone: 'none', explain: 'No test file cites it' },
};

/** The honesty sentence shown under every test status (design 3.4). */
export const TESTED_MEANS = 'Tested means a test file cites the ID. It is a reference, not a proof of coverage.';

export function openDefects(ctx: AppContext, id: ReqId, runtime?: Runtime): readonly Defect[] {
  return (ctx.index.defectsByReq.get(id) ?? []).filter(
    (d) => d.status.state === 'open' && (runtime === undefined || d.runtimes.includes(runtime)),
  );
}

export function testState(ctx: AppContext, id: ReqId, runtime: Runtime): TestState {
  const defects = openDefects(ctx, id, runtime);
  if (defects.length > 0) return { state: 'defect', defects };
  const cov = ctx.data.coverage[id]?.tests[runtime];
  return cov?.state === 'tested' ? { state: 'tested', refs: cov.refs } : { state: 'untested' };
}

/** "Proved in Lean" for card counts (design 12): a Lean block with a `holds` theorem. */
export function provedInLean(ctx: AppContext, id: ReqId): boolean {
  return ctx.index.lean(id).some((b) => b.evidence.some((e) => e.role === 'holds'));
}
