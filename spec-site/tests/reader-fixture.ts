/**
 * A small hand-written `SiteData` and an `AppContext` over it, for the reader, md and search
 * tests. Shapes follow `src/model.ts`; the texts are taken from the real spec and Lean report.
 */
import type { AppContext } from '../src/app/context.js';
import { buildIndex } from '../src/app/indexes.js';
import type { NavigateOptions, Route } from '../src/app/router.js';
import type { CoverageRow, LeanBlock, SiteData, SpecBlock } from '../src/model.js';

const untested = { state: 'untested' } as const;

function cov(id: string, tested: readonly ('java' | 'typescript' | 'rust' | 'python')[], leanRef = false): CoverageRow {
  const t = (r: 'java' | 'typescript' | 'rust' | 'python') => (tested.includes(r) ? { state: 'tested' as const, refs: r === 'rust' ? ['rust/libpetri-core/tests/arcs.rs'] : [] } : untested);
  return { id, leanProofs: [], leanRef, tests: { java: t('java'), typescript: t('typescript'), rust: t('rust'), python: t('python') } };
}

function block(over: Partial<SpecBlock> & Pick<SpecBlock, 'id' | 'title' | 'file' | 'line'>): SpecBlock {
  return {
    section: null,
    priority: 'MUST',
    kind: 'B',
    status: { state: 'active' },
    body: [],
    acceptance: [],
    notes: [],
    dependsOn: [],
    mentions: [],
    testDerivation: null,
    terms: [],
    ...over,
  };
}

const core031Lean: LeanBlock = {
  id: 'CORE-031',
  title: 'Inhibitor arc',
  decl: 'Libpetri.Spec.CORE_031',
  module: 'Libpetri.Spec.Core',
  kind: 'B',
  sourceRef: 'spec/01-core-model.md',
  source: 'verbatim',
  scope: 'all executors',
  quotes: [
    '*While* an inhibitor place of a transition is marked, the transition *shall not* fire.',
    '*While* an inhibitor place of a transition is unmarked, the inhibitor arc *shall not* affect whether the transition can fire.',
  ],
  reading: [
    'For every transition t and every inhibitor place p of t:',
    't does not fire from a marking in which p is marked;',
    "from a marking m in which p is unmarked, t fires to m' exactly when t without its inhibitor arcs on p fires from m to m'.",
  ],
  assumes: ['A firing is read as one step from a marking to a marking (glossary: Fire).'],
  statement: 'fun {N} [DecidableEq N] F ↦\n  ∀ (t : Reference.Trans N) (p : N),\n    InhibitorArc t p →\n      (while fun m ↦ Marked m p, never Fire F t)',
  signoff: { state: 'signed', date: '2026-11-10', hash: '4f884470bf67c07e' },
  hash: '4f884470bf67c07e',
  evidence: [
    { theorem: 'Libpetri.Spec.CORE_031_reference', role: 'holds', module: 'Libpetri.Spec.Core', doc: 'The reference semantics satisfies CORE-031: `Seam.enabledNA` requires every inhibitor place to be empty.' },
    { theorem: 'Libpetri.Spec.CORE_031_forbids_ignoresInhibitor', role: 'forbids', module: 'Libpetri.Spec.Core', doc: '✗ Ignoring the inhibitor arc violates CORE-031.' },
    { theorem: 'Libpetri.Spec.CORE_031_mutant_a', role: 'mutant', module: 'Libpetri.Spec.Core', doc: null },
    { theorem: 'Libpetri.Spec.CORE_031_nonvacuous', role: 'nonvacuous', module: 'Libpetri.Spec.Core', doc: null },
  ],
};

const conc005: LeanBlock = {
  ...core031Lean,
  id: 'CONC-005',
  title: 'Dirty Set Optimization',
  decl: 'Libpetri.Spec.CONC_005',
  module: 'Libpetri.Spec.Req.CONC_005',
  sourceRef: 'spec/05-concurrency.md',
  quotes: ['*When* a firing writes one of a transition\'s arc places, the executor *shall* re-run the check.'],
  reading: ['For every timed net X:', 'line one;', 'line two;'],
  signoff: { state: 'pending' },
  hash: '1441f040342f4b81',
  evidence: [{ theorem: 'Libpetri.Spec.CONC_005_reference', role: 'holds', module: 'Libpetri.Spec.Req.CONC_005', doc: null }],
};

const conc005Cycle: LeanBlock = {
  ...conc005,
  title: 'Dirty Set Optimization (executor cycle)',
  decl: 'Libpetri.Spec.CONC_005_cycle',
  module: 'Libpetri.Spec.Req.CONC_005_cycle',
  evidence: [{ theorem: 'Libpetri.Spec.CONC_005_cycle_reference', role: 'holds', module: 'Libpetri.Spec.Req.CONC_005_cycle', doc: null }],
};

export const BLOCKS: readonly SpecBlock[] = [
  block({
    id: 'CORE-030',
    title: 'Input Arc',
    file: '01-core-model.md',
    line: 250,
    body: [{ kind: 'shall', text: '*When* a transition fires, it *shall* consume from each input place.' }],
    acceptance: ['Tokens are consumed.'],
  }),
  block({
    id: 'CORE-031',
    title: 'Inhibitor Arc',
    file: '01-core-model.md',
    line: 275,
    dependsOn: ['CORE-030'],
    body: [
      { kind: 'prose', text: 'An inhibitor arc connects a place to a transition as a **negative precondition**.' },
      { kind: 'shall', text: '*While* an inhibitor place of a transition is marked, the transition *shall not* fire.' },
      { kind: 'prose', text: 'The inhibitor arc does not consume tokens; see [CORE-030].' },
    ],
    acceptance: ['Inhibitor place empty → transition enablement unaffected by inhibitor.', 'Inhibitor place has tokens → transition disabled.'],
    notes: [{ label: 'Note', text: 'Compare `Out.Timeout` <b>never</b> markup.' }],
    mentions: ['CORE-030'],
    testDerivation: 'Create transition with inhibitor; verify disabled when inhibitor place has tokens.',
    terms: ['inhibitor-arc', 'marked', 'place'],
  }),
  block({ id: 'IO-001', title: 'Exactly One', file: '02-input-output-specs.md', line: 10, kind: 'F', body: [{ kind: 'shall', text: 'A transition *shall* consume one token.' }] }),
  block({
    id: 'IO-006',
    title: 'Input Guard Predicate',
    file: '02-input-output-specs.md',
    line: 147,
    status: { state: 'removed' },
    priority: null,
    kind: null,
    body: [{ kind: 'prose', text: 'Removed: guards are gone, see [NU-021].' }],
    mentions: ['NU-021'],
  }),
  block({ id: 'CONC-005', title: 'Dirty Set Optimization', file: '05-concurrency.md', line: 90, dependsOn: ['CORE-031'], body: [{ kind: 'shall', text: 'The executor *shall* re-run checks.' }] }),
  block({ id: 'NU-021', title: 'Match as the Sole Per-Token Filter', file: '12-nu-nets.md', line: 40, kind: 'F', body: [{ kind: 'shall', text: 'The ν match *shall* be the only filter.' }] }),
];

export function fixtureData(): SiteData {
  return {
    schema: 1,
    contentHash: '000000000000',
    counts: {
      specFiles: 4,
      activeIds: 5,
      removedIds: 1,
      proposedIds: 0,
      leanBlocks: 3,
      leanIds: 2,
      signedBlocks: 1,
      citedIds: 1,
      openDefects: 1,
      situations: 1,
      replayed: 1,
      glossaryTerms: 3,
      untestedIds: 2,
    },
    links: { repo: 'https://github.com/debe/libpetri', blob: 'https://github.com/debe/libpetri/blob/main/', proofGraph: '../proof-graph/', home: '../' },
    files: [
      { file: '01-core-model.md', number: '01', title: 'Core Model', prefixes: ['CORE'], sections: [{ title: 'Arcs', ids: ['CORE-030', 'CORE-031'] }] },
      { file: '02-input-output-specs.md', number: '02', title: 'Input and Output Specs', prefixes: ['IO'], sections: [{ title: 'Inputs', ids: ['IO-001', 'IO-006'] }] },
      { file: '05-concurrency.md', number: '05', title: 'Concurrency', prefixes: ['CONC'], sections: [{ title: 'Checks', ids: ['CONC-005'] }] },
      { file: '12-nu-nets.md', number: '12', title: 'ν-Nets', prefixes: ['NU'], sections: [{ title: 'Match', ids: ['NU-021'] }] },
    ],
    blocks: BLOCKS,
    glossary: [
      { term: 'Place', slug: 'place', group: 'Glossary: firing semantics', text: 'A named container that holds tokens [CORE-001].', refs: ['CORE-001'] },
      { term: 'Marked', slug: 'marked', group: 'Glossary: firing semantics', text: 'A place is marked when its token count is not zero.', refs: [] },
      { term: 'Inhibitor arc', slug: 'inhibitor-arc', group: 'Glossary: firing semantics', text: 'An arc that blocks a transition while its place is marked [CORE-031].', refs: ['CORE-031'] },
    ],
    lean: { 'CORE-031': [core031Lean], 'CONC-005': [conc005, conc005Cycle] },
    citations: [{ id: 'IO-001', theorem: 'Libpetri.Spec.io001_consume_one', module: 'Libpetri.Spec.Req.IO_001', fragment: 'one token is consumed' }],
    coverage: {
      'CORE-030': cov('CORE-030', ['java', 'typescript', 'rust']),
      'CORE-031': cov('CORE-031', ['java', 'typescript', 'rust']),
      'CONC-005': cov('CONC-005', []),
      'IO-001': cov('IO-001', ['rust']),
      'NU-021': cov('NU-021', [], true),
    },
    defects: [
      {
        id: 'RD-01',
        title: 'Java fires through a marked inhibitor',
        requirements: ['CORE-031'],
        runtimes: ['java'],
        text: 'The Java executor ignores the inhibitor arc.',
        evidence: ['Libpetri.Spec.CORE_031_forbids_ignoresInhibitor'],
        evidenceText: '`CORE_031_forbids_ignoresInhibitor`',
        status: { state: 'open' },
      },
    ],
    situations: [],
    edges: [{ kind: 'depends-on', from: 'CORE-031', to: 'CORE-030' }],
  };
}

export interface FixtureContext extends AppContext {
  readonly navigations: { route: Route; options: NavigateOptions | undefined }[];
}

export function fixtureContext(data: SiteData = fixtureData()): FixtureContext {
  const navigations: { route: Route; options: NavigateOptions | undefined }[] = [];
  const ctx: FixtureContext = {
    data,
    index: buildIndex(data),
    render: () => {
      throw new Error('render is not used in these tests');
    },
    navigate: (route, options) => {
      navigations.push({ route, options });
    },
    navigations,
  };
  return ctx;
}
