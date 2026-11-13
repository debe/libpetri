/**
 * A small SiteData for the conformance and graph tests, assembled by the real `buildSiteData`
 * so the edges and counts are the generator's own.
 *
 *   CORE-001 Place      Lean block (holds, forbids)   Java + TS tested
 *   CORE-002 Token      Lean mention                  untested everywhere          depends on CORE-001
 *   CORE-003            removed (tombstone)
 *   CORE-004 Arc        Lean block (holds)            all tested, RD-01 open (TS, Python)
 *                                                     depends on CORE-002, mentions CORE-001, uses term inhibitor-arc
 *   IO-001   Input      cited by one theorem          untested everywhere          depends on CORE-004
 *   IO-002   Output     no Lean                       Rust tested, RD-02 fixed     depends on IO-001, mentions CORE-002
 *   situation s1 cites CORE-004
 */
import type { AppContext } from '../src/app/context.js';
import { buildIndex } from '../src/app/indexes.js';
import type { CoverageRow, Defect, GlossaryTerm, LeanBlock, ReqId, ReqKind, Runtime, SiteData, SpecBlock } from '../src/model.js';
import { buildSiteData } from '../src/gen/site.js';

function block(id: ReqId, title: string, file: string, line: number, kind: ReqKind | null, more: Partial<SpecBlock> = {}): SpecBlock {
  return {
    id,
    title,
    file,
    line,
    section: null,
    priority: 'MUST',
    kind,
    status: { state: 'active' },
    body: [{ kind: 'shall', text: `${title} shall hold.` }],
    acceptance: [],
    notes: [],
    dependsOn: [],
    mentions: [],
    testDerivation: null,
    terms: [],
    ...more,
  };
}

function cov(id: ReqId, tested: Partial<Record<Runtime, readonly string[]>>, leanRef = false): CoverageRow {
  const t = (r: Runtime): CoverageRow['tests'][Runtime] => {
    const refs = tested[r];
    return refs === undefined ? { state: 'untested' } : { state: 'tested', refs };
  };
  return { id, leanProofs: [], leanRef, tests: { java: t('java'), typescript: t('typescript'), rust: t('rust'), python: t('python') } };
}

function lean(id: ReqId, evidence: LeanBlock['evidence']): LeanBlock {
  return {
    id,
    title: id,
    decl: `Libpetri.Spec.${id.replace('-', '_')}`,
    module: `Libpetri.Spec.Req.${id.replace('-', '_')}`,
    kind: 'B',
    sourceRef: 'spec/01-core-model.md',
    source: 'verbatim',
    scope: 'all executors',
    quotes: [],
    reading: [],
    assumes: [],
    statement: 'True',
    signoff: { state: 'pending' },
    hash: '0123456789abcdef',
    evidence,
  };
}

const term: GlossaryTerm = { term: 'Inhibitor arc', slug: 'inhibitor-arc', group: 'Glossary: arcs', text: 'An arc that blocks.', refs: ['CORE-004'] };

const defects: readonly Defect[] = [
  {
    id: 'RD-01',
    title: 'Arc ignored',
    requirements: ['CORE-004'],
    runtimes: ['typescript', 'python'],
    text: 'The arc is ignored.',
    evidence: [],
    evidenceText: 'None.',
    fix: null,
    status: { state: 'open' },
  },
  {
    id: 'RD-02',
    title: 'Output lost',
    requirements: ['IO-002'],
    runtimes: ['java'],
    text: 'Lost.',
    evidence: [],
    evidenceText: 'None.',
    fix: null,
    status: { state: 'fixed', version: '2.0.0' },
  },
];

export function fixtureData(): SiteData {
  const C = '01-core-model.md';
  const I = '03-io.md';
  const blocks = [
    block('CORE-001', 'Place', C, 10, 'B'),
    block('CORE-002', 'Token', C, 20, 'F', { dependsOn: ['CORE-001'] }),
    block('CORE-003', 'Old rule', C, 30, null, { status: { state: 'removed' }, priority: null }),
    block('CORE-004', 'Arc', C, 40, 'B', { dependsOn: ['CORE-002'], mentions: ['CORE-001'], terms: ['inhibitor-arc'] }),
    block('IO-001', 'Input', I, 10, 'T', { dependsOn: ['CORE-004'] }),
    block('IO-002', 'Output', I, 20, 'B', { dependsOn: ['IO-001'], mentions: ['CORE-002'] }),
  ];
  return buildSiteData({
    spec: {
      files: [
        { file: C, number: '01', title: 'Core Model', prefixes: ['CORE'], sections: [{ title: 'Places', ids: ['CORE-001', 'CORE-002', 'CORE-003', 'CORE-004'] }] },
        { file: I, number: '03', title: 'Input and Output', prefixes: ['IO'], sections: [{ title: 'Arcs', ids: ['IO-001', 'IO-002'] }] },
      ],
      blocks,
    },
    glossary: [term],
    lean: {
      blocks: [
        lean('CORE-001', [
          { theorem: 'Libpetri.Spec.CORE_001_holds', role: 'holds', module: 'Libpetri.Spec.Req.CORE_001', doc: 'Example: a place.' },
          { theorem: 'Libpetri.Spec.CORE_001_forbids', role: 'forbids', module: 'Libpetri.Spec.Req.CORE_001', doc: null },
        ]),
        lean('CORE-004', [{ theorem: 'Libpetri.Spec.CORE_004_holds', role: 'holds', module: 'Libpetri.Spec.Req.CORE_004', doc: null }]),
      ],
      citations: [{ id: 'IO-001', theorem: 'Libpetri.Spec.io_fragment', module: 'Libpetri.IO', fragment: 'one input arc' }],
    },
    coverage: {
      'CORE-001': cov('CORE-001', { java: ['java/src/test/PlaceTest.java'], typescript: [] }),
      'CORE-002': cov('CORE-002', {}, true),
      'CORE-004': cov('CORE-004', { java: [], typescript: [], rust: [], python: [] }),
      'IO-001': cov('IO-001', {}),
      'IO-002': cov('IO-002', { rust: ['rust/tests/io.rs'] }),
    },
    defects,
    situations: [
      {
        situation: {
          slug: 's1',
          title: 'Blocked arc',
          text: 'An arc blocks.',
          group: 'Firing',
          cites: ['CORE-004'],
          replay: false,
          notReplayed: 'timed',
          net: { places: [], marking: {}, transitions: [], properties: [] },
          steps: [],
        },
        result: null,
      },
    ],
    diagrams: new Set(),
  });
}

/** A context over the fixture; `navigate` records the routes it was given. */
export function fixtureCtx(data: SiteData = fixtureData()): AppContext & { readonly navigations: unknown[] } {
  const navigations: unknown[] = [];
  return {
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
}
