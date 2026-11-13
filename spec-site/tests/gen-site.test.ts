/** Site assembly from the inputs: exercised rules, cross-input checks, and the real inputs. */
import { describe, expect, it } from 'vitest';
import { decode } from '../src/decode.js';
import { siteData } from '../src/decode-site.js';
import { readCoverage } from '../src/gen/inputs/coverage.js';
import { readDefects } from '../src/gen/inputs/defects.js';
import { readGlossary } from '../src/gen/inputs/glossary.js';
import { readLean } from '../src/gen/inputs/lean.js';
import { readSituations } from '../src/gen/inputs/situations.js';
import { readSpec } from '../src/gen/inputs/spec.js';
import { stableStringify } from '../src/gen/json.js';
import { REPO_ROOT } from '../src/gen/paths.js';
import { buildSiteData, exercisedRules, inputProblems, resolveDefectEvidence, type SiteInputs, situationRules } from '../src/gen/site.js';
import type { Defect, NetTransition, Situation, SpecBlock } from '../src/model.js';

const t = (name: string, extra: Partial<NetTransition> = {}): NetTransition => ({
  name,
  inputs: [{ kind: 'one', place: 'a' }],
  inhibitors: [],
  reads: [],
  resets: [],
  output: { type: 'place', place: 'b' },
  priority: 0,
  timing: null,
  ...extra,
});

const sit = (transitions: NetTransition[], cites: string[] = []): Situation => ({
  slug: 's',
  title: 'S',
  text: 'T.',
  group: 'Firing',
  cites,
  replay: true,
  notReplayed: null,
  net: { places: [], marking: {}, transitions, properties: [] },
  steps: [{ fire: transitions[0]?.name ?? 'x', branch: 0, timeout: false, text: null, expect: 'fired' }],
});

const block = (id: string, state: SpecBlock['status']['state'] = 'active'): SpecBlock => ({
  id,
  title: id,
  file: '01-core-model.md',
  line: 1,
  section: null,
  priority: 'MUST',
  kind: 'B',
  status: { state },
  body: [],
  acceptance: [],
  notes: [],
  dependsOn: [],
  mentions: [],
  testDerivation: null,
  terms: [],
});

describe('exercised rules', () => {
  it('maps net features to the rules that govern them', () => {
    expect(exercisedRules(sit([t('x')]))).toEqual(['IO-001']);
    const rich = t('x', {
      inputs: [
        { kind: 'all', place: 'a' },
        { kind: 'exactly', place: 'c', n: 2 },
      ],
      inhibitors: ['i'],
      reads: ['r'],
      resets: ['z'],
      output: { type: 'xor', children: [{ type: 'and', children: [{ type: 'place', place: 'b' }] }, { type: 'timeout', afterMs: 5, child: { type: 'forward', from: 'a', to: 'b' } }] },
    });
    expect(exercisedRules(sit([rich]))).toEqual(['CORE-031', 'CORE-032', 'CORE-034', 'IO-002', 'IO-003', 'IO-007', 'IO-011', 'IO-012', 'IO-013', 'IO-014', 'IO-016']);
    expect(exercisedRules(sit([t('x'), t('y')]))).toEqual(['CORE-022', 'IO-001']);
  });

  it('links rules cited, by step and exercised, in spec order, keeping only active IDs', () => {
    const s = sit([t('x', { inhibitors: ['i'] })], ['CORE-031', 'IO-001']);
    const order = new Map([
      ['CORE-031', 0],
      ['IO-001', 1],
    ]);
    const blocked = {
      slug: 's',
      reference: 'r',
      initial: {},
      complete: false,
      steps: [{ kind: 'blocked' as const, index: 0, fire: 'x', branch: 0, timeout: false, reason: { kind: 'inhibitorMarked' as const, place: 'i', count: 1 }, requirement: 'CORE-031', message: 'm' }],
    };
    expect(situationRules(s, blocked, order)).toEqual([
      { id: 'CORE-031', links: [{ kind: 'cited' }, { kind: 'step', index: 0 }, { kind: 'exercised' }] },
      { id: 'IO-001', links: [{ kind: 'cited' }, { kind: 'exercised' }] },
    ]);
    expect(situationRules(sit([t('x', { reads: ['r'] })]), null, order)).toEqual([{ id: 'IO-001', links: [{ kind: 'exercised' }] }]);
  });
});

describe('cross-input checks', () => {
  const base: SiteInputs = {
    spec: { files: [], blocks: [block('CORE-001'), block('CORE-009', 'removed')], units: new Map([['CORE-001', [{ sents: ['A place holds tokens.'], ac: null }]]]) },
    glossary: [{ term: 'Place', slug: 'place', group: 'G', text: 'x', refs: ['CORE-404'] }],
    lean: { blocks: [], citations: [{ id: 'CORE-009', theorem: 'T', module: 'M', fragment: 'f' }] },
    coverage: {},
    defects: [],
    situations: [{ situation: sit([t('x')], ['IO-001']), result: null }],
    diagrams: new Set(),
  };

  it('lists every disagreement and refuses to build from disk inputs that have one', () => {
    expect(inputProblems(base)).toEqual([
      'glossary term "Place": CORE-404 is not a requirement',
      'citation T: CORE-009 is removed',
      'situation s: IO-001 is not a requirement',
      'coverage matrix: no row for CORE-001',
    ]);
    expect(() => buildSiteData(base)).toThrow(/the site inputs disagree:\n {2}glossary term/);
  });

  it('checks that every verbatim Lean quote is text of its block', () => {
    const leanBlock = (quote: string) => ({
      id: 'CORE-001',
      title: 't',
      decl: 'Libpetri.Spec.CORE_001',
      module: 'm',
      kind: 'B' as const,
      sourceRef: 'spec/01-core-model.md',
      source: 'verbatim',
      scope: 's',
      quotes: [quote],
      reading: [],
      assumes: [],
      statement: 's',
      signoff: { state: 'pending' as const },
      hash: '0123456789abcdef',
      evidence: [],
    });
    const ok: SiteInputs = { ...base, glossary: [], lean: { blocks: [leanBlock('A *place* holds tokens.')], citations: [] }, coverage: {}, situations: [] };
    expect(inputProblems(ok)).toEqual(['coverage matrix: no row for CORE-001']);
    const bad: SiteInputs = { ...ok, lean: { blocks: [leanBlock('A place holds')], citations: [] } };
    expect(inputProblems(bad)).toContain('Lean block Libpetri.Spec.CORE_001: quote is not text of CORE-001: "A place holds"');
  });

  it('names defect evidence by its full theorem when exactly one matches', () => {
    const d: Defect = { id: 'RD-01', title: 't', requirements: [], runtimes: ['java'], text: 'x', evidence: ['f_holds', 'helper', 'twin'], evidenceText: 'x', fix: null, status: { state: 'open' } };
    const lean = {
      blocks: [],
      citations: [
        { id: 'CORE-001', theorem: 'Libpetri.Spec.f_holds', module: 'm', fragment: 'f' },
        { id: 'CORE-001', theorem: 'Libpetri.A.twin', module: 'm', fragment: 'f' },
        { id: 'CORE-001', theorem: 'Libpetri.B.twin', module: 'm', fragment: 'f' },
      ],
    };
    expect(resolveDefectEvidence([d], lean)[0]?.evidence).toEqual(['Libpetri.Spec.f_holds', 'helper', 'twin']);
  });
});

describe('the real inputs', () => {
  const read = (): SiteInputs => {
    const glossary = readGlossary(REPO_ROOT);
    return {
      spec: readSpec(REPO_ROOT, glossary),
      glossary,
      lean: readLean(REPO_ROOT),
      coverage: readCoverage(REPO_ROOT),
      defects: readDefects(REPO_ROOT),
      situations: readSituations(REPO_ROOT),
      diagrams: new Set(),
    };
  };

  it('read twice give byte-identical site data that the app decoder accepts', () => {
    const first = stableStringify(buildSiteData(read()));
    const second = stableStringify(buildSiteData(read()));
    expect(second).toBe(first);
    decode(siteData, JSON.parse(first) as unknown);
  });

  it('agree with each other and with the registry counts', () => {
    const inputs = read();
    expect(inputProblems(inputs)).toEqual([]);
    const data = buildSiteData(inputs);
    const active = data.blocks.filter((b) => b.status.state !== 'removed');
    expect(data.counts.activeIds).toBe(active.length);
    expect(Object.keys(data.coverage).sort()).toEqual(active.map((b) => b.id).sort());
    expect(data.counts.leanBlocks).toBe(inputs.lean.blocks.length);
    expect(data.files.reduce((n, f) => n + f.sections.reduce((m, s) => m + s.ids.length, 0), 0)).toBe(data.blocks.length);
    for (const s of data.situations) expect(s.result === null).toBe(!s.replay);
    for (const e of data.edges) if (e.kind === 'uses-term') expect(data.glossary.some((g) => g.slug === e.to)).toBe(true);
  });
});
