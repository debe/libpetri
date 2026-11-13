import { describe, expect, it } from 'vitest';
import { defectsOf } from '../src/gen/inputs/defects.js';
import { glossaryTerms, termSlug } from '../src/gen/inputs/glossary.js';
import { parseSpecJson, type SpecJson } from '../src/gen/inputs/spec-json.js';
import { specInput, termMatchers, termsIn } from '../src/gen/inputs/spec.js';
import type { GlossaryTerm } from '../src/model.js';

const glossary: GlossaryTerm[] = [
  { term: 'Place', slug: 'place', group: 'G', text: 'x', refs: [] },
  { term: 'Input arc', slug: 'input-arc', group: 'G', text: 'x', refs: [] },
  { term: 'Fire', slug: 'fire', group: 'G', text: 'x', refs: [] },
];

const requirement = {
  id: 'CORE-001',
  title: 'Place Definition',
  priority: 'MUST',
  kind: 'B',
  status: 'active',
  file: '01-core-model.md',
  line: 9,
  section: 'Places',
  source: 'lean/Libpetri/Spec/Text/CORE_001.lean',
  body: 'A place holds tokens.\n\n⟦…⟧',
  spans: [{ label: 's1', text: 'When a transition fires, it *shall* consume.' }],
  paragraphs: [
    { kind: 'prose', text: 'A place holds tokens.' },
    { kind: 'shall', text: 'When a transition fires, it *shall* consume.' },
    { kind: 'code', text: 'place fires' },
  ],
  acceptance: ['A place can be created.'],
  notes: [{ label: 'Note', text: 'Names follow [MOD-010].' }],
  dependsOn: ['CORE-002'],
  mentions: ['MOD-010'],
  testDerivation: 'Create a place.',
};

const file = {
  $comment: 'c',
  chapters: [{ file: '01-core-model.md', number: '01', title: 'Core Model', scope: 's', prefixes: ['CORE'], sections: [{ title: 'Places', ids: ['CORE-001'] }] }],
  requirements: [requirement, { ...requirement, id: 'CORE-009', title: 'Gone', priority: null, kind: null, status: 'removed', paragraphs: [] }],
  glossary: [
    { term: 'Token count', group: 'Glossary: firing', text: 'The number [CORE-070].', refs: ['CORE-070'] },
    { term: 'Needs-mask', group: 'Timing', text: 'A mask.', refs: [] },
  ],
  defects: [
    {
      id: 'RD-01',
      title: 'T',
      requirements: ['EXEC-021'],
      runtimes: ['Rust', 'Java'],
      text: 'd',
      evidence: ['f_holds'],
      evidenceText: '`f_holds` (F.lean).',
      fix: null,
      status: { state: 'fixed', version: null },
    },
  ],
  unbuilt: [],
  divergences: [],
};

const data = (patch: Record<string, unknown> = {}): SpecJson => parseSpecJson(JSON.stringify({ ...file, ...patch }), 'spec.json');

describe('glossary terms in block text', () => {
  it('matches whole words, plurals and case, but not code or longer words', () => {
    const m = termMatchers(glossary);
    expect(termsIn('Places hold tokens; it fires.', m)).toEqual(['fire', 'place']);
    expect(termsIn('`place` and placement and input-arcs', m)).toEqual([]);
    expect(termsIn('two input  arcs', m)).toEqual(['input-arc']);
  });
});

describe('spec.json', () => {
  it('maps chapters and requirements onto the site model, terms from prose only', () => {
    const spec = specInput(data(), glossary);
    expect(spec.files).toEqual([{ file: '01-core-model.md', number: '01', title: 'Core Model', prefixes: ['CORE'], sections: [{ title: 'Places', ids: ['CORE-001'] }] }]);
    expect(spec.checked).toBe(true);
    expect(spec.blocks[0]).toEqual({
      id: 'CORE-001',
      title: 'Place Definition',
      file: '01-core-model.md',
      line: 9,
      section: 'Places',
      priority: 'MUST',
      kind: 'B',
      status: { state: 'active' },
      body: requirement.paragraphs,
      acceptance: ['A place can be created.'],
      notes: [{ label: 'Note', text: 'Names follow [MOD-010].' }],
      dependsOn: ['CORE-002'],
      mentions: ['MOD-010'],
      testDerivation: 'Create a place.',
      terms: ['fire', 'place'],
    });
    expect(spec.blocks[1]).toMatchObject({ id: 'CORE-009', status: { state: 'removed' }, priority: null, kind: null, terms: [] });
  });

  it('fails on an unknown key, priority, status or paragraph kind', () => {
    expect(() => data({ extra: 1 })).toThrow(/spec.json: \$\.extra: unknown key/);
    expect(() => data({ requirements: [{ ...requirement, priority: 'OFTEN' }] })).toThrow(/\$\.requirements\[0\]\.priority/);
    expect(() => data({ requirements: [{ ...requirement, status: 'gone' }] })).toThrow(/\$\.requirements\[0\]\.status/);
    expect(() => data({ requirements: [{ ...requirement, paragraphs: [{ kind: 'quote', text: 'x' }] }] })).toThrow(/paragraphs\[0\]\.kind/);
  });

  it('gives each glossary term a unique slug', () => {
    expect(glossaryTerms(data())).toEqual([
      { term: 'Token count', slug: 'token-count', group: 'Glossary: firing', text: 'The number [CORE-070].', refs: ['CORE-070'] },
      { term: 'Needs-mask', slug: 'needs-mask', group: 'Timing', text: 'A mask.', refs: [] },
    ]);
    expect(termSlug('ν verification')).toBe('ν-verification');
    expect(() => glossaryTerms(data({ glossary: [{ term: 'A b', group: 'G', text: 'x', refs: [] }, { term: 'A-B', group: 'G', text: 'y', refs: [] }] }))).toThrow(/slug "a-b"/);
  });

  it('orders defect runtimes and maps the status', () => {
    expect(defectsOf(data())).toEqual([
      { id: 'RD-01', title: 'T', requirements: ['EXEC-021'], runtimes: ['java', 'rust'], text: 'd', evidence: ['f_holds'], evidenceText: '`f_holds` (F.lean).', fix: null, status: { state: 'fixed', version: null } },
    ]);
    const open = { ...file.defects[0], status: { state: 'open' } };
    expect(defectsOf(data({ defects: [open] }))[0]?.status).toEqual({ state: 'open' });
    expect(() => defectsOf(data({ defects: [{ ...open, runtimes: ['Go'] }] }))).toThrow(/RD-01: unknown runtime/);
  });
});
