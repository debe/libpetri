/** Fixture tests for the Lean report, coverage, defect ledger and situation readers. */
import { describe, expect, it } from 'vitest';
import { coverageRows, parseCoverageMatrix, parseProofCoverage } from '../src/gen/inputs/coverage.js';
import { evidenceNames, parseDefects, parseDefectStatus, parseRuntimes } from '../src/gen/inputs/defects.js';
import { parseLeanReport, parseSignoff } from '../src/gen/inputs/lean.js';
import { checkReplay, parseReplay, parseSituation } from '../src/gen/inputs/situations.js';
import type { Citation } from '../src/model.js';

// ---------------------------------------------------------------------------------------------
// Lean report
// ---------------------------------------------------------------------------------------------

function leanBlock(extra: Record<string, unknown> = {}): Record<string, unknown> {
  return {
    title: 'Inhibitor Arc',
    statement: 'fun R ↦ ∀ C, True',
    sourceRef: 'spec/01-core-model.md',
    source: 'verbatim',
    signoff: 'pending',
    scope: 'all executors',
    reading: ['For every executor R:'],
    quotes: ['A quote.'],
    module: 'Libpetri.Spec.Req.CORE_031',
    kind: 'B',
    id: 'CORE-031',
    hash: '0123456789abcdef',
    evidence: [
      { theorem: 'Libpetri.Spec.CORE_031_holds', role: 'holds', module: 'Libpetri.Spec.Req.CORE_031', doc: '**Example.** One token.' },
      { theorem: 'Libpetri.Spec.CORE_031_mutant', role: 'mutant', module: 'Libpetri.Spec.Req.CORE_031', doc: '' },
      { theorem: 'Libpetri.Spec.CORE_031_forbids', role: 'forbids', module: 'Libpetri.Spec.Req.CORE_031' },
    ],
    decl: 'Libpetri.Spec.CORE_031',
    assumes: [],
    ...extra,
  };
}

const cite = (id: string, theorem: string, fragment = 'f'): Record<string, unknown> => ({ theorem, role: 'cites', module: 'Libpetri.M', id, fragment, doc: 'd' });

describe('Lean report', () => {
  it('reads blocks, keeps docstrings, turns an empty or missing doc into null, sorts citations', () => {
    const text = JSON.stringify({
      title: 'libpetri requirements',
      requirements: [leanBlock({ signoff: '2026-11-10 104625b4eefcf18b' })],
      citations: [cite('IO-001', 'Libpetri.b'), cite('CORE-031', 'Libpetri.z'), cite('CORE-031', 'Libpetri.a')],
    });
    const lean = parseLeanReport(text);
    expect(lean.blocks).toHaveLength(1);
    expect(lean.blocks[0]?.signoff).toEqual({ state: 'signed', date: '2026-11-10', hash: '104625b4eefcf18b' });
    expect(lean.blocks[0]?.evidence.map((e) => e.doc)).toEqual(['**Example.** One token.', null, null]);
    expect(lean.citations.map((c) => `${c.id} ${c.theorem}`)).toEqual(['CORE-031 Libpetri.a', 'CORE-031 Libpetri.z', 'IO-001 Libpetri.b']);
    expect(lean.citations[0]).toEqual({ id: 'CORE-031', theorem: 'Libpetri.a', module: 'Libpetri.M', fragment: 'f' });
  });

  it('fails on an unknown role, kind, key or signoff and on a repeated decl', () => {
    const report = (blocks: unknown[]): string => JSON.stringify({ title: 't', requirements: blocks, citations: [] });
    const bad = leanBlock();
    bad['evidence'] = [{ theorem: 't', role: 'proves', module: 'm', doc: '' }];
    expect(() => parseLeanReport(report([bad]))).toThrow(/role "proves" is unknown; add it to EVIDENCE_ROLES/);
    expect(() => parseLeanReport(report([leanBlock({ kind: 'Z' })]))).toThrow(/unknown kind "Z"/);
    expect(() => parseLeanReport(report([leanBlock({ extra: 1 })]))).toThrow(/\$\.requirements\[0\]\.extra: unknown key/);
    expect(() => parseLeanReport(report([leanBlock({ signoff: 'yes' })]))).toThrow(/signoff "yes"/);
    expect(() => parseLeanReport(report([leanBlock(), leanBlock()]))).toThrow(/decl appears twice/);
    expect(parseSignoff('pending')).toEqual({ state: 'pending' });
    expect(parseSignoff('2026-11-10 104625b4e')).toBeNull();
  });
});

// ---------------------------------------------------------------------------------------------
// Coverage
// ---------------------------------------------------------------------------------------------

const MATRIX = `# Spec Proof/Test Coverage Matrix

## 01-core-model.md — CORE

| ID | Lean proof (theorem + fragment) | Lean ref | java | typescript | rust | python |
|----|---------------------------------|----------|------|------------|------|--------|
| CORE-001 | \`core001_place\` — a \\| b<br>\`other\` — c | ✓ | — | — | ✓ | — |
| CORE-002 | — | — | ✓ | — | — | — |
`;

describe('coverage', () => {
  const citations: Citation[] = [
    { id: 'CORE-001', theorem: 'Libpetri.Spec.core001_place', module: 'Libpetri.Spec.Req.CORE_001', fragment: 'a | b' },
    { id: 'CORE-001', theorem: 'Libpetri.other', module: 'Libpetri.Other', fragment: 'c' },
  ];
  const proofs = JSON.stringify({
    $comment: 'generated',
    theorems: [
      { name: 'other', module: 'Libpetri/Other.lean', specIds: [{ id: 'CORE-001', fragment: 'c' }] },
      { name: 'core001_place', module: 'Libpetri/Spec/Req/CORE_001.lean', specIds: [{ id: 'CORE-001', fragment: 'a | b ' }] },
    ],
  });

  it('reads the matrix columns, escaped pipes included', () => {
    expect(parseCoverageMatrix(MATRIX)).toEqual([
      { id: 'CORE-001', proved: true, leanRef: true, tested: { java: false, typescript: false, rust: true, python: false } },
      { id: 'CORE-002', proved: false, leanRef: false, tested: { java: true, typescript: false, rust: false, python: false } },
    ]);
  });

  it('names proofs by their full theorem, in module order', () => {
    const map = parseProofCoverage(proofs, citations);
    expect(map.get('CORE-001')).toEqual([
      { theorem: 'Libpetri.other', fragment: 'c' },
      { theorem: 'Libpetri.Spec.core001_place', fragment: 'a | b' },
    ]);
    expect(() => parseProofCoverage(proofs, citations.slice(1))).toThrow(/core001_place .* 0 matching citations/);
  });

  it('joins rows with the test files and fails when the matrix is stale', () => {
    const matrix = parseCoverageMatrix(MATRIX);
    const proofMap = parseProofCoverage(proofs, citations);
    const none = new Map<string, string[]>();
    const refs = { java: new Map([['CORE-002', ['java/src/test/A.java']]]), typescript: none, rust: new Map([['CORE-001', ['rust/x/tests/a.rs']]]), python: none };
    const rows = coverageRows(matrix, proofMap, refs);
    expect(rows['CORE-002']?.tests).toEqual({ java: { state: 'tested', refs: ['java/src/test/A.java'] }, typescript: { state: 'untested' }, rust: { state: 'untested' }, python: { state: 'untested' } });
    expect(rows['CORE-001']?.leanRef).toBe(true);
    expect(() => coverageRows(matrix, proofMap, { ...refs, python: new Map([['CORE-002', ['python/tests/t.py']]]) })).toThrow(/python column says untested but 1 test files cite it; .*--update/);
    expect(() => coverageRows(matrix, new Map(), refs)).toThrow(/CORE-001: Lean proof column disagrees/);
  });
});

// ---------------------------------------------------------------------------------------------
// Defects
// ---------------------------------------------------------------------------------------------

const LEDGER = `# Runtime Defect Ledger

| ID | Requirements | Runtimes | Status |
|---|---|---|---|
| RD-01 | EXEC-021, IO-013 | Java, TypeScript | open |
| RD-02 | CORE-041 | all | fixed in 12.0.1 |

### RD-01. The timeout outcome is validated

- **Requirements:** EXEC-021, IO-013 (ruling D24 (a)).
- **Runtimes:** TypeScript, and Java.
- **Defect:** both validate the outcome,
  \`java/Foo.java:12\`.
- **Lean evidence:** \`clash_conflict\` (Clashes.lean),
  \`EXEC_021_forbids_x\` (EXEC_021.lean).
- **Status:** open.

### RD-02. Live sets

- **Requirements:** CORE-041.
- **Runtimes:** all.
- **Defect:** \`build()\` passes its sets.
- **Lean evidence:** none; the \`NamesDistinct\` assumption keeps it out.
- **Status:** fixed in 12.0.1.
`;

describe('defects', () => {
  it('reads the entries in ledger order', () => {
    expect(parseDefects(LEDGER)).toEqual([
      {
        id: 'RD-01',
        title: 'The timeout outcome is validated',
        requirements: ['EXEC-021', 'IO-013'],
        runtimes: ['java', 'typescript'],
        text: 'both validate the outcome, `java/Foo.java:12`.',
        evidence: ['clash_conflict', 'EXEC_021_forbids_x'],
        evidenceText: '`clash_conflict` (Clashes.lean), `EXEC_021_forbids_x` (EXEC_021.lean).',
        status: { state: 'open' },
      },
      {
        id: 'RD-02',
        title: 'Live sets',
        requirements: ['CORE-041'],
        runtimes: ['java', 'typescript', 'rust', 'python'],
        text: '`build()` passes its sets.',
        evidence: [],
        evidenceText: 'none; the `NamesDistinct` assumption keeps it out.',
        status: { state: 'fixed', version: '12.0.1' },
      },
    ]);
  });

  it('maps runtime names and statuses, and fails on unknown ones or table drift', () => {
    expect(parseRuntimes('Rust, Java, TypeScript, and Python through Rust.')).toEqual(['java', 'typescript', 'rust', 'python']);
    expect(parseRuntimes('Go')).toBeNull();
    expect(parseDefectStatus('open.')).toEqual({ state: 'open' });
    expect(parseDefectStatus('closed')).toBeNull();
    expect(evidenceNames('none yet (`X`)')).toEqual([]);
    expect(() => parseDefects(LEDGER.replace('- **Runtimes:** all.', '- **Runtimes:** Kotlin.'))).toThrow(/runtime-defects.md:18: RD-02: unknown runtime/);
    expect(() => parseDefects(LEDGER.replace('| RD-02 | CORE-041 |', '| RD-02 | CORE-042 |'))).toThrow(/the table names CORE-042, the entry CORE-041/);
    expect(() => parseDefects(LEDGER.replace('- **Status:** fixed in 12.0.1.', '- **Status:** open.'))).toThrow(/the table says "fixed in 12.0.1"/);
  });
});

// ---------------------------------------------------------------------------------------------
// Situations
// ---------------------------------------------------------------------------------------------

const SITUATION = {
  title: 'A held lock',
  group: 'Firing',
  text: 'Explained.',
  cites: ['CORE-031'],
  places: ['job', 'lock'],
  marking: { lock: 0, job: 2 },
  transitions: [
    { name: 'take', inputs: [{ place: 'job', kind: 'exactly', n: 1 }], inhibitors: ['lock'], output: { type: 'place', place: 'lock' }, timing: { kind: 'deadline', latestMs: 5 } },
  ],
  steps: [{ fire: 'take', text: 'Fires.' }, { fire: 'take', branch: 0, expect: 'blocked' }],
};

const EXPECTED = {
  slug: 'held-lock',
  reference: 'abc',
  initial: { job: 2 },
  complete: false,
  steps: [
    { index: 0, fire: 'take', branch: 0, fired: true, marking: { lock: 1, job: 1 } },
    {
      index: 1,
      fire: 'take',
      branch: 0,
      blocked: true,
      reason: { kind: 'inhibitorMarked', place: 'lock', count: 1 },
      requirement: 'CORE-031',
      message: "'take' is not enabled: inhibitor place 'lock' holds 1 token",
    },
  ],
};

describe('situations', () => {
  const situation = parseSituation('held-lock', JSON.stringify(SITUATION), 'held-lock.json');

  it('fills the defaults of the authored file', () => {
    expect(situation).toEqual({
      slug: 'held-lock',
      title: 'A held lock',
      text: 'Explained.',
      group: 'Firing',
      cites: ['CORE-031'],
      replay: true,
      notReplayed: null,
      net: {
        places: ['job', 'lock'],
        marking: { job: 2 },
        transitions: [
          {
            name: 'take',
            inputs: [{ kind: 'exactly', place: 'job', n: 1 }],
            inhibitors: ['lock'],
            reads: [],
            resets: [],
            output: { type: 'place', place: 'lock' },
            priority: 0,
            timing: { kind: 'deadline', earliestMs: null, latestMs: 5 },
          },
        ],
        properties: [],
      },
      steps: [
        { fire: 'take', branch: 0, timeout: false, text: 'Fires.', expect: 'fired' },
        { fire: 'take', branch: 0, timeout: false, text: null, expect: 'blocked' },
      ],
    });
  });

  it('enforces the site rules: title, group, notReplayed, unknown keys', () => {
    const parse = (o: object): unknown => parseSituation('s', JSON.stringify(o), 's.json');
    expect(() => parse({ ...SITUATION, group: 'Misc' })).toThrow(/group "Misc" is not one of Firing/);
    const { title: _, ...untitled } = SITUATION;
    expect(() => parse(untitled)).toThrow(/\$\.title: missing key/);
    expect(() => parse({ ...SITUATION, replay: false })).toThrow(/needs "notReplayed"/);
    expect(() => parse({ ...SITUATION, steps: [{ fire: 'take', expect: 'blocked' }, { fire: 'take' }] })).toThrow(/a blocked step must be the last one/);
    expect(() => parse({ ...SITUATION, steps: [{ fire: 'take', expect: 'maybe' }] })).toThrow(/\$\.steps\[0\]\.expect/);
    // A malformed marking names the file and the JSON path, like every other key.
    expect(() => parse({ ...SITUATION, marking: [1] })).toThrow(/^s\.json: \$\.marking: expected an object of token counts$/);
    expect(() => parse({ ...SITUATION, notReplayed: 'timed' })).toThrow(/belongs only in a "replay": false file/);
    expect(() => parse({ ...SITUATION, colour: 'red' })).toThrow(/\$\.colour: unknown key/);
    expect(() => parseSituation('Bad_Name', JSON.stringify(SITUATION), 'x.json')).toThrow(/lowercase words/);
    const timed = parseSituation('t', JSON.stringify({ ...SITUATION, replay: false, notReplayed: 'timed', steps: undefined }), 't.json');
    expect(timed).toMatchObject({ replay: false, notReplayed: 'timed', steps: [] });
  });

  it('maps fired / blocked to kind, fills timeout and arc.n, sorts markings', () => {
    const result = parseReplay(JSON.stringify(EXPECTED), 'expected/held-lock.json');
    expect(result.steps[0]).toEqual({ kind: 'fired', index: 0, fire: 'take', branch: 0, timeout: false, marking: { job: 1, lock: 1 } });
    expect(Object.keys(result.steps[0]?.kind === 'fired' ? result.steps[0].marking : {})).toEqual(['job', 'lock']);
    expect(result.steps[1]).toMatchObject({ kind: 'blocked', requirement: 'CORE-031', timeout: false, reason: { kind: 'inhibitorMarked', place: 'lock', count: 1 } });
    const short = { ...EXPECTED, steps: [{ ...EXPECTED.steps[1], index: 0, reason: { kind: 'inputShort', place: 'job', arc: { kind: 'one' }, need: 1, have: 0 } }] };
    expect(parseReplay(JSON.stringify(short), 'x').steps[0]).toMatchObject({ reason: { kind: 'inputShort', arc: { kind: 'one', n: null } } });
    const branch = { ...EXPECTED, steps: [{ ...EXPECTED.steps[1], index: 0, reason: { kind: 'noSuchBranch', branch: 2 } }] };
    expect(parseReplay(JSON.stringify(branch), 'x').steps[0]).toMatchObject({ reason: { kind: 'noSuchBranch', branch: 2, timeout: false } });
    checkReplay(situation, result, 'expected/held-lock.json');
  });

  it('fails when the replay does not follow the authored steps', () => {
    const result = parseReplay(JSON.stringify(EXPECTED), 'e.json');
    const renamed = { ...situation, steps: [{ fire: 'take', branch: 0, timeout: false, text: null, expect: 'fired' as const }, { fire: 'release', branch: 0, timeout: false, text: null, expect: 'fired' as const }] };
    expect(() => checkReplay(renamed, result, 'e.json')).toThrow(/step 1 replays take .*fires release; regenerate/);
    expect(() => checkReplay(situation, { ...result, complete: true }, 'e.json')).toThrow(/"complete" is true/);
    expect(() => checkReplay({ ...situation, slug: 'other' }, result, 'e.json')).toThrow(/slug "held-lock"/);
    // The author's expectation is checked: a step meant to fire that Lean blocks fails the build.
    const meantToFire = { ...situation, steps: situation.steps.map((st) => ({ ...st, expect: 'fired' as const })) };
    expect(() => checkReplay(meantToFire, result, 'e.json')).toThrow(/step 2 \(take\) expects "fired", but the Lean replay says "blocked"/);
    // A block before the last authored step fails too.
    const longer = { ...situation, steps: [...situation.steps, { fire: 'take', branch: 0, timeout: false, text: null, expect: 'fired' as const }] };
    expect(() => checkReplay(longer, result, 'e.json')).toThrow(/stops at a blocked step 2, but the situation has 3 steps/);
    expect(() => parseReplay(JSON.stringify({ ...EXPECTED, steps: [{ index: 0, fire: 'take', branch: 0 }] }), 'e.json')).toThrow(/e\.json: \$\.steps\[0\]\.kind: unknown tag/);
  });
});
