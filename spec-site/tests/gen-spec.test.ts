import { describe, expect, it } from 'vitest';
import { matchQuote, norm, scanLines, sentences, splitLines, stripMarkdown, units } from '../src/gen/inputs/alignment.js';
import { parseGlossary, termSlug } from '../src/gen/inputs/glossary.js';
import { joinMarkdown, toChunks } from '../src/gen/inputs/markdown.js';
import { parseSpecFile, parseSpecIndex, termMatchers, termsIn } from '../src/gen/inputs/spec.js';
import type { GlossaryTerm } from '../src/model.js';

const INDEX = `# Index

## Spec Files

| File | Prefix | Scope | Req Count |
|------|--------|-------|-----------|
| [01-core-model.md](01-core-model.md) | CORE | Places | 3 |
| **Total** | | | **3** |

## Alphabetical Cross-Reference Index

### CORE — Core Model
| ID | Title | Priority | Depends On |
|----|-------|----------|------------|
| CORE-001 | Place | MUST | — |
| CORE-002 | Identity | MUST | — |
| CORE-003 | Later | MAY | — |
| ~~CORE-009~~ | ~~Gone~~ (Removed) | — | — |

## Priority Distribution

| CORE-777 | not | in | the index |
`;

const FILE = `# 01 — Core Model

Intro.

---

## Places

#### CORE-001: Place Definition

**Priority:** MUST
**Kind:** B

A place holds tokens. Each place has a name. It can:
1. hold tokens,
2. be named.

*When* a transition fires, it *shall* consume from each input place.

\`\`\`
#### NOT-001: inside a fence
\`\`\`

**Note:** Names follow [MOD-010] and [CORE-009]
for subnets.

More of the note.

**Acceptance Criteria:**
1. A place can be created.
2. The name is kept,
   across a restart.
   - nested detail

3. After a blank line the list goes on.

Context after the list cites [CORE-002].

**Depends on:** [CORE-002],
[CORE-003]
**Test derivation:** Create a place.

A second paragraph of the derivation.

---

## Removed things

#### CORE-009: ~~Gone~~ (Removed)

**Status:** Removed

Kept as a tombstone.

#### CORE-002: Identity

**Priority:** MUST

Two places are the same place when their names are equal [RV-08].

**Acceptance Criteria:**
1. Equal names, same place.

#### CORE-003: Later

**Priority:** MAY

The engine *shall* do it later.

**Acceptance Criteria:**
1. Later.

**Status:** Proposed
**Implementation status:** Java only.

It *shall* be visible in every runtime later.
`;

const glossary: GlossaryTerm[] = [
  { term: 'Place', slug: 'place', group: 'G', text: 'x', refs: [] },
  { term: 'Input arc', slug: 'input-arc', group: 'G', text: 'x', refs: [] },
  { term: 'Fire', slug: 'fire', group: 'G', text: 'x', refs: [] },
];

describe('alignment port', () => {
  it('splits lines like Python splitlines', () => {
    expect(splitLines('a\nb\r\nc\n')).toEqual(['a', 'b', 'c']);
    expect(splitLines('a b')).toEqual(['a', 'b']);
    expect(splitLines('')).toEqual([]);
  });

  it('blanks fences and comments, drops strikethrough', () => {
    expect(stripMarkdown(['a <!-- x', 'y --> b', '```', '# no', '```', '~~gone~~ kept'])).toEqual(['a ', ' b', '', '', '', ' kept']);
    expect(scanLines(['~~~', 'x', '~~~~']).map((l) => l.fence)).toEqual([true, true, true]);
  });

  it('cuts units and numbers acceptance criteria', () => {
    const u = units(['A *first* one. Second one.', '', 'Acceptance Criteria:', '1. One.', '2. Two.', '', 'After.']);
    expect(u.map((x) => [x.sents, x.ac])).toEqual([
      [['A first one.', 'Second one.'], null],
      [['Acceptance Criteria:'], null],
      [['One.'], 1],
      [['Two.'], 2],
      [['After.'], null],
    ]);
  });

  it('matches a quote only as a whole sentence run', () => {
    const u = units(['One. Two. Three.']);
    expect(matchQuote(norm('Two. Three.'), u)).toEqual([[0, 1], [0, 2]]);
    expect(matchQuote(norm('Tw'), u)).toEqual([]);
    expect(sentences('Ends with "quote." Next')).toEqual(['Ends with "quote."', 'Next']);
  });
});

describe('markdown chunks', () => {
  it('joins wrapped prose with a space and keeps list items and fences on their lines', () => {
    const lines = scanLines(['Para line one', 'line two:', '- item a', '  wrapped a', '```', 'code', '```']);
    expect(joinMarkdown(lines)).toBe('Para line one line two:\n\n- item a wrapped a\n```\ncode\n```');
  });

  it('splits chunks at blank lines and label lines', () => {
    const chunks = toChunks(scanLines(['**A:** x', '**B:** y', 'z', '', 'w']), 10, /^\*\*[^*]+:\*\*/);
    expect(chunks.map((c) => [c.line, c.lines.map((l) => l.text)])).toEqual([
      [10, ['**A:** x']],
      [11, ['**B:** y', 'z']],
      [14, ['w']],
    ]);
  });
});

describe('spec index', () => {
  it('reads active IDs and tombstones only from the cross-reference section', () => {
    const index = parseSpecIndex(INDEX);
    expect([...index.active]).toEqual(['CORE-001', 'CORE-002', 'CORE-003']);
    expect([...index.tombstones]).toEqual(['CORE-009']);
    expect(index.files).toEqual([{ file: '01-core-model.md', prefix: 'CORE', count: 3 }]);
  });
});

describe('spec file', () => {
  const parsed = parseSpecFile('01-core-model.md', FILE, parseSpecIndex(INDEX), termMatchers(glossary));
  const block = (id: string) => {
    const b = parsed.blocks.find((x) => x.id === id);
    if (b === undefined) throw new Error(`no ${id}`);
    return b;
  };

  it('reads the file title, sections and prefixes', () => {
    expect(parsed.file).toEqual({
      file: '01-core-model.md',
      number: '01',
      title: 'Core Model',
      prefixes: ['CORE'],
      sections: [
        { title: 'Places', ids: ['CORE-001'] },
        { title: 'Removed things', ids: ['CORE-009', 'CORE-002', 'CORE-003'] },
      ],
    });
    expect(parsed.blocks.map((b) => b.id)).toEqual(['CORE-001', 'CORE-009', 'CORE-002', 'CORE-003']);
  });

  it('sorts a block into metadata, body, notes, acceptance and test derivation', () => {
    const b = block('CORE-001');
    expect(b).toMatchObject({ title: 'Place Definition', line: 9, section: 'Places', priority: 'MUST', kind: 'B', status: { state: 'active' } });
    expect(b.body).toEqual([
      { kind: 'prose', text: 'A place holds tokens. Each place has a name. It can:' },
      { kind: 'prose', text: '1. hold tokens,\n2. be named.' },
      { kind: 'shall', text: '*When* a transition fires, it *shall* consume from each input place.' },
      { kind: 'code', text: '#### NOT-001: inside a fence' },
      { kind: 'prose', text: 'Context after the list cites [CORE-002].' },
    ]);
    expect(b.notes).toEqual([{ label: 'Note', text: 'Names follow [MOD-010] and [CORE-009] for subnets.\n\nMore of the note.' }]);
    expect(b.acceptance).toEqual(['A place can be created.', 'The name is kept, across a restart.\n\n- nested detail', 'After a blank line the list goes on.']);
    expect(b.dependsOn).toEqual(['CORE-002', 'CORE-003']);
    // CORE-002 is a dependency, not a mention; MOD has no file in this index.
    expect(b.mentions).toEqual(['CORE-009']);
    expect(b.testDerivation).toBe('Create a place.\n\nA second paragraph of the derivation.');
    expect(b.terms).toEqual(['fire', 'place']);
  });

  it('marks tombstones and proposed blocks, cleans the title, skips bibliography brackets', () => {
    expect(block('CORE-009')).toMatchObject({ title: 'Gone', status: { state: 'removed' }, priority: null, body: [{ kind: 'prose', text: 'Kept as a tombstone.' }] });
    expect(block('CORE-002').mentions).toEqual([]);
    const later = block('CORE-003');
    expect(later.status).toEqual({ state: 'proposed' });
    expect(later.notes).toEqual([{ label: 'Implementation status', text: 'Java only.' }]);
    expect(later.body.map((p) => p.kind)).toEqual(['shall', 'shall']);
  });

  it('fails on a block the index does not know and on a duplicate heading', () => {
    const index = parseSpecIndex(INDEX);
    expect(() => parseSpecFile('01-core-model.md', `# 01 — X\n\n#### CORE-404: Lost\n\nText.\n`, index, [])).toThrow(/CORE-404 is not listed/);
    expect(() => parseSpecFile('01-core-model.md', `# 01 — X\n\n#### CORE-001: A\n\nx\n\n#### CORE-001: B\n\ny\n`, index, [])).toThrow(/second '#### CORE-001:'/);
    expect(() => parseSpecFile('01-core-model.md', `# 01 — X\n\n#### CORE-001: A\n\n**Priority:** OFTEN\n`, index, [])).toThrow(/:5: priority "OFTEN"/);
  });
});

describe('glossary terms', () => {
  it('matches whole words, plurals and case, but not code or longer words', () => {
    const m = termMatchers(glossary);
    expect(termsIn('Places hold tokens; it fires.', m)).toEqual(['fire', 'place']);
    expect(termsIn('`place` and placement and input-arcs', m)).toEqual([]);
    expect(termsIn('two input  arcs', m)).toEqual(['input-arc']);
  });

  it('parses terms under group headings with refs in order', () => {
    const terms = parseGlossary(`# Glossary: firing\n\nIntro.\n\n### Token count\n\nThe number [CORE-070], see [IO-001] and [CORE-070].\n\nSecond paragraph.\n\n---\n\n## Timing\n\n### Needs-mask\n\nA mask.\n`);
    expect(terms).toEqual([
      { term: 'Token count', slug: 'token-count', group: 'Glossary: firing', text: 'The number [CORE-070], see [IO-001] and [CORE-070].\n\nSecond paragraph.', refs: ['CORE-070', 'IO-001'] },
      { term: 'Needs-mask', slug: 'needs-mask', group: 'Timing', text: 'A mask.', refs: [] },
    ]);
    expect(termSlug('ν verification')).toBe('ν-verification');
    expect(() => parseGlossary('# G\n\n### A b\n\nx\n\n### A-B\n\ny\n')).toThrow(/slug "a-b"/);
  });
});
