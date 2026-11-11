/**
 * Body paragraphs read from the real spec: fenced code becomes its own `code` paragraph (never
 * text with backticks inside a paragraph), and list items keep one line each.
 */
import { describe, expect, it } from 'vitest';
import { readGlossary } from '../src/gen/inputs/glossary.js';
import { readSpec } from '../src/gen/inputs/spec.js';
import { REPO_ROOT } from '../src/gen/paths.js';

const spec = readSpec(REPO_ROOT, readGlossary(REPO_ROOT));
const body = (id: string) => spec.blocks.find((b) => b.id === id)?.body ?? [];

describe('spec body paragraphs', () => {
  it('keeps the error messages of IO-013 as code paragraphs', () => {
    expect(body('IO-013').filter((p) => p.kind === 'code').map((p) => p.text)).toEqual([
      "output spec of transition '<t>' has <n> Timeout nodes; an output spec has at most one, nested or not (IO-013)",
      "output spec of transition '<t>' has a Xor node inside the child of its Timeout node; the timeout outcome deposits one fixed set of places (IO-013)",
    ]);
  });

  it('has no fence left inside any paragraph of any requirement', () => {
    const leaks = spec.blocks.flatMap((b) => b.body.filter((p) => p.kind !== 'code' && p.text.includes('```')).map(() => b.id));
    expect(leaks).toEqual([]);
  });

  it('keeps the bullet list of IO-015 one item per line', () => {
    const list = body('IO-015').find((p) => p.text.startsWith('- **Place**'));
    expect(list?.text.split('\n').map((l) => /^- \*\*(\w+)\*\*/.exec(l)?.[1])).toEqual(['Place', 'ForwardInput', 'And', 'Xor', 'Timeout']);
  });
});
