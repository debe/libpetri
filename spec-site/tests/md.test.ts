// @vitest-environment happy-dom
import { describe, expect, it } from 'vitest';
import { blocks, earsRole, inline, parseBlocks, parseInline, plainText, safeHref, splitBy, termPattern } from '../src/app/md.js';
import { fixtureContext } from './reader-fixture.js';

describe('parseInline', () => {
  it('reads code, emphasis, strong, requirement links and links', () => {
    expect(parseInline('a `x*y` *When* **bold** [CORE-031] [site](https://libpetri.org)')).toEqual([
      { t: 'text', v: 'a ' },
      { t: 'code', v: 'x*y' },
      { t: 'text', v: ' ' },
      { t: 'em', c: [{ t: 'text', v: 'When' }] },
      { t: 'text', v: ' ' },
      { t: 'strong', c: [{ t: 'text', v: 'bold' }] },
      { t: 'text', v: ' ' },
      { t: 'req', id: 'CORE-031' },
      { t: 'text', v: ' ' },
      { t: 'link', href: 'https://libpetri.org', c: [{ t: 'text', v: 'site' }] },
    ]);
  });

  it('leaves a lone star, an unclosed code span and plain brackets as text', () => {
    expect(plainText('a * b and `open and [not an id]')).toBe('a * b and `open and [not an id]');
  });

  it('nests strong inside emphasis', () => {
    expect(parseInline('*a **b** c*')).toEqual([
      { t: 'em', c: [{ t: 'text', v: 'a ' }, { t: 'strong', c: [{ t: 'text', v: 'b' }] }, { t: 'text', v: ' c' }] },
    ]);
  });

  it('honours backslash escapes', () => {
    expect(plainText('\\*not em\\*')).toBe('*not em*');
  });

  it('gives plain text with IDs kept', () => {
    expect(plainText('*While* p is marked, see [CORE-030]–[CORE-031].')).toBe('While p is marked, see CORE-030–CORE-031.');
  });
});

describe('parseBlocks', () => {
  it('splits paragraphs, lists, fences and tables', () => {
    const text = 'One\nline.\n\n- a\n- b\n  more\n\n2. x\n3. y\n\n```\ncode\n```\n\n| a | b |\n|---|---|\n\n> quoted';
    expect(parseBlocks(text)).toEqual([
      { t: 'p', text: 'One line.' },
      { t: 'ul', items: ['a', 'b more'] },
      { t: 'ol', items: ['x', 'y'], start: 2 },
      { t: 'pre', text: 'code' },
      { t: 'pre', text: '| a | b |\n|---|---|' },
      { t: 'quote', text: 'quoted' },
    ]);
  });
});

describe('helpers', () => {
  it('rejects unsafe link schemes', () => {
    expect(safeHref('javascript:alert(1)')).toBeNull();
    expect(safeHref('data:text/html,x')).toBeNull();
    expect(safeHref('https://libpetri.org/')).toBe('https://libpetri.org/');
    expect(safeHref('#/req/CORE-031')).toBe('#/req/CORE-031');
    expect(safeHref('../proof-graph/')).toBe('../proof-graph/');
  });

  it('knows the EARS words', () => {
    expect(earsRole('When')).toBe('trigger');
    expect(earsRole('then')).toBe('trigger');
    expect(earsRole('shall not')).toBe('modal');
    expect(earsRole('never')).toBe('modal');
    expect(earsRole('marked')).toBeNull();
  });

  it('matches terms with plurals, not inside words', () => {
    const re = termPattern(['Place', 'Inhibitor arc']);
    expect(re).not.toBeNull();
    const found = (text: string): string[] => [...text.matchAll(re ?? /$^/g)].map((m) => m[0]);
    expect(found('Two places and an inhibitor arcs.')).toEqual(['places', 'inhibitor arcs']);
    expect(found('replace placed workplace')).toEqual([]);
  });

  it('splits text by a pattern', () => {
    expect(splitBy('a shall b shall not c', /\bshall(?: not)?\b/g).map((p) => p.text)).toEqual(['a ', 'shall', ' b ', 'shall not', ' c']);
  });
});

describe('rendering', () => {
  const ctx = fixtureContext();

  it('highlights EARS words and links IDs', () => {
    const el = document.createElement('p');
    el.append(inline(ctx, '*While* p is marked, t *shall not* fire [CORE-030].'));
    expect(el.querySelector('.ears-trigger')?.textContent).toBe('While');
    expect(el.querySelector('.ears-modal')?.textContent).toBe('shall not');
    expect(el.querySelector('a.req-id')?.getAttribute('href')).toBe('#/req/CORE-030');
  });

  it('turns EARS off on request', () => {
    const el = document.createElement('p');
    el.append(inline(ctx, '*While* x *shall* y', { ears: false }));
    expect(el.querySelector('.ears-trigger')).toBeNull();
    expect(el.querySelectorAll('em')).toHaveLength(2);
  });

  it('never turns text into markup', () => {
    const el = document.createElement('div');
    el.append(blocks(ctx, 'Text with <b>bold</b> and <script>x</script>.\n\n[x](javascript:alert(1))'));
    expect(el.querySelector('b')).toBeNull();
    expect(el.querySelector('script')).toBeNull();
    expect(el.querySelector('a')).toBeNull();
    expect(el.textContent).toContain('<b>bold</b>');
  });

  it('marks the first occurrence of a term per requirement only', () => {
    const seen = new Set<string>();
    const el = document.createElement('div');
    el.append(inline(ctx, 'An inhibitor arc on a place. Another inhibitor arc.', { terms: ['inhibitor-arc', 'place'], seen }));
    el.append(inline(ctx, 'The place again, an inhibitor arc again.', { terms: ['inhibitor-arc', 'place'], seen }));
    const marked = [...el.querySelectorAll('button.term')].map((b) => b.getAttribute('data-term'));
    expect(marked).toEqual(['inhibitor-arc', 'place']);
  });

  it('does not mark terms inside code or links', () => {
    const el = document.createElement('div');
    el.append(inline(ctx, '`place` and [a place](https://x.org)', { terms: true }));
    expect(el.querySelector('button.term')).toBeNull();
  });
});
