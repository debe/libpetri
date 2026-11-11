// @vitest-environment happy-dom
/**
 * The spec body as the reader shows it: a code paragraph is a code block, list lines become a
 * list, a glossary term keeps the punctuation after it on its line, and links stay safe.
 */
import { describe, expect, it } from 'vitest';
import { bodyNode } from '../src/app/reader.js';
import { inline, safeHref } from '../src/app/md.js';
import { ROLE_META, ROLE_ORDER } from '../src/app/status.js';
import { fixtureContext } from './reader-fixture.js';

describe('body paragraphs', () => {
  it('renders a code paragraph as a code block', () => {
    const pre = bodyNode(fixtureContext(), { kind: 'code', text: "output spec of transition '<t>' has <n> Timeout nodes" }, [], new Set());
    expect(pre.tagName).toBe('PRE');
    expect(pre.querySelector('code')?.textContent).toBe("output spec of transition '<t>' has <n> Timeout nodes");
  });

  it('renders list lines as a list (IO-015 lists the claim of each node kind)', () => {
    const text = '- **Place** — claims that place.\n- **ForwardInput** — claims `to`.\n- **And** — claims the union.';
    const node = bodyNode(fixtureContext(), { kind: 'prose', text }, [], new Set());
    expect([...node.querySelectorAll('ul > li')].map((li) => li.textContent?.split(' — ')[0])).toEqual(['Place', 'ForwardInput', 'And']);
  });
});

describe('inline details', () => {
  it('keeps a term and the full stop after it together', () => {
    const ctx = fixtureContext();
    const el = document.createElement('p');
    el.append(inline(ctx, 'It reads an inhibitor arc. Then more.', { terms: ['inhibitor-arc'] }));
    const wrap = el.querySelector('.term-wrap');
    expect(wrap?.textContent).toBe('inhibitor arc.');
    expect(wrap?.querySelector('button.term')).not.toBeNull();
  });

  it('refuses link targets with control characters or an unknown scheme', () => {
    expect(safeHref('\u0001javascript:alert(1)')).toBeNull();
    expect(safeHref('java\tscript:alert(1)')).toBeNull();
    expect(safeHref(' \u0000https://x.org')).toBeNull();
    expect(safeHref('vbscript:x')).toBeNull();
    expect(safeHref('01-core-model.md#core-031')).toBe('01-core-model.md#core-031');
    expect(safeHref('./a b')).toBeNull();
  });

  it('lists every evidence role once, in ROLE_META order', () => {
    expect(ROLE_ORDER).toEqual(Object.keys(ROLE_META));
  });
});
