// @vitest-environment happy-dom
import { afterEach, describe, expect, it } from 'vitest';
import {
  blockLabel,
  filtersToQuery,
  groupEvidence,
  groupOpen,
  leanRuns,
  matchesFilters,
  neighbour,
  quoteLayout,
  docLabel,
  parseFilters,
  renderReader,
  toggle,
} from '../src/app/reader.js';
import { formatRoute, R } from '../src/app/router.js';
import type { Evidence } from '../src/model.js';
import { fixtureContext, fixtureData } from './reader-fixture.js';

const render = (id: string | null, query: Record<string, string> = {}) => {
  const ctx = fixtureContext(fixtureData());
  const view = renderReader(ctx, R.req(id, query));
  document.body.replaceChildren(view.node);
  return { ctx, view, root: document.body };
};

afterEach(() => {
  document.body.replaceChildren();
});

describe('filters', () => {
  it('parse and print the query, dropping unknown values and defaults', () => {
    const f = parseFilters({ kind: 'F,X,B', lean: 'block,maybe', f: 'untested', q: ' core ' });
    expect(f).toEqual({ kinds: ['B', 'F'], lean: ['block'], flags: ['untested'], q: 'core' });
    expect(filtersToQuery(f)).toEqual({ kind: 'B,F', lean: 'block', f: 'untested', q: 'core' });
    expect(filtersToQuery(parseFilters({}))).toEqual({});
  });

  it('toggle keeps the canonical order', () => {
    expect(toggle(['F'], 'B', ['A', 'B', 'F'])).toEqual(['B', 'F']);
    expect(toggle(['B', 'F'], 'B', ['A', 'B', 'F'])).toEqual(['F']);
  });

  it('match within a filter by any value and across filters by all', () => {
    const ctx = fixtureContext();
    const ids = (q: Record<string, string>): string[] =>
      ctx.data.blocks.filter((b) => matchesFilters(ctx, b, parseFilters(q))).map((b) => b.id);
    expect(ids({ kind: 'F' })).toEqual(['IO-001', 'NU-021']);
    expect(ids({ lean: 'block' })).toEqual(['CORE-031', 'CONC-005']);
    expect(ids({ lean: 'cited,none' })).toEqual(['CORE-030', 'IO-001']);
    expect(ids({ lean: 'mention' })).toEqual(['NU-021']);
    expect(ids({ f: 'signed' })).toEqual(['CORE-031']);
    expect(ids({ f: 'defect' })).toEqual(['CORE-031']);
    expect(ids({ f: 'untested' })).toEqual(['CONC-005', 'NU-021']);
    expect(ids({ kind: 'B', f: 'untested' })).toEqual(['CONC-005']);
    expect(ids({ q: 'core031' })).toEqual(['CORE-031']);
    expect(ids({ q: 'inhibitor' })).toEqual(['CORE-031']);
    // Tombstones show only without filters.
    expect(ids({})).toContain('IO-006');
  });

  it('j/k move through the filtered list, from a hidden rule to its nearest neighbour', () => {
    const order = ['A-1', 'A-2', 'A-3', 'A-4'];
    expect(neighbour(order, order, 'A-2', 1)).toBe('A-3');
    expect(neighbour(order, order, 'A-1', -1)).toBeNull();
    expect(neighbour(order, ['A-1', 'A-4'], 'A-2', 1)).toBe('A-4');
    expect(neighbour(order, ['A-1', 'A-4'], 'A-3', -1)).toBe('A-1');
  });
});

describe('Lean helpers', () => {
  it('pairs quotes with reading lines only when their counts match', () => {
    const paired = quoteLayout(['q1', 'q2'], ['For every t:', 'r1', 'r2']);
    expect(paired).toEqual({ preamble: ['For every t:'], paired: true, quotes: ['q1', 'q2'], lines: ['r1', 'r2'] });
    // One reading line too many: two plain lists, nothing numbered.
    expect(quoteLayout(['q1', 'q2'], ['For every t:', 'r1', 'r2', 'r3']).paired).toBe(false);
    // A "Let ..." line sets the scene, like a line ending in a colon.
    expect(quoteLayout(['q'], ['Let Build be the builder.', 'r']).preamble).toEqual(['Let Build be the builder.']);
    expect(quoteLayout(['q'], ['Let Build be the builder.', 'r']).paired).toBe(true);
    // The last line is never preamble.
    expect(quoteLayout(['q'], ['only line:'])).toMatchObject({ preamble: [], paired: true });
  });

  it('labels a theorem docstring by what it holds for its role', () => {
    expect(docLabel('forbids')).toBe('Counterexample');
    expect(docLabel('nonvacuous')).toBe('Witness');
    expect(docLabel('holds')).toBe('What it says');
  });

  it('group evidence in the design order and open the important groups', () => {
    const ev = (role: Evidence['role']): Evidence => ({ theorem: role, role, module: 'M', doc: null });
    const groups = groupEvidence([ev('mutant'), ev('forbids'), ev('holds'), ev('forbids')]);
    expect(groups.map((g) => [g.role, g.items.length])).toEqual([['holds', 1], ['forbids', 2], ['mutant', 1]]);
    expect(groupOpen('holds', 30)).toBe(true);
    expect(groupOpen('forbids', 5)).toBe(false);
    expect(groupOpen('forbids', 4)).toBe(true);
  });

  it('labels companion blocks by their title suffix', () => {
    const lean = fixtureData().lean['CONC-005'] ?? [];
    expect(lean.map((b, i) => blockLabel(b, i))).toEqual(['CONC-005', 'CONC-005 (executor cycle)']);
  });

  it('splits a statement into keywords and connectives', () => {
    expect(leanRuns('∀ t, while p, never Fire t on x')).toEqual([
      { kind: 'sym', text: '∀' },
      { kind: 'text', text: ' t, ' },
      { kind: 'kw', text: 'while' },
      { kind: 'text', text: ' p, ' },
      { kind: 'kw', text: 'never' },
      { kind: 'text', text: ' Fire t ' },
      { kind: 'kw', text: 'on' },
      { kind: 'text', text: ' x' },
    ]);
  });
});

describe('reader view', () => {
  it('renders a rule with one h1, the spec beside What Lean checks, and the side panels', () => {
    const { view, root } = render('CORE-031');
    expect(view.title).toBe('CORE-031 Inhibitor Arc');
    expect(root.querySelectorAll('h1')).toHaveLength(1);
    expect(root.querySelector('h1')?.textContent).toBe('Inhibitor Arc');
    expect(root.querySelector('nav[aria-label="Requirements"]')).not.toBeNull();
    expect(root.querySelector('aside[aria-label="Rule details"]')).not.toBeNull();
    expect(root.querySelector('.reader__lean h2')?.textContent).toBe('What Lean checks');
    expect(root.querySelectorAll('.reader__shall')).toHaveLength(1);
    expect(root.querySelector('.reader__shall .ears-trigger')?.textContent).toBe('While');
    // Pairs: preamble + two numbered rows.
    expect(root.querySelector('.reader__preamble')?.textContent).toContain('For every transition t');
    expect([...root.querySelectorAll('.reader__pair-n')].map((n) => n.textContent)).toEqual(['1', '2']);
    // Evidence groups in order, with proof graph links and docs as an Example disclosure.
    expect([...root.querySelectorAll('.reader__role-summary')].map((s) => s.textContent?.trim())).toEqual([
      '✓ holds · 1',
      '◉ nonvacuous · 1',
      '✗ forbids · 1',
      '✗m mutant killed · 1',
    ]);
    expect(root.querySelector('.reader__thm-pg')?.getAttribute('href')).toBe('../proof-graph/#Libpetri.Spec.CORE_031_reference');
    expect(root.querySelectorAll('.reader__example')).toHaveLength(2);
    // Signoff and hash.
    expect(root.querySelector('.reader__lean-foot')?.textContent).toContain('Signed 2026-11-10');
    expect(root.querySelector('.reader__lean-foot')?.textContent).toContain('4f884470b');
    // Acceptance and derivation.
    expect(root.querySelectorAll('.reader__acceptance li')).toHaveLength(2);
    expect(root.textContent).toContain('Test derivation');
    expect(root.textContent).toContain('No situation shows this rule yet.');
    // Side: depends on, the open defect, tests per language.
    expect(root.querySelector('.reader__side')?.textContent).toContain('Depends on (1)');
    expect(root.querySelector('.reader__side .reader__defect-badge')?.textContent).toContain('RD-01');
    const tests = [...root.querySelectorAll('.reader__test-name')].map((n) => n.textContent?.replace(' ⓘ', ''));
    expect(tests).toEqual(['Lean', 'Java', 'TypeScript', 'Rust', 'Python']);
    expect(root.querySelector('.reader__refs code')?.textContent).toBe('rust/libpetri-core/tests/arcs.rs');
    // Glossary terms marked once each.
    const terms = [...root.querySelectorAll('.reader__spec button.term')].map((b) => b.getAttribute('data-term'));
    expect(new Set(terms).size).toBe(terms.length);
    expect(terms).toContain('inhibitor-arc');
    // Notes never render markup.
    expect(root.querySelector('.reader__note b')).toBeNull();
    // The current nav row.
    expect(root.querySelector('.reader__row[aria-current="page"]')?.textContent).toContain('CORE-031');
    view.dispose?.();
  });

  it('shows companion blocks as extra cards', () => {
    const { root, view } = render('CONC-005');
    const cards = root.querySelectorAll('.reader__lean-block');
    expect(cards).toHaveLength(2);
    expect([...root.querySelectorAll('.reader__lean-block h3')].map((x) => x.textContent)).toEqual(['CONC-005', 'CONC-005 (executor cycle)']);
    // Companion blocks sit behind a tablist; arrow keys move the selection.
    const tabs = [...root.querySelectorAll<HTMLElement>('[role="tablist"] [role="tab"]')];
    expect(tabs.map((t) => t.textContent)).toEqual(['CONC-005', 'CONC-005 (executor cycle)']);
    const shown = (): number => [...root.querySelectorAll<HTMLElement>('[role="tabpanel"]')].filter((p) => !p.hidden).length;
    expect(shown()).toBe(1);
    tabs[0]?.dispatchEvent(new KeyboardEvent('keydown', { key: 'ArrowRight', bubbles: true }));
    expect(tabs[1]?.getAttribute('aria-selected')).toBe('true');
    expect(tabs[0]?.tabIndex).toBe(-1);
    expect(shown()).toBe(1);
    expect(root.querySelector('.reader__meta')?.textContent).toContain('Not signed');
    view.dispose?.();
  });

  it('shows the no-Lean card with citations or the mention state', () => {
    const cited = render('IO-001');
    expect(cited.root.querySelector('.reader__no-lean')?.textContent).toContain('No Lean block yet.');
    expect(cited.root.querySelector('.reader__no-lean')?.textContent).toContain('Cited by 1 theorem');
    cited.view.dispose?.();
    const mention = render('NU-021');
    expect(mention.root.querySelector('.reader__no-lean')?.textContent).toContain('Mentioned in Lean comments only.');
    mention.view.dispose?.();
  });

  it('renders a tombstone page without Lean column or side panels', () => {
    const { root, view } = render('IO-006');
    expect(root.querySelectorAll('h1')).toHaveLength(1);
    expect(root.textContent).toContain('This requirement was removed and is kept for traceability.');
    expect(root.querySelector('.reader__lean')).toBeNull();
    expect(root.querySelector('.reader__side')).toBeNull();
    expect(root.querySelector('.reader__tombstone a.req-id')?.textContent).toBe('NU-021');
    view.dispose?.();
  });

  it('accepts a lower-case or compact ID and explains an unknown one', () => {
    expect(render('core031').view.title).toBe('CORE-031 Inhibitor Arc');
    const unknown = render('CORE-999');
    expect(unknown.view.title).toBe('No requirement CORE-999');
    expect(unknown.root.querySelectorAll('h1')).toHaveLength(1);
    expect(unknown.root.textContent).toContain('this ID was never used');
  });

  it('renders the index with one card per file', () => {
    const { root, view } = render(null);
    expect(view.title).toBe('Rules');
    expect(root.querySelectorAll('h1')).toHaveLength(1);
    expect(root.querySelectorAll('.reader__file-card')).toHaveLength(4);
    expect(root.querySelector('.reader__file-card')?.getAttribute('href')).toBe('#/req/CORE-030');
    expect(root.querySelector('.view__lede')?.textContent).toBe('5 active requirements in 4 files. Each one has acceptance criteria; 2 have a Lean block.');
  });

  it('filters the nav from the query and writes chip changes back silently', () => {
    const { ctx, root, view } = render('CORE-031', { kind: 'F' });
    const rows = [...root.querySelectorAll('.reader__row')].map((r) => r.querySelector('.reader__row-id')?.textContent);
    expect(rows).toEqual(['IO-001', 'NU-021']);
    const chip = [...root.querySelectorAll<HTMLButtonElement>('.filter-chip')].find((b) => b.textContent?.startsWith('✓F'));
    expect(chip?.getAttribute('aria-pressed')).toBe('true');
    chip?.click();
    expect(chip?.getAttribute('aria-pressed')).toBe('false');
    const last = ctx.navigations[ctx.navigations.length - 1];
    expect(last?.options?.silent).toBe(true);
    expect(last && formatRoute(last.route)).toBe('#/req/CORE-031');
    // Without filters the tombstone row is back.
    expect(root.querySelector('.reader__row--removed')).not.toBeNull();
    // Row links keep the filters.
    const signed = [...root.querySelectorAll<HTMLButtonElement>('.filter-chip')].find((b) => b.textContent?.includes('Signed'));
    signed?.click();
    expect(root.querySelector('.reader__row')?.getAttribute('href')).toBe('#/req/CORE-031?f=signed');
    view.dispose?.();
  });

  it('shows the empty filter copy with a Clear filters button', () => {
    const { root, view } = render('CORE-031', { q: 'nothing-matches-this' });
    const empty = root.querySelector('.reader__empty');
    expect(empty?.hasAttribute('hidden')).toBe(false);
    expect(empty?.textContent).toContain('No rules match these filters.');
    empty?.querySelector('button')?.click();
    expect(root.querySelector('.reader__empty')?.hasAttribute('hidden')).toBe(true);
    view.dispose?.();
  });

  it('moves with j and k and stops listening after dispose', () => {
    const { ctx, view } = render('CORE-031');
    document.dispatchEvent(new KeyboardEvent('keydown', { key: 'j', bubbles: true }));
    document.dispatchEvent(new KeyboardEvent('keydown', { key: 'k', bubbles: true }));
    expect(ctx.navigations.map((n) => formatRoute(n.route))).toEqual(['#/req/IO-001', '#/req/CORE-030']);
    view.dispose?.();
    document.dispatchEvent(new KeyboardEvent('keydown', { key: 'j', bubbles: true }));
    expect(ctx.navigations).toHaveLength(2);
  });
});
