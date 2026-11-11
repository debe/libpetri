// @vitest-environment happy-dom
import { describe, expect, it } from 'vitest';
import { formatRoute } from '../src/app/router.js';
import { compact, highlightRuns, renderSearchPanel, searchSite, sentences, shortTheorem, snippetAround, words } from '../src/app/search.js';
import { fixtureContext, fixtureData } from './reader-fixture.js';

const ctx = fixtureContext();
const keys = (q: string): string[] => searchSite(ctx, q).map((h) => `${h.kind}:${h.key}`);

describe('normalisation', () => {
  it('ignores case, hyphens and spaces, and reads nu as ν', () => {
    expect(compact('CORE-031')).toBe('core031');
    expect(compact('core 031')).toBe('core031');
    expect(words('ν Join')).toEqual(['nu', 'join']);
  });

  it('splits sentences and clips snippets around the match', () => {
    expect(sentences('One thing. Two things: more. `x` here')).toEqual(['One thing.', 'Two things: more.', '`x` here']);
    expect(sentences('- Zero or more arcs\n| Inhibitor | No |\n|---|---|')).toEqual(['Zero or more arcs', 'Inhibitor · No']);
    const long = `${'a '.repeat(100)}needle ${'b '.repeat(100)}`;
    const s = snippetAround(long, ['needle']);
    expect(s).toContain('needle');
    expect(s.length).toBeLessThanOrEqual(162);
    expect(s.startsWith('…')).toBe(true);
  });

  it('shortens theorem names', () => {
    expect(shortTheorem('Libpetri.Spec.CORE_031_reference')).toBe('CORE_031_reference');
    expect(shortTheorem('Other.x')).toBe('Other.x');
  });
});

describe('ranking', () => {
  it('puts the exact ID first, also without the hyphen', () => {
    expect(keys('CORE-031')[0]).toBe('req:CORE-031');
    expect(keys('core031')[0]).toBe('req:CORE-031');
  });

  it('ranks ID prefixes above title words above body text', () => {
    const k = keys('core-03');
    expect(k.slice(0, 2)).toEqual(['req:CORE-030', 'req:CORE-031']);
    const inhib = keys('inhibitor');
    expect(inhib[0]).toBe('req:CORE-031');
    expect(inhib).toContain('term:inhibitor-arc');
    expect(inhib.indexOf('req:CORE-031')).toBeLessThan(inhib.indexOf('term:inhibitor-arc'));
  });

  it('finds theorems, defects and body sentences', () => {
    expect(keys('CORE_031_reference')).toContain('theorem:Libpetri.Spec.CORE_031_reference');
    expect(keys('RD-01')[0]).toBe('defect:RD-01');
    const body = searchSite(ctx, 'negative precondition');
    expect(body[0]?.key).toBe('CORE-031');
    expect(body[0]?.snippet).toContain('negative precondition');
  });

  it('finds ν through nu and ranks tombstones below live rules', () => {
    expect(keys('nu')).toContain('req:NU-021');
    const guard = searchSite(ctx, 'guard');
    expect(guard.map((h) => h.key)).toContain('IO-006');
  });

  it('returns nothing for an empty query and honours the limit', () => {
    expect(searchSite(ctx, '   ')).toEqual([]);
    expect(searchSite(ctx, 'a', 2)).toHaveLength(2);
  });

  it('routes rules to the reader and theorems to the graph', () => {
    const [rule] = searchSite(ctx, 'CORE-031');
    expect(rule && formatRoute(rule.route)).toBe('#/req/CORE-031');
    const thm = searchSite(ctx, 'CORE_031_reference').find((h) => h.kind === 'theorem');
    expect(thm && formatRoute(thm.route)).toBe('#/graph/thm:Libpetri.Spec.CORE_031_reference');
  });
});

describe('highlightRuns', () => {
  it('marks every query word, case-insensitively', () => {
    expect(highlightRuns('Inhibitor arc and inhibitor', ['inhibitor'])).toEqual([
      { mark: true, text: 'Inhibitor' },
      { mark: false, text: ' arc and ' },
      { mark: true, text: 'inhibitor' },
    ]);
  });
});

describe('panel', () => {
  it('shows grouped results with a combobox and moves with the arrow keys', () => {
    const c = fixtureContext(fixtureData());
    const panel = renderSearchPanel(c, 'inhibitor');
    document.body.append(panel);
    const input = panel.querySelector('input');
    expect(input?.getAttribute('role')).toBe('combobox');
    expect(input?.getAttribute('aria-expanded')).toBe('true');
    const options = panel.querySelectorAll('[role="option"]');
    expect(options.length).toBeGreaterThan(1);
    expect(panel.querySelector('.search__group-title')?.textContent).toContain('Rules');
    expect(input?.getAttribute('aria-activedescendant')).toBe(options[0]?.id);
    input?.dispatchEvent(new KeyboardEvent('keydown', { key: 'ArrowDown', bubbles: true }));
    expect(input?.getAttribute('aria-activedescendant')).toBe(options[1]?.id);
    input?.dispatchEvent(new KeyboardEvent('keydown', { key: 'ArrowUp', bubbles: true }));
    input?.dispatchEvent(new KeyboardEvent('keydown', { key: 'Enter', bubbles: true }));
    expect(c.navigations.map((n) => formatRoute(n.route))).toEqual(['#/req/CORE-031']);
    expect(panel.querySelector('mark')?.textContent?.toLowerCase()).toBe('inhibitor');
    panel.remove();
  });

  it('opens the graph with Ctrl Enter', () => {
    const c = fixtureContext(fixtureData());
    const panel = renderSearchPanel(c, 'CORE-031');
    panel.querySelector('input')?.dispatchEvent(new KeyboardEvent('keydown', { key: 'Enter', ctrlKey: true, bubbles: true }));
    expect(formatRoute(c.navigations[0]?.route ?? { view: 'notfound', path: '/', query: {} })).toBe('#/graph/CORE-031');
  });

  it('says so when nothing matches, and Esc first clears the query', () => {
    const c = fixtureContext(fixtureData());
    const panel = renderSearchPanel(c, 'zzzqqq');
    expect(panel.querySelector('.search__empty')?.textContent).toBe(
      'No matches for "zzzqqq". Try an ID like CORE-031, a term like inhibitor arc, or a theorem name.',
    );
    const input = panel.querySelector('input');
    const esc = new KeyboardEvent('keydown', { key: 'Escape', bubbles: true, cancelable: true });
    input?.dispatchEvent(esc);
    expect(esc.defaultPrevented).toBe(true);
    expect(input?.value).toBe('');
    expect(panel.querySelector('.search__try')).not.toBeNull();
    const esc2 = new KeyboardEvent('keydown', { key: 'Escape', bubbles: true, cancelable: true });
    input?.dispatchEvent(esc2);
    expect(esc2.defaultPrevented).toBe(false);
  });
});
