// @vitest-environment happy-dom
import { afterEach, describe, expect, it } from 'vitest';
import {
  buildConfRows,
  cellDisplay,
  columnSummary,
  confBands,
  confQuery,
  matchesText,
  moveInGrid,
  NO_FILTERS,
  parseConfFilters,
  renderConf,
} from '../src/app/conf.js';
import { closeAllOverlays } from '../src/app/overlay.js';
import { R } from '../src/app/router.js';
import { fixtureCtx } from './conf-graph-fixture.js';

const ids = (rows: readonly { readonly block: { readonly id: string } }[]): string[] => rows.map((r) => r.block.id);

describe('conformance matrix derivation', () => {
  const ctx = fixtureCtx();
  const rows = buildConfRows(ctx);
  const row = (id: string) => {
    const r = rows.find((x) => x.block.id === id);
    if (r === undefined) throw new Error(`no row ${id}`);
    return r;
  };

  it('has one row per active requirement, in spec order, tombstones left out', () => {
    expect(ids(rows)).toEqual(['CORE-001', 'CORE-002', 'CORE-004', 'IO-001', 'IO-002']);
  });

  it('derives the Lean state: block, mention, cited, none', () => {
    expect(rows.map((r) => r.lean)).toEqual(['block', 'mention', 'block', 'cited', 'none']);
  });

  it('lets an open defect override tested for its runtimes only; fixed defects do not count', () => {
    expect(row('CORE-004').tests.typescript.state).toBe('defect');
    expect(row('CORE-004').tests.python.state).toBe('defect');
    expect(row('CORE-004').tests.java.state).toBe('tested');
    expect(row('IO-002').tests.java.state).toBe('untested');
    expect(ids(rows.filter((r) => r.defects.length > 0))).toEqual(['CORE-004']);
  });

  it('marks rows untested when no runtime has a test file', () => {
    expect(ids(rows.filter((r) => r.untested))).toEqual(['CORE-002', 'IO-001']);
    expect(rows.filter((r) => r.untested).length).toBe(ctx.data.counts.untestedIds);
  });

  it('shows the defect ID in the cell, the word for screen readers', () => {
    const d = cellDisplay(row('CORE-004'), 'typescript');
    expect(d).toMatchObject({ glyph: '⚠', text: 'RD-01', tone: 'defect' });
    // The defect cell still says whether a test file cites the rule.
    expect(d.word).toMatch(/^open defect RD-01; (a|no) test file cites the rule$/);
    expect(d.under).toBe(d.word.endsWith('no test file cites the rule') ? '○' : '✓');
    expect(cellDisplay(row('CORE-001'), 'java')).toMatchObject({ glyph: '✓', text: '', word: 'tested', tone: 'ok' });
    expect(cellDisplay(row('IO-001'), 'lean')).toMatchObject({ glyph: '◇', word: 'cited' });
  });

  it('summarises each column with counts that add up', () => {
    const ts = columnSummary(rows, 'typescript');
    expect(ts.text).toBe('1 tested · 1 open defect · 3 untested');
    expect(ts.segments.reduce((n, s) => n + s.count, 0)).toBe(rows.length);
    expect(columnSummary(rows, 'lean').text).toBe('2 with a Lean block · 1 cited · 1 mentioned · 1 none');
  });

  it('round-trips filters through the route query and drops defaults', () => {
    const f = parseConfFilters({ f: 'untested,defects,bogus', kind: 'f,b,Z', q: 'arc', gap: 'python' });
    expect(f).toEqual({ q: 'arc', defectsFirst: true, untested: true, noLean: false, gap: 'python', kinds: ['B', 'F'] });
    expect(confQuery(f)).toEqual({ f: 'defects,untested', gap: 'python', kind: 'B,F', q: 'arc' });
    expect(parseConfFilters({ gap: 'cobol' }).gap).toBeNull();
    expect(confQuery(NO_FILTERS)).toEqual({});
    expect(parseConfFilters({})).toEqual(NO_FILTERS);
  });

  it('matches IDs ignoring case and hyphens, titles by every word', () => {
    const b = row('CORE-004').block;
    expect(matchesText(b, 'core004')).toBe(true);
    expect(matchesText(b, 'CORE-00')).toBe(true);
    expect(matchesText(b, 'arc')).toBe(true);
    expect(matchesText(b, 'arc input')).toBe(false);
    expect(matchesText(b, '  ')).toBe(true);
  });

  it('groups rows by file and applies filters with AND', () => {
    const all = confBands(ctx.data, rows, NO_FILTERS);
    expect(all.map((b) => [b.title, b.prefixes, b.total, ids(b.rows)])).toEqual([
      ['01 Core Model', 'CORE', 3, ['CORE-001', 'CORE-002', 'CORE-004']],
      ['03 Input and Output', 'IO', 2, ['IO-001', 'IO-002']],
    ]);
    const first = confBands(ctx.data, rows, { ...NO_FILTERS, defectsFirst: true });
    expect(ids(first[0]?.rows ?? [])).toEqual(['CORE-004', 'CORE-001', 'CORE-002']);
    const untested = confBands(ctx.data, rows, { ...NO_FILTERS, untested: true, kinds: ['T'] });
    expect(untested.map((b) => ids(b.rows))).toEqual([[], ['IO-001']]);
    const noLean = confBands(ctx.data, rows, { ...NO_FILTERS, noLean: true });
    expect(noLean.flatMap((b) => ids(b.rows))).toEqual(['CORE-002', 'IO-001', 'IO-002']);
  });
});

describe('moveInGrid', () => {
  // A band row (1 item), two data rows (6 items), a band row, a data row.
  const widths = [1, 6, 6, 1, 6];

  it('moves within a row and clamps at the ends', () => {
    expect(moveInGrid(widths, { row: 1, col: 2 }, 'ArrowRight', false, 2)).toEqual({ row: 1, col: 3 });
    expect(moveInGrid(widths, { row: 1, col: 5 }, 'ArrowRight', false, 5)).toEqual({ row: 1, col: 5 });
    expect(moveInGrid(widths, { row: 1, col: 0 }, 'ArrowLeft', false, 0)).toEqual({ row: 1, col: 0 });
    expect(moveInGrid(widths, { row: 2, col: 3 }, 'Home', false, 3)).toEqual({ row: 2, col: 0 });
    expect(moveInGrid(widths, { row: 2, col: 3 }, 'End', false, 3)).toEqual({ row: 2, col: 5 });
  });

  it('keeps the wanted column through a one-item band row', () => {
    const onBand = moveInGrid(widths, { row: 2, col: 4 }, 'ArrowDown', false, 4);
    expect(onBand).toEqual({ row: 3, col: 0 });
    expect(moveInGrid(widths, onBand ?? { row: 0, col: 0 }, 'ArrowDown', false, 4)).toEqual({ row: 4, col: 4 });
  });

  it('jumps by page and to the grid corners, and ignores other keys', () => {
    expect(moveInGrid(widths, { row: 1, col: 1 }, 'PageDown', false, 1)).toEqual({ row: 4, col: 1 });
    expect(moveInGrid(widths, { row: 4, col: 1 }, 'PageUp', false, 1)).toEqual({ row: 0, col: 0 });
    expect(moveInGrid(widths, { row: 2, col: 2 }, 'Home', true, 2)).toEqual({ row: 0, col: 0 });
    expect(moveInGrid(widths, { row: 2, col: 2 }, 'End', true, 2)).toEqual({ row: 4, col: 5 });
    expect(moveInGrid(widths, { row: 2, col: 2 }, 'x', false, 2)).toBeNull();
    expect(moveInGrid([], { row: 0, col: 0 }, 'ArrowDown', false, 0)).toBeNull();
  });
});

describe('renderConf', () => {
  afterEach(() => {
    closeAllOverlays();
    document.body.replaceChildren();
  });

  it('renders one h1, the bands and one tab stop', () => {
    const view = renderConf(fixtureCtx(), R.conf());
    document.body.append(view.node);
    expect(view.title).toBe('Conformance');
    expect(document.querySelectorAll('h1').length).toBe(1);
    expect(document.querySelectorAll('tr[data-row]').length).toBe(5);
    expect(document.querySelectorAll('tr[data-band]').length).toBe(2);
    expect(document.querySelectorAll('table [tabindex="0"]').length).toBe(1);
    expect(document.querySelector('.conf__status')?.textContent).toBe('Showing 5 of 5 rules');
    view.dispose?.();
  });

  it('reads filters from the route and writes changes back silently', () => {
    const ctx = fixtureCtx();
    const view = renderConf(ctx, R.conf({ f: 'untested' }));
    document.body.append(view.node);
    expect(Array.from(document.querySelectorAll('tr[data-row]')).map((tr) => tr.getAttribute('data-id'))).toEqual(['CORE-002', 'IO-001']);
    const noLean = Array.from(document.querySelectorAll<HTMLButtonElement>('.conf__chip')).find((b) => b.textContent?.includes('No Lean block'));
    noLean?.click();
    expect(noLean?.getAttribute('aria-pressed')).toBe('true');
    expect(ctx.navigations.at(-1)).toEqual({ route: R.conf({ f: 'nolean,untested' }), options: { silent: true } });
    view.dispose?.();
  });

  it('shows the empty state with a working Clear filters button', () => {
    const view = renderConf(fixtureCtx(), R.conf({ q: 'nothing matches this' }));
    document.body.append(view.node);
    expect(document.querySelector('.conf__empty')?.textContent).toContain('No rules match these filters.');
    document.querySelector<HTMLButtonElement>('.conf__empty button')?.click();
    expect(document.querySelectorAll('tr[data-row]').length).toBe(5);
    view.dispose?.();
  });

  it('collapses a band and opens a cell drawer', () => {
    const view = renderConf(fixtureCtx(), R.conf());
    document.body.append(view.node);
    const band = document.querySelector<HTMLButtonElement>('button[data-band="01-core-model.md"]');
    band?.click();
    expect(band?.getAttribute('aria-expanded')).toBe('false');
    expect(document.querySelectorAll('tr[data-row]:not([hidden])').length).toBe(2);
    document.querySelector<HTMLButtonElement>('button[data-id="IO-002"][data-col="java"]')?.click();
    const drawer = document.querySelector('.drawer');
    expect(drawer?.getAttribute('aria-label')).toBe('IO-002 in Java');
    expect(drawer?.textContent).toContain('No Java test file cites this ID.');
    closeAllOverlays();
    document.querySelector<HTMLButtonElement>('button[data-id="IO-002"][data-col="rust"]')?.click();
    expect(document.querySelector('.drawer')?.textContent).toContain('rust/tests/io.rs');
    view.dispose?.();
  });

  it('moves the tab stop with the arrow keys', () => {
    const view = renderConf(fixtureCtx(), R.conf());
    document.body.append(view.node);
    const stop = document.querySelector<HTMLElement>('table [tabindex="0"]');
    expect(stop?.dataset['band']).toBe('01-core-model.md');
    stop?.focus();
    stop?.dispatchEvent(new KeyboardEvent('keydown', { key: 'ArrowDown', bubbles: true }));
    const next = document.activeElement;
    expect(next?.textContent).toBe('CORE-001');
    expect(next?.getAttribute('tabindex')).toBe('0');
    next?.dispatchEvent(new KeyboardEvent('keydown', { key: 'End', bubbles: true }));
    expect((document.activeElement as HTMLElement | null)?.dataset['col']).toBe('python');
    view.dispose?.();
  });
});
