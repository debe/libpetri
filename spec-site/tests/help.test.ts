// @vitest-environment happy-dom
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, expect, it } from 'vitest';
import type { AppContext } from '../src/app/context.js';
import { EARS_NOTATION, HELP_SECTIONS, helpSectionId, keySeparator, LEAN_NAMES, type LegendRow, renderHelpPanel } from '../src/app/help.js';
import { buildIndex } from '../src/app/indexes.js';
import { SHORTCUTS } from '../src/app/shortcuts.js';
import { buildSiteData } from '../src/gen/site.js';

// happy-dom replaces import.meta.url, so resolve from the package root vitest runs in.
const REPORT = resolve(process.cwd(), '../lean/report/requirements.md');

/** The rows of the first Markdown table after the line `**<title>**` in the report. */
function reportTable(text: string, title: string): readonly LegendRow[] {
  const lines = text.split('\n');
  const start = lines.findIndex((l) => l.startsWith(`**${title}**`));
  if (start < 0) throw new Error(`no "${title}" in the report`);
  const rows: LegendRow[] = [];
  let inTable = false;
  for (const line of lines.slice(start + 1)) {
    if (line.startsWith('|')) {
      inTable = true;
      const cells = line.slice(1, -1).split(' | ').map((c) => c.trim());
      const [term, meaning] = cells;
      if (term === undefined || meaning === undefined || /^-+$/.test(term)) continue;
      rows.push({ term, meaning });
    } else if (inTable) break;
  }
  return rows.slice(1); // drop the header row
}

function context(): AppContext {
  const data = buildSiteData({
    spec: { files: [], blocks: [] },
    glossary: [],
    lean: { blocks: [], citations: [] },
    coverage: {},
    defects: [],
    situations: [],
    diagrams: new Set(),
  });
  return { data, index: buildIndex(data), render: () => { throw new Error('unused'); }, navigate: () => {} };
}

describe('help: Lean tables follow the generated report', () => {
  const report = readFileSync(REPORT, 'utf8');

  it('names in the Lean statements', () => {
    expect(LEAN_NAMES).toEqual(reportTable(report, 'Names in the Lean statements'));
  });

  it('EARS keywords', () => {
    expect(EARS_NOTATION).toEqual(reportTable(report, 'EARS keywords'));
  });
});

describe('help panel', () => {
  it('has the four sections as h2 with their ids and no h1', () => {
    const panel = renderHelpPanel(context());
    expect(panel.querySelectorAll('h1')).toHaveLength(0);
    for (const s of HELP_SECTIONS) expect(panel.querySelector(`#${helpSectionId(s.section)}`)?.tagName).toBe('H2');
    expect(panel.querySelectorAll('.help__keys dt')).toHaveLength(SHORTCUTS.length);
  });

  it('adds a close button only when asked', () => {
    let closed = 0;
    expect(renderHelpPanel(context()).querySelector('.help__close')).toBeNull();
    renderHelpPanel(context(), () => closed++).querySelector<HTMLButtonElement>('.help__close')?.click();
    expect(closed).toBe(1);
  });

  it('joins keys as chords, sequences or alternatives', () => {
    expect(keySeparator(['Ctrl', 'K'])).toBe('+');
    expect(keySeparator(['g', 's'])).toBe('then');
    expect(keySeparator(['j', 'k'])).toBe('/');
    expect(keySeparator(['Home', 'End'])).toBe('/');
  });
});
