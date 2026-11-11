// @vitest-environment happy-dom
import { afterEach, describe, expect, it } from 'vitest';
import {
  hopLabel,
  impactLayers,
  impactMarkdown,
  impactOf,
  impactTotals,
  mostConnected,
  neighbourGroups,
  nodeComparator,
  nodeInfo,
  pickerMatches,
  renderGraph,
} from '../src/app/graph.js';
import { R, reqGraph } from '../src/app/router.js';
import { nodeKey } from '../src/model.js';
import { fixtureCtx } from './conf-graph-fixture.js';

const ctx = fixtureCtx();
const core1 = { kind: 'req', id: 'CORE-001' } as const;
const keys = (layers: readonly (readonly { readonly key: string }[])[]): string[][] => layers.map((l) => l.map((x) => x.key));

describe('impact BFS', () => {
  it('walks incoming edges by distance, three hops, mentions left out by default', () => {
    const impact = impactOf(ctx.index, core1, { compare: nodeComparator(ctx.data) });
    expect(keys(impact.layers)).toEqual([['CORE-002'], ['CORE-004'], ['IO-001', 'sit:s1', 'RD-01']]);
    // IO-002 and the citing theorem (4 hops), RD-02 (5 hops).
    expect(impact.beyond).toBe(3);
  });

  it('records the node each hit was reached through and the edge kind', () => {
    const impact = impactOf(ctx.index, core1);
    const third = impact.layers[2] ?? [];
    expect(third.map((h) => [h.key, nodeKey(h.via), h.edge])).toContainEqual(['RD-01', 'CORE-004', 'breaks']);
    expect(impact.layers[0]?.[0]).toMatchObject({ key: 'CORE-002', edge: 'depends-on', viaKey: 'CORE-001' });
  });

  it('follows mentions when asked, keeping each node at its shortest distance', () => {
    const impact = impactOf(ctx.index, core1, { mentions: true, compare: nodeComparator(ctx.data) });
    expect(keys(impact.layers)).toEqual([
      ['CORE-002', 'CORE-004'],
      ['IO-001', 'IO-002', 'sit:s1', 'RD-01'],
      ['thm:Libpetri.Spec.io_fragment', 'RD-02'],
    ]);
    expect(impact.beyond).toBe(0);
  });

  it('honours the hop limit and handles leaves and unknown nodes', () => {
    expect(impactOf(ctx.index, core1, { hops: 1 }).beyond).toBe(7);
    expect(impactOf(ctx.index, { kind: 'defect', id: 'RD-01' }).layers).toEqual([]);
    expect(impactOf(ctx.index, { kind: 'req', id: 'NOPE-1' })).toEqual({ layers: [], beyond: 0, depth: 0 });
  });

  it('starts from a theorem: the rules that use it as evidence', () => {
    const impact = impactOf(ctx.index, { kind: 'theorem', name: 'Libpetri.Spec.CORE_004_holds' }, { hops: 1 });
    expect(keys(impact.layers)).toEqual([['CORE-004']]);
    expect(impact.layers[0]?.[0]?.edge).toBe('evidence');
  });

  it('keeps the requirement-only layers of impactLayers', () => {
    expect(impactLayers(ctx.index, 'CORE-001')).toEqual([['CORE-001'], ['CORE-002'], ['CORE-004'], ['IO-001'], ['IO-002']]);
  });

  it('labels hops and totals by kind', () => {
    expect([0, 1, 2].map(hopLabel)).toEqual(['Directly', '2 steps', '3 steps']);
    const impact = impactOf(ctx.index, core1, { mentions: true });
    expect(impactTotals(ctx, impact)).toBe('In all: 4 rules, 1 theorem, 1 situation, 1 open defect, 1 fixed defect.');
    // Fewer layers than the closure: the line says how far it looks.
    expect(impactTotals(ctx, impactOf(ctx.index, core1, { mentions: true, hops: 1 }))).toMatch(/^Within 1 step: /);
  });

  it('writes the impact as Markdown', () => {
    const md = impactMarkdown(ctx, core1, impactOf(ctx.index, core1, { compare: nodeComparator(ctx.data) }));
    expect(md).toBe([
      '## Impact of CORE-001 Place',
      '',
      'If CORE-001 changes, these depend on it, directly or through others.',
      '',
      '### Directly (1)',
      '',
      '- CORE-002 Token: depends on it',
      '',
      '### 2 steps (1)',
      '',
      '- CORE-004 Arc: via CORE-002',
      '',
      '### 3 steps (3)',
      '',
      '- IO-001 Input: via CORE-004',
      '- Blocked arc (situation): via CORE-004',
      '- RD-01 Arc ignored (defect): via CORE-004',
      '',
      'Within 3 steps: 3 rules, 1 situation, 1 open defect.',
      '',
      '3 more nodes are 4 to 5 steps away.',
      '',
    ].join('\n'));
    expect(impactMarkdown(ctx, { kind: 'defect', id: 'RD-01' }, { layers: [], beyond: 0, depth: 0 })).toBe('## Impact of RD-01\n\nNothing depends on RD-01.\n');
  });
});

describe('neighbourhood', () => {
  it('groups edges by kind in both directions', () => {
    const cmp = nodeComparator(ctx.data);
    const incoming = neighbourGroups(ctx.index, 'CORE-004', 'in', cmp);
    expect(incoming.map((g) => [g.label, g.items.map((i) => i.key)])).toEqual([
      ['Used by', ['IO-001']],
      ['Shown in situations', ['sit:s1']],
      ['Defects', ['RD-01']],
    ]);
    const outgoing = neighbourGroups(ctx.index, 'CORE-004', 'out', cmp);
    expect(outgoing.map((g) => [g.label, g.items.map((i) => i.key)])).toEqual([
      ['Depends on', ['CORE-002']],
      ['Mentions', ['CORE-001']],
      ['Evidence', ['thm:Libpetri.Spec.CORE_004_holds']],
      ['Uses terms', ['term:inhibitor-arc']],
    ]);
  });

  it('describes nodes and flags unknown ones', () => {
    expect(nodeInfo(ctx, { kind: 'theorem', name: 'Libpetri.Spec.CORE_001_holds' })).toMatchObject({ label: 'CORE_001_holds', exists: true });
    expect(nodeInfo(ctx, { kind: 'term', slug: 'inhibitor-arc' })).toMatchObject({ label: 'Inhibitor arc', exists: true });
    expect(nodeInfo(ctx, { kind: 'req', id: 'CORE-999' }).exists).toBe(false);
    expect(nodeInfo(ctx, { kind: 'theorem', name: 'Nope' }).exists).toBe(false);
  });

  it('finds picker matches and the most connected rules', () => {
    // The exact ID ranks first; a theorem whose name contains it follows.
    expect(pickerMatches(ctx, 'core-004').map(nodeKey)).toEqual(['CORE-004', 'thm:Libpetri.Spec.CORE_004_holds']);
    expect(pickerMatches(ctx, 'inhib').map(nodeKey)).toEqual(['term:inhibitor-arc']);
    expect(pickerMatches(ctx, 'core_001_h').map(nodeKey)).toEqual(['thm:Libpetri.Spec.CORE_001_holds']);
    expect(pickerMatches(ctx, '')).toEqual([]);
    expect(mostConnected(ctx, 2)).toEqual(['CORE-004', 'CORE-001']);
  });
});

describe('renderGraph', () => {
  afterEach(() => document.body.replaceChildren());

  const routes = [
    R.graph(),
    reqGraph('CORE-004'),
    reqGraph('CORE-004', 'impact'),
    reqGraph('CORE-003'),
    reqGraph('NOPE-1'),
    reqGraph('NOPE-1', 'impact'),
    R.graph({ kind: 'term', slug: 'inhibitor-arc' }),
    R.graph({ kind: 'theorem', name: 'Libpetri.Spec.CORE_001_holds' }),
    R.graph({ kind: 'defect', id: 'RD-02' }),
    R.graph({ kind: 'situation', slug: 's1' }),
    R.impact({ kind: 'defect', id: 'RD-01' }),
  ];

  it.each(routes.map((r) => [r]))('renders %j with one h1 and a title', (route) => {
    const view = renderGraph(ctx, route);
    document.body.append(view.node);
    expect(document.querySelectorAll('h1').length).toBe(1);
    expect(view.title).not.toBe('');
    view.dispose?.();
  });

  it('draws dependency columns that count depends-on edges only, as the rule page does', () => {
    const view = renderGraph(ctx, reqGraph('CORE-004'));
    document.body.append(view.node);
    expect(view.title).toBe('Graph: CORE-004');
    expect(document.querySelector('.graph__focus-title')?.textContent).toBe('Arc');
    const title = (key: string): string | null | undefined => document.querySelector(`.graph__col--${key} .graph__col-title`)?.textContent;
    expect(title('depends')).toBe('Depends on (1)');
    expect(title('usedby')).toBe('Used by (1)');
    expect(title('lean')).toBe('Lean and terms (2)');
    expect(title('other')).toBe('Mentions and situations (3)');
    expect(document.querySelector('.graph__col--lean .graph__tag')?.textContent).toContain('holds');
    expect(Array.from(document.querySelectorAll('.graph__col--other .graph__group-title')).map((e) => e.textContent))
      .toEqual(['Mentions (1)', 'Shown in situations (1)', 'Defects (1)']);
    view.dispose?.();
  });

  it('shows the impact columns and the not-found copy', () => {
    const view = renderGraph(ctx, reqGraph('CORE-001', 'impact'));
    document.body.append(view.node);
    expect(Array.from(document.querySelectorAll('.graph__hop h2')).map((e) => e.textContent)).toEqual(['Directly (1 rule)', '2 steps (1 rule)', '3 steps (1 rule)']);
    // Theorems, situations and defects get their own groups under the rule count.
    expect(Array.from(document.querySelectorAll('.graph__hop:nth-child(3) .graph__group-title')).map((e) => e.textContent)).toEqual(['Rules (1)', 'Situations (1)', 'Defects (1)']);
    document.querySelector<HTMLButtonElement>('.graph__toggle')?.click();
    expect(Array.from(document.querySelectorAll('.graph__hop h2')).map((e) => e.textContent)).toEqual(['Directly (2 rules)', '2 steps (2 rules)', '3 steps (0 rules)']);
    view.dispose?.();
    document.body.replaceChildren();
    const missing = renderGraph(ctx, reqGraph('NOPE-1'));
    document.body.append(missing.node);
    expect(document.body.textContent).toContain('No requirement NOPE-1. Removed requirements stay listed as tombstones; this ID was never used.');
    missing.dispose?.();
  });

  it('toggles neighbourhood and impact with i', () => {
    const local = fixtureCtx();
    const view = renderGraph(local, reqGraph('CORE-004'));
    document.body.append(view.node);
    document.dispatchEvent(new KeyboardEvent('keydown', { key: 'i', bubbles: true }));
    expect(local.navigations).toEqual([{ route: reqGraph('CORE-004', 'impact'), options: undefined }]);
    view.dispose?.();
    document.dispatchEvent(new KeyboardEvent('keydown', { key: 'i', bubbles: true }));
    expect(local.navigations.length).toBe(1);
  });
});
