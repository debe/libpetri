import { describe, expect, it } from 'vitest';
import { mapToGraph } from 'libpetri/export';
import type { CorpusNet, NetTransition } from '../src/model.js';
import {
  annotateSvg,
  buildPetriNet,
  decodeEntities,
  dotOrder,
  nodeKindOf,
  renderDiagram,
  renderDiagrams,
  situationGraph,
} from '../src/gen/diagrams.js';
import { loadSituation, situationSlugs } from './player-fixture.js';

function t(name: string, extra: Partial<NetTransition> = {}): NetTransition {
  return { name, inputs: [], inhibitors: [], reads: [], resets: [], output: null, priority: 0, timing: null, ...extra };
}

/** Every arc kind, a junction pair and a place name `sanitize` changes. */
const RICH: CorpusNet = {
  places: ['in-box', 'lock', 'cfg', 'log', 'a', 'b', 'c'],
  marking: { 'in-box': 2, cfg: 1 },
  properties: [],
  transitions: [
    t('take it', {
      inputs: [{ kind: 'exactly', place: 'in-box', n: 2 }],
      inhibitors: ['lock'],
      reads: ['cfg'],
      resets: ['log'],
      output: { type: 'xor', children: [{ type: 'place', place: 'a' }, { type: 'and', children: [{ type: 'place', place: 'b' }, { type: 'place', place: 'c' }] }] },
      priority: 2,
      timing: { kind: 'window', earliestMs: 5, latestMs: 50 },
    }),
  ],
};

const attrs = (svg: string, name: string): string[] => [...svg.matchAll(new RegExp(`${name}="([^"]*)"`, 'g'))].map((m) => m[1] ?? '');

describe('buildPetriNet', () => {
  it('builds the net with the libpetri builder, keeping names and arcs', () => {
    const net = buildPetriNet('rich', RICH);
    const take = net.transitions.values().next().value;
    expect(take?.name).toBe('take it');
    expect(take?.inhibitors.map((a) => a.place.name)).toEqual(['lock']);
    expect(take?.reads.map((a) => a.place.name)).toEqual(['cfg']);
    expect(take?.resets.map((a) => a.place.name)).toEqual(['log']);
    expect(take?.priority).toBe(2);
  });

  it('refuses a net the builder refuses (two input arcs on one place)', () => {
    const bad: CorpusNet = { ...RICH, transitions: [t('x', { inputs: [{ kind: 'one', place: 'p' }, { kind: 'one', place: 'p' }] })] };
    expect(() => buildPetriNet('bad', bad)).toThrow();
  });
});

describe('annotateSvg', () => {
  it('adds data attributes from the graph and strips ids, prolog and comments', async () => {
    const svg = await renderDiagram('rich', RICH);
    expect(svg.startsWith('<svg preserveAspectRatio="xMidYMid meet"')).toBe(true);
    expect(svg).not.toMatch(/\sid="/);
    expect(svg).not.toMatch(/<\?xml|<!DOCTYPE|<!--|<script|<\/template/);
    expect(attrs(svg, 'data-node')).toEqual(expect.arrayContaining(['p_in_box', 'p_lock', 't_take_it', 'j_take_it__xor_0', 'j_take_it__and_1']));
    // data-name maps back to the net's own names, not the sanitized ids.
    expect(svg).toContain('data-node="p_in_box" data-kind="place" data-name="in-box"');
    expect(svg).toContain('data-node="t_take_it" data-kind="transition" data-name="take it"');
    expect(svg).toContain('data-kind="junction" data-name="j_take_it__xor_0"');
    const arcs = new Map(attrs(svg, 'data-edge').map((e, i) => [e.replace(/&gt;/g, '>'), attrs(svg, 'data-arc')[i]]));
    expect(arcs.get('p_in_box->t_take_it')).toBe('input');
    expect(arcs.get('p_lock->t_take_it')).toBe('inhibitor');
    expect(arcs.get('p_cfg->t_take_it')).toBe('read');
    expect(arcs.get('t_take_it->p_log')).toBe('reset');
    expect(arcs.get('t_take_it->j_take_it__xor_0')).toBe('output');
  });

  it('keeps the exporter colours (EXP rules): no restyling', async () => {
    const svg = await renderDiagram('rich', RICH);
    expect(svg).toContain('fill="#fff3cd"'); // transition fill
    expect(svg).toContain('stroke="#dc3545"'); // inhibitor arc
  });

  it('is deterministic', async () => {
    expect(await renderDiagram('rich', RICH)).toBe(await renderDiagram('rich', RICH));
  });

  it('fails when a group title does not match the graph', () => {
    const { graph } = situationGraph('rich', RICH);
    const svg = '<svg viewBox="0 0 1 1"><g id="graph0" class="graph"><g id="node1" class="node">\n<title>p_wrong</title></g></g></svg>';
    expect(() => annotateSvg(svg, graph)).toThrow(/node1 is 'p_wrong'/);
  });

  it('fails when groups are missing', () => {
    const { graph } = situationGraph('rich', RICH);
    expect(() => annotateSvg('<svg viewBox="0 0 1 1"></svg>', graph)).toThrow(/0 node and 0 edge groups/);
  });

  it('follows renderDot order through clusters (prefixed names)', async () => {
    const net: CorpusNet = {
      places: [],
      marking: {},
      properties: [],
      transitions: [
        t('left/go', { inputs: [{ kind: 'one', place: 'left/in' }], output: { type: 'place', place: 'shared' } }),
        t('right/go', { inputs: [{ kind: 'one', place: 'right/in' }], output: { type: 'place', place: 'right/out' } }),
      ],
    };
    const graph = mapToGraph(buildPetriNet('clusters', net));
    expect(graph.subgraphs.length).toBeGreaterThan(0);
    const order = dotOrder(graph);
    expect(order.nodes.length).toBe(6);
    const svg = await renderDiagram('clusters', net);
    expect(svg).toContain('data-name="left/go"');
    expect(svg).not.toMatch(/\sid="/);
  });
});

describe('helpers', () => {
  it('decodes the character references Graphviz writes', () => {
    expect(decodeEntities('p_a&#45;&gt;t_b')).toBe('p_a->t_b');
    expect(decodeEntities('&#x41;&amp;&lt;&quot;&unknown;')).toBe('A&<"&unknown;');
  });

  it('names node kinds by EXP-014 prefix', () => {
    expect(nodeKindOf('p_x')).toBe('place');
    expect(nodeKindOf('t_x')).toBe('transition');
    expect(nodeKindOf('j_x__xor_0')).toBe('junction');
    expect(() => nodeKindOf('x')).toThrow();
  });
});

describe('authored situations', () => {
  it('render, with a place node for every arc place and a transition node per transition', async () => {
    const inputs = situationSlugs().map(loadSituation);
    expect(inputs.length).toBeGreaterThan(0);
    const diagrams = await renderDiagrams(inputs);
    expect([...diagrams.keys()]).toEqual(situationSlugs());
    for (const { situation } of inputs) {
      const svg = diagrams.get(situation.slug) ?? '';
      for (const tr of situation.net.transitions) {
        expect(svg).toContain(`data-kind="transition" data-name="${tr.name}"`);
        for (const arc of tr.inputs) expect(svg).toContain(`data-kind="place" data-name="${arc.place}"`);
      }
    }
  });

  it('report the situation file when a net does not build', async () => {
    const { situation } = loadSituation(situationSlugs()[0] ?? '');
    const broken = { ...situation, net: { ...situation.net, transitions: [t('x', { inputs: [{ kind: 'exactly', place: 'p', n: 0 }] })] } };
    await expect(renderDiagrams([{ situation: broken, result: null }])).rejects.toThrow(/spec\/situations\/.*\.json: diagram/);
  });
});
