/**
 * Integration regression net for the C0 instance-method API.
 *
 * The existing chrome tests in `cluster-overlay.test.ts` exercise the
 * sidebar-chip → handle.setVisibility callback chain end-to-end. This file
 * complements them by verifying direct API-level invocation of
 * `handle.highlight()` and `handle.setVisibility()` against the SVG
 * produced by the C0 pipeline (after `discoverClusters` + `tagReplicas` +
 * `annotateSvgForC0` have run). Closes the gap of "no test exercises the
 * full mount + visibility + highlight chain through the handle surface".
 *
 * Gap closed: a programmatic consumer (test harness, external UI) can
 * drive visibility and highlight without going through the sidebar DOM.
 *
 * @vitest-environment happy-dom
 */
import { describe, it, expect, beforeEach } from 'vitest';
import './setup.js';
import { setMockSvgFactory } from './setup.js';
import { mount } from '../../src/viewer/index.js';

const SVG_NS = 'http://www.w3.org/2000/svg';

function makeNode(graphId: string): SVGGElement {
  const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
  g.setAttribute('class', 'node');
  const title = document.createElementNS(SVG_NS, 'title');
  title.textContent = graphId;
  g.appendChild(title);
  return g;
}

function makeEdge(from: string, to: string): SVGGElement {
  const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
  g.setAttribute('class', 'edge');
  const title = document.createElementNS(SVG_NS, 'title');
  title.textContent = `${from}->${to}`;
  g.appendChild(title);
  return g;
}

function makeCluster(prefix: string, nodeNames: string[]): SVGGElement {
  const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
  g.setAttribute('class', 'cluster');
  const title = document.createElementNS(SVG_NS, 'title');
  title.textContent = `cluster_${prefix}`;
  g.appendChild(title);
  const border = document.createElementNS(SVG_NS, 'polygon');
  border.setAttribute('points', '0,0 100,0 100,100 0,100');
  g.appendChild(border);
  for (const name of nodeNames) g.appendChild(makeNode(name));
  return g;
}

function makePipelineFixture(): SVGSVGElement {
  const svg = document.createElementNS(SVG_NS, 'svg') as SVGSVGElement;
  svg.appendChild(makeCluster('buf1', ['buf1/in', 'buf1/out']));
  svg.appendChild(makeCluster('buf2', ['buf2/in', 'buf2/out']));
  svg.appendChild(makeEdge('buf1/out', 'buf2/in'));
  return svg;
}

function clusterByPrefix(svg: SVGSVGElement, prefix: string): SVGGElement {
  const all = Array.from(svg.querySelectorAll<SVGGElement>('g.cluster'));
  const found = all.find((c) =>
    (c.querySelector(':scope > title')?.textContent ?? '') === `cluster_${prefix}`,
  );
  if (!found) throw new Error(`cluster_${prefix} not in fixture`);
  return found;
}

describe('viewer integration: handle.setVisibility + handle.highlight (C0 API)', () => {
  let container: HTMLElement;

  beforeEach(() => {
    document.body.innerHTML = '';
    container = document.createElement('div');
    document.body.appendChild(container);
    setMockSvgFactory(makePipelineFixture);
  });

  it('handle.setVisibility hides excluded cluster, member nodes, and dependent edges', async () => {
    const handle = await mount('digraph G {}', container, { chrome: true });

    handle.setVisibility({
      visibleClusters: new Set(['buf1']),
      includeSharedPlaces: false,
    });

    expect(clusterByPrefix(handle.svg, 'buf1').classList.contains('is-hidden')).toBe(false);
    expect(clusterByPrefix(handle.svg, 'buf2').classList.contains('is-hidden')).toBe(true);

    const buf2Nodes = handle.svg.querySelectorAll('g.node[data-instance="buf2"]');
    expect(buf2Nodes.length).toBeGreaterThan(0);
    for (const n of buf2Nodes) {
      expect(n.classList.contains('is-hidden')).toBe(true);
    }

    const edge = handle.svg.querySelector('g.edge')!;
    expect(edge.classList.contains('is-hidden')).toBe(true);
  });

  it('handle.setVisibility re-applied with all clusters restores everything', async () => {
    const handle = await mount('digraph G {}', container, { chrome: true });

    handle.setVisibility({
      visibleClusters: new Set(['buf1']),
      includeSharedPlaces: false,
    });
    handle.setVisibility({
      visibleClusters: new Set(['buf1', 'buf2']),
      includeSharedPlaces: true,
    });

    for (const c of handle.svg.querySelectorAll('g.cluster')) {
      expect(c.classList.contains('is-hidden')).toBe(false);
    }
    for (const n of handle.svg.querySelectorAll('g.node[data-instance]')) {
      expect(n.classList.contains('is-hidden')).toBe(false);
    }
    expect(handle.svg.querySelector('g.edge')!.classList.contains('is-hidden')).toBe(false);
  });

  it('handle.highlight tags focus, walks to direct neighbor, fades the rest', async () => {
    const handle = await mount('digraph G {}', container, { chrome: true });

    handle.highlight('buf1/out');

    const focus = handle.svg.querySelector('g.node[data-id="buf1/out"]');
    expect(focus).not.toBeNull();
    expect(focus!.classList.contains('is-highlight')).toBe(true);

    const neighbor = handle.svg.querySelector('g.node[data-id="buf2/in"]');
    expect(neighbor!.classList.contains('is-neighbor')).toBe(true);

    const unrelated = handle.svg.querySelector('g.node[data-id="buf1/in"]');
    expect(unrelated!.classList.contains('is-faded')).toBe(true);

    expect(handle.highlightedNodeId).toBe('buf1/out');
  });

  it('handle.highlight(null) clears every highlight class and the tracked id', async () => {
    const handle = await mount('digraph G {}', container, { chrome: true });
    handle.highlight('buf1/out');
    handle.highlight(null);

    for (const n of handle.svg.querySelectorAll('g.node')) {
      expect(n.classList.contains('is-highlight')).toBe(false);
      expect(n.classList.contains('is-neighbor')).toBe(false);
      expect(n.classList.contains('is-faded')).toBe(false);
    }
    expect(handle.highlightedNodeId).toBeNull();
  });

  it('handle.highlight is a no-op under layout=graphviz (C0-only API)', async () => {
    const handle = await mount('digraph G {}', container, { layout: 'graphviz' });
    handle.highlight('buf1/out');

    expect(handle.highlightedNodeId).toBeNull();
    for (const n of handle.svg.querySelectorAll('g.node')) {
      expect(n.classList.contains('is-highlight')).toBe(false);
    }
  });
});
