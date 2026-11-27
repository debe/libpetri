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

describe('viewer integration: click an arc to highlight it', () => {
  let container: HTMLElement;

  beforeEach(() => {
    document.body.innerHTML = '';
    container = document.createElement('div');
    document.body.appendChild(container);
    setMockSvgFactory(makePipelineFixture);
  });

  function click(el: Element): void {
    el.dispatchEvent(new MouseEvent('click', { bubbles: true }));
  }

  it('clicking an arc selects it end to end; clicking it again clears', async () => {
    const handle = await mount('digraph G {}', container, { chrome: true });
    const edge = handle.svg.querySelector('g.edge')!;
    const src = edge.getAttribute('data-src')!;
    const dst = edge.getAttribute('data-dst')!;

    click(edge.querySelector('title')!);

    expect(handle.highlightedArcs).toEqual([{ src, dst }]);
    expect(edge.classList.contains('is-arc-selected')).toBe(true);
    expect(handle.svg.querySelector(`g.node[data-id="${src}"]`)!.classList.contains('is-highlight')).toBe(true);
    expect(handle.svg.querySelector(`g.node[data-id="${dst}"]`)!.classList.contains('is-highlight')).toBe(true);

    click(edge);
    expect(handle.highlightedArcs).toEqual([]);
    expect(edge.classList.contains('is-arc-selected')).toBe(false);
  });

  it('a node click replaces the arc selection, and vice versa', async () => {
    const handle = await mount('digraph G {}', container, { chrome: true });
    const edge = handle.svg.querySelector('g.edge')!;
    click(edge);
    click(handle.svg.querySelector('g.node[data-id="buf1/in"]')!);

    expect(handle.highlightedArcs).toEqual([]);
    expect(handle.highlightedNodeId).toBe('buf1/in');
    expect(edge.classList.contains('is-arc-selected')).toBe(false);

    click(edge);
    expect(handle.highlightedNodeId).toBeNull();
    expect(handle.highlightedArcs).toHaveLength(1);
  });

  it('the highlight-mode toggle disables arc clicks', async () => {
    const handle = await mount('digraph G {}', container, { chrome: true });
    const label = Array.from(container.querySelectorAll('.libpetri-sidebar-checkbox'))
      .find((l) => l.textContent?.includes('highlight'))!;
    const toggle = label.querySelector<HTMLInputElement>('input[type="checkbox"]')!;
    toggle.checked = false;
    toggle.dispatchEvent(new Event('change'));
    click(handle.svg.querySelector('g.edge')!);
    expect(handle.highlightedArcs).toEqual([]);
  });

  it('a routing re-mount keeps the selected arc', async () => {
    const handle = await mount('digraph G {}', container, { chrome: true });
    click(handle.svg.querySelector('g.edge')!);
    const selected = handle.highlightedArcs;
    const next = await handle.setEdgeRouting({ mergeEdges: false });

    expect(next.highlightedArcs).toEqual(selected);
    expect(next.svg.querySelector('g.edge.is-arc-selected')).not.toBeNull();
  });

  it('drops arcs that are not in the diagram', async () => {
    const handle = await mount('digraph G {}', container, { chrome: true });
    handle.highlightArcs([{ src: 't_x', dst: 'p_gone' }]);
    expect(handle.highlightedArcs).toEqual([]);
  });

  it('switching highlight mode off takes the click band away until a re-mount', async () => {
    const handle = await mount('digraph G {}', container, { chrome: true });
    const label = Array.from(container.querySelectorAll('.libpetri-sidebar-checkbox'))
      .find((l) => l.textContent?.includes('highlight'))!;
    const toggle = label.querySelector<HTMLInputElement>('input[type="checkbox"]')!;
    toggle.checked = false;
    toggle.dispatchEvent(new Event('change'));
    expect(container.classList.contains('lpv-click-highlight-off')).toBe(true);

    await mount('digraph G {}', container, { chrome: true, previousHandle: handle });
    expect(container.classList.contains('lpv-click-highlight-off')).toBe(false);
  });

  it('through a junction: a second click on the trace clears it, the trunk widens it', async () => {
    setMockSvgFactory(() => {
      const svg = document.createElementNS(SVG_NS, 'svg') as SVGSVGElement;
      for (const [a, b] of [['t_a', 'j_1'], ['j_1', 'p_b'], ['j_1', 'p_c']]) svg.appendChild(makeEdge(a!, b!));
      for (const id of ['t_a', 'j_1', 'p_b', 'p_c']) svg.appendChild(makeNode(id));
      return svg;
    });
    const handle = await mount('digraph G {}', container, { chrome: true });
    const seg = (s: string, d: string) =>
      handle.svg.querySelector(`g.edge[data-src="${s}"][data-dst="${d}"]`)!;
    const selected = () =>
      Array.from(handle.svg.querySelectorAll('g.edge.is-arc-selected'))
        .map((e) => `${e.getAttribute('data-src')}->${e.getAttribute('data-dst')}`).sort();

    click(seg('j_1', 'p_b'));
    expect(selected()).toEqual(['j_1->p_b', 't_a->j_1']);
    click(seg('t_a', 'j_1'));
    expect(selected()).toEqual(['j_1->p_b', 'j_1->p_c', 't_a->j_1']);
    click(seg('j_1', 'p_c'));
    expect(selected()).toEqual(['j_1->p_c', 't_a->j_1']);
    click(seg('t_a', 'j_1'));
    click(seg('t_a', 'j_1'));
    expect(selected()).toEqual([]);
    expect(handle.highlightedArcs).toEqual([]);
  });

  it('is a no-op under layout=graphviz', async () => {
    const handle = await mount('digraph G {}', container, { layout: 'graphviz' });
    handle.highlightArcs([{ src: 'buf1/out', dst: 'buf2/in' }]);
    expect(handle.highlightedArcs).toEqual([]);
  });
});

describe('viewer integration: edge-routing toggles', () => {
  let container: HTMLElement;

  beforeEach(() => {
    document.body.innerHTML = '';
    container = document.createElement('div');
    document.body.appendChild(container);
    setMockSvgFactory(makePipelineFixture);
  });

  function nextRemount(): Promise<{ handle: Awaited<ReturnType<typeof mount>> }> {
    return new Promise((resolve) => {
      container.addEventListener(
        'libpetri-viewer:remount',
        (ev) => resolve((ev as CustomEvent).detail),
        { once: true },
      );
    });
  }

  it('defaults to merged edges and no arc ports', async () => {
    const handle = await mount('digraph G {}', container, { chrome: true });
    expect(handle.mergeEdges).toBe(true);
    expect(handle.arcPorts).toBe(false);
    expect(container.querySelector('.btn-merge-edges')!.textContent).toBe('Merge edges: on');
    expect(container.querySelector('.btn-arc-ports')!.textContent).toBe('Ports per arc type: off');
  });

  it('the merge-edges button re-mounts with mergeEdges flipped and keeps the highlight', async () => {
    const handle = await mount('digraph G {}', container, { chrome: true });
    handle.highlight('buf1/out');
    const remounted = nextRemount();
    (container.querySelector('.btn-merge-edges') as HTMLButtonElement).click();
    const { handle: next } = await remounted;

    expect(next).not.toBe(handle);
    expect(next.mergeEdges).toBe(false);
    expect(next.arcPorts).toBe(false);
    expect(next.highlightedNodeId).toBe('buf1/out');
    expect(container.querySelectorAll('.btn-merge-edges')).toHaveLength(1);
    expect(container.querySelector('.btn-merge-edges')!.getAttribute('aria-pressed')).toBe('false');
  });

  it('the arc-ports button re-mounts with arcPorts flipped', async () => {
    await mount('digraph G {}', container, { chrome: true, mergeEdges: false });
    const remounted = nextRemount();
    (container.querySelector('.btn-arc-ports') as HTMLButtonElement).click();
    const { handle: next } = await remounted;

    expect(next.arcPorts).toBe(true);
    expect(next.mergeEdges).toBe(false);
    expect(container.querySelector('.btn-arc-ports')!.textContent).toBe('Ports per arc type: on');
  });

  it('a re-mount inherits the routing of the previous handle', async () => {
    const first = await mount('digraph G {}', container, { arcPorts: true, mergeEdges: false });
    const second = await mount('digraph G {}', container, { previousHandle: first });
    expect(second.arcPorts).toBe(true);
    expect(second.mergeEdges).toBe(false);
  });
});
