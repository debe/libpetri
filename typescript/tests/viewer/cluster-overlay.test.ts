/**
 * Cluster-overlay behaviour tests for the canonical viewer module.
 *
 * Migrated from `debug-ui/tests/net/actions/diagram-cluster-collapse.test.ts`
 * and adapted to the new instance-based API exposed by
 * `typescript/src/viewer/index.ts`. The debug-ui test file remains in place
 * until the consumer migration ships; this file is the new canonical
 * regression net for cluster discovery, palette determinism, collapse /
 * expand, isolate filtering, and overlay state survival across re-mounts.
 *
 * @vitest-environment happy-dom
 */
import { describe, it, expect, beforeEach } from 'vitest';
import './setup.js';
import { setMockSvgFactory } from './setup.js';
import {
  colorForPrefix,
  discoverClusters,
  mount,
  type ViewerHandle,
} from '../../src/viewer/index.js';
import { applyFilter } from '../../src/viewer/cluster-overlay.js';

const SVG_NS = 'http://www.w3.org/2000/svg';

function makePipelineSvg(): SVGSVGElement {
  const svg = document.createElementNS(SVG_NS, 'svg') as SVGSVGElement;
  svg.appendChild(makeCluster('buf1', ['buf1/in', 'buf1/out']));
  svg.appendChild(makeCluster('buf2', ['buf2/in', 'buf2/out']));
  svg.appendChild(makeEdge('buf1/out', 'buf2/in'));
  return svg;
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

  const label = document.createElementNS(SVG_NS, 'text');
  label.setAttribute('x', '50');
  label.setAttribute('y', '10');
  label.setAttribute('text-anchor', 'middle');
  label.textContent = prefix;
  g.appendChild(label);

  for (const name of nodeNames) g.appendChild(makeNode(name));
  return g;
}

function makeNode(graphId: string): SVGGElement {
  const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
  g.setAttribute('class', 'node');
  const title = document.createElementNS(SVG_NS, 'title');
  title.textContent = graphId;
  g.appendChild(title);
  const ellipse = document.createElementNS(SVG_NS, 'ellipse');
  g.appendChild(ellipse);
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

describe('viewer cluster overlay', () => {
  let container: HTMLElement;

  beforeEach(() => {
    document.body.innerHTML = '';
    container = document.createElement('div');
    document.body.appendChild(container);
    setMockSvgFactory(makePipelineSvg);
  });

  describe('discoverClusters', () => {
    it('discovers both clusters and tags nodes with data-instance', () => {
      const svg = makePipelineSvg();
      document.body.appendChild(svg);
      const clusters = discoverClusters(svg);

      expect(clusters.size).toBe(2);
      expect([...clusters.keys()].sort()).toEqual(['buf1', 'buf2']);
      const taggedBuf1 = svg.querySelectorAll('g.node[data-instance="buf1"]');
      const taggedBuf2 = svg.querySelectorAll('g.node[data-instance="buf2"]');
      expect(taggedBuf1.length).toBe(2);
      expect(taggedBuf2.length).toBe(2);
    });

    it('returns empty map when no clusters present', () => {
      const svg = document.createElementNS(SVG_NS, 'svg') as SVGSVGElement;
      svg.appendChild(makeNode('orphan'));
      document.body.appendChild(svg);
      expect(discoverClusters(svg).size).toBe(0);
    });
  });

  describe('colorForPrefix', () => {
    it('returns the same HSL string for the same prefix', () => {
      expect(colorForPrefix('buf1')).toBe(colorForPrefix('buf1'));
      expect(colorForPrefix('outer/inner')).toBe(colorForPrefix('outer/inner'));
    });

    it('produces visually distinct hues for adjacent prefixes', () => {
      expect(colorForPrefix('buf1')).not.toBe(colorForPrefix('buf2'));
      expect(colorForPrefix('a')).not.toBe(colorForPrefix('b'));
    });

    it('emits HSL strings with the doclet-fixed 60% saturation, 45% lightness', () => {
      const c = colorForPrefix('anything');
      expect(c).toMatch(/^hsl\(\d+, 60%, 45%\)$/);
    });
  });

  describe('mount().collapse / expand', () => {
    it('collapse hides internal nodes via CSS class and adds a badge', async () => {
      const handle = await mount('digraph G {}', container);
      handle.collapse('buf1');

      const buf1 = handle.svg.querySelectorAll('g.cluster')[0]!;
      expect(buf1.classList.contains('cluster-collapsed')).toBe(true);
      // Graphviz emits nodes as siblings of the cluster <g> in production;
      // the test fixture uses the simpler DOM-contained shape. Either way,
      // collapsed-interior nodes are flagged with the petri-collapsed-inside
      // class so the canonical viewer.css can hide them.
      const visibleNodes = handle.svg.querySelectorAll(
        'g.node[data-instance="buf1"]:not(.petri-collapsed-inside)',
      );
      expect(visibleNodes.length).toBe(0);
      const hiddenNodes = handle.svg.querySelectorAll(
        'g.node[data-instance="buf1"].petri-collapsed-inside',
      );
      expect(hiddenNodes.length).toBe(2);
      const badge = buf1.querySelector('.cluster-collapsed-badge');
      expect(badge).not.toBeNull();
      expect(badge!.textContent).toContain('2 internal nodes');
      expect(handle.collapsedPrefixes.has('buf1')).toBe(true);
    });

    it('expand restores internals', async () => {
      const handle = await mount('digraph G {}', container);
      handle.collapse('buf1');
      handle.expand('buf1');

      const buf1 = handle.svg.querySelectorAll('g.cluster')[0]!;
      expect(buf1.classList.contains('cluster-collapsed')).toBe(false);
      const stillHidden = handle.svg.querySelectorAll(
        'g.node[data-instance="buf1"].petri-collapsed-inside',
      );
      expect(stillHidden.length).toBe(0);
      const buf1Nodes = handle.svg.querySelectorAll('g.node[data-instance="buf1"]');
      expect(buf1Nodes.length).toBe(2);
      expect(handle.collapsedPrefixes.has('buf1')).toBe(false);
    });

    it('cluster border is painted with the deterministic prefix colour', async () => {
      const handle = await mount('digraph G {}', container);
      const buf1Border = handle.svg.querySelectorAll('g.cluster')[0]!.querySelector('polygon');
      expect(buf1Border!.getAttribute('stroke')).toBe(colorForPrefix('buf1'));
      // Thickened per "make clusters visually obvious".
      expect(buf1Border!.getAttribute('stroke-width')).toBe('2.2');
    });

    it('collapseAll/expandAll cycles every cluster', async () => {
      const handle = await mount('digraph G {}', container);
      handle.collapseAll();
      expect(handle.collapsedPrefixes.size).toBe(2);
      handle.expandAll();
      expect(handle.collapsedPrefixes.size).toBe(0);
    });

    it('fires onClusterCollapse with prefix + bool', async () => {
      const events: Array<[string, boolean]> = [];
      const handle = await mount('digraph G {}', container, {
        onClusterCollapse: (p, c) => events.push([p, c]),
      });
      handle.collapse('buf1');
      handle.expand('buf1');
      expect(events).toEqual([['buf1', true], ['buf1', false]]);
    });
  });

  describe('mount().filter', () => {
    it('dims non-matching nodes and tags the SVG', async () => {
      const handle = await mount('digraph G {}', container);
      handle.filter('buf1');

      const buf1Nodes = handle.svg.querySelectorAll('g.node[data-instance="buf1"]');
      const buf2Nodes = handle.svg.querySelectorAll('g.node[data-instance="buf2"]');
      buf1Nodes.forEach((n) => expect(n.classList.contains('petri-dimmed')).toBe(false));
      buf2Nodes.forEach((n) => expect(n.classList.contains('petri-dimmed')).toBe(true));
      expect(handle.svg.classList.contains('has-active-filter')).toBe(true);
      expect(handle.svg.getAttribute('data-active-filter')).toBe('buf1');
      expect(handle.activeFilter).toBe('buf1');
    });

    it('passing null clears the filter', async () => {
      const handle = await mount('digraph G {}', container);
      handle.filter('buf1');
      handle.filter(null);

      handle.svg.querySelectorAll('g.node').forEach((n) => {
        expect(n.classList.contains('petri-dimmed')).toBe(false);
      });
      expect(handle.svg.classList.contains('has-active-filter')).toBe(false);
      expect(handle.svg.getAttribute('data-active-filter')).toBeNull();
      expect(handle.activeFilter).toBeNull();
    });

    it('keeps cross-cluster edges visible when one endpoint matches', async () => {
      const handle = await mount('digraph G {}', container);
      handle.filter('buf1');
      const edge = handle.svg.querySelector('g.edge')!;
      // buf1/out -> buf2/in: one endpoint matches buf1 → not dimmed.
      expect(edge.classList.contains('petri-dimmed')).toBe(false);
    });

    it('dims edges with both endpoints outside the prefix', async () => {
      setMockSvgFactory(() => {
        const svg = makePipelineSvg();
        const buf3 = makeCluster('buf3', ['buf3/in', 'buf3/out']);
        svg.appendChild(buf3);
        svg.appendChild(makeEdge('buf3/in', 'buf3/out'));
        return svg;
      });
      const handle = await mount('digraph G {}', container);
      handle.filter('buf1');

      const edges = handle.svg.querySelectorAll('g.edge');
      const interior = [...edges].find(
        (e) => (e.querySelector('title')?.textContent ?? '').startsWith('buf3/in->buf3/out'),
      );
      expect(interior).toBeDefined();
      expect(interior!.classList.contains('petri-dimmed')).toBe(true);
    });

    it('fires onClusterFilter when filter changes', async () => {
      const filters: Array<string | null> = [];
      const handle = await mount('digraph G {}', container, {
        onClusterFilter: (p) => filters.push(p),
      });
      handle.filter('buf1');
      handle.filter(null);
      expect(filters).toEqual(['buf1', null]);
    });
  });

  describe('mount().isInsideCollapsedCluster', () => {
    it('returns true for an internal node of a collapsed cluster', async () => {
      const handle = await mount('digraph G {}', container);
      expect(handle.isInsideCollapsedCluster('buf1/in')).toBe(false);
      handle.collapse('buf1');
      expect(handle.isInsideCollapsedCluster('buf1/in')).toBe(true);
      expect(handle.isInsideCollapsedCluster('buf1/out')).toBe(true);
      expect(handle.isInsideCollapsedCluster('buf2/in')).toBe(false);
    });

    it('returns false again after the cluster expands', async () => {
      const handle = await mount('digraph G {}', container);
      handle.collapse('buf1');
      handle.expand('buf1');
      expect(handle.isInsideCollapsedCluster('buf1/in')).toBe(false);
    });
  });

  describe('state preservation across re-mount', () => {
    it('preserves collapse + filter when previousHandle is supplied', async () => {
      const first = await mount('digraph G {}', container);
      first.collapse('buf1');
      first.filter('buf1');

      const second = await mount('digraph G {}', container, { previousHandle: first });
      const buf1 = second.svg.querySelectorAll('g.cluster')[0]!;
      expect(buf1.classList.contains('cluster-collapsed')).toBe(true);
      expect(second.collapsedPrefixes.has('buf1')).toBe(true);
      expect(second.activeFilter).toBe('buf1');
      expect(second.svg.classList.contains('has-active-filter')).toBe(true);
    });
  });

  describe('dispose', () => {
    it('removes chrome elements and is idempotent', async () => {
      const handle = await mount('digraph G {}', container, { chrome: true });
      expect(container.querySelector('.libpetri-viewer-chrome')).not.toBeNull();
      handle.dispose();
      expect(container.querySelector('.libpetri-viewer-chrome')).toBeNull();
      // No throw on second dispose.
      expect(() => handle.dispose()).not.toThrow();
    });

    it('ignores collapse/filter after dispose', async () => {
      const handle = await mount('digraph G {}', container);
      handle.dispose();
      handle.collapse('buf1');
      handle.filter('buf1');
      expect(handle.collapsedPrefixes.size).toBe(0);
      expect(handle.activeFilter).toBeNull();
    });
  });

  describe('chrome', () => {
    it('mounts the C0 sidebar with one chip per cluster', async () => {
      const handle = await mount('digraph G {}', container, { chrome: true });
      const sidebar = container.querySelector('.libpetri-sidebar');
      expect(sidebar).not.toBeNull();
      const chips = sidebar!.querySelectorAll<HTMLElement>('.libpetri-sidebar-chip');
      expect(chips.length).toBe(2);
      expect([...chips].map((c) => c.dataset.prefix).sort()).toEqual(['buf1', 'buf2']);
      // Initial state: all chips visible (no .is-off)
      for (const c of chips) expect(c.classList.contains('is-off')).toBe(false);
      handle.dispose();
      expect(container.querySelector('.libpetri-sidebar')).toBeNull();
    });

    it('chip click toggles cluster visibility and adds is-hidden to the cluster', async () => {
      const handle = await mount('digraph G {}', container, { chrome: true });
      const chip = container.querySelector<HTMLElement>(
        '.libpetri-sidebar-chip[data-prefix="buf1"]',
      )!;
      chip.click();
      expect(chip.classList.contains('is-off')).toBe(true);
      const buf1Cluster = handle.svg.querySelectorAll('g.cluster')[0]!;
      expect(buf1Cluster.classList.contains('is-hidden')).toBe(true);
      chip.click();
      expect(chip.classList.contains('is-off')).toBe(false);
      expect(buf1Cluster.classList.contains('is-hidden')).toBe(false);
    });

    it('"hide all" hides every cluster + orphans, "show all" restores', async () => {
      const handle = await mount('digraph G {}', container, { chrome: true });
      const sidebar = container.querySelector('.libpetri-sidebar')!;
      const [showAll, hideAll] = Array.from(
        sidebar.querySelectorAll<HTMLButtonElement>('.libpetri-sidebar-actions button'),
      );
      hideAll!.click();
      const clusters = handle.svg.querySelectorAll('g.cluster');
      for (const c of clusters) expect(c.classList.contains('is-hidden')).toBe(true);
      showAll!.click();
      for (const c of clusters) expect(c.classList.contains('is-hidden')).toBe(false);
    });
  });

  describe('module-level applyFilter (standalone)', () => {
    it('works on a hand-built SVG without going through mount()', () => {
      const svg = makePipelineSvg();
      document.body.appendChild(svg);
      // discoverClusters tags data-instance on nodes — needed for filter to match.
      discoverClusters(svg);

      applyFilter(svg, 'buf1');
      const buf2Nodes = svg.querySelectorAll('g.node[data-instance="buf2"]');
      buf2Nodes.forEach((n) => expect(n.classList.contains('petri-dimmed')).toBe(true));

      applyFilter(svg, null);
      buf2Nodes.forEach((n) => expect(n.classList.contains('petri-dimmed')).toBe(false));
    });
  });

  // ----------------------------------------------------------------------
  // Direct composition (MOD-026): nodes keep their original, un-prefixed
  // names, so cluster membership cannot be recovered from `p_<prefix>_…` /
  // `<prefix>/…` name segments. discoverClusters must fall back to geometric
  // containment — a node whose rendered centre sits inside the cluster's
  // border box belongs to that cluster.
  // ----------------------------------------------------------------------
  describe('direct composition (geometric membership)', () => {
    function geoNode(graphId: string, cx: number, cy: number): SVGGElement {
      const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
      g.setAttribute('class', 'node');
      const title = document.createElementNS(SVG_NS, 'title');
      title.textContent = graphId;
      g.appendChild(title);
      const ellipse = document.createElementNS(SVG_NS, 'ellipse');
      ellipse.setAttribute('cx', String(cx));
      ellipse.setAttribute('cy', String(cy));
      ellipse.setAttribute('rx', '8');
      ellipse.setAttribute('ry', '8');
      g.appendChild(ellipse);
      return g;
    }

    // Graphviz draws a `rounded,dashed` cluster border as a <path>, not a
    // <polygon> — mirror that so the test exercises the real code path.
    function geoCluster(
      prefix: string, x0: number, y0: number, x1: number, y1: number,
    ): SVGGElement {
      const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
      g.setAttribute('class', 'cluster');
      const title = document.createElementNS(SVG_NS, 'title');
      title.textContent = `cluster_${prefix}`;
      g.appendChild(title);
      const border = document.createElementNS(SVG_NS, 'path');
      border.setAttribute(
        'd',
        `M${x0},${y0} L${x1},${y0} L${x1},${y1} L${x0},${y1} Z`,
      );
      g.appendChild(border);
      const label = document.createElementNS(SVG_NS, 'text');
      label.textContent = prefix;
      g.appendChild(label);
      return g;
    }

    // A directly-composed pipeline: producer + consumer subnets, each with
    // private plain-named nodes, plus a shared rendezvous place `p_pipe`
    // rendered between (outside) both cluster boxes. Graphviz emits nodes as
    // SIBLINGS of the cluster <g>, so this fixture does too.
    function makeDirectComposedSvg(): SVGSVGElement {
      const svg = document.createElementNS(SVG_NS, 'svg') as SVGSVGElement;
      svg.appendChild(geoCluster('PipeProducer', 0, 0, 100, 100));
      svg.appendChild(geoCluster('PipeConsumer', 200, 0, 300, 100));
      svg.appendChild(geoNode('p_seed', 30, 50)); // inside producer
      svg.appendChild(geoNode('t_emit', 70, 50)); // inside producer
      svg.appendChild(geoNode('p_sink', 230, 50)); // inside consumer
      svg.appendChild(geoNode('t_eat', 270, 50)); // inside consumer
      svg.appendChild(geoNode('p_pipe', 150, 50)); // shared — between boxes
      svg.appendChild(makeEdge('p_seed', 't_emit')); // interior to producer
      svg.appendChild(makeEdge('t_emit', 'p_pipe')); // producer -> shared
      svg.appendChild(makeEdge('p_pipe', 't_eat')); // shared -> consumer
      return svg;
    }

    it('counts cluster members by geometric containment', () => {
      const svg = makeDirectComposedSvg();
      document.body.appendChild(svg);
      const clusters = discoverClusters(svg);

      expect(clusters.get('PipeProducer')?.nodeCount).toBe(2);
      expect(clusters.get('PipeConsumer')?.nodeCount).toBe(2);
    });

    it('leaves the shared rendezvous place outside every cluster', () => {
      const svg = makeDirectComposedSvg();
      document.body.appendChild(svg);
      discoverClusters(svg);

      const pipe = [...svg.querySelectorAll('g.node')].find(
        (n) => n.querySelector('title')?.textContent === 'p_pipe',
      );
      expect(pipe).toBeDefined();
      expect(pipe!.getAttribute('data-instance')).toBeNull();
    });

    it('tags geometrically-contained nodes with data-instance', () => {
      const svg = makeDirectComposedSvg();
      document.body.appendChild(svg);
      discoverClusters(svg);

      expect(svg.querySelectorAll('g.node[data-instance="PipeProducer"]').length).toBe(2);
      expect(svg.querySelectorAll('g.node[data-instance="PipeConsumer"]').length).toBe(2);
    });

    it('collapse hides interior nodes + the interior edge, keeps the boundary edge', async () => {
      setMockSvgFactory(makeDirectComposedSvg);
      const handle = await mount('digraph G {}', container);
      handle.collapse('PipeProducer');

      const hiddenNodes = handle.svg.querySelectorAll(
        'g.node[data-instance="PipeProducer"].petri-collapsed-inside',
      );
      expect(hiddenNodes.length).toBe(2);

      const edges = [...handle.svg.querySelectorAll('g.edge')];
      const interior = edges.find(
        (e) => e.querySelector('title')?.textContent === 'p_seed->t_emit',
      );
      const boundary = edges.find(
        (e) => e.querySelector('title')?.textContent === 't_emit->p_pipe',
      );
      expect(interior!.classList.contains('petri-collapsed-inside')).toBe(true);
      expect(boundary!.classList.contains('petri-collapsed-inside')).toBe(false);
    });

    it('filter keeps a direct-composed interior edge visible', async () => {
      setMockSvgFactory(makeDirectComposedSvg);
      const handle = await mount('digraph G {}', container);
      handle.filter('PipeProducer');

      const interior = [...handle.svg.querySelectorAll('g.edge')].find(
        (e) => e.querySelector('title')?.textContent === 'p_seed->t_emit',
      );
      expect(interior!.classList.contains('petri-dimmed')).toBe(false);
    });
  });
});
