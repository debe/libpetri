/**
 * Find-by-name: label matching, hit marks, stepping through hits via the
 * handle and the chrome search box, and the zoom-onto-node arithmetic.
 *
 * @vitest-environment happy-dom
 */
import { describe, it, expect, beforeEach } from 'vitest';
import './setup.js';
import { setMockSvgFactory } from './setup.js';
import { mount } from '../../src/viewer/index.js';
import {
  applySearchMarks,
  findMatches,
  focusNode,
  searchableText,
} from '../../src/viewer/search.js';
import type { PanzoomInstance } from '../../src/viewer/pan-zoom.js';

const SVG_NS = 'http://www.w3.org/2000/svg';

function makeNode(id: string, label?: string): SVGGElement {
  const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
  g.setAttribute('class', 'node');
  const title = document.createElementNS(SVG_NS, 'title');
  title.textContent = id;
  g.appendChild(title);
  g.appendChild(document.createElementNS(SVG_NS, 'ellipse'));
  if (label !== undefined) {
    const text = document.createElementNS(SVG_NS, 'text');
    text.textContent = label;
    g.appendChild(text);
  }
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

function makeFixture(): SVGSVGElement {
  const svg = document.createElementNS(SVG_NS, 'svg') as SVGSVGElement;
  svg.appendChild(makeNode('p_OrderPending', 'OrderPending'));
  svg.appendChild(makeNode('t_PlaceOrder', 'PlaceOrder [0, 5s]'));
  svg.appendChild(makeNode('p_OrderDone', 'OrderDone'));
  svg.appendChild(makeNode('j_1'));
  svg.appendChild(makeNode('p_Budget'));
  svg.appendChild(makeNode('p_Budget__rep__retry'));
  svg.appendChild(makeEdge('p_OrderPending', 't_PlaceOrder'));
  svg.appendChild(makeEdge('t_PlaceOrder', 'p_OrderDone'));
  return svg;
}

function ids(nodes: readonly Element[]): string[] {
  return nodes.map((n) => n.querySelector('title')!.textContent!);
}

describe('findMatches', () => {
  it('matches the visible label case-insensitively, in DOM order', () => {
    const svg = makeFixture();
    expect(ids(findMatches(svg, 'order'))).toEqual([
      'p_OrderPending', 't_PlaceOrder', 'p_OrderDone',
    ]);
    expect(ids(findMatches(svg, '  PLACEORDER '))).toEqual(['t_PlaceOrder']);
  });

  it('falls back to the id without prefix and replica suffix for unlabelled nodes', () => {
    const svg = makeFixture();
    expect(searchableText(svg.querySelector('g.node:nth-of-type(6)')!)).toBe('Budget');
    // Each replica is its own hit; the `p_` / `__rep__` parts never match.
    expect(ids(findMatches(svg, 'budget'))).toEqual(['p_Budget', 'p_Budget__rep__retry']);
    expect(findMatches(svg, 'rep__')).toEqual([]);
  });

  it('skips junctions, hidden and collapsed nodes, and an empty query', () => {
    const svg = makeFixture();
    expect(findMatches(svg, 'j_1')).toEqual([]);
    expect(findMatches(svg, '1')).toEqual([]);
    expect(findMatches(svg, '   ')).toEqual([]);
    svg.querySelectorAll('g.node')[0]!.classList.add('is-hidden');
    svg.querySelectorAll('g.node')[2]!.classList.add('petri-collapsed-inside');
    expect(ids(findMatches(svg, 'order'))).toEqual(['t_PlaceOrder']);
  });
});

describe('applySearchMarks', () => {
  it('marks every hit and the current one, and clears stale marks', () => {
    const svg = makeFixture();
    const hits = findMatches(svg, 'order');
    applySearchMarks(svg, hits, 1);
    expect(ids(Array.from(svg.querySelectorAll('.is-search-match')))).toHaveLength(3);
    expect(ids(Array.from(svg.querySelectorAll('.is-search-current')))).toEqual(['t_PlaceOrder']);
    applySearchMarks(svg, [], -1);
    expect(svg.querySelectorAll('.is-search-match, .is-search-current')).toHaveLength(0);
  });
});

describe('focusNode', () => {
  function rect(left: number, top: number, width: number, height: number): DOMRect {
    return { left, top, width, height, right: left + width, bottom: top + height, x: left, y: top } as DOMRect;
  }

  it('zooms so the node spans 1/8 of the shorter side and centres it', () => {
    const viewport = document.createElement('div');
    const svg = document.createElementNS(SVG_NS, 'svg') as SVGSVGElement;
    const node = makeNode('p_X', 'X');
    svg.appendChild(node);
    viewport.appendChild(svg);
    document.body.appendChild(viewport);

    // Current transform: scale 0.5, panned by (20, 10); the SVG's layout
    // origin sits at (5, 7) inside an 800×600 viewport placed at (100, 50).
    const transform = { x: 20, y: 10, scale: 0.5 };
    viewport.getBoundingClientRect = () => rect(100, 50, 800, 600);
    svg.getBoundingClientRect = () => rect(100 + 5 + 20, 50 + 7 + 10, 400, 300);
    // At scale 1 the node is 40×40 with its centre at (300, 200) in SVG space.
    node.getBoundingClientRect = () =>
      rect(100 + 5 + 20 + 280 * 0.5, 50 + 7 + 10 + 180 * 0.5, 20, 20);
    const panzoom = {
      getTransform: () => transform,
      zoomAbs: (_x: number, _y: number, s: number) => { transform.scale = s; },
      moveTo: (x: number, y: number) => { transform.x = x; transform.y = y; },
    } as unknown as PanzoomInstance;

    focusNode(panzoom, node);

    // 600 / 8 = 75 px for a 40 px node.
    expect(transform.scale).toBeCloseTo(75 / 40);
    // Node centre lands on the viewport centre (400, 300).
    expect(5 + transform.x + 300 * transform.scale).toBeCloseTo(400);
    expect(7 + transform.y + 200 * transform.scale).toBeCloseTo(300);
  });
});

describe('viewer handle: search', () => {
  let container: HTMLElement;

  beforeEach(() => {
    document.body.innerHTML = '';
    container = document.createElement('div');
    document.body.appendChild(container);
    setMockSvgFactory(makeFixture);
  });

  it('search marks hits, highlights the current one, and steps with wrap-around', async () => {
    const handle = await mount('digraph G {}', container);
    expect(handle.search('order')).toBe(3);
    expect(handle.searchState).toEqual({ query: 'order', index: 0, count: 3 });
    expect(handle.highlightedNodeId).toBe('p_OrderPending');

    handle.searchNext();
    expect(handle.searchState.index).toBe(1);
    expect(handle.highlightedNodeId).toBe('t_PlaceOrder');
    expect(handle.svg.querySelector('.is-search-current')!.getAttribute('data-id'))
      .toBe('t_PlaceOrder');

    handle.searchNext();
    handle.searchNext();
    expect(handle.searchState.index).toBe(0);
    handle.searchPrev();
    expect(handle.searchState.index).toBe(2);
  });

  it('clearSearch drops marks and its own highlight but keeps a clicked one', async () => {
    const handle = await mount('digraph G {}', container);
    handle.search('order');
    handle.clearSearch();
    expect(handle.searchState).toEqual({ query: '', index: -1, count: 0 });
    expect(handle.svg.querySelectorAll('.is-search-match')).toHaveLength(0);
    expect(handle.highlightedNodeId).toBeNull();

    handle.search('order');
    handle.highlight('p_Budget');
    handle.clearSearch();
    expect(handle.highlightedNodeId).toBe('p_Budget');
  });

  it('a hit hidden by setVisibility drops out of the hit list', async () => {
    const handle = await mount('digraph G {}', container);
    handle.search('order');
    handle.svg.querySelector('g.node[data-id="p_OrderDone"]')!.classList.add('is-hidden');
    handle.setVisibility({ visibleClusters: new Set(), includeSharedPlaces: true });
    const done = handle.svg.querySelector('g.node[data-id="p_OrderDone"]')!;
    expect(done.classList.contains('is-hidden')).toBe(true);
    expect(done.classList.contains('is-search-match')).toBe(false);
    expect(handle.searchState.count).toBeLessThan(3);
  });

  it('the search survives a re-mount', async () => {
    const handle = await mount('digraph G {}', container);
    handle.search('order');
    handle.searchNext();
    const next = await handle.setEdgeRouting({ arcPorts: true });
    expect(next.searchState).toEqual({ query: 'order', index: 1, count: 3 });
    expect(next.svg.querySelectorAll('.is-search-match')).toHaveLength(3);
  });

  it('chrome search box: Enter runs the query, then steps; Esc clears', async () => {
    const handle = await mount('digraph G {}', container, { chrome: true });
    const input = container.querySelector<HTMLInputElement>('.diagram-search-input')!;
    const count = container.querySelector('.diagram-search-count')!;
    const key = (k: string, shiftKey = false): void => {
      input.dispatchEvent(new KeyboardEvent('keydown', { key: k, shiftKey, bubbles: true }));
    };

    input.value = 'order';
    key('Enter');
    expect(count.textContent).toBe('1/3');
    key('Enter');
    expect(count.textContent).toBe('2/3');
    key('Enter', true);
    expect(count.textContent).toBe('1/3');

    input.value = 'nothing-like-this';
    key('Enter');
    expect(count.textContent).toBe('0/0');
    expect(count.classList.contains('is-empty')).toBe(true);

    key('Escape');
    expect(input.value).toBe('');
    expect(handle.searchState.query).toBe('');
    expect(count.textContent).toBe('');
  });

  it('keys typed into the search box do not reach the container', async () => {
    await mount('digraph G {}', container, { chrome: true });
    const input = container.querySelector<HTMLInputElement>('.diagram-search-input')!;
    let reached = false;
    container.addEventListener('keydown', () => { reached = true; });
    input.dispatchEvent(new KeyboardEvent('keydown', { key: 'ArrowUp', bubbles: true }));
    expect(reached).toBe(false);
  });
});
