/**
 * Tests for {@link applyHighlight} + {@link findAllCopies}.
 *
 * Builds a small annotated SVG by hand — same DOM shape `annotateSvgForC0`
 * produces from real Graphviz output — and asserts the highlight walks
 * through junctions and surfaces real neighbors / fades the rest.
 *
 * @vitest-environment happy-dom
 */
import { describe, expect, it } from 'vitest';
import { applyHighlight, findAllCopies } from '../../src/viewer/highlight.js';

const SVG_NS = 'http://www.w3.org/2000/svg';

function node(id: string, attrs: Record<string, string> = {}): SVGGElement {
  const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
  g.setAttribute('class', 'node');
  g.setAttribute('data-id', id);
  for (const [k, v] of Object.entries(attrs)) g.setAttribute(k, v);
  return g;
}

function edge(src: string, dst: string): SVGGElement {
  const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
  g.setAttribute('class', 'edge');
  g.setAttribute('data-src', src);
  g.setAttribute('data-dst', dst);
  return g;
}

function svgWith(...children: Element[]): SVGSVGElement {
  const svg = document.createElementNS(SVG_NS, 'svg') as SVGSVGElement;
  for (const c of children) svg.appendChild(c);
  return svg;
}

describe('findAllCopies', () => {
  it('returns the focus plus original plus every sibling replica', () => {
    const orig = node('p_Hub', { 'data-replica-of': 'Hub' });
    const repA = node('p_Hub__rep__alpha', { 'data-replica-of': 'Hub' });
    const repB = node('p_Hub__rep__beta', { 'data-replica-of': 'Hub' });
    const unrelated = node('p_Other');
    const svg = svgWith(orig, repA, repB, unrelated);

    const copies = findAllCopies(svg, 'p_Hub__rep__alpha');

    expect(copies).toEqual(new Set(['p_Hub__rep__alpha', 'p_Hub', 'p_Hub__rep__beta']));
  });

  it('returns just {focusId} for an unshared node', () => {
    const a = node('p_Solo');
    const svg = svgWith(a);
    expect(findAllCopies(svg, 'p_Solo')).toEqual(new Set(['p_Solo']));
  });
});

describe('applyHighlight', () => {
  it('highlights focus + walks through junctions to real neighbors', () => {
    // p_a -> j_split -> p_b (real neighbor of p_a through the junction)
    //                 -> p_c (also a neighbor of p_a)
    const pA = node('p_a');
    const jSplit = node('j_split');
    const pB = node('p_b');
    const pC = node('p_c');
    const pUnrelated = node('p_d');
    const eAJ = edge('p_a', 'j_split');
    const eJB = edge('j_split', 'p_b');
    const eJC = edge('j_split', 'p_c');
    const eUnrelated = edge('p_d', 'p_c');
    const svg = svgWith(pA, jSplit, pB, pC, pUnrelated, eAJ, eJB, eJC, eUnrelated);

    applyHighlight(svg, 'p_a');

    expect(pA.classList.contains('is-highlight')).toBe(true);
    expect(pB.classList.contains('is-neighbor')).toBe(true);
    expect(pC.classList.contains('is-neighbor')).toBe(true);
    // The junction itself is on the path — stays neutral (no class)
    expect(jSplit.classList.contains('is-faded')).toBe(false);
    expect(jSplit.classList.contains('is-neighbor')).toBe(false);
    // Unrelated node stays faded
    expect(pUnrelated.classList.contains('is-faded')).toBe(true);
    // Path edges are highlighted; unrelated edge is faded
    expect(eAJ.classList.contains('is-highlight')).toBe(true);
    expect(eJB.classList.contains('is-highlight')).toBe(true);
    expect(eJC.classList.contains('is-highlight')).toBe(true);
    expect(eUnrelated.classList.contains('is-faded')).toBe(true);
  });

  it('highlights every copy of a shared place together', () => {
    const orig = node('p_Hub', { 'data-replica-of': 'Hub' });
    const rep = node('p_Hub__rep__alpha', { 'data-replica-of': 'Hub' });
    const t = node('t_consumer');
    const e = edge('p_Hub__rep__alpha', 't_consumer');
    const svg = svgWith(orig, rep, t, e);

    applyHighlight(svg, 'p_Hub');

    expect(orig.classList.contains('is-highlight')).toBe(true);
    expect(rep.classList.contains('is-highlight')).toBe(true);
    expect(t.classList.contains('is-neighbor')).toBe(true);
  });

  it('skips hidden nodes when traversing', () => {
    const pA = node('p_a');
    const pB = node('p_b');
    const pHidden = node('p_hidden');
    pHidden.classList.add('is-hidden');
    const eVisible = edge('p_a', 'p_b');
    const eHidden = edge('p_a', 'p_hidden');
    eHidden.classList.add('is-hidden');
    const svg = svgWith(pA, pB, pHidden, eVisible, eHidden);

    applyHighlight(svg, 'p_a');

    expect(pB.classList.contains('is-neighbor')).toBe(true);
    expect(pHidden.classList.contains('is-neighbor')).toBe(false);
    expect(eHidden.classList.contains('is-highlight')).toBe(false);
  });

  it('clears classes when called with null', () => {
    const pA = node('p_a');
    pA.classList.add('is-highlight');
    const pB = node('p_b');
    pB.classList.add('is-faded');
    const svg = svgWith(pA, pB);

    applyHighlight(svg, null);

    expect(pA.classList.contains('is-highlight')).toBe(false);
    expect(pB.classList.contains('is-faded')).toBe(false);
  });
});
