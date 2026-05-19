/**
 * Tests for {@link tagReplicas}.
 *
 * @vitest-environment happy-dom
 */
import { describe, expect, it } from 'vitest';
import { tagReplicas } from '../../src/viewer/replica-tagging.js';

const SVG_NS = 'http://www.w3.org/2000/svg';

function makeNode(titleText: string): SVGGElement {
  const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
  g.setAttribute('class', 'node');
  const title = document.createElementNS(SVG_NS, 'title');
  title.textContent = titleText;
  g.appendChild(title);
  return g;
}

function makeSvg(...nodes: SVGGElement[]): SVGSVGElement {
  const svg = document.createElementNS(SVG_NS, 'svg') as SVGSVGElement;
  for (const n of nodes) svg.appendChild(n);
  return svg;
}

describe('tagReplicas', () => {
  it('tags both replica clones and their original with the same data-replica-of', () => {
    const orig = makeNode('p_SearchProductsCustomerIntent');
    const repA = makeNode('p_SearchProductsCustomerIntent__rep__productSearch');
    const repB = makeNode('p_SearchProductsCustomerIntent__rep__handoff');
    const unrelated = makeNode('p_SomeOther');
    const svg = makeSvg(orig, repA, repB, unrelated);

    tagReplicas(svg);

    expect(orig.classList.contains('petri-replica')).toBe(true);
    expect(orig.getAttribute('data-replica-of')).toBe('SearchProductsCustomerIntent');
    expect(repA.classList.contains('petri-replica')).toBe(true);
    expect(repA.getAttribute('data-replica-of')).toBe('SearchProductsCustomerIntent');
    expect(repB.classList.contains('petri-replica')).toBe(true);
    expect(repB.getAttribute('data-replica-of')).toBe('SearchProductsCustomerIntent');

    expect(unrelated.classList.contains('petri-replica')).toBe(false);
    expect(unrelated.hasAttribute('data-replica-of')).toBe(false);
  });

  it('does nothing when there are no replicas', () => {
    const a = makeNode('p_Foo');
    const b = makeNode('p_Bar');
    const svg = makeSvg(a, b);
    tagReplicas(svg);
    for (const n of [a, b]) {
      expect(n.classList.contains('petri-replica')).toBe(false);
      expect(n.hasAttribute('data-replica-of')).toBe(false);
    }
  });

  it('is idempotent — re-running does not duplicate the class', () => {
    const orig = makeNode('p_Hub');
    const rep = makeNode('p_Hub__rep__alpha');
    const svg = makeSvg(orig, rep);

    tagReplicas(svg);
    tagReplicas(svg);

    expect(rep.getAttribute('class')).toBe('node petri-replica');
    expect(orig.getAttribute('class')).toBe('node petri-replica');
  });

  it('does not tag transitions or junctions that look like replicas', () => {
    // Only places (p_ prefix) get replicated; transitions and junctions
    // never have __rep__ ids in libpetri-emitted DOT.
    const tx = makeNode('t_DeriveFacets');
    const j = makeNode('j_DeriveFacets__xor_0');
    const svg = makeSvg(tx, j);

    tagReplicas(svg);

    expect(tx.classList.contains('petri-replica')).toBe(false);
    expect(j.classList.contains('petri-replica')).toBe(false);
  });
});
