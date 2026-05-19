/**
 * Tests for {@link annotateSvgForC0}.
 *
 * @vitest-environment happy-dom
 */
import { describe, expect, it } from 'vitest';
import { annotateSvgForC0 } from '../../src/viewer/c0-annotations.js';

const SVG_NS = 'http://www.w3.org/2000/svg';

function makeNode(id: string): SVGGElement {
  const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
  g.setAttribute('class', 'node');
  const title = document.createElementNS(SVG_NS, 'title');
  title.textContent = id;
  g.appendChild(title);
  return g;
}

function makeEdge(src: string, dst: string): SVGGElement {
  const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
  g.setAttribute('class', 'edge');
  const title = document.createElementNS(SVG_NS, 'title');
  title.textContent = `${src}->${dst}`;
  g.appendChild(title);
  return g;
}

function makeCluster(shortName: string, ...children: SVGGElement[]): SVGGElement {
  const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
  g.setAttribute('class', 'cluster');
  const title = document.createElementNS(SVG_NS, 'title');
  title.textContent = `cluster_${shortName}`;
  g.appendChild(title);
  for (const c of children) g.appendChild(c);
  return g;
}

function makeSvg(...children: SVGGElement[]): SVGSVGElement {
  const svg = document.createElementNS(SVG_NS, 'svg') as SVGSVGElement;
  for (const c of children) svg.appendChild(c);
  return svg;
}

describe('annotateSvgForC0', () => {
  it('tags each node with data-id from its title and data-instance from its cluster', () => {
    const a = makeNode('p_alpha_one');
    const b = makeNode('t_alpha_two');
    const orphan = makeNode('p_loose');
    const svg = makeSvg(makeCluster('alpha', a, b), orphan);

    annotateSvgForC0(svg);

    expect(a.getAttribute('data-id')).toBe('p_alpha_one');
    expect(a.getAttribute('data-instance')).toBe('alpha');
    expect(b.getAttribute('data-instance')).toBe('alpha');
    expect(orphan.getAttribute('data-id')).toBe('p_loose');
    expect(orphan.hasAttribute('data-instance')).toBe(false);
  });

  it('tags intra-cluster edges with data-cluster and intra-cluster class', () => {
    const a = makeNode('p_alpha_a');
    const b = makeNode('p_alpha_b');
    const intra = makeEdge('p_alpha_a', 'p_alpha_b');
    const svg = makeSvg(makeCluster('alpha', a, b), intra);

    annotateSvgForC0(svg);

    expect(intra.classList.contains('intra-cluster')).toBe(true);
    expect(intra.classList.contains('cross-cluster')).toBe(false);
    expect(intra.getAttribute('data-cluster')).toBe('alpha');
    expect(intra.getAttribute('data-src-cluster')).toBe('alpha');
    expect(intra.getAttribute('data-dst-cluster')).toBe('alpha');
  });

  it('tags cross-cluster edges as cross-cluster (no data-cluster)', () => {
    const a = makeNode('p_alpha_a');
    const b = makeNode('p_beta_b');
    const cross = makeEdge('p_alpha_a', 'p_beta_b');
    const svg = makeSvg(
      makeCluster('alpha', a),
      makeCluster('beta', b),
      cross,
    );

    annotateSvgForC0(svg);

    expect(cross.classList.contains('cross-cluster')).toBe(true);
    expect(cross.classList.contains('intra-cluster')).toBe(false);
    expect(cross.hasAttribute('data-cluster')).toBe(false);
    expect(cross.getAttribute('data-src-cluster')).toBe('alpha');
    expect(cross.getAttribute('data-dst-cluster')).toBe('beta');
  });

  it('treats orphan-orphan edges as cross-cluster with empty cluster names', () => {
    const a = makeNode('p_loose_a');
    const b = makeNode('p_loose_b');
    const e = makeEdge('p_loose_a', 'p_loose_b');
    const svg = makeSvg(a, b, e);

    annotateSvgForC0(svg);

    // Both endpoints are orphans → src-cluster = dst-cluster = '' → not intra
    expect(e.classList.contains('cross-cluster')).toBe(true);
    expect(e.getAttribute('data-src-cluster')).toBe('');
    expect(e.getAttribute('data-dst-cluster')).toBe('');
  });

  it('derives data-instance for replicas from the __rep__<short> suffix', () => {
    // Replicas live in their TARGET cluster; their semantic id starts with
    // the foreign place's `p_…` prefix so the libpetri convention used by
    // discoverClusters never tags them. annotateSvgForC0 picks up the
    // `__rep__<short>` suffix and pins the replica to its host cluster.
    const replica = makeNode('p_SearchProductsCustomerIntent__rep__intent');
    const original = makeNode('p_intent_local');
    const svg = makeSvg(makeCluster('intent', original), replica);

    annotateSvgForC0(svg);

    expect(replica.getAttribute('data-instance')).toBe('intent');
    expect(original.getAttribute('data-instance')).toBe('intent');
  });

  it('is idempotent', () => {
    const a = makeNode('p_alpha_a');
    const b = makeNode('p_alpha_b');
    const e = makeEdge('p_alpha_a', 'p_alpha_b');
    const svg = makeSvg(makeCluster('alpha', a, b), e);

    annotateSvgForC0(svg);
    annotateSvgForC0(svg);

    expect(e.classList.value.split(/\s+/).filter(c => c === 'intra-cluster').length).toBe(1);
  });
});
