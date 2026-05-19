/**
 * Tests for {@link computeVisibleOrphans} + {@link applyVisibility}.
 *
 * @vitest-environment happy-dom
 */
import { describe, expect, it } from 'vitest';
import {
  applyVisibility,
  computeVisibleOrphans,
} from '../../src/viewer/visibility.js';

const SVG_NS = 'http://www.w3.org/2000/svg';

function node(
  id: string,
  opts: { instance?: string } = {},
): SVGGElement {
  const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
  g.setAttribute('class', 'node');
  g.setAttribute('data-id', id);
  if (opts.instance) g.setAttribute('data-instance', opts.instance);
  return g;
}

function edge(
  src: string,
  dst: string,
  opts: { srcCluster?: string; dstCluster?: string } = {},
): SVGGElement {
  const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
  g.setAttribute('class', 'edge');
  g.setAttribute('data-src', src);
  g.setAttribute('data-dst', dst);
  const sCl = opts.srcCluster ?? '';
  const dCl = opts.dstCluster ?? '';
  g.setAttribute('data-src-cluster', sCl);
  g.setAttribute('data-dst-cluster', dCl);
  if (sCl !== '' && sCl === dCl) {
    g.classList.add('intra-cluster');
    g.setAttribute('data-cluster', sCl);
  } else {
    g.classList.add('cross-cluster');
  }
  return g;
}

function cluster(shortName: string, ...children: SVGGElement[]): SVGGElement {
  const g = document.createElementNS(SVG_NS, 'g') as SVGGElement;
  g.setAttribute('class', 'cluster');
  const title = document.createElementNS(SVG_NS, 'title');
  title.textContent = `cluster_${shortName}`;
  g.appendChild(title);
  for (const c of children) g.appendChild(c);
  return g;
}

function svgWith(...children: Element[]): SVGSVGElement {
  const svg = document.createElementNS(SVG_NS, 'svg') as SVGSVGElement;
  for (const c of children) svg.appendChild(c);
  return svg;
}

describe('computeVisibleOrphans', () => {
  it('returns empty when no clusters are visible', () => {
    const svg = svgWith(node('p_orphan'));
    expect(computeVisibleOrphans(svg, new Set())).toEqual(new Set());
  });

  it('seeds upstream orphans that feed INTO a visible cluster', () => {
    const inAlpha = node('p_alpha_in', { instance: 'alpha' });
    const orphan = node('p_upstream');
    const e = edge('p_upstream', 'p_alpha_in', { dstCluster: 'alpha' });
    const svg = svgWith(cluster('alpha', inAlpha), orphan, e);

    expect(computeVisibleOrphans(svg, new Set(['alpha']))).toEqual(new Set(['p_upstream']));
  });

  it('walks upstream orphan-chain backwards from the seeds', () => {
    // p_far → p_mid → p_near → cluster_alpha
    const inAlpha = node('p_alpha_in', { instance: 'alpha' });
    const pFar = node('p_far');
    const pMid = node('p_mid');
    const pNear = node('p_near');
    const eFM = edge('p_far', 'p_mid');
    const eMN = edge('p_mid', 'p_near');
    const eNA = edge('p_near', 'p_alpha_in', { dstCluster: 'alpha' });
    const svg = svgWith(cluster('alpha', inAlpha), pFar, pMid, pNear, eFM, eMN, eNA);

    expect(computeVisibleOrphans(svg, new Set(['alpha']))).toEqual(
      new Set(['p_far', 'p_mid', 'p_near']),
    );
  });

  it('stays hidden if reachability is in the wrong direction', () => {
    // p_unrelated <- cluster_beta, but only cluster_alpha is visible
    const inAlpha = node('p_alpha_in', { instance: 'alpha' });
    const inBeta = node('p_beta_in', { instance: 'beta' });
    const pUnrelated = node('p_unrelated');
    const eFromBeta = edge('p_beta_in', 'p_unrelated', { srcCluster: 'beta' });
    const svg = svgWith(
      cluster('alpha', inAlpha),
      cluster('beta', inBeta),
      pUnrelated,
      eFromBeta,
    );

    expect(computeVisibleOrphans(svg, new Set(['alpha']))).toEqual(new Set());
  });
});

describe('applyVisibility', () => {
  it('hides clusters not in the visible set', () => {
    const alpha = cluster('alpha', node('p_alpha_in', { instance: 'alpha' }));
    const beta = cluster('beta', node('p_beta_in', { instance: 'beta' }));
    const svg = svgWith(alpha, beta);

    applyVisibility(svg, { visibleClusters: new Set(['alpha']), includeSharedPlaces: true });

    expect(alpha.classList.contains('is-hidden')).toBe(false);
    expect(beta.classList.contains('is-hidden')).toBe(true);
  });

  it('hides cluster member nodes when their cluster is off', () => {
    // Regression: Graphviz emits cluster nodes as SIBLINGS of g.cluster.
    // Toggling is-hidden on g.cluster alone leaves transitions and
    // junctions inside still visible — "Hide all" was leaking them.
    const a = node('p_alpha_a', { instance: 'alpha' });
    const t = node('t_alpha_run', { instance: 'alpha' });
    const j = node('j_alpha_xor', { instance: 'alpha' });
    const svg = svgWith(cluster('alpha'), a, t, j);

    applyVisibility(svg, { visibleClusters: new Set(), includeSharedPlaces: false });

    expect(a.classList.contains('is-hidden')).toBe(true);
    expect(t.classList.contains('is-hidden')).toBe(true);
    expect(j.classList.contains('is-hidden')).toBe(true);
  });

  it('hides intra-cluster edges when their cluster is off', () => {
    const a = node('p_alpha_a', { instance: 'alpha' });
    const b = node('p_alpha_b', { instance: 'alpha' });
    const e = edge('p_alpha_a', 'p_alpha_b', { srcCluster: 'alpha', dstCluster: 'alpha' });
    const svg = svgWith(cluster('alpha'), a, b, e);

    applyVisibility(svg, { visibleClusters: new Set(), includeSharedPlaces: true });

    expect(e.classList.contains('is-hidden')).toBe(true);
  });

  it('hides replicas and originals of shared places when includeSharedPlaces is false', () => {
    // Replica + original both carry .petri-replica; toggling the
    // "Shared places" checkbox off must hide both, even when their
    // containing cluster is otherwise visible.
    const original = node('p_shared', { instance: 'alpha' });
    original.classList.add('petri-replica');
    const replica = node('p_shared__rep__beta', { instance: 'beta' });
    replica.classList.add('petri-replica');
    const inAlpha = node('p_alpha_in', { instance: 'alpha' });
    const svg = svgWith(
      cluster('alpha'),
      cluster('beta'),
      original,
      replica,
      inAlpha,
    );

    applyVisibility(svg, {
      visibleClusters: new Set(['alpha', 'beta']),
      includeSharedPlaces: false,
    });

    expect(original.classList.contains('is-hidden')).toBe(true);
    expect(replica.classList.contains('is-hidden')).toBe(true);
    // Non-shared cluster member stays visible.
    expect(inAlpha.classList.contains('is-hidden')).toBe(false);
  });

  it('hides edges whose endpoint hides', () => {
    // Cross-cluster edge from a hidden cluster's member should hide
    // along with its source.
    const a = node('p_alpha_in', { instance: 'alpha' });
    const b = node('p_beta_in', { instance: 'beta' });
    const cross = edge('p_alpha_in', 'p_beta_in', {
      srcCluster: 'alpha',
      dstCluster: 'beta',
    });
    const svg = svgWith(cluster('alpha'), cluster('beta'), a, b, cross);

    applyVisibility(svg, {
      visibleClusters: new Set(['beta']),
      includeSharedPlaces: true,
    });

    expect(a.classList.contains('is-hidden')).toBe(true);
    expect(cross.classList.contains('is-hidden')).toBe(true);
  });
});
