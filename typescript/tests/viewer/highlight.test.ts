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
import {
  addArcHitAreas,
  applyArcHighlight,
  applyHighlight,
  arcSegments,
  ARC_HIT_CLASS,
  bundleAt,
  coincidentWith,
  nearestLine,
  nearestOnPolyline,
  findAllCopies,
} from '../../src/viewer/highlight.js';

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

describe('arcSegments / applyArcHighlight', () => {
  // t_a -> j_xor -> p_b
  //              -> j_and -> p_c
  //                       -> p_d
  // p_e -> t_a   (an unrelated input arc of the same transition)
  function fixture() {
    const nodes = {
      tA: node('t_a'), jXor: node('j_xor'), jAnd: node('j_and'),
      pB: node('p_b'), pC: node('p_c'), pD: node('p_d'), pE: node('p_e'),
    };
    const edges = {
      aX: edge('t_a', 'j_xor'), xB: edge('j_xor', 'p_b'), xAnd: edge('j_xor', 'j_and'),
      andC: edge('j_and', 'p_c'), andD: edge('j_and', 'p_d'), eA: edge('p_e', 't_a'),
    };
    const svg = svgWith(...Object.values(nodes), ...Object.values(edges));
    return { svg, ...nodes, ...edges };
  }

  it('a plain arc is just its own segment', () => {
    const f = fixture();
    expect(arcSegments(f.svg, { src: 'p_e', dst: 't_a' })).toEqual([f.eA]);
  });

  it('a branch leaf walks upstream to the transition, not into sibling branches', () => {
    const f = fixture();
    const segs = new Set(arcSegments(f.svg, { src: 'j_and', dst: 'p_c' }));
    expect(segs).toEqual(new Set([f.andC, f.xAnd, f.aX]));
  });

  it('the trunk of an output tree carries every branch', () => {
    const f = fixture();
    const segs = new Set(arcSegments(f.svg, { src: 't_a', dst: 'j_xor' }));
    expect(segs).toEqual(new Set([f.aX, f.xB, f.xAnd, f.andC, f.andD]));
  });

  it('skips hidden segments and unknown arcs', () => {
    const f = fixture();
    f.xAnd.classList.add('is-hidden');
    expect(new Set(arcSegments(f.svg, { src: 'j_and', dst: 'p_c' }))).toEqual(new Set([f.andC]));
    expect(arcSegments(f.svg, { src: 'p_x', dst: 't_y' })).toEqual([]);
  });

  it('marks the arc and its two ends, keeps its junctions, fades the rest', () => {
    const f = fixture();
    applyArcHighlight(f.svg, [{ src: 'j_xor', dst: 'p_b' }]);

    for (const e of [f.aX, f.xB]) {
      expect(e.classList.contains('is-arc-selected')).toBe(true);
      expect(e.classList.contains('is-highlight')).toBe(true);
    }
    for (const e of [f.xAnd, f.andC, f.andD, f.eA]) {
      expect(e.classList.contains('is-arc-selected')).toBe(false);
      expect(e.classList.contains('is-faded')).toBe(true);
    }
    expect(f.tA.classList.contains('is-highlight')).toBe(true);
    expect(f.pB.classList.contains('is-highlight')).toBe(true);
    expect(f.jXor.classList.contains('is-faded')).toBe(false);
    for (const n of [f.pC, f.pD, f.pE, f.jAnd]) expect(n.classList.contains('is-faded')).toBe(true);
  });

  it('raises the arc above the other edges but keeps it below every node', () => {
    // Edges first, as the ELK layout writes them (outputorder=edgesfirst).
    const eAB = edge('p_a', 't_b');
    const eCD = edge('p_c', 't_d');
    const nodes = ['p_a', 't_b', 'p_c', 't_d'].map((id) => node(id));
    const svg = svgWith(eAB, eCD, ...nodes);

    applyArcHighlight(svg, [{ src: 'p_a', dst: 't_b' }]);

    expect(Array.from(svg.children)).toEqual([eCD, eAB, ...nodes]);
  });

  it('skips segments inside a collapsed cluster', () => {
    const f = fixture();
    f.xAnd.classList.add('petri-collapsed-inside');
    f.jAnd.classList.add('petri-collapsed-inside');
    f.pC.classList.add('petri-collapsed-inside');

    expect(new Set(arcSegments(f.svg, { src: 't_a', dst: 'j_xor' }))).toEqual(new Set([f.aX, f.xB]));
    applyArcHighlight(f.svg, [{ src: 't_a', dst: 'j_xor' }]);
    expect(f.xAnd.classList.contains('is-arc-selected')).toBe(false);
    expect(f.pC.classList.contains('is-highlight')).toBe(false);
  });

  it('returns only the arcs it found, and draws nothing for none', () => {
    const f = fixture();
    expect(applyArcHighlight(f.svg, [{ src: 'p_e', dst: 't_a' }, { src: 'p_gone', dst: 't_a' }]))
      .toEqual([{ src: 'p_e', dst: 't_a' }]);
    expect(applyArcHighlight(f.svg, [{ src: 'p_gone', dst: 't_a' }])).toEqual([]);
    expect(f.svg.querySelectorAll('.is-faded')).toHaveLength(0);
  });

  it('a node highlight drops the arc selection and null clears it', () => {
    const f = fixture();
    applyArcHighlight(f.svg, [{ src: 'p_e', dst: 't_a' }]);
    applyHighlight(f.svg, 'p_b');
    expect(f.svg.querySelectorAll('.is-arc-selected')).toHaveLength(0);

    applyArcHighlight(f.svg, [{ src: 'p_e', dst: 't_a' }]);
    applyArcHighlight(f.svg, []);
    for (const cls of ['is-arc-selected', 'is-highlight', 'is-faded', 'is-neighbor']) {
      expect(f.svg.querySelectorAll('.' + cls)).toHaveLength(0);
    }
  });
});

describe('applyArcHighlight with several arcs', () => {
  it('highlights the union of their segments and every end', () => {
    const pA = node('p_a'), pB = node('p_b'), pC = node('p_c'), tT = node('t_t');
    const eAT = edge('p_a', 't_t'), eTB = edge('t_t', 'p_b'), eTC = edge('t_t', 'p_c');
    const svg = svgWith(pA, pB, pC, tT, eAT, eTB, eTC);

    applyArcHighlight(svg, [{ src: 't_t', dst: 'p_b' }, { src: 't_t', dst: 'p_c' }]);

    expect(eTB.classList.contains('is-arc-selected')).toBe(true);
    expect(eTC.classList.contains('is-arc-selected')).toBe(true);
    expect(eAT.classList.contains('is-faded')).toBe(true);
    for (const n of [tT, pB, pC]) expect(n.classList.contains('is-highlight')).toBe(true);
    expect(pA.classList.contains('is-faded')).toBe(true);
  });
});

describe('coincidentWith / nearestOnPolyline', () => {
  // Out of a junction at (0,0): two branches share the line to (10,0), then
  // part. A third arc converges on the same node from below.
  const branchB = [{ x: 0, y: 0 }, { x: 10, y: 0 }, { x: 10, y: 20 }];
  const branchC = [{ x: 0, y: 0 }, { x: 10, y: 0 }, { x: 10, y: -20 }];
  const converging = [{ x: 0, y: 30 }, { x: 0, y: 0 }];

  it('projects onto the nearest segment', () => {
    expect(nearestOnPolyline(branchB, { x: 4, y: 3 })).toEqual({ x: 4, y: 0 });
    expect(nearestOnPolyline([], { x: 0, y: 0 })).toBeNull();
  });

  it('a click on the shared stretch keeps the merged sibling', () => {
    expect(coincidentWith(branchB, { x: 5, y: 3 }, [branchC], 1.5)).toEqual([true]);
  });

  it('a click past the split drops it', () => {
    expect(coincidentWith(branchB, { x: 12, y: 10 }, [branchC], 1.5)).toEqual([false]);
  });

  it('the clicked line is the one nearest the pointer, not the first listed', () => {
    const near = [{ x: 0, y: 4 }, { x: 20, y: 4 }];
    const far = [{ x: 0, y: 0 }, { x: 20, y: 0 }];
    expect(nearestLine([far, near], { x: 10, y: 3 })).toBe(1);
  });

  it('an arc converging on the same node stays out near that node', () => {
    // 4 units from the shared node: inside both click bands, not on one line.
    expect(coincidentWith(branchB, { x: 4, y: 2 }, [converging], 1.5)).toEqual([false]);
  });
});

describe('bundleAt', () => {
  it('without path geometry, returns the clicked arc alone', () => {
    // happy-dom cannot measure paths: a sibling sharing j_and is under the
    // pointer, but coincidence cannot be proven, so it stays out.
    const top = edge('j_and', 'p_b');
    const sibling = edge('j_and', 'p_c');
    const svg = svgWith(top, sibling);
    document.body.appendChild(svg);
    const original = document.elementsFromPoint;
    document.elementsFromPoint = () => [top, sibling];
    try {
      expect(bundleAt(svg, top, 0, 0)).toEqual([{ src: 'j_and', dst: 'p_b' }]);
    } finally {
      document.elementsFromPoint = original;
      svg.remove();
    }
  });
});

describe('addArcHitAreas', () => {
  it('adds one transparent wide copy of each edge path, idempotently', () => {
    const e = edge('p_a', 't_b');
    const line = document.createElementNS(SVG_NS, 'path');
    line.setAttribute('d', 'M0,0L10,0');
    e.appendChild(line);
    const svg = svgWith(e);

    addArcHitAreas(svg);
    addArcHitAreas(svg);

    const hits = e.querySelectorAll(`path.${ARC_HIT_CLASS}`);
    expect(hits).toHaveLength(1);
    expect(hits[0]!.getAttribute('d')).toBe('M0,0L10,0');
    expect(hits[0]!.getAttribute('stroke')).toBe('transparent');
    expect(e.lastElementChild).toBe(hits[0]);
  });
});
