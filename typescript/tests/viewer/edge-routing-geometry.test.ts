/**
 * Unit tests for the orthogonal edge-routing geometry that `writeBack` emits
 * for Graphviz `nop2` (see `edgePosSpline` / `approachEndpoint` / `visualExtent`
 * in `elk-place.ts`). The routing helpers are module-private, so we drive them
 * through the public `writeBack(graph, layout)` with hand-built inputs and
 * assert invariants on the emitted `pos="e,…"` spline — no ELK, no browser.
 *
 * Invariants exercised:
 *   - every drawn segment is axis-aligned (right-angle routing),
 *   - the arrowhead tip lands on the target's *visual* boundary,
 *   - the drawn line is pulled back from the tip by ~ARROW_LEN (10pt),
 *     and NEVER overshoots a shorter final segment (regression for the
 *     unclamped-pullback backtracking spike),
 *   - a fan-in that would miss a small shape funnels to its centre with a jog,
 *   - an edge with no ELK route falls back to an orthogonal L-corner,
 *   - libpetri's per-arc attrs (inhibitor `odot`) coexist with `pos=`.
 *
 * @vitest-environment happy-dom
 */
import { describe, expect, it } from 'vitest';
import type { GraphModel, ParsedEdge, ParsedNode } from '../../src/viewer/layout/preprocess.js';
import { writeBack } from '../../src/viewer/layout/elk-place.js';
import type { EdgePath, LayoutResult, NodePosition } from '../../src/viewer/layout/elk-place.js';

const ARROW_LEN = 10; // mirrors elk-place.ts
const PLACE_R = 0.35 * 36; // 12.6pt — libpetri place circle radius

// ---- hand-built fixtures -------------------------------------------------

interface Pt {
  x: number;
  y: number;
}

/** A node whose *drawn* centre is `center`; `box` is the ELK layout bbox. */
function node(id: string, attrs: Record<string, string>): ParsedNode {
  const kind = id.startsWith('t_') ? 'transition' : id.startsWith('j_') ? 'junction' : 'place';
  return { id, kind, attrs };
}

/** A NodePosition (top-left + bbox) whose drawnCenter is `center`. */
function posAt(center: Pt, box = { w: 40, h: 40 }): NodePosition {
  return { x: center.x - box.w / 2, y: center.y - box.h / 2, width: box.w, height: box.h };
}

function graphOf(nodes: ParsedNode[], edges: ParsedEdge[]): GraphModel {
  return {
    nodes: new Map(nodes.map(n => [n.id, n])),
    clusters: new Map(),
    nodeToCluster: new Map(),
    orphans: nodes.map(n => n.id),
    edges,
  };
}

function layoutOf(
  positions: Record<string, NodePosition>,
  edgePaths: Record<string, EdgePath> = {},
): LayoutResult {
  return {
    nodePositions: new Map(Object.entries(positions)),
    clusterBoxes: new Map(),
    edgePaths: new Map(Object.entries(edgePaths)),
    totalWidth: 1000,
    totalHeight: 1000,
  };
}

// ---- spline parsing ------------------------------------------------------

/** The full DOT edge line for `src -> dst`. */
function edgeLine(dot: string, src: string, dst: string): string {
  const line = dot.split('\n').find(l => l.includes(`${src} -> ${dst}`));
  expect(line, `no edge line for ${src} -> ${dst}`).toBeDefined();
  return line!;
}

interface Spline {
  tip: Pt;
  /** Endpoints of each drawn cubic (which is collinear ⇒ a straight segment). */
  anchors: Pt[];
}

/**
 * Parse the `pos="e,<tip> <start> <c1> <c2> <p> …"` spline. The drawn anchors
 * are `start` then every 3rd point (the endpoint of each collinear cubic).
 */
function parseSpline(line: string): Spline {
  const m = line.match(/pos="e,([^"]+)"/);
  expect(m, `no pos="e,…" on: ${line}`).not.toBeNull();
  const pts = m![1]!.trim().split(/\s+/).map(tok => {
    const [x, y] = tok.split(',').map(Number);
    return { x: x!, y: y! };
  });
  const [tip, ...rest] = pts;
  const anchors: Pt[] = [];
  for (let i = 0; i < rest.length; i += 3) anchors.push(rest[i]!); // start, then each cubic end
  return { tip: tip!, anchors };
}

const dist = (a: Pt, b: Pt): number => Math.hypot(a.x - b.x, a.y - b.y);

/** Assert every consecutive drawn segment is axis-aligned (a right angle). */
function expectOrthogonal(anchors: Pt[]): void {
  expect(anchors.length).toBeGreaterThanOrEqual(2);
  for (let i = 1; i < anchors.length; i++) {
    const a = anchors[i - 1]!;
    const b = anchors[i]!;
    const aligned = Math.abs(a.x - b.x) < 0.02 || Math.abs(a.y - b.y) < 0.02;
    expect(aligned, `segment ${JSON.stringify(a)}→${JSON.stringify(b)} not axis-aligned`).toBe(true);
  }
}

// ---- tests ---------------------------------------------------------------

describe('edgePosSpline geometry (via writeBack)', () => {
  it('routes a straight edge orthogonally, lands the tip on the circle boundary, and pulls back by ARROW_LEN', () => {
    const t = node('t_src', { shape: 'box', width: '0.8', height: '0.4', label: 'Src' });
    const p = node('p_dst', { shape: 'circle', width: '0.35', label: '' });
    const graph = graphOf([t, p], [{ src: 't_src', dst: 'p_dst', arc: 'normal', rawAttrs: 'arrowhead="normal"' }]);
    const center = { x: 100, y: 300 };
    const layout = layoutOf(
      { t_src: posAt({ x: 100, y: 100 }, { w: 60, h: 30 }), p_dst: posAt(center) },
      { 't_src->p_dst': { start: { x: 100, y: 115 }, end: { x: 100, y: 285 }, bends: [] } },
    );

    const { tip, anchors } = parseSpline(edgeLine(writeBack(graph, layout), 't_src', 'p_dst'));

    expectOrthogonal(anchors);
    // Tip sits on the visual circle boundary (r = 12.6pt), not the layout box.
    expect(dist(tip, center)).toBeCloseTo(PLACE_R, 1);
    // The last drawn anchor is pulled back ~ARROW_LEN from the tip (long segment).
    expect(dist(anchors[anchors.length - 1]!, tip)).toBeCloseTo(ARROW_LEN, 1);
  });

  it('does NOT overshoot the arrow base past `prev` on a final segment shorter than ARROW_LEN (D1-1 regression)', () => {
    const t = node('t_src', { shape: 'box', width: '0.8', height: '0.4', label: 'Src' });
    const p = node('p_dst', { shape: 'circle', width: '0.35', label: '' });
    const graph = graphOf([t, p], [{ src: 't_src', dst: 'p_dst', arc: 'normal', rawAttrs: 'arrowhead="normal"' }]);
    const center = { x: 100, y: 300 };
    // Approach from the right; the last bend (x=120) sits only ~7.4pt outside
    // the drawn boundary (x=112.6), so the final orthogonal segment is < 10pt.
    const layout = layoutOf(
      { t_src: posAt({ x: 250, y: 300 }, { w: 60, h: 30 }), p_dst: posAt(center) },
      { 't_src->p_dst': { start: { x: 230, y: 300 }, end: { x: 113, y: 300 }, bends: [{ x: 120, y: 300 }] } },
    );

    const { tip, anchors } = parseSpline(edgeLine(writeBack(graph, layout), 't_src', 'p_dst'));
    expectOrthogonal(anchors);

    const arrowBase = anchors[anchors.length - 1]!;
    const prev = anchors[anchors.length - 2]!;
    const finalSeg = dist(prev, tip);
    expect(finalSeg).toBeLessThan(ARROW_LEN); // the short-stub condition we set up
    // The pull-back is clamped to the segment: the arrow base never lands
    // beyond `prev` (that was the backtracking-spike bug). So the drawn tail
    // stays within the segment: dist(arrowBase, tip) ≤ segment length.
    expect(dist(arrowBase, tip)).toBeLessThanOrEqual(finalSeg + 0.05);
    // arrowBase lies between prev and tip (not past prev): it is no farther
    // from the tip than prev is.
    expect(dist(arrowBase, tip)).toBeLessThanOrEqual(dist(prev, tip) + 0.05);
  });

  it('funnels a fan-in that would miss the small circle to its centre, with a right-angle jog', () => {
    const t = node('t_src', { shape: 'box', width: '0.8', height: '0.4', label: 'Src' });
    const p = node('p_dst', { shape: 'circle', width: '0.35', label: '' });
    const graph = graphOf([t, p], [{ src: 't_src', dst: 'p_dst', arc: 'normal', rawAttrs: 'arrowhead="normal"' }]);
    const center = { x: 100, y: 300 };
    // ELK enters vertically at x=140 — 40pt right of centre, far beyond the
    // 12.6pt radius. approachEndpoint must funnel to the near-side centre.
    const layout = layoutOf(
      { t_src: posAt({ x: 140, y: 100 }, { w: 60, h: 30 }), p_dst: posAt(center) },
      { 't_src->p_dst': { start: { x: 140, y: 120 }, end: { x: 140, y: 285 }, bends: [{ x: 140, y: 200 }] } },
    );

    const { tip, anchors } = parseSpline(edgeLine(writeBack(graph, layout), 't_src', 'p_dst'));
    expectOrthogonal(anchors);
    // Tip funnelled to the circle's near-side centre (x ≈ 100), NOT the ELK
    // approach x=140, and still on the boundary above centre.
    expect(tip.x).toBeCloseTo(center.x, 1);
    expect(dist(tip, center)).toBeCloseTo(PLACE_R, 1);
    // A jog corner sits at the funnel x (≈100) before the tip.
    expect(anchors.some(a => Math.abs(a.x - center.x) < 0.5)).toBe(true);
  });

  it('falls back to an orthogonal L-corner when the edge has no ELK route', () => {
    const a = node('t_a', { shape: 'box', width: '0.8', height: '0.4', label: 'A' });
    const b = node('p_b', { shape: 'circle', width: '0.35', label: '' });
    // No edgePaths entry for t_a->p_b → edgePosSpline builds an L-corner.
    const graph = graphOf([a, b], [{ src: 't_a', dst: 'p_b', arc: 'normal', rawAttrs: 'arrowhead="normal"' }]);
    const layout = layoutOf({
      t_a: posAt({ x: 100, y: 100 }, { w: 60, h: 30 }),
      p_b: posAt({ x: 300, y: 220 }),
    });

    const { anchors } = parseSpline(edgeLine(writeBack(graph, layout), 't_a', 'p_b'));
    // Still right-angled despite the diagonal centre-to-centre displacement.
    expectOrthogonal(anchors);
    expect(anchors.length).toBeGreaterThanOrEqual(3); // a genuine corner, not a diagonal
  });

  it('keeps a diagonal ELK route right-angled via the safety-net corner', () => {
    const a = node('t_a', { shape: 'box', width: '0.8', height: '0.4', label: 'A' });
    const c = node('t_c', { shape: 'box', width: '0.8', height: '0.4', label: 'C' });
    const graph = graphOf([a, c], [{ src: 't_a', dst: 't_c', arc: 'normal', rawAttrs: 'arrowhead="normal"' }]);
    // A single diagonal 2-point ELK section (start and end differ in x AND y).
    const layout = layoutOf(
      { t_a: posAt({ x: 100, y: 100 }, { w: 60, h: 30 }), t_c: posAt({ x: 300, y: 160 }, { w: 60, h: 30 }) },
      { 't_a->t_c': { start: { x: 135, y: 100 }, end: { x: 265, y: 160 }, bends: [] } },
    );

    const { anchors } = parseSpline(edgeLine(writeBack(graph, layout), 't_a', 't_c'));
    expectOrthogonal(anchors);
  });

  it('preserves an inhibitor `arrowhead="odot"` on the same line as the routed `pos=`', () => {
    const p = node('p_src', { shape: 'circle', width: '0.35', label: '' });
    const t = node('t_dst', { shape: 'box', width: '0.8', height: '0.4', label: 'Dst' });
    const graph = graphOf(
      [p, t],
      [{ src: 'p_src', dst: 't_dst', arc: 'inhibitor', rawAttrs: 'arrowhead="odot", color="#dc3545"' }],
    );
    const layout = layoutOf(
      { p_src: posAt({ x: 100, y: 100 }), t_dst: posAt({ x: 100, y: 300 }, { w: 60, h: 30 }) },
      { 'p_src->t_dst': { start: { x: 100, y: 115 }, end: { x: 100, y: 285 }, bends: [] } },
    );

    const line = edgeLine(writeBack(graph, layout), 'p_src', 't_dst');
    expect(line).toMatch(/arrowhead="odot"[^\n]*pos="e,/);
  });
});
