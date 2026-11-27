/**
 * Click-to-highlight overlay for the C0 layout.
 *
 * Two operations:
 *
 *   findAllCopies(svg, focusId) — given a node id, returns the set of every
 *   DOM node representing the same logical place. For a replica it returns
 *   the original + every sibling replica; for an original of a shared place
 *   it returns itself + every replica; for an unshared node it returns just
 *   `{focusId}`.
 *
 *   applyHighlight(svg, focusId)  — highlights the focus group, walks
 *   junctions (`j_*` routing nodes) transparently to reveal the real
 *   downstream place/transition neighbors, and fades everything else.
 *   Pass `null` to clear.
 *
 *   applyArcHighlight(svg, arcs)  — highlights arcs end to end: each named
 *   segment plus, through junctions, the segments that carry it to a real
 *   place/transition on either side. Their endpoints are marked, everything
 *   else fades. Pass `[]` to clear.
 *
 *   bundleAt(svg, top, x, y)      — the arcs drawn on top of each other
 *   where the pointer is, so a click on a merged bundle selects all of it.
 *
 *   addArcHitAreas(svg)           — gives every edge a wide transparent
 *   stroke so a 1px arc can be clicked.
 *
 * Ported from v3 `applyHighlight` / `findAllCopies` (lines 971–1047). All
 * SVG queries assume the DOM has been through {@link annotateSvgForC0}.
 *
 * @module viewer/highlight
 */

const HIGHLIGHT_CLASSES = ['is-highlight', 'is-neighbor', 'is-faded', 'is-arc-selected'] as const;

/** Class of the transparent click target {@link addArcHitAreas} adds. */
export const ARC_HIT_CLASS = 'lpv-arc-hit';

/** Width, in SVG units, of an arc's click target. */
const ARC_HIT_WIDTH = 10;

/** Classes that take an element out of the rendered diagram. */
const HIDDEN_CLASSES = ['is-hidden', 'petri-collapsed-inside'] as const;

/** Spacing, in SVG units, at which an arc's drawn path is sampled. */
const SAMPLE_STEP = 2;

/** How far apart, in SVG units, two drawn paths may be and still count as one line. */
const COINCIDE_TOLERANCE = 1.5;

/** A point in SVG user space. */
export interface Point {
  readonly x: number;
  readonly y: number;
}

function isHidden(el: Element): boolean {
  return HIDDEN_CLASSES.some((cls) => el.classList.contains(cls));
}

/** An arc segment as Graphviz draws it: one `<g class="edge">`. */
export interface ArcRef {
  /** `data-src` of the edge — a node id, possibly a junction. */
  readonly src: string;
  /** `data-dst` of the edge — a node id, possibly a junction. */
  readonly dst: string;
}

function clearHighlightClasses(svg: SVGSVGElement): void {
  for (const cls of HIGHLIGHT_CLASSES) {
    for (const el of Array.from(svg.querySelectorAll<Element>('.' + cls))) {
      el.classList.remove(cls);
    }
  }
}

/**
 * Resolve every DOM node representing the same logical place as `focusId`.
 *
 * Replicas carry `data-replica-of="<semanticName>"`. The original of a
 * shared place is itself tagged with `data-replica-of="<semanticName>"` so
 * a single attribute query finds the whole family.
 */
export function findAllCopies(svg: SVGSVGElement, focusId: string): Set<string> {
  const focus = svg.querySelector<SVGGElement>(`g.node[data-id="${cssEscape(focusId)}"]`);
  if (!focus) return new Set([focusId]);
  const copies = new Set<string>([focusId]);
  const origLabel = focus.getAttribute('data-replica-of')
    ?? (focusId.startsWith('p_') ? focusId.slice(2) : null);
  if (origLabel) {
    const orig = svg.querySelector<SVGGElement>(`g.node[data-id="${cssEscape('p_' + origLabel)}"]`);
    if (orig) {
      const id = orig.getAttribute('data-id');
      if (id) copies.add(id);
    }
    for (const sibling of Array.from(
      svg.querySelectorAll<SVGGElement>(`g.node[data-replica-of="${cssEscape(origLabel)}"]`),
    )) {
      const id = sibling.getAttribute('data-id');
      if (id) copies.add(id);
    }
  }
  return copies;
}

/**
 * Highlight `focusId` (and every DOM copy of the same logical place),
 * walking through junctions to reveal real downstream/upstream neighbors.
 *
 * Pass `null` to clear. Hidden nodes/edges are skipped so toggling a
 * cluster off doesn't bring them back into the path.
 */
export function applyHighlight(svg: SVGSVGElement, focusId: string | null): void {
  clearHighlightClasses(svg);
  if (focusId === null) return;

  const copies = findAllCopies(svg, focusId);
  for (const id of copies) {
    const n = svg.querySelector<SVGGElement>(`g.node[data-id="${cssEscape(id)}"]`);
    if (n && !n.classList.contains('is-hidden')) n.classList.add('is-highlight');
  }

  // BFS through edges; junctions are transparent — the true neighbour is
  // the place/transition on the other side of the routing node.
  const neighbors = new Set<string>();
  const pathJunctions = new Set<string>();
  const pathEdges: SVGGElement[] = [];
  const queue: string[] = Array.from(copies);
  const visited = new Set<string>(copies);

  const allEdges = Array.from(svg.querySelectorAll<SVGGElement>('g.edge'));
  while (queue.length > 0) {
    const nodeId = queue.shift()!;
    for (const e of allEdges) {
      if (e.classList.contains('is-hidden')) continue;
      const s = e.getAttribute('data-src');
      const d = e.getAttribute('data-dst');
      if (s !== nodeId && d !== nodeId) continue;
      const otherId = s === nodeId ? d : s;
      if (!otherId) continue;
      pathEdges.push(e);
      if (visited.has(otherId)) continue;
      visited.add(otherId);
      if (otherId.startsWith('j_')) {
        pathJunctions.add(otherId);
        queue.push(otherId);
      } else {
        neighbors.add(otherId);
      }
    }
  }

  for (const e of pathEdges) e.classList.add('is-highlight');

  for (const n of Array.from(svg.querySelectorAll<SVGGElement>('g.node'))) {
    if (n.classList.contains('is-hidden') || n.classList.contains('is-highlight')) continue;
    if (neighbors.has(n.getAttribute('data-id') ?? '')) n.classList.add('is-neighbor');
  }

  fadeUnmarked(svg, pathJunctions);
}

/**
 * The segments one arc is drawn with, in no particular order.
 *
 * Junctions (`j_*`) split a transition's XOR/AND output into a tree, so the
 * clicked segment may stop at one. From there the walk goes upstream through
 * a junction's incoming segments and downstream through its outgoing ones,
 * never sideways: clicking `j → p_b` yields `t → j → p_b`, not the sibling
 * branch `j → p_c`; clicking `t → j` yields the whole tree, since every
 * branch carries it. Segments hidden by the visibility filter or inside a
 * collapsed cluster are skipped.
 */
export function arcSegments(svg: SVGSVGElement, arc: ArcRef): SVGGElement[] {
  const edges = Array.from(svg.querySelectorAll<SVGGElement>('g.edge'))
    .filter((e) => !isHidden(e));
  const found = new Set<SVGGElement>(
    edges.filter((e) =>
      e.getAttribute('data-src') === arc.src && e.getAttribute('data-dst') === arc.dst),
  );
  if (found.size === 0) return [];

  const walk = (start: string, from: 'data-src' | 'data-dst', to: 'data-src' | 'data-dst'): void => {
    const queue = [start];
    const seen = new Set<string>();
    while (queue.length > 0) {
      const id = queue.shift()!;
      if (!id.startsWith('j_') || seen.has(id)) continue;
      seen.add(id);
      for (const e of edges) {
        if (e.getAttribute(from) !== id || found.has(e)) continue;
        found.add(e);
        queue.push(e.getAttribute(to) ?? '');
      }
    }
  };
  walk(arc.src, 'data-dst', 'data-src'); // upstream: segments ending at a junction source
  walk(arc.dst, 'data-src', 'data-dst'); // downstream: segments leaving a junction target
  return Array.from(found);
}

/**
 * Highlight the arcs `arcs` are segments of (see {@link arcSegments}), mark
 * the places/transitions at their ends and fade the rest. The segments are
 * raised above every other edge, still below the nodes, so the arcs read
 * through crossings without covering a node or its click target. Pass `[]`
 * to clear. Returns the arcs that were found and drawn.
 */
export function applyArcHighlight(svg: SVGSVGElement, arcs: readonly ArcRef[]): ArcRef[] {
  clearHighlightClasses(svg);
  const drawn = arcs.filter((arc) => arcSegments(svg, arc).length > 0);
  const segments = new Set(drawn.flatMap((arc) => arcSegments(svg, arc)));
  if (segments.size === 0) return [];

  const junctions = new Set<string>();
  const ends = new Set<string>();
  for (const e of segments) {
    e.classList.add('is-highlight', 'is-arc-selected');
    raiseAboveEdges(e);
    for (const id of [e.getAttribute('data-src'), e.getAttribute('data-dst')]) {
      if (!id) continue;
      (id.startsWith('j_') ? junctions : ends).add(id);
    }
  }
  for (const n of Array.from(svg.querySelectorAll<SVGGElement>('g.node'))) {
    if (isHidden(n)) continue;
    if (ends.has(n.getAttribute('data-id') ?? '')) n.classList.add('is-highlight');
  }

  fadeUnmarked(svg, junctions);
  return drawn;
}

/**
 * Move an edge to the end of the edge run of its layer. The ELK layout
 * writes edges before nodes (`outputorder="edgesfirst"`), so the edge goes
 * just before the first node: on top of the other edges, under every node.
 */
function raiseAboveEdges(edge: SVGGElement): void {
  const parent = edge.parentNode;
  if (!parent) return;
  let firstNode: Element | null = null;
  for (const child of Array.from(parent.childNodes)) {
    if (child instanceof Element && child.classList.contains('node')) {
      firstNode = child;
      break;
    }
  }
  parent.insertBefore(edge, firstNode);
}

/**
 * The arcs drawn on one line where the pointer is.
 *
 * Every visible edge under client point (`x`, `y`) is a candidate; with
 * 10-unit click bands, that includes lines a few units beside the one the
 * user aimed at, and the band drawn on top need not belong to the nearest
 * line. So the clicked arc is the candidate whose drawn path passes nearest
 * the pointer, and the others join it only where they share an endpoint
 * with it and their paths pass through the same point of the line.
 *
 * With `mergeEdges` on, ELK bundles the arcs entering or leaving a node onto
 * one line, so a click there cannot tell them apart, and picking one would
 * present an arbitrary branch as the clicked one; they are all returned.
 * Arcs that merely cross the line share no endpoint; arcs that converge on
 * a node share one but pass beside the clicked point. Both stay out.
 *
 * Falls back to `top`, the edge the click landed on, where the document
 * cannot hit-test a point or measure a path.
 */
export function bundleAt(svg: SVGSVGElement, top: SVGGElement, x: number, y: number): ArcRef[] {
  const topRef = arcRef(top);
  if (!topRef) return [];
  const doc = svg.ownerDocument;
  const under = typeof doc.elementsFromPoint === 'function' ? doc.elementsFromPoint(x, y) : [];
  const edges: SVGGElement[] = [top];
  const seen = new Set<string>([arcKey(topRef)]);
  for (const el of under) {
    const e = el.closest<SVGGElement>('g.edge');
    if (!e || !svg.contains(e) || isHidden(e)) continue;
    const r = arcRef(e);
    if (!r || seen.has(arcKey(r))) continue;
    seen.add(arcKey(r));
    edges.push(e);
  }
  if (edges.length === 1) return [topRef];

  const lines = edges.map((e) => {
    const line = drawnPath(e);
    return line ? samplePath(line) : null;
  });
  const ctm = drawnPath(top)?.getScreenCTM?.();
  if (!ctm || lines.some((pts) => pts === null)) return [topRef];
  const local = new DOMPoint(x, y).matrixTransform(ctm.inverse());
  const at = { x: local.x, y: local.y };
  const pts = lines as Point[][];

  const primary = nearestLine(pts, at);
  const ref = arcRef(edges[primary]!)!;
  const others = edges.map((_, i) => i).filter((i) => {
    if (i === primary) return false;
    const r = arcRef(edges[i]!)!;
    return r.src === ref.src || r.src === ref.dst || r.dst === ref.src || r.dst === ref.dst;
  });
  const keep = coincidentWith(pts[primary]!, at, others.map((i) => pts[i]!), COINCIDE_TOLERANCE);
  return [ref, ...others.filter((_, k) => keep[k]).map((i) => arcRef(edges[i]!)!)];
}

/** Index of the polyline in `lines` that passes nearest `at`. */
export function nearestLine(lines: readonly (readonly Point[])[], at: Point): number {
  let best = 0;
  let bestD = Infinity;
  lines.forEach((pts, i) => {
    const q = nearestOnPolyline(pts, at);
    const d = q ? Math.hypot(q.x - at.x, q.y - at.y) : Infinity;
    if (d < bestD) {
      best = i;
      bestD = d;
    }
  });
  return best;
}

/**
 * For each polyline in `others`, whether it passes within `tolerance` of the
 * point of polyline `top` nearest `at`. Pure geometry behind
 * {@link bundleAt}.
 */
export function coincidentWith(
  top: readonly Point[],
  at: Point,
  others: readonly (readonly Point[])[],
  tolerance: number,
): boolean[] {
  const q = nearestOnPolyline(top, at);
  if (!q) return others.map(() => false);
  return others.map((pts) => {
    const r = nearestOnPolyline(pts, q);
    return r !== null && Math.hypot(r.x - q.x, r.y - q.y) <= tolerance;
  });
}

/** The point of polyline `pts` nearest `p`, or `null` for an empty polyline. */
export function nearestOnPolyline(pts: readonly Point[], p: Point): Point | null {
  if (pts.length === 0) return null;
  let best: Point = pts[0]!;
  let bestD = Math.hypot(best.x - p.x, best.y - p.y);
  for (let i = 1; i < pts.length; i++) {
    const a = pts[i - 1]!;
    const b = pts[i]!;
    const dx = b.x - a.x;
    const dy = b.y - a.y;
    const len2 = dx * dx + dy * dy;
    const t = len2 === 0 ? 0 : Math.max(0, Math.min(1, ((p.x - a.x) * dx + (p.y - a.y) * dy) / len2));
    const c = { x: a.x + t * dx, y: a.y + t * dy };
    const d = Math.hypot(c.x - p.x, c.y - p.y);
    if (d < bestD) {
      best = c;
      bestD = d;
    }
  }
  return best;
}

function arcRef(e: Element): ArcRef | null {
  const src = e.getAttribute('data-src');
  const dst = e.getAttribute('data-dst');
  return src && dst ? { src, dst } : null;
}

function arcKey(r: ArcRef): string {
  return `${r.src}->${r.dst}`;
}

/** An edge's visible line, not its click target. */
function drawnPath(e: Element): SVGPathElement | null {
  return e.querySelector<SVGPathElement>(`path:not(.${ARC_HIT_CLASS})`);
}

/** `path` sampled every {@link SAMPLE_STEP} units; `null` where it cannot be measured. */
function samplePath(path: SVGPathElement): Point[] | null {
  if (typeof path.getTotalLength !== 'function') return null;
  const len = path.getTotalLength();
  if (!(len > 0)) return null;
  const n = Math.max(1, Math.ceil(len / SAMPLE_STEP));
  const pts: Point[] = [];
  for (let i = 0; i <= n; i++) {
    const p = path.getPointAtLength((len * i) / n);
    pts.push({ x: p.x, y: p.y });
  }
  return pts;
}

/**
 * Fade every visible edge and node that carries no highlight class, except
 * the junctions on the highlighted path, plus every subnet cluster's frame.
 */
function fadeUnmarked(svg: SVGSVGElement, pathJunctions: ReadonlySet<string>): void {
  for (const e of Array.from(svg.querySelectorAll<SVGGElement>('g.edge'))) {
    if (e.classList.contains('is-hidden') || e.classList.contains('is-highlight')) continue;
    e.classList.add('is-faded');
  }

  for (const n of Array.from(svg.querySelectorAll<SVGGElement>('g.node'))) {
    if (n.classList.contains('is-hidden')) continue;
    if (n.classList.contains('is-highlight') || n.classList.contains('is-neighbor')) continue;
    if (pathJunctions.has(n.getAttribute('data-id') ?? '')) continue;
    n.classList.add('is-faded');
  }

  for (const c of Array.from(
    svg.querySelectorAll<SVGGElement>('g.cluster:not(.cluster-orchestrator)'),
  )) {
    if (c.classList.contains('is-hidden')) continue;
    c.classList.add('is-faded');
  }
}

/**
 * Give every edge a click target wider than its 1px line: a copy of its
 * path with a transparent {@link ARC_HIT_WIDTH} stroke, appended last so it
 * catches the pointer along the whole band. Idempotent.
 */
export function addArcHitAreas(svg: SVGSVGElement): void {
  for (const e of Array.from(svg.querySelectorAll<SVGGElement>('g.edge'))) {
    if (e.querySelector(`path.${ARC_HIT_CLASS}`)) continue;
    const d = e.querySelector('path')?.getAttribute('d');
    if (!d) continue;
    const hit = svg.ownerDocument.createElementNS('http://www.w3.org/2000/svg', 'path');
    hit.setAttribute('class', ARC_HIT_CLASS);
    hit.setAttribute('d', d);
    hit.setAttribute('fill', 'none');
    hit.setAttribute('stroke', 'transparent');
    hit.setAttribute('stroke-width', String(ARC_HIT_WIDTH));
    hit.setAttribute('pointer-events', 'stroke');
    e.appendChild(hit);
  }
}

/**
 * Escape a string for use inside a CSS attribute selector value.
 *
 * Built-in `CSS.escape` covers identifier characters; node ids contain
 * `_` and digits which `CSS.escape` accepts, plus the `__rep__` separator
 * which is also safe. We only need to escape the few syntactic chars
 * (`"`, `\`).
 */
function cssEscape(value: string): string {
  return value.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
}
