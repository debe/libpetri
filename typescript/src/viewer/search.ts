/**
 * Find-by-name for the viewer: match places and transitions by their visible
 * label and bring one match into view.
 *
 *   findMatches(svg, query)        — every visible node whose label contains
 *   `query` (case-insensitive), in DOM order. Junctions (`j_*`) never match;
 *   each replica of a shared place is its own hit because it sits elsewhere.
 *
 *   applySearchMarks(svg, matches, current) — tag every hit `.is-search-match`
 *   and the current one `.is-search-current`. Pass an empty list to clear.
 *
 *   focusNode(panzoom, node)       — zoom so the node reads at a comfortable
 *   size and centre it in the viewport.
 *
 * Node queries assume the DOM has been through {@link annotateSvgForC0}
 * (`data-id`); under the plain Graphviz layout `data-id` is absent and
 * the Graphviz `<title>` is used instead.
 *
 * @module viewer/search
 */

import type { PanzoomInstance } from './pan-zoom.js';

const MATCH_CLASS = 'is-search-match';
const CURRENT_CLASS = 'is-search-current';

/** Classes that take a node out of the rendered diagram. */
const HIDDEN_CLASSES = ['is-hidden', 'petri-collapsed-inside'] as const;

/** Share of the shorter viewport side a focused node should span. */
const FOCUS_FRACTION = 1 / 8;

/** Graph id of a node: `data-id` when annotated, else its Graphviz `<title>`. */
export function nodeId(node: Element): string {
  const id = node.getAttribute('data-id');
  if (id) return id;
  for (const child of Array.from(node.children)) {
    if (child.tagName === 'title') return child.textContent ?? '';
  }
  return '';
}

/**
 * The text a node is searched by: its rendered labels (a place's name is an
 * `xlabel`, a transition's a `label`), or, for a node drawn without text, its
 * id without the `p_` / `t_` prefix and any `__rep__<cluster>` replica suffix.
 */
export function searchableText(node: Element): string {
  const text = Array.from(node.querySelectorAll('text'))
    .map((t) => t.textContent ?? '')
    .join(' ')
    .trim();
  if (text) return text;
  return nodeId(node).replace(/^[pt]_/, '').replace(/__rep__[A-Za-z0-9_]+$/, '');
}

/** Visible place and transition nodes whose label contains `query`. */
export function findMatches(svg: SVGSVGElement, query: string): SVGGElement[] {
  const needle = query.trim().toLowerCase();
  if (!needle) return [];
  return Array.from(svg.querySelectorAll<SVGGElement>('g.node')).filter((node) => {
    const id = nodeId(node);
    if (!id || id.startsWith('j_')) return false;
    if (HIDDEN_CLASSES.some((cls) => node.classList.contains(cls))) return false;
    return searchableText(node).toLowerCase().includes(needle);
  });
}

/** Mark every hit, and the hit at `current` (if any) as the current one. */
export function applySearchMarks(
  svg: SVGSVGElement,
  matches: readonly SVGGElement[],
  current: number,
): void {
  for (const cls of [MATCH_CLASS, CURRENT_CLASS]) {
    for (const el of Array.from(svg.querySelectorAll<Element>('.' + cls))) {
      el.classList.remove(cls);
    }
  }
  matches.forEach((node, i) => {
    node.classList.add(MATCH_CLASS);
    if (i === current) node.classList.add(CURRENT_CLASS);
  });
}

/**
 * Zoom so `node` spans {@link FOCUS_FRACTION} of the shorter viewport side and
 * centre it.
 *
 * Panzoom drives the `<svg>` with a CSS `matrix(s,0,0,s,x,y)` whose origin is
 * the SVG's untransformed top-left, so a node's offset from the SVG's current
 * bounding box divided by the current scale is its position at scale 1. The
 * viewport is the panzoom owner, the SVG's parent.
 */
export function focusNode(panzoom: PanzoomInstance, node: SVGGElement): void {
  const svg = node.ownerSVGElement;
  const viewport = svg?.parentElement;
  if (!svg || !viewport) return;
  const before = panzoom.getTransform();
  const nodeBox = node.getBoundingClientRect();
  const svgBox = svg.getBoundingClientRect();
  const viewBox = viewport.getBoundingClientRect();
  if (before.scale <= 0 || viewBox.width === 0 || viewBox.height === 0) return;

  // Node centre and size at scale 1, relative to the SVG's origin.
  const cx = (nodeBox.left + nodeBox.width / 2 - svgBox.left) / before.scale;
  const cy = (nodeBox.top + nodeBox.height / 2 - svgBox.top) / before.scale;
  const size = Math.max(nodeBox.width, nodeBox.height) / before.scale;
  // Where the SVG's origin sits in the viewport apart from the pan offset.
  const offX = svgBox.left - viewBox.left - before.x;
  const offY = svgBox.top - viewBox.top - before.y;

  const target = size > 0
    ? (Math.min(viewBox.width, viewBox.height) * FOCUS_FRACTION) / size
    : before.scale;
  // zoomAbs clamps to panzoom's min/max zoom; read back the scale it applied.
  panzoom.zoomAbs(0, 0, target);
  const scale = panzoom.getTransform().scale;
  panzoom.moveTo(
    viewBox.width / 2 - offX - cx * scale,
    viewBox.height / 2 - offY - cy * scale,
  );
}
