/**
 * Replica detection + DOM tagging for the C0 layout.
 *
 * `replicateShared` (in `layout/preprocess.ts`) emits clones of shared
 * places with ids of the form `${placeId}__rep__${shortCluster}`. After
 * Graphviz renders the pinned DOT, those replica clones appear as
 * `<g class="node">` siblings whose inner `<title>` carries the replica
 * id. The original `placeId` also gets a sibling for every cluster it
 * touches and stays marked as a shared place.
 *
 * {@link tagReplicas} walks the rendered SVG once and adds:
 *  - `class="petri-replica"` on every replica node AND its original (so
 *    `data-locations` / ⇄ glyph styling can target both).
 *  - `data-replica-of="<semantic-place-name>"` — the original place name
 *    stripped of the `p_` prefix. Click-all-copies (Stage 4) looks up
 *    every node with the same `data-replica-of` value.
 *
 * The ⇄ glyph + dashed border land in CSS (Stage 5); this module only
 * does the attribute tagging.
 *
 * @module viewer/replica-tagging
 */

const REPLICA_RE = /^(p_[A-Za-z0-9_]+)__rep__/;

/**
 * Stable semantic id for a logical place — strips the `p_` prefix so the
 * value matches the `name` field on libpetri's Place model. Click-all-
 * copies in the overlay keys off this value, not the rendered DOM id.
 */
function semanticName(placeId: string): string {
  return placeId.replace(/^p_/, '');
}

/**
 * Walk every `<g class="node">` in `svg`, detect replicas and originals of
 * shared places, and tag them with `petri-replica` + `data-replica-of`.
 *
 * Idempotent: re-running on an already-tagged SVG is a no-op (the attrs
 * already match).
 */
export function tagReplicas(svg: SVGSVGElement): void {
  // First pass: collect every original whose id appears as the prefix of
  // at least one replica's title. We can't tag the originals until we
  // know which ones got copies.
  const originalsWithCopies = new Set<string>();
  const allNodes = Array.from(svg.querySelectorAll<SVGGElement>('g.node'));
  for (const g of allNodes) {
    const title = g.querySelector('title')?.textContent ?? '';
    const m = REPLICA_RE.exec(title);
    if (m) originalsWithCopies.add(m[1]!);
  }

  // Second pass: tag both replicas and their (matching) originals + append
  // the shared-place ⇄ glyph. SVG has no ::after pseudo-element so the
  // glyph is injected as a <text> child of the node's <g>.
  for (const g of allNodes) {
    const title = g.querySelector('title')?.textContent ?? '';
    const replicaMatch = REPLICA_RE.exec(title);
    let semantic: string | null = null;
    if (replicaMatch) {
      semantic = semanticName(replicaMatch[1]!);
    } else if (originalsWithCopies.has(title)) {
      semantic = semanticName(title);
    }
    if (semantic === null) continue;
    g.classList.add('petri-replica');
    g.setAttribute('data-replica-of', semantic);
    appendSharedGlyph(g);
  }
}

const SVG_NS = 'http://www.w3.org/2000/svg';
const GLYPH_CLASS = 'libpetri-replica-glyph';

/**
 * Inject a ⇄ marker adjacent to the upper-right of the node's place shape.
 * Positioned OUTSIDE the circle so it doesn't overlap the boundary stroke
 * or the inner fill (libpetri places are 25pt circles — anything drawn
 * inside is unreadable). Anchored top-left at `(cx + rx + 2, cy - ry + 2)`
 * with a 9pt sans-serif glyph; the styling is finished by the canonical
 * CSS via the `libpetri-replica-glyph` class.
 *
 * Idempotent.
 */
function appendSharedGlyph(g: SVGGElement): void {
  if (g.querySelector(`text.${GLYPH_CLASS}`)) return;
  const shape = g.querySelector('ellipse, circle');
  if (!shape) return;
  let cx = 0, cy = 0, rx = 0, ry = 0;
  if (shape.tagName === 'ellipse') {
    cx = parseFloat(shape.getAttribute('cx') ?? '0');
    cy = parseFloat(shape.getAttribute('cy') ?? '0');
    rx = parseFloat(shape.getAttribute('rx') ?? '0');
    ry = parseFloat(shape.getAttribute('ry') ?? '0');
  } else {
    cx = parseFloat(shape.getAttribute('cx') ?? '0');
    cy = parseFloat(shape.getAttribute('cy') ?? '0');
    rx = parseFloat(shape.getAttribute('r') ?? '0');
    ry = rx;
  }
  const text = document.createElementNS(SVG_NS, 'text');
  text.setAttribute('class', GLYPH_CLASS);
  // Anchored at the upper-right OUTSIDE the circle (top-left of the glyph
  // sits at +2 / -2 from the bounding-box corner so it doesn't kiss the
  // stroke). text-anchor=start so the glyph extends to the right.
  text.setAttribute('x', (cx + rx + 2).toFixed(2));
  text.setAttribute('y', (cy - ry + 2).toFixed(2));
  text.setAttribute('text-anchor', 'start');
  text.setAttribute('font-size', '9');
  text.textContent = '⇄';
  g.appendChild(text);
}
