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
 * Ported from v3 `applyHighlight` / `findAllCopies` (lines 971–1047). All
 * SVG queries assume the DOM has been through {@link annotateSvgForC0}.
 *
 * @module viewer/highlight
 */

const HIGHLIGHT_CLASSES = ['is-highlight', 'is-neighbor', 'is-faded'] as const;

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

  for (const e of allEdges) {
    if (e.classList.contains('is-hidden') || e.classList.contains('is-highlight')) continue;
    e.classList.add('is-faded');
  }

  for (const n of Array.from(svg.querySelectorAll<SVGGElement>('g.node'))) {
    if (n.classList.contains('is-hidden')) continue;
    const id = n.getAttribute('data-id') ?? '';
    if (copies.has(id)) continue;
    if (neighbors.has(id)) n.classList.add('is-neighbor');
    else if (pathJunctions.has(id)) continue;
    else n.classList.add('is-faded');
  }

  for (const c of Array.from(
    svg.querySelectorAll<SVGGElement>('g.cluster:not(.cluster-orchestrator)'),
  )) {
    if (c.classList.contains('is-hidden')) continue;
    c.classList.add('is-faded');
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
