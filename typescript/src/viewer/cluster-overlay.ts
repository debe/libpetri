/**
 * Cluster overlay for the canonical libpetri viewer.
 *
 * Post-processes a rendered SVG to surface subnet structure visually:
 *  1. Discover `<g class="cluster">` subgraphs, derive each prefix from the
 *     contained `<title>` (Graphviz emits `cluster_<sanitizedPrefix>`).
 *  2. Tag every contained `<g class="node">` with `data-instance="<prefix>"`
 *     so filtering can target it via attribute selectors.
 *  3. Assign each cluster a deterministic HSL colour (FNV-1a hash + golden
 *     ratio hue increment) and paint its border.
 *  4. Provide collapse/expand and "show only <prefix>" filtering.
 *
 * Unlike the previous debug-ui cluster-overlay, this module is instance-
 * based: every `mount()` call gets its own `ClusterOverlay` so multiple
 * viewers on the same page don't share collapse/isolate state.
 *
 * @module viewer/cluster-overlay
 */

/** A discovered cluster with its DOM group, node count, and palette colour. */
export interface ClusterDescriptor {
  readonly prefix: string;
  readonly group: SVGGElement;
  readonly nodeCount: number;
  readonly color: string;
}

/**
 * Augmentation slots stashed on the cluster `<g>` element across collapse
 * cycles. We don't subclass SVGElement; we tag arbitrary properties on the
 * DOM node, matching the doclet's `petrinet-diagrams.js` so the cross-surface
 * mental model is identical.
 *
 * `_petriHiddenSiblings` holds the sibling `<g class="node">` and
 * `<g class="edge">` elements (sibling to the cluster, not its DOM children
 * — Graphviz never nests nodes inside cluster groups) tagged as belonging
 * to this prefix at the moment of collapse. They retain their place in the
 * SVG tree; we hide them via the `petri-collapsed-inside` class so the
 * underlying layout is preserved for a cheap re-expand.
 */
interface ClusterAugment {
  _petriHiddenSiblings?: Element[];
  _petriCollapsedBadge?: SVGTextElement | null;
}
type AugmentedGroup = SVGGElement & ClusterAugment;

/** Axis-aligned bounding box parsed from a cluster's border shape. */
interface Rect {
  readonly minX: number;
  readonly minY: number;
  readonly maxX: number;
  readonly maxY: number;
}

/**
 * Walk the SVG, find every `<g class="cluster">`, derive the prefix from
 * each cluster's `<title>` (`cluster_<sanitized>`), and tag every cluster-
 * interior `<g class="node">` with `data-instance="<prefix>"`. Returns one
 * descriptor per cluster.
 *
 * Graphviz emits cluster nodes as SIBLINGS of the cluster `<g>`, not as
 * children — `<g class="cluster">` only carries title, polygon border, and
 * the cluster's text label. Cluster membership is recovered two ways:
 *
 *  - **Name-based** — instance composition prefixes interior names
 *    (`p_<prefix>_…`, `t_<prefix>_…`, `j_<prefix>_…`) or uses slash-separated
 *    names (`<prefix>/…`).
 *  - **Geometric** — direct composition (spec MOD-026) keeps each node's
 *    original, un-prefixed name, so the only structural signal left in the
 *    rendered SVG is the node's drawn position: a node whose centre falls
 *    inside the cluster's border box belongs to it. This is what Graphviz
 *    itself draws the box around.
 *
 * Does not split nested-cluster prefixes (`outer_inner` could mean either
 * `outer/inner` or a flat `outer_inner` prefix — Graphviz sanitisation is
 * lossy). We treat every cluster as its own top-level entry, matching the
 * doclet's pragmatism.
 */
export function discoverClusters(svg: SVGSVGElement): Map<string, ClusterDescriptor> {
  const out = new Map<string, ClusterDescriptor>();
  const clusterGroups = svg.querySelectorAll<SVGGElement>('g.cluster');
  if (!clusterGroups.length) return out;

  const allNodes = Array.from(svg.querySelectorAll<SVGGElement>('g.node'));

  for (const g of Array.from(clusterGroups)) {
    const titleEl = directChild(g, 'title');
    if (!titleEl) continue;
    const raw = titleEl.textContent ?? '';
    if (!raw.startsWith('cluster_')) continue;
    const prefix = raw.slice('cluster_'.length);
    if (out.has(prefix)) continue;

    const rect = clusterRect(g);
    let nodeCount = 0;
    for (const node of allNodes) {
      // Don't re-tag a node already claimed by an inner (more specific)
      // cluster — outer clusters can still match by string-prefix at filter
      // time, but the data-instance is the leaf.
      if (node.getAttribute('data-instance')) continue;
      const nodeTitle = directChild(node, 'title');
      if (!nodeTitle) continue;
      const id = (nodeTitle.textContent ?? '').trim();
      if (nodeBelongsToCluster(id, node, prefix, rect)) {
        node.setAttribute('data-instance', prefix);
        nodeCount++;
      }
    }

    out.set(prefix, {
      prefix,
      group: g,
      nodeCount,
      color: colorForPrefix(prefix),
    });
  }
  return out;
}

/**
 * Does this node belong to the cluster — by name (instance composition) or
 * by geometry (direct composition, MOD-026)? The name test is exact and
 * cheap, so it runs first; the geometric fallback only fires for plain-named
 * nodes whose owning cluster left no trace in the node id.
 *
 * The geometric test assumes Graphviz lays cluster boxes out disjointly —
 * which holds for direct-composition clusters: the mapper always emits those
 * as top-level subgraphs (subnet names are sanitised of `/`, so they never
 * nest). A node is claimed by the first document-order cluster whose border
 * box contains its centre; a shared rendezvous place, drawn between clusters,
 * falls inside none. Geometry is never consulted for prefix-named nodes, so
 * nested instance clusters — whose nodes always carry a `/`-prefix — keep
 * their exact name-based membership.
 */
function nodeBelongsToCluster(
  nodeId: string,
  node: SVGGElement,
  prefix: string,
  rect: Rect | null,
): boolean {
  if (nodeBelongsToPrefix(nodeId, prefix)) return true;
  if (rect) {
    const c = nodeCenter(node);
    if (
      c &&
      c.x >= rect.minX &&
      c.x <= rect.maxX &&
      c.y >= rect.minY &&
      c.y <= rect.maxY
    ) {
      return true;
    }
  }
  return false;
}

/**
 * Does this node id belong to the cluster with the given prefix?
 *
 * libpetri's DOT renderer prefixes interior names: places as `p_<prefix>_…`,
 * transitions as `t_<prefix>_…`, junctions as `j_<prefix>_…`. Generic DOT
 * may also use slash-separated names (`<prefix>/…`). We accept both shapes
 * so non-libpetri DOT graphs and bare-Graphviz fixtures still match.
 */
function nodeBelongsToPrefix(nodeId: string, prefix: string): boolean {
  return (
    nodeId === prefix ||
    nodeId.startsWith(`${prefix}/`) ||
    nodeId.startsWith(`p_${prefix}_`) ||
    nodeId.startsWith(`t_${prefix}_`) ||
    nodeId.startsWith(`j_${prefix}_`)
  );
}

/**
 * Parse a cluster `<g>`'s border into an axis-aligned bounding box. The
 * border is a `<polygon>` (square clusters) or `<path>` (rounded clusters);
 * either way every coordinate number is extracted and reduced to min/max.
 * Returns `null` when no border or no coordinates are present.
 */
function clusterRect(group: SVGGElement): Rect | null {
  const border = directChild(group, 'polygon') ?? directChild(group, 'path');
  if (!border) return null;
  const raw =
    border.getAttribute('points') ?? border.getAttribute('d') ?? '';
  return boundsOf(raw);
}

/**
 * Resolve a node `<g>`'s centre from its first drawn shape — `cx`/`cy` for an
 * ellipse, or the bounding-box centre of a polygon/path. Returns `null` when
 * the node carries no positioned shape (e.g. a hand-built test fixture).
 */
function nodeCenter(node: SVGGElement): { x: number; y: number } | null {
  const ellipse = directChild(node, 'ellipse');
  if (ellipse) {
    const x = parseFloat(ellipse.getAttribute('cx') ?? '');
    const y = parseFloat(ellipse.getAttribute('cy') ?? '');
    if (!Number.isNaN(x) && !Number.isNaN(y)) return { x, y };
  }
  const shape = directChild(node, 'polygon') ?? directChild(node, 'path');
  if (shape) {
    const bounds = boundsOf(
      shape.getAttribute('points') ?? shape.getAttribute('d') ?? '',
    );
    if (bounds) {
      return {
        x: (bounds.minX + bounds.maxX) / 2,
        y: (bounds.minY + bounds.maxY) / 2,
      };
    }
  }
  return null;
}

/**
 * Reduce a coordinate string (SVG `points` or path `d`) to a bounding box.
 * Numbers alternate x,y — the convention for both polygon points and the
 * absolute `M`/`L`/`C` commands Graphviz emits for cluster/node shapes.
 */
function boundsOf(coords: string): Rect | null {
  const nums = coords.match(/-?\d+(?:\.\d+)?/g);
  if (!nums || nums.length < 2) return null;
  let minX = Infinity;
  let minY = Infinity;
  let maxX = -Infinity;
  let maxY = -Infinity;
  for (let i = 0; i + 1 < nums.length; i += 2) {
    const x = parseFloat(nums[i]!);
    const y = parseFloat(nums[i + 1]!);
    if (x < minX) minX = x;
    if (x > maxX) maxX = x;
    if (y < minY) minY = y;
    if (y > maxY) maxY = y;
  }
  if (minX === Infinity) return null;
  return { minX, minY, maxX, maxY };
}

/**
 * Build a `node graph-id → cluster prefix` map from the `data-instance`
 * attributes {@link discoverClusters} tagged. Lets edge-level logic resolve
 * an endpoint's cluster without re-deriving membership from the node name —
 * essential for direct composition, where node names carry no prefix.
 */
function nodeClusterMap(svg: SVGSVGElement): Map<string, string> {
  const map = new Map<string, string>();
  svg.querySelectorAll<SVGGElement>('g.node[data-instance]').forEach((node) => {
    const di = node.getAttribute('data-instance');
    const title = directChild(node, 'title');
    const id = (title?.textContent ?? '').trim();
    if (di && id) map.set(id, di);
  });
  return map;
}

/**
 * Does an edge endpoint (a node graph-id) belong to the given cluster? Tries
 * the name-based test first (instance composition, incl. nested prefixes via
 * string-prefix), then the resolved membership map (direct composition).
 */
function endpointInCluster(
  id: string,
  prefix: string,
  clusterMap: Map<string, string>,
): boolean {
  return nodeBelongsToPrefix(id, prefix) || clusterMap.get(id) === prefix;
}

/**
 * Deterministic HSL palette. FNV-1a-ish hash of the prefix, multiplied by
 * the golden-ratio fraction (0.61803...) to spread adjacent prefixes
 * visually. Saturation/lightness are fixed (60% / 45%) so the palette
 * stays readable on both the doc background and the dark debug UI.
 */
export function colorForPrefix(prefix: string): string {
  let h = 2166136261;
  for (let i = 0; i < prefix.length; i++) {
    h ^= prefix.charCodeAt(i);
    h = (h * 16777619) >>> 0;
  }
  let hue = Math.floor(((h / 4294967296) * 360 + (h % 360) * 0.61803) % 360);
  if (hue < 0) hue += 360;
  return `hsl(${hue}, 60%, 45%)`;
}

/** Paint the cluster border with the deterministic prefix colour. */
export function paintClusterBorders(clusters: Map<string, ClusterDescriptor>): void {
  for (const c of clusters.values()) {
    const border = directChild(c.group, 'polygon') ?? directChild(c.group, 'path');
    if (border) {
      border.setAttribute('stroke', c.color);
      // Slightly thicker than the old 2.0 — the user asked for clusters to
      // be visually obvious. Backed off from 3 to keep it readable at the
      // tiniest zoom.
      border.setAttribute('stroke-width', '2.2');
    }
  }
}

/**
 * Collapse / expand a cluster.
 *
 * Graphviz emits nodes and edges as siblings of the cluster `<g>`, not as
 * its DOM children. So "collapsing" cannot work by detaching the cluster's
 * children — that only removes title/border/label. Instead, we identify the
 * cluster-interior nodes (`data-instance="<prefix>"`) and edges with both
 * endpoints inside the cluster, then add the `petri-collapsed-inside` class
 * so the canonical viewer.css hides them. Stash the list on the cluster
 * group so re-expand is a constant-time class removal.
 *
 * Edges that cross the cluster boundary (one endpoint inside, one outside)
 * are intentionally left visible — they show the cluster's external wiring
 * even when the interior is hidden.
 *
 * A small `<text>` badge with the actual interior node count is appended
 * inside the cluster `<g>` (which keeps its layout box).
 */
export function setClusterCollapsed(cluster: ClusterDescriptor, collapsed: boolean): void {
  const g = cluster.group as AugmentedGroup;
  const isCollapsed = g.classList.contains('cluster-collapsed');
  const root = g.ownerSVGElement;
  if (!root) return;

  if (collapsed && !isCollapsed) {
    g.classList.add('cluster-collapsed');
    const hidden: Element[] = [];

    // Hide interior nodes (sibling elements tagged with this prefix).
    root
      .querySelectorAll<SVGGElement>(`g.node[data-instance="${cssEscape(cluster.prefix)}"]`)
      .forEach((node) => {
        node.classList.add('petri-collapsed-inside');
        hidden.push(node);
      });

    // Hide interior-interior edges. Edges' titles are `from->to`; we hide
    // an edge only when BOTH endpoints belong to this cluster.
    const clusterMap = nodeClusterMap(root);
    root.querySelectorAll<SVGGElement>('g.edge').forEach((edge) => {
      const titleEl = directChild(edge, 'title');
      if (!titleEl) return;
      const t = (titleEl.textContent ?? '').trim();
      const arrow = t.indexOf('->');
      if (arrow < 0) return;
      const from = t.slice(0, arrow);
      const to = t.slice(arrow + 2);
      if (
        endpointInCluster(from, cluster.prefix, clusterMap) &&
        endpointInCluster(to, cluster.prefix, clusterMap)
      ) {
        edge.classList.add('petri-collapsed-inside');
        hidden.push(edge);
      }
    });

    g._petriHiddenSiblings = hidden;

    if (!g._petriCollapsedBadge) {
      const label = directChild(g, 'text') as SVGTextElement | null;
      if (label) {
        const badge = document.createElementNS('http://www.w3.org/2000/svg', 'text');
        badge.setAttribute('x', label.getAttribute('x') ?? '0');
        const labelY = parseFloat(label.getAttribute('y') ?? '0');
        badge.setAttribute('y', String(labelY + 16));
        badge.setAttribute('text-anchor', label.getAttribute('text-anchor') ?? 'middle');
        badge.setAttribute('font-size', '11');
        badge.setAttribute('fill', '#9ca3af');
        badge.setAttribute('class', 'cluster-collapsed-badge');
        badge.textContent = `(${cluster.nodeCount} internal node${cluster.nodeCount === 1 ? '' : 's'})`;
        g.appendChild(badge);
        g._petriCollapsedBadge = badge;
      }
    }
  } else if (!collapsed && isCollapsed) {
    g.classList.remove('cluster-collapsed');
    if (g._petriHiddenSiblings) {
      g._petriHiddenSiblings.forEach((el) => el.classList.remove('petri-collapsed-inside'));
      g._petriHiddenSiblings = undefined;
    }
    if (g._petriCollapsedBadge && g._petriCollapsedBadge.parentNode === g) {
      g.removeChild(g._petriCollapsedBadge);
      g._petriCollapsedBadge = null;
    }
  }
}

/**
 * Toggle the "show only <prefix>" filter. Passing `null` (or the same
 * prefix already active) clears the filter. Mirrors the doclet's
 * `applyFilter`, including the edge-dimming heuristic that parses each
 * edge's `<title>` (`from->to`) and keeps an edge visible when either
 * endpoint matches the active prefix.
 */
export function applyFilter(svg: SVGSVGElement, prefix: string | null): void {
  if (prefix == null) {
    svg.removeAttribute('data-active-filter');
    svg.classList.remove('has-active-filter');
    svg.querySelectorAll('g.node, g.edge').forEach((el) => el.classList.remove('petri-dimmed'));
    return;
  }
  svg.setAttribute('data-active-filter', prefix);
  svg.classList.add('has-active-filter');
  const clusterMap = nodeClusterMap(svg);
  svg.querySelectorAll('g.node').forEach((node) => {
    const di = node.getAttribute('data-instance');
    const match =
      !!di &&
      (di === prefix || di.indexOf(prefix + '_') === 0 || di.indexOf(prefix + '/') === 0);
    if (match) node.classList.remove('petri-dimmed');
    else node.classList.add('petri-dimmed');
  });
  svg.querySelectorAll('g.edge').forEach((edge) => {
    const titleEl = directChild(edge, 'title');
    if (!titleEl) return;
    const titleText = titleEl.textContent ?? '';
    const arrow = titleText.indexOf('->');
    if (arrow < 0) {
      edge.classList.remove('petri-dimmed');
      return;
    }
    const from = titleText.slice(0, arrow);
    const to = titleText.slice(arrow + 2);
    const matches = (name: string): boolean =>
      name.indexOf(prefix + '/') >= 0 ||
      name.indexOf(prefix + '_') >= 0 ||
      name === prefix ||
      clusterMap.get(name) === prefix;
    if (matches(from) || matches(to)) edge.classList.remove('petri-dimmed');
    else edge.classList.add('petri-dimmed');
  });
}

/**
 * Returns true when the place/transition node identified by `graphId` is
 * currently inside a collapsed cluster (i.e. detached from the live SVG).
 * Live consumers (e.g. highlight code in debug-ui) use this to skip lookups
 * that would otherwise hit a stale cache entry pointing at a detached node.
 */
export function isInsideCollapsedCluster(
  svg: SVGSVGElement | null,
  clusters: Map<string, ClusterDescriptor>,
  collapsedPrefixes: ReadonlySet<string>,
  graphId: string,
): boolean {
  if (collapsedPrefixes.size === 0) return false;
  if (!svg) return false;
  const clusterMap = nodeClusterMap(svg);
  for (const prefix of collapsedPrefixes) {
    if (!clusters.has(prefix)) continue;
    if (endpointInCluster(graphId, prefix, clusterMap)) return true;
  }
  return false;
}

/** Minimal CSS.escape polyfill — happy-dom may not implement CSS globals. */
function cssEscape(s: string): string {
  if (typeof CSS !== 'undefined' && typeof CSS.escape === 'function') return CSS.escape(s);
  return s.replace(/[^a-zA-Z0-9_-]/g, (c) => `\\${c}`);
}

/**
 * `:scope > <tag>` polyfill — happy-dom doesn't reliably resolve `:scope`
 * against namespaced SVG elements (returns null even when the child exists).
 * Walk `children` directly instead, matching by lower-cased tag name.
 */
function directChild(parent: Element, tagName: string): Element | null {
  const lc = tagName.toLowerCase();
  for (const child of Array.from(parent.children)) {
    if (child.tagName.toLowerCase() === lc) return child;
  }
  return null;
}
