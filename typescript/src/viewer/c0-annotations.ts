/**
 * Post-render SVG annotation for the C0 layout pipeline.
 *
 * Graphviz emits a clean SVG but without the `data-id`, `data-src`,
 * `data-dst`, `data-cluster`, `data-instance` attributes the click-all-
 * copies, highlight-through-junctions, and directed-reachability overlays
 * key off. {@link annotateSvgForC0} walks the rendered SVG once and adds
 * those attributes, plus `intra-cluster` / `cross-cluster` classes on
 * `<g class="edge">` so the visibility layer can toggle edges as their
 * containing cluster's state changes.
 *
 * Mirrors the SVG-side conventions used by v3
 * (`run16_GOOD_v3_skip-junctions.mjs` overlay block, lines 876–905) but
 * derived from Graphviz's emitted DOM shape (`<g class="node"><title>`,
 * `<g class="edge"><title>src-&gt;dst</title>`) rather than the manual
 * emission v3 did.
 *
 * @module viewer/c0-annotations
 */

/** Read the immediate `<title>` child's text content (Graphviz convention). */
function ownTitle(g: Element): string {
  for (const child of Array.from(g.children)) {
    if (child.tagName === 'title') return child.textContent ?? '';
  }
  return '';
}

/**
 * Walk to the nearest ancestor `<g class="cluster">` and return its
 * short name (with the leading `cluster_` stripped), or `''` if the node
 * lives at root (i.e. it's an orphan inside the synthetic orchestrator).
 *
 * Graphviz emits clusters as DOM **siblings** of their member nodes (not
 * parents), so `closest('g.cluster')` is null in our pipeline — this is
 * effectively a no-op fallback. Cluster membership is established up
 * front by {@link discoverClusters} via `<title>` prefix matching.
 */
function enclosingClusterShortName(node: Element): string {
  const cluster = node.parentElement?.closest('g.cluster');
  if (!cluster) return '';
  return ownTitle(cluster).replace(/^cluster_/, '');
}

/**
 * Annotate a Graphviz-rendered SVG with the data attributes + edge classes
 * the C0 overlay layer relies on. Idempotent.
 *
 * Must run AFTER {@link discoverClusters}, which seeds `data-instance` via
 * title prefix matching (cluster → its member nodes by `t_${prefix}_…` /
 * `p_${prefix}_…` etc.). This function never clears `data-instance` —
 * Graphviz nests neither nodes inside clusters nor anything else, so DOM
 * ancestry is not a reliable source of cluster membership here.
 */
export function annotateSvgForC0(svg: SVGSVGElement): void {
  // Nodes — data-id (from title). Prefer the cluster tag discoverClusters
  // already wrote. Replicas (id ends `__rep__<shortName>`) override that
  // tag with their target cluster so the visibility layer can hide them
  // alongside the cluster they belong to — discoverClusters keys off the
  // libpetri prefix convention (`p_<short>_`) which replica ids don't match.
  const nodes = Array.from(svg.querySelectorAll<SVGGElement>('g.node'));
  for (const node of nodes) {
    const id = ownTitle(node);
    if (!id) continue;
    node.setAttribute('data-id', id);
    const replicaM = /__rep__([A-Za-z0-9_]+)$/.exec(id);
    if (replicaM) {
      node.setAttribute('data-instance', replicaM[1]!);
    } else if (!node.hasAttribute('data-instance')) {
      const inst = enclosingClusterShortName(node);
      if (inst) node.setAttribute('data-instance', inst);
    }
  }

  // Index nodes by data-id for fast cluster lookup on edge endpoints
  const nodeIndex = new Map<string, SVGGElement>();
  for (const n of nodes) {
    const id = n.getAttribute('data-id');
    if (id) nodeIndex.set(id, n);
  }

  // Edges — parse "src->dst" from title; tag with data-src/data-dst,
  // their cluster short names, and intra-/cross-cluster class.
  for (const edge of Array.from(svg.querySelectorAll<SVGGElement>('g.edge'))) {
    const title = ownTitle(edge);
    const arrow = title.indexOf('->');
    if (arrow <= 0) continue;
    const src = title.slice(0, arrow).trim();
    const dst = title.slice(arrow + 2).trim();
    edge.setAttribute('data-src', src);
    edge.setAttribute('data-dst', dst);

    const srcInst = nodeIndex.get(src)?.getAttribute('data-instance') ?? '';
    const dstInst = nodeIndex.get(dst)?.getAttribute('data-instance') ?? '';
    edge.setAttribute('data-src-cluster', srcInst);
    edge.setAttribute('data-dst-cluster', dstInst);

    edge.classList.remove('intra-cluster', 'cross-cluster');
    if (srcInst !== '' && srcInst === dstInst) {
      edge.classList.add('intra-cluster');
      edge.setAttribute('data-cluster', srcInst);
    } else {
      edge.classList.add('cross-cluster');
      edge.removeAttribute('data-cluster');
    }
  }
}
