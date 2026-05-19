/**
 * Directed-reachability orphan visibility for the C0 layout.
 *
 * When only a subset of clusters is visible, orphan transitions (and
 * places) should appear iff they participate in a chain that ends at a
 * visible cluster — the chain direction matters. v3's `computeVisibleOrphans`
 * (lines 892–918) walks orphan-orphan edges backwards from "seed upstream"
 * orphans (those that feed INTO a visible cluster) and forwards from
 * "seed downstream" orphans (those a visible cluster feeds INTO). This
 * keeps `ResponseAwaited` hidden when only `productSearch` is visible
 * while exposing legitimate upstream chains like
 * `SearchProductsToolRequest → ForkSearchProductsToolRequest → … → productSearch`.
 *
 * @module viewer/visibility
 */

import { annotateSvgForC0 } from './c0-annotations.js';

/**
 * Set of orphan ids whose visibility is justified by the current cluster
 * selection. Caller toggles `is-hidden` on the corresponding `<g class="node">`s.
 */
export function computeVisibleOrphans(
  svg: SVGSVGElement,
  visibleClusters: ReadonlySet<string>,
): Set<string> {
  if (visibleClusters.size === 0) return new Set();

  const orphanNodes = Array.from(
    svg.querySelectorAll<SVGGElement>('g.node:not([data-instance])'),
  );
  const orphanIds = new Set<string>();
  for (const n of orphanNodes) {
    const id = n.getAttribute('data-id');
    if (id) orphanIds.add(id);
  }

  const fwdAdj = new Map<string, Set<string>>();
  const bwdAdj = new Map<string, Set<string>>();
  const link = (m: Map<string, Set<string>>, k: string, v: string): void => {
    let s = m.get(k);
    if (!s) { s = new Set(); m.set(k, s); }
    s.add(v);
  };

  // Orphan-orphan edges feed the BFS walk
  for (const e of Array.from(svg.querySelectorAll<SVGGElement>('g.edge'))) {
    const s = e.getAttribute('data-src') ?? '';
    const d = e.getAttribute('data-dst') ?? '';
    if (orphanIds.has(s) && orphanIds.has(d)) {
      link(fwdAdj, s, d);
      link(bwdAdj, d, s);
    }
  }

  // Seed orphans = orphans on either end of a cross-cluster edge whose
  // other endpoint sits in a visible cluster.
  const seedUpstream = new Set<string>();
  const seedDownstream = new Set<string>();
  for (const e of Array.from(
    svg.querySelectorAll<SVGGElement>('g.edge.cross-cluster'),
  )) {
    const s = e.getAttribute('data-src') ?? '';
    const d = e.getAttribute('data-dst') ?? '';
    const sCl = e.getAttribute('data-src-cluster') ?? '';
    const dCl = e.getAttribute('data-dst-cluster') ?? '';
    if (orphanIds.has(s) && visibleClusters.has(dCl)) seedUpstream.add(s);
    if (orphanIds.has(d) && visibleClusters.has(sCl)) seedDownstream.add(d);
  }

  const visible = new Set<string>();
  const bfs = (seeds: Set<string>, adj: Map<string, Set<string>>): void => {
    const q: string[] = [];
    for (const s of seeds) { visible.add(s); q.push(s); }
    while (q.length) {
      const cur = q.shift()!;
      const next = adj.get(cur);
      if (!next) continue;
      for (const x of next) {
        if (!visible.has(x)) { visible.add(x); q.push(x); }
      }
    }
  };
  bfs(seedUpstream, bwdAdj);
  bfs(seedDownstream, fwdAdj);
  return visible;
}

export interface VisibilityState {
  /** Cluster short names currently visible. */
  readonly visibleClusters: ReadonlySet<string>;
  /**
   * When false, hide every replica/shared place (`g.node.petri-replica`)
   * regardless of which cluster it belongs to. The corresponding sidebar
   * checkbox is labelled "Shared places".
   */
  readonly includeSharedPlaces: boolean;
}

/**
 * Apply visibility state to an annotated SVG. Idempotent — re-call to
 * reflect a new state.
 *
 * Graphviz emits cluster member nodes as DOM SIBLINGS of the cluster `<g>`,
 * not its children. Toggling `is-hidden` on the cluster `<g>` alone hides
 * only the cluster outline + label — the nodes, junctions, transitions and
 * intra-cluster edges inside stay visible. So this routine hides them
 * explicitly:
 *
 *   1. Cluster outlines via `g.cluster` ↔ `visibleClusters`.
 *   2. Cluster member nodes via `g.node[data-instance]` ↔ `visibleClusters`.
 *   3. Orphan nodes (no `data-instance`) via directed-reachability — when
 *      no cluster is visible they all hide, otherwise only the chain
 *      reaching a visible cluster shows.
 *   4. Replica + original shared places (`g.node.petri-replica`) hide as a
 *      group when `includeSharedPlaces=false`.
 *   5. Edges follow their endpoints — hide if either is hidden.
 */
export function applyVisibility(svg: SVGSVGElement, state: VisibilityState): void {
  annotateSvgForC0(svg);

  const { visibleClusters, includeSharedPlaces } = state;

  // 1. Cluster outlines.
  for (const c of Array.from(
    svg.querySelectorAll<SVGGElement>('g.cluster:not(.cluster-orchestrator)'),
  )) {
    const titleEl = c.querySelector(':scope > title');
    const shortName = (titleEl?.textContent ?? '').replace(/^cluster_/, '');
    c.classList.toggle('is-hidden', !visibleClusters.has(shortName));
  }

  // 2. Cluster member nodes follow their cluster's visibility.
  for (const n of Array.from(svg.querySelectorAll<SVGGElement>('g.node[data-instance]'))) {
    const inst = n.getAttribute('data-instance') ?? '';
    n.classList.toggle('is-hidden', !visibleClusters.has(inst));
  }

  // 3. Orphan nodes (no data-instance) — orchestrator-level transitions
  //    + unclustered places. Reachability emptys to ∅ when no cluster is
  //    on, which hides every orphan — the "Hide all" case.
  const visOrphans = computeVisibleOrphans(svg, visibleClusters);
  for (const n of Array.from(
    svg.querySelectorAll<SVGGElement>('g.node:not([data-instance])'),
  )) {
    const id = n.getAttribute('data-id') ?? '';
    n.classList.toggle('is-hidden', !visOrphans.has(id));
  }

  // 4. Shared places (replicas + originals). The `petri-replica` class is
  //    set by `replica-tagging.ts` on BOTH the replica clones and the
  //    original whose cross-cluster shape spawned them — toggling them as a
  //    group lets the user collapse the shared-place clutter in one click.
  if (!includeSharedPlaces) {
    for (const n of Array.from(svg.querySelectorAll<SVGGElement>('g.node.petri-replica'))) {
      n.classList.add('is-hidden');
    }
  }

  // 5. Edges follow their endpoints. Map lookup beats N*M querySelector.
  const nodeById = new Map<string, SVGGElement>();
  for (const n of Array.from(svg.querySelectorAll<SVGGElement>('g.node'))) {
    const id = n.getAttribute('data-id');
    if (id) nodeById.set(id, n);
  }
  for (const e of Array.from(svg.querySelectorAll<SVGGElement>('g.edge'))) {
    const s = e.getAttribute('data-src') ?? '';
    const d = e.getAttribute('data-dst') ?? '';
    const sHidden = nodeById.get(s)?.classList.contains('is-hidden') ?? false;
    const dHidden = nodeById.get(d)?.classList.contains('is-hidden') ?? false;
    e.classList.toggle('is-hidden', sHidden || dHidden);
  }
}
