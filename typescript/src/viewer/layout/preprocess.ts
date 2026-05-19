/**
 * Graph pre-processing for the C0-replicate-default layout pipeline.
 *
 * Three pure-ish transforms operate on a {@link GraphModel} parsed from a
 * libpetri-exported DOT string:
 *
 *   parseLibpetriDot(dot)           → GraphModel
 *   foldOrphans(graph, threshold)   → GraphModel    (REASSIGN_ORPHANS)
 *   replicateShared(graph, opts)    → GraphModel    (REPLICATE_SHARED)
 *
 * The pipeline turns a flat cluster soup into a cluster-internal one by
 * (a) folding orphan nodes whose edges concentrate in one cluster into that
 * cluster, and (b) cloning shared places into every foreign cluster they
 * touch so cross-cluster spaghetti disappears. The resulting GraphModel is
 * what ELK lays out (Stage 2) and Graphviz then renders in pin-mode.
 *
 * Algorithm lineage: ported from
 * `/home/db/otto-repos/nucleus_marvin/.scratch/javadoc-layout-exp/CHECKPOINTS/run16_GOOD_v3_skip-junctions.mjs`
 * lines 14–220. The arc-type detection, replica naming
 * (`${placeId}__rep__${clusterShortName}`), and the `__replica` /
 * `replicaOf` markers are load-bearing — downstream stages key off them.
 *
 * @module viewer/layout/preprocess
 */

export type ArcType = 'normal' | 'reset' | 'inhibitor' | 'read';
export type NodeKind = 'place' | 'transition' | 'junction';

export interface ParsedNode {
  readonly id: string;
  readonly kind: NodeKind;
  readonly attrs: Record<string, string>;
  /** True iff this node was emitted by replicateShared. */
  readonly replica?: boolean;
  /** For a replica, the id of the original logical place. */
  readonly replicaOf?: string;
}

export interface ParsedEdge {
  readonly src: string;
  readonly dst: string;
  readonly arc: ArcType;
  /**
   * Raw attribute body from the libpetri DOT (between the `[…]` brackets,
   * brackets stripped). Carries style/penwidth/label that we want to
   * round-trip verbatim so the rendered output matches `DotExporter`'s
   * native look.
   */
  readonly rawAttrs: string;
}

export interface ParsedCluster {
  readonly id: string;          // "cluster_productSearch"
  readonly shortName: string;   // "productSearch"
  readonly nodes: readonly string[];
}

export interface GraphModel {
  readonly nodes: ReadonlyMap<string, ParsedNode>;
  readonly clusters: ReadonlyMap<string, ParsedCluster>;
  readonly nodeToCluster: ReadonlyMap<string, string>;
  /** Node ids not in any cluster (rendered at the orchestrator root). */
  readonly orphans: readonly string[];
  readonly edges: readonly ParsedEdge[];
}

function classifyKind(id: string): NodeKind {
  if (id.startsWith('p_')) return 'place';
  if (id.startsWith('t_')) return 'transition';
  return 'junction';
}

/**
 * Recover key=value attributes from inside a DOT `[...]` block.
 *
 * Mirrors v3 line 29. The regex is intentionally permissive about quoted
 * values containing escaped quotes; it does not validate DOT syntax.
 */
function parseAttrs(body: string): Record<string, string> {
  const attrs: Record<string, string> = {};
  for (const m of body.matchAll(/(\w+)=("(?:[^"]|\\.)*"|\S+?)(?=[\s,]|$)/g)) {
    const [, key, raw] = m as unknown as [string, string, string];
    const v = raw.startsWith('"') && raw.endsWith('"') ? raw.slice(1, -1) : raw;
    attrs[key] = v;
  }
  return attrs;
}

/**
 * Parse a libpetri-exported DOT string into a {@link GraphModel}.
 *
 * Tolerates the current exporter shape (see
 * `java/src/main/java/org/libpetri/export/StyleConstants.java`):
 *  - inhibitor arcs use `arrowhead="odot"` + color `#dc3545`
 *  - reset arcs use `label="reset"` + color `#fd7e14`
 *  - read arcs use `label="read"` + color `#6c757d`
 *
 * Mirrors v3 lines 24–103.
 */
export function parseLibpetriDot(dot: string): GraphModel {
  const nodes = new Map<string, ParsedNode>();
  // Greedy `.*` (no /s flag) consumes the full attrs body up to the line's
  // trailing `];`. The v3 reference used `[^\]]*` which silently dropped
  // transitions whose label contained `[…]` text (e.g., `"[0, ∞]ms"`); we
  // can't tolerate that here because the typed model wants every cluster
  // member to have a Node entry.
  for (const m of dot.matchAll(/^\s*([pjt]_[A-Za-z0-9_]+)\s*\[(.*)\];\s*$/gm)) {
    const [, id, body] = m as unknown as [string, string, string];
    nodes.set(id, { id, kind: classifyKind(id), attrs: parseAttrs(body) });
  }

  const clusters = new Map<string, ParsedCluster>();
  const nodeToCluster = new Map<string, string>();
  for (const cm of dot.matchAll(/subgraph (cluster_\w+)\s*\{([^]*?)^\s*\}/gm)) {
    const [, clusterId, body] = cm as unknown as [string, string, string];
    const memberIds = [...body.matchAll(/^\s*([pjt]_[A-Za-z0-9_]+)\s*\[/gm)]
      .map(m => (m as unknown as [string, string])[1]);
    clusters.set(clusterId, {
      id: clusterId,
      shortName: clusterId.replace(/^cluster_/, ''),
      nodes: memberIds,
    });
    for (const n of memberIds) nodeToCluster.set(n, clusterId);
  }

  // Catch nodes declared at root (orphans) — strip cluster bodies, then scan
  const stripped = dot.replace(/subgraph cluster_\w+\s*\{[^]*?^\s*\}/gm, '');
  for (const m of stripped.matchAll(/^\s*([pjt]_[A-Za-z0-9_]+)\s*\[/gm)) {
    const id = (m as unknown as [string, string])[1];
    if (!nodes.has(id)) {
      // Root-declared node without full attrs (rare); seed with empty attrs.
      nodes.set(id, { id, kind: classifyKind(id), attrs: {} });
    }
  }

  const orphans = [...nodes.keys()].filter(n => !nodeToCluster.has(n));

  const edges: ParsedEdge[] = [];
  for (const m of dot.matchAll(/([pjt]_[A-Za-z0-9_]+)\s*->\s*([pjt]_[A-Za-z0-9_]+)\s*(\[[^\]]*\])?/g)) {
    const [, src, dst, rawAttrs] = m as unknown as [string, string, string, string | undefined];
    const attrs = rawAttrs ?? '';
    // Cluster-anchor edges (lhead/ltail) are exporter-internal routing hints,
    // not real arcs in the Petri net — skip per v3 line 97.
    if (attrs.includes('lhead=') || attrs.includes('ltail=')) continue;
    let arc: ArcType = 'normal';
    if (attrs.includes('label="reset"') || attrs.includes('#fd7e14')) arc = 'reset';
    else if (attrs.includes('arrowhead="odot"') || attrs.includes('#dc3545')) arc = 'inhibitor';
    else if (attrs.includes('label="read"')) arc = 'read';
    // Strip the `[…]` brackets so writeBack can splice the body into a new
    // attr list. Empty if libpetri emitted a bare `src -> dst;`.
    const stripped = attrs.startsWith('[') && attrs.endsWith(']')
      ? attrs.slice(1, -1)
      : '';
    edges.push({ src, dst, arc, rawAttrs: stripped });
  }

  return { nodes, clusters, nodeToCluster, orphans, edges };
}

/**
 * Adopt orphan nodes into the cluster their edges most prefer.
 *
 * For each orphan, tally how many of its edges touch each cluster. If the
 * dominant cluster gets at least `threshold` of the orphan's cluster-touching
 * edges, the orphan is reassigned to that cluster.
 *
 * Mirrors v3 lines 105–136. Default threshold 0.7 matches REASSIGN_ORPHANS.
 */
export function foldOrphans(graph: GraphModel, threshold = 0.7): GraphModel {
  if (threshold <= 0) return graph;

  const nodeToCluster = new Map(graph.nodeToCluster);
  const clusterMembers = new Map<string, string[]>();
  for (const [id, c] of graph.clusters) clusterMembers.set(id, [...c.nodes]);

  const tally = new Map<string, Map<string, number>>();
  const bump = (orphan: string, other: string): void => {
    const oc = nodeToCluster.get(other);
    if (!oc) return;
    let t = tally.get(orphan);
    if (!t) { t = new Map(); tally.set(orphan, t); }
    t.set(oc, (t.get(oc) ?? 0) + 1);
  };

  for (const e of graph.edges) {
    const sIsOrphan = !nodeToCluster.has(e.src);
    const dIsOrphan = !nodeToCluster.has(e.dst);
    if (sIsOrphan && !dIsOrphan) bump(e.src, e.dst);
    if (dIsOrphan && !sIsOrphan) bump(e.dst, e.src);
  }

  for (const id of graph.orphans) {
    const t = tally.get(id);
    if (!t) continue;
    let total = 0;
    let bestCluster: string | null = null;
    let bestCount = 0;
    for (const [c, n] of t) {
      total += n;
      if (n > bestCount) { bestCount = n; bestCluster = c; }
    }
    if (bestCluster && total > 0 && bestCount / total >= threshold) {
      clusterMembers.get(bestCluster)!.push(id);
      nodeToCluster.set(id, bestCluster);
    }
  }

  const clusters = new Map<string, ParsedCluster>();
  for (const [id, c] of graph.clusters) {
    clusters.set(id, { ...c, nodes: clusterMembers.get(id)! });
  }
  const orphans = [...graph.nodes.keys()].filter(n => !nodeToCluster.has(n));
  return { ...graph, clusters, nodeToCluster, orphans };
}

export interface ReplicateOptions {
  /**
   * Skip places that touch more than this many foreign clusters. Per the
   * plan's "no cap" decision, default is `Infinity`. Set to a finite value
   * to suppress replication of hub places that would otherwise produce many
   * copies.
   */
  readonly max?: number;
  /** If true, replicate transitions as well as places. Default false. */
  readonly replicateTransitions?: boolean;
}

export interface ReplicateStats {
  readonly replicatedPlaces: number;
  readonly totalCopies: number;
}

/**
 * For each place P, replicate it into every foreign cluster touched by its
 * edges, and redirect those cross-cluster edges to the local copy.
 *
 * Replica id convention is load-bearing: `${placeId}__rep__${shortClusterName}`.
 * Downstream stages (mount-time tagging, overlay highlight, click-all-copies)
 * key off this naming and the `replica: true` / `replicaOf` markers.
 *
 * If P has a home cluster (folded earlier), the original stays as the primary
 * copy and is also marked as a replica so the ⇄ glyph renders consistently.
 * If P is an orphan with all its edges redirected, the original is dropped.
 *
 * Mirrors v3 lines 138–221.
 */
export function replicateShared(
  graph: GraphModel,
  opts: ReplicateOptions = {},
): GraphModel & { readonly replicateStats: ReplicateStats } {
  const max = opts.max ?? Infinity;
  const replicateTransitions = opts.replicateTransitions ?? false;

  const nodes = new Map(graph.nodes);
  const nodeToCluster = new Map(graph.nodeToCluster);
  const clusterMembers = new Map<string, string[]>();
  for (const [id, c] of graph.clusters) clusterMembers.set(id, [...c.nodes]);
  const edges = graph.edges.map(e => ({ ...e }));

  // 1. Compute foreign-cluster set per replicable node.
  const foreignByNode = new Map<string, Set<string>>();
  const noteForeign = (nodeId: string, otherId: string): void => {
    if (!nodeId.startsWith('p_') && !(replicateTransitions && nodeId.startsWith('t_'))) return;
    const home = nodeToCluster.get(nodeId);
    const otherCluster = nodeToCluster.get(otherId);
    if (!otherCluster) return;
    if (otherCluster === home) return;
    let s = foreignByNode.get(nodeId);
    if (!s) { s = new Set(); foreignByNode.set(nodeId, s); }
    s.add(otherCluster);
  };
  for (const e of edges) {
    noteForeign(e.src, e.dst);
    noteForeign(e.dst, e.src);
  }

  // 2. Emit replicas for nodes within the cap.
  const replicaMap = new Map<string, Map<string, string>>();  // orig → cluster → replicaId
  let replicatedPlaces = 0;
  let totalCopies = 0;
  for (const [placeId, foreigns] of foreignByNode) {
    if (foreigns.size === 0) continue;
    if (foreigns.size > max) continue;
    const perCluster = new Map<string, string>();
    const orig = nodes.get(placeId);
    if (!orig) continue;
    for (const clusterId of foreigns) {
      const shortName = clusterId.replace(/^cluster_/, '');
      const repId = `${placeId}__rep__${shortName}`;
      perCluster.set(clusterId, repId);
      clusterMembers.get(clusterId)!.push(repId);
      nodeToCluster.set(repId, clusterId);
      nodes.set(repId, {
        id: repId,
        kind: orig.kind,
        attrs: { ...orig.attrs },
        replica: true,
        replicaOf: placeId,
      });
      totalCopies++;
    }
    replicaMap.set(placeId, perCluster);
    replicatedPlaces++;
    // Mark the original as a shared place so the ⇄ glyph renders uniformly.
    nodes.set(placeId, { ...orig, replica: true, replicaOf: placeId });
  }

  // 3. Redirect cross-cluster edges to the local replica on each end.
  for (const e of edges) {
    const sMap = replicaMap.get(e.src);
    const dMap = replicaMap.get(e.dst);
    if (sMap) {
      const dCl = nodeToCluster.get(e.dst);
      if (dCl && sMap.has(dCl)) e.src = sMap.get(dCl)!;
    }
    if (dMap) {
      const sCl = nodeToCluster.get(e.src);
      if (sCl && dMap.has(sCl)) e.dst = dMap.get(sCl)!;
    }
  }

  // 4. Drop orphan originals whose edges all got redirected away.
  for (const [origId] of replicaMap) {
    if (nodeToCluster.has(origId)) continue;  // folded — keep as primary
    const stillHasEdge = edges.some(e => e.src === origId || e.dst === origId);
    if (!stillHasEdge) nodes.delete(origId);
  }

  const clusters = new Map<string, ParsedCluster>();
  for (const [id, c] of graph.clusters) {
    clusters.set(id, { ...c, nodes: clusterMembers.get(id)! });
  }
  const orphans = [...nodes.keys()].filter(n => !nodeToCluster.has(n));

  return {
    nodes,
    clusters,
    nodeToCluster,
    orphans,
    edges,
    replicateStats: { replicatedPlaces, totalCopies },
  };
}
