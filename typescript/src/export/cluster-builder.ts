/**
 * Builds nested `subgraph cluster_*` blocks for DOT export per
 * `spec/11-modular-composition.md` **MOD-040** and `spec/09-export.md`
 * **EXP-016**.
 *
 * Given a flat list of nodes and edges plus a `nodeId -> prefix` map
 * produced during mapping (see {@link import('./petri-net-mapper.js').mapToGraph}),
 * this partitioner:
 *
 * 1. Walks every distinct prefix to produce the cluster tree (nested
 *    {@link Subgraph} entries).
 * 2. Routes each node into the deepest cluster whose prefix equals the
 *    node's prefix; nodes without a prefix stay at the top level.
 * 3. Routes each edge into the deepest cluster that contains **both**
 *    endpoints; edges crossing cluster boundaries (or with at least one
 *    top-level endpoint) stay at the top level so Graphviz routes them
 *    correctly without truncating cluster boxes.
 * 4. Applies a default cluster style (rounded, dashed, light fill) when
 *    none is provided — readable defaults sufficient until task #9 layers
 *    the doclet styling on top.
 *
 * This partitioner is structural-only: it does not consult any
 * {@link import('../core/subnet-def').SubnetDef} or {@link
 * import('../core/instance').Instance} — it operates exclusively on the
 * flattened post-composition node names per **MOD-023**.
 *
 * @module export/cluster-builder
 */

import type { GraphEdge, GraphNode, Subgraph } from './graph.js';
import { sanitize } from './petri-net-mapper.js';
import { parentOf } from './subnet-prefixes.js';

/** Result of partitioning nodes/edges into a clustered hierarchy. */
export interface Partition {
  readonly topLevelNodes: readonly GraphNode[];
  readonly topLevelEdges: readonly GraphEdge[];
  readonly topLevelSubgraphs: readonly Subgraph[];
}

/**
 * Default cluster styling (per [EXP-016] visual contract). These values
 * mirror the `cluster.subnet-cluster` entry in
 * `spec/petri-net-styles.json` so cross-language output stays
 * byte-equivalent.
 */
export const DEFAULT_CLUSTER_ATTRS: Readonly<Record<string, string>> = {
  style: 'rounded,dashed',
  bgcolor: '#FAFAFA',
  penwidth: '1.5',
};

interface MutableCluster {
  readonly prefix: string;
  readonly nodes: GraphNode[];
  readonly edges: GraphEdge[];
  readonly childPrefixes: string[];
}

/**
 * Partitions nodes and edges into a cluster hierarchy. Mutates neither input
 * collection.
 *
 * @param nodes all nodes (places, transitions, junctions)
 * @param edges all edges
 * @param nodeIdToPrefix per-node instance prefix; absent entries stay
 *                       top-level
 * @returns the partitioned cluster hierarchy
 */
export function partition(
  nodes: readonly GraphNode[],
  edges: readonly GraphEdge[],
  nodeIdToPrefix: ReadonlyMap<string, string>,
): Partition {
  // Fast path: no prefixes => no clusters. Preserves byte-equal output for
  // flat (non-composed) nets.
  if (nodeIdToPrefix.size === 0) {
    return {
      topLevelNodes: [...nodes],
      topLevelEdges: [...edges],
      topLevelSubgraphs: [],
    };
  }

  // Step 1: walk every prefix to produce the cluster tree shape. We need
  // every internal prefix node, not just leaf prefixes — e.g. a node
  // "outer/inner/leaf" requires both "outer" and "outer/inner" to exist as
  // cluster blocks per [EXP-016] / [MOD-013].
  //
  // We use a Map for insertion-order iteration (deterministic per [EXP-014]).
  const prefixOrder = new Map<string, true>();
  for (const prefix of nodeIdToPrefix.values()) {
    registerPrefixChain(prefix, prefixOrder);
  }

  // prefix -> (mutable nodes, mutable edges, mutable child prefixes)
  const prefixState = new Map<string, MutableCluster>();
  for (const prefix of prefixOrder.keys()) {
    prefixState.set(prefix, { prefix, nodes: [], edges: [], childPrefixes: [] });
  }
  // Wire parent -> child relationships.
  for (const prefix of prefixState.keys()) {
    const parent = parentOf(prefix);
    if (parent !== undefined) {
      prefixState.get(parent)!.childPrefixes.push(prefix);
    }
  }

  // Step 2: route nodes into their deepest cluster.
  const topLevelNodes: GraphNode[] = [];
  for (const node of nodes) {
    const prefix = nodeIdToPrefix.get(node.id);
    if (prefix === undefined) {
      topLevelNodes.push(node);
    } else {
      prefixState.get(prefix)!.nodes.push(node);
    }
  }

  // Step 3: route edges into the deepest cluster containing both endpoints.
  // Cross-cluster edges stay at top-level so Graphviz draws them between
  // cluster boxes rather than inside one.
  const topLevelEdges: GraphEdge[] = [];
  for (const edge of edges) {
    const fromPrefix = nodeIdToPrefix.get(edge.from);
    const toPrefix = nodeIdToPrefix.get(edge.to);
    const common = deepestCommonPrefix(fromPrefix, toPrefix);
    if (common === undefined) {
      topLevelEdges.push(edge);
    } else {
      prefixState.get(common)!.edges.push(edge);
    }
  }

  // Step 3.5: synthesize ghost edges for 1-hop cluster_X → orphan → cluster_Y
  // paths so Graphviz (with compound=true) can constrain the two clusters'
  // relative layout. Ghost edges are style=invis — they carry layout weight
  // only; the visible flow still goes through the orphan via the real edges.
  // Per spec EXP-017.
  for (const ghost of synthesizeGhostEdges(nodes, edges, nodeIdToPrefix)) {
    topLevelEdges.push(ghost);
  }

  // Step 4: assemble Subgraph records bottom-up so children are built before
  // they're consumed by parents.
  const built = new Map<string, Subgraph>();
  // Reverse the insertion order: parents were inserted before children in
  // registerPrefixChain so iterating reversed produces a deepest-first order.
  const iterationOrder = [...prefixState.keys()].reverse();
  for (const prefix of iterationOrder) {
    const state = prefixState.get(prefix)!;
    const children: Subgraph[] = [];
    for (const childPrefix of state.childPrefixes) {
      const child = built.get(childPrefix);
      if (child !== undefined) {
        children.push(child);
      }
    }
    // Children were built deepest-first, so they're reversed relative to
    // their original insertion order. Restore the original order.
    children.reverse();

    const subgraph: Subgraph = {
      id: sanitize(prefix),
      label: prefix,
      nodes: [...state.nodes],
      edges: [...state.edges],
      subgraphs: children,
      attrs: DEFAULT_CLUSTER_ATTRS,
    };
    built.set(prefix, subgraph);
  }

  // Top-level subgraphs are those whose prefix has no parent.
  const topLevelSubgraphs: Subgraph[] = [];
  for (const prefix of prefixState.keys()) {
    if (parentOf(prefix) === undefined) {
      topLevelSubgraphs.push(built.get(prefix)!);
    }
  }

  return {
    topLevelNodes,
    topLevelEdges,
    topLevelSubgraphs,
  };
}

/**
 * Walks a prefix root-to-leaf, registering every intermediate prefix in
 * `accumulator` (no-op when already present). Ensures parents are inserted
 * before children.
 */
function registerPrefixChain(prefix: string | undefined, accumulator: Map<string, true>): void {
  if (prefix == null || prefix.length === 0) return;
  const segments = prefix.split('/');
  let built = '';
  for (const seg of segments) {
    if (built.length > 0) built += '/';
    built += seg;
    if (!accumulator.has(built)) {
      accumulator.set(built, true);
    }
  }
}

/**
 * Synthesizes one invisible ghost edge per ordered (cluster_X, cluster_Y)
 * pair that is bridged by at least one top-level orphan node via a 1-hop
 * path (i.e. some edge X-node → orphan and some edge orphan → Y-node). The
 * ghost edge carries `style=invis, ltail=cluster_<sanitizedX>,
 * lhead=cluster_<sanitizedY>` so Graphviz (with `compound=true`) treats it
 * as a real cluster-to-cluster layout constraint without producing any
 * visible artifact. Per spec EXP-017.
 *
 * Determinism: walks orphans in `nodes` order, walks each orphan's
 * incoming/outgoing edges in `edges` order. First-witness wins for anchor
 * node selection. This matches the iteration discipline in the Java/Rust
 * mirrors so cross-language byte-parity holds.
 */
function synthesizeGhostEdges(
  nodes: readonly GraphNode[],
  edges: readonly GraphEdge[],
  nodeIdToPrefix: ReadonlyMap<string, string>,
): GraphEdge[] {
  // Index edges by their orphan endpoint. An orphan is any node whose id is
  // not in nodeIdToPrefix.
  const incomingByOrphan = new Map<string, GraphEdge[]>();
  const outgoingByOrphan = new Map<string, GraphEdge[]>();
  for (const edge of edges) {
    const fromHasPrefix = nodeIdToPrefix.has(edge.from);
    const toHasPrefix = nodeIdToPrefix.has(edge.to);
    if (fromHasPrefix && !toHasPrefix) {
      let list = incomingByOrphan.get(edge.to);
      if (list === undefined) {
        list = [];
        incomingByOrphan.set(edge.to, list);
      }
      list.push(edge);
    }
    if (!fromHasPrefix && toHasPrefix) {
      let list = outgoingByOrphan.get(edge.from);
      if (list === undefined) {
        list = [];
        outgoingByOrphan.set(edge.from, list);
      }
      list.push(edge);
    }
  }

  // Walk orphans in nodes order. For each (clusterX_prefix, clusterY_prefix)
  // ordered pair with X !== Y, record the first witness anchor pair.
  // Map<"X\0Y", { from, to, x, y }> — using an insertion-ordered Map for
  // deterministic emission order.
  const ghosts = new Map<string, { from: string; to: string; x: string; y: string }>();
  for (const node of nodes) {
    if (nodeIdToPrefix.has(node.id)) continue;
    const incoming = incomingByOrphan.get(node.id);
    const outgoing = outgoingByOrphan.get(node.id);
    if (incoming === undefined || outgoing === undefined) continue;
    for (const eIn of incoming) {
      const x = nodeIdToPrefix.get(eIn.from)!;
      for (const eOut of outgoing) {
        const y = nodeIdToPrefix.get(eOut.to)!;
        if (x === y) continue;
        const key = `${x}\0${y}`;
        if (!ghosts.has(key)) {
          ghosts.set(key, { from: eIn.from, to: eOut.to, x, y });
        }
      }
    }
  }

  const result: GraphEdge[] = [];
  for (const { from, to, x, y } of ghosts.values()) {
    result.push({
      from,
      to,
      color: '#000000',
      style: 'invis',
      arrowhead: 'none',
      arcType: 'ghost',
      attrs: {
        ltail: 'cluster_' + sanitize(x),
        lhead: 'cluster_' + sanitize(y),
      },
    });
  }
  return result;
}

/**
 * Returns the deepest prefix that is a (non-strict) ancestor of both sides,
 * or `undefined` when there is no shared cluster (top-level routing).
 */
function deepestCommonPrefix(a: string | undefined, b: string | undefined): string | undefined {
  if (a === undefined || b === undefined) return undefined;
  if (a === b) return a;

  const aSegs = a.split('/');
  const bSegs = b.split('/');
  let built = '';
  let matched = 0;
  const min = Math.min(aSegs.length, bSegs.length);
  for (let i = 0; i < min; i++) {
    if (aSegs[i] !== bSegs[i]) break;
    if (matched > 0) built += '/';
    built += aSegs[i];
    matched++;
  }
  return matched === 0 ? undefined : built;
}
