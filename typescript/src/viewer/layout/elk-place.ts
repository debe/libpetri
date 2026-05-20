/**
 * ELK placement + DOT pin-mode rewrite.
 *
 * Stage 2 of the C0 pipeline. Takes the {@link GraphModel} produced by
 * {@link parseLibpetriDot} → {@link foldOrphans} → {@link replicateShared},
 * runs ELKjs to compute absolute `(x, y)` per node and bounding boxes per
 * cluster, then emits a fresh DOT string with positions pinned via
 * `pos="x,y!"` and `bb="…"`. Downstream callers render the result through
 * `@viz-js/viz` with `engine: 'neato'` + `graphAttributes: { nop: '1' }` —
 * Graphviz uses the pinned positions verbatim and routes edges around the
 * pinned cluster boundaries.
 *
 * `elkLayout` takes (graph, cfg?); `writeBack` takes (graph, layout).
 * Neither touches the original DOT text — the model after replication has
 * nodes the original DOT doesn't, so patching the original would be
 * incorrect.
 *
 * Layout is configurable via {@link ElkLayoutConfig}: the per-subnet
 * algorithm (`clusterLayout`) and whether clusters dominated by side-effect
 * leaf places pack those leaves into a grid sub-block (`leafPacking`).
 *
 * @module viewer/layout/elk-place
 */

import ELK from 'elkjs/lib/elk.bundled.js';
import type {
  ElkExtendedEdge,
  ElkNode,
} from 'elkjs/lib/elk-api.js';
import type { ArcType, GraphModel, ParsedCluster, ParsedNode } from './preprocess.js';

const ORCHESTRATOR_CLUSTER_ID = 'cluster_orchestrator';

// Visual sizing — kept proportional to the v3 reference renderer so the
// resulting bounding box is comparable to C0-GOOD_v3.svg.
const PLACE_RADIUS = 22;
const PLACE_CHARW = 7.4;
const PLACE_PAD_BELOW = 16;
const FONT_PLACE = 13;
const TRANSITION_MIN_W = 180;
const TRANSITION_H = 40;
const TRANSITION_CHARW = 8.5;
const JUNCTION_SIZE = 28;
const FONT_CLUSTER = 17;
const ROOT_SPACING = 90;
const CLUSTER_SPACING = 16;

/**
 * Width/height in points that ELK should reserve for a node. Mirrors
 * `nodeDims` in v3 lines 66–78 — places get extra height to leave room for
 * the xlabel underneath the circle.
 */
function nodeDims(node: ParsedNode): { width: number; height: number } {
  if (node.kind === 'place') {
    const label = (node.attrs.xlabel ?? node.attrs.label ?? node.id).replace(/\\n/g, ' ');
    const labelWidth = label.length * PLACE_CHARW;
    const circleD = PLACE_RADIUS * 2 + 4;
    return {
      width: Math.max(circleD, labelWidth),
      height: circleD + PLACE_PAD_BELOW + FONT_PLACE,
    };
  }
  if (node.kind === 'junction') {
    return { width: JUNCTION_SIZE, height: JUNCTION_SIZE };
  }
  const label = (node.attrs.label ?? node.id).replace(/\\n/g, ' ');
  return {
    width: Math.max(TRANSITION_MIN_W, label.length * TRANSITION_CHARW),
    height: TRANSITION_H,
  };
}

export interface NodePosition {
  readonly x: number;
  readonly y: number;
  readonly width: number;
  readonly height: number;
}

export interface ClusterBox {
  readonly x: number;
  readonly y: number;
  readonly width: number;
  readonly height: number;
}

export interface EdgePath {
  readonly start: { x: number; y: number };
  readonly end: { x: number; y: number };
  readonly bends: ReadonlyArray<{ x: number; y: number }>;
}

export interface LayoutResult {
  readonly nodePositions: ReadonlyMap<string, NodePosition>;
  readonly clusterBoxes: ReadonlyMap<string, ClusterBox>;
  /** Keyed on `${src}->${dst}` — ELK-computed edge routes for `nop=2`. */
  readonly edgePaths: ReadonlyMap<string, EdgePath>;
  readonly totalWidth: number;
  readonly totalHeight: number;
}

const CLUSTER_OPTIONS: Record<string, string> = {
  'elk.padding': `[top=${FONT_CLUSTER + 16},left=16,bottom=16,right=16]`,
  'elk.algorithm': 'layered',
  'elk.direction': 'DOWN',
  'elk.spacing.nodeNode': String(CLUSTER_SPACING),
  'elk.layered.spacing.nodeNodeBetweenLayers': String(CLUSTER_SPACING + 6),
  'elk.edgeRouting': 'ORTHOGONAL',
};

const ROOT_OPTIONS: Record<string, string> = {
  'elk.algorithm': 'org.eclipse.elk.rectpacking',
  'elk.aspectRatio': '1.4',
  'elk.padding': '[top=24,left=24,bottom=24,right=24]',
  'elk.spacing.nodeNode': String(ROOT_SPACING),
};

const ORCHESTRATOR_OPTIONS: Record<string, string> = {
  ...CLUSTER_OPTIONS,
  'elk.aspectRatio': '2.4',
  'elk.spacing.nodeNode': '10',
};

/**
 * Layout options for the synthetic orchestrator when it IS the whole
 * diagram — the flat "one-net" view (no real subnet clusters).
 *
 * `ORCHESTRATOR_OPTIONS` deliberately packs the orphan block tight
 * (`nodeNode: 10`, `aspectRatio: 2.4`) so it stays compact next to the
 * real subnet blocks the `rectpacking` root arranges. When the graph is
 * flat there are no other blocks: that compaction just bunches the whole
 * net up. Flat mode instead gets a generous layered layout — a clean
 * place→transition rank flow — with no forced aspect ratio.
 */
const FLAT_OPTIONS: Record<string, string> = {
  'elk.padding': `[top=24,left=24,bottom=24,right=24]`,
  'elk.algorithm': 'layered',
  'elk.direction': 'DOWN',
  'elk.spacing.nodeNode': '45',
  'elk.layered.spacing.nodeNodeBetweenLayers': '60',
  'elk.edgeRouting': 'ORTHOGONAL',
};

/**
 * Per-subnet ELK algorithm used when {@link ElkLayoutConfig.clusterLayout}
 * is `'rectpacking'` — packs a cluster's nodes as a 2-D grid, ignoring
 * intra-cluster edges. Maximally compact, but the place→transition flow
 * reading order is lost.
 */
const RECTPACK_CLUSTER_OPTIONS: Record<string, string> = {
  'elk.padding': `[top=${FONT_CLUSTER + 16},left=16,bottom=16,right=16]`,
  'elk.algorithm': 'org.eclipse.elk.rectpacking',
  'elk.aspectRatio': '1.3',
  'elk.spacing.nodeNode': String(CLUSTER_SPACING),
};

// Sub-layout options for a leaf-packed cluster: the flow part keeps the
// layered place→transition rank flow; the leaf part is a compact grid.
const FLOW_SUB_OPTIONS: Record<string, string> = {
  'elk.algorithm': 'layered',
  'elk.direction': 'DOWN',
  'elk.spacing.nodeNode': String(CLUSTER_SPACING),
  'elk.layered.spacing.nodeNodeBetweenLayers': String(CLUSTER_SPACING + 6),
  'elk.edgeRouting': 'ORTHOGONAL',
};
const LEAF_SUB_OPTIONS: Record<string, string> = {
  'elk.algorithm': 'org.eclipse.elk.rectpacking',
  'elk.aspectRatio': '1.4',
  'elk.spacing.nodeNode': String(CLUSTER_SPACING),
};
/** Gap between the layered flow and the packed leaf block, in points. */
const LEAF_BLOCK_GAP = 40;
/** Padding inside a leaf-packed cluster box (left/right/bottom). */
const SUB_PAD = 16;
/** Top padding inside a cluster box — room for the cluster label. */
const SUB_PAD_TOP = FONT_CLUSTER + 16;

// ======================== Layout configuration ========================

/** Per-subnet ELK algorithm. */
export type ClusterLayout = 'layered' | 'rectpacking';

/** Tuning for side-effect-leaf packing — see {@link ElkLayoutConfig}. */
export interface LeafPackingOptions {
  /**
   * A cluster is "dominated" — and its side-effect leaf places get packed
   * into a grid sub-block — when it has at least this many of them.
   * Default 10.
   */
  readonly minLeaves?: number;
  /**
   * Arc types that mark a place as a side-effect leaf (a place whose every
   * intra-cluster arc is one of these carries no data-flow ordering).
   * Default `['reset', 'read']`.
   */
  readonly arcs?: readonly ArcType[];
}

/**
 * Layout configuration for {@link elkLayout}, surfaced to viewer callers
 * via `MountOptions`.
 */
export interface ElkLayoutConfig {
  /** Per-subnet ELK algorithm. Default `'layered'`. */
  readonly clusterLayout?: ClusterLayout;
  /**
   * Pack side-effect leaf places into a rectpacking sub-block, in clusters
   * where they dominate. `true` (default) enables it with defaults; `false`
   * disables it; an object tunes the threshold / arc types. Only takes
   * effect when `clusterLayout` is `'layered'`.
   */
  readonly leafPacking?: boolean | LeafPackingOptions;
}

interface ResolvedConfig {
  readonly clusterLayout: ClusterLayout;
  readonly leafPacking: {
    readonly enabled: boolean;
    readonly minLeaves: number;
    readonly arcs: ReadonlySet<ArcType>;
  };
}

const DEFAULT_MIN_LEAVES = 10;

function resolveConfig(cfg?: ElkLayoutConfig): ResolvedConfig {
  const lp = cfg?.leafPacking ?? true;
  const lpObj: LeafPackingOptions = typeof lp === 'object' ? lp : {};
  return {
    clusterLayout: cfg?.clusterLayout ?? 'layered',
    leafPacking: {
      enabled: lp !== false,
      minLeaves: lpObj.minLeaves ?? DEFAULT_MIN_LEAVES,
      arcs: new Set(lpObj.arcs ?? ['reset', 'read']),
    },
  };
}

/** A cluster pre-laid-out as [layered flow] stacked over [packed leaves]. */
interface PrebuiltCluster {
  readonly width: number;
  readonly height: number;
  /** member node id → position relative to the cluster's top-left. */
  readonly rel: ReadonlyMap<string, NodePosition>;
}

/**
 * Split a cluster's members into flow nodes and "side-effect leaf places".
 *
 * A side-effect leaf is a place whose every intra-cluster arc is a
 * side-effect arc (per `arcs` — reset/read). Such a place is not on any
 * data-flow path, so packing it as a grid cell loses no reading order.
 */
function classifyLeaves(
  graph: GraphModel,
  cluster: ParsedCluster,
  arcs: ReadonlySet<ArcType>,
): { flow: string[]; leaves: string[] } {
  const members = new Set(cluster.nodes);
  const intraDegree = new Map<string, number>();
  const intraSideEffect = new Map<string, number>();
  for (const e of graph.edges) {
    if (!members.has(e.src) || !members.has(e.dst)) continue;
    const sideEffect = arcs.has(e.arc) ? 1 : 0;
    for (const id of [e.src, e.dst]) {
      intraDegree.set(id, (intraDegree.get(id) ?? 0) + 1);
      intraSideEffect.set(id, (intraSideEffect.get(id) ?? 0) + sideEffect);
    }
  }
  const flow: string[] = [];
  const leaves: string[] = [];
  for (const id of cluster.nodes) {
    const node = graph.nodes.get(id);
    if (!node) continue;
    const deg = intraDegree.get(id) ?? 0;
    const isLeaf =
      node.kind === 'place' &&
      deg >= 1 &&
      (intraSideEffect.get(id) ?? 0) === deg;
    (isLeaf ? leaves : flow).push(id);
  }
  return { flow, leaves };
}

/**
 * Lay a dominated cluster out as two stacked blocks: the flow nodes via
 * `layered` (place→transition rank flow), the side-effect leaves via
 * `rectpacking` (a compact grid). Returns the cluster's overall size and
 * every member node's position relative to the cluster's top-left.
 */
async function layoutDominatedCluster(
  elk: InstanceType<typeof ELK>,
  graph: GraphModel,
  flow: string[],
  leaves: string[],
): Promise<PrebuiltCluster> {
  const dimsOf = (id: string): { width: number; height: number } =>
    nodeDims(graph.nodes.get(id)!);

  const flowSet = new Set(flow);
  const flowEdges: ElkExtendedEdge[] = [];
  graph.edges.forEach((e, i) => {
    if (flowSet.has(e.src) && flowSet.has(e.dst)) {
      flowEdges.push({ id: `fe${i}`, sources: [e.src], targets: [e.dst] });
    }
  });

  const flowLayout: ElkNode = await elk.layout({
    id: '__flow',
    layoutOptions: FLOW_SUB_OPTIONS,
    children: flow.map(id => ({ id, ...dimsOf(id) })),
    edges: flowEdges,
  });
  const leafLayout: ElkNode = await elk.layout({
    id: '__leaves',
    layoutOptions: LEAF_SUB_OPTIONS,
    children: leaves.map(id => ({ id, ...dimsOf(id) })),
    edges: [],
  });

  const flowW = flowLayout.width ?? 0;
  const flowH = flowLayout.height ?? 0;
  const leafW = leafLayout.width ?? 0;
  const leafH = leafLayout.height ?? 0;
  const contentW = Math.max(flowW, leafW);
  const contentH = flowH + (leaves.length > 0 ? LEAF_BLOCK_GAP + leafH : 0);

  const rel = new Map<string, NodePosition>();
  const flowOffX = SUB_PAD + (contentW - flowW) / 2;
  for (const ch of flowLayout.children ?? []) {
    rel.set(ch.id, {
      x: flowOffX + (ch.x ?? 0),
      y: SUB_PAD_TOP + (ch.y ?? 0),
      width: ch.width ?? 0,
      height: ch.height ?? 0,
    });
  }
  const leafOffX = SUB_PAD + (contentW - leafW) / 2;
  const leafOffY = SUB_PAD_TOP + flowH + LEAF_BLOCK_GAP;
  for (const ch of leafLayout.children ?? []) {
    rel.set(ch.id, {
      x: leafOffX + (ch.x ?? 0),
      y: leafOffY + (ch.y ?? 0),
      width: ch.width ?? 0,
      height: ch.height ?? 0,
    });
  }

  return {
    width: contentW + 2 * SUB_PAD,
    height: contentH + SUB_PAD_TOP + SUB_PAD,
    rel,
  };
}

/**
 * Group edges by the cluster that contains both endpoints (or 'root' if
 * the edge crosses cluster boundaries).
 *
 * Orphans count as living in `cluster_orchestrator` for routing purposes,
 * matching v3's `ownerOf` (line 223).
 */
function partitionEdges(graph: GraphModel): {
  byCluster: Map<string, ElkExtendedEdge[]>;
  cross: ElkExtendedEdge[];
  /** edgeId → "src->dst" so the layout walk can recover the original key. */
  edgeIdToKey: Map<string, string>;
} {
  const byCluster = new Map<string, ElkExtendedEdge[]>();
  const cross: ElkExtendedEdge[] = [];
  const edgeIdToKey = new Map<string, string>();
  const ownerOf = (id: string): string =>
    graph.nodeToCluster.get(id) ?? ORCHESTRATOR_CLUSTER_ID;

  graph.edges.forEach((e, i) => {
    const so = ownerOf(e.src);
    const dt = ownerOf(e.dst);
    const id = `e${i}`;
    edgeIdToKey.set(id, `${e.src}->${e.dst}`);
    const elkEdge: ElkExtendedEdge = {
      id,
      sources: [e.src],
      targets: [e.dst],
    };
    if (so === dt) {
      let list = byCluster.get(so);
      if (!list) { list = []; byCluster.set(so, list); }
      list.push(elkEdge);
    } else {
      cross.push(elkEdge);
    }
  });
  return { byCluster, cross, edgeIdToKey };
}

/**
 * Run ELK layout against the C0 graph and return absolute positions.
 *
 * Orphan nodes are wrapped in a synthetic `cluster_orchestrator` so ELK
 * lays them out as a single block alongside the real subnets, which the
 * `rectpacking` root algorithm then packs.
 *
 * With the default config a cluster dominated by side-effect leaf places
 * (≥ `leafPacking.minLeaves` of them) is pre-laid-out as a layered flow
 * stacked over a packed grid of those leaves — so a transition with many
 * reset arcs no longer strings its leaves into one wide row. See
 * {@link ElkLayoutConfig}.
 */
export async function elkLayout(
  graph: GraphModel,
  cfg?: ElkLayoutConfig,
): Promise<LayoutResult> {
  const config = resolveConfig(cfg);
  const { byCluster, cross, edgeIdToKey } = partitionEdges(graph);
  const elk = new ELK();
  const clusterOptions =
    config.clusterLayout === 'rectpacking' ? RECTPACK_CLUSTER_OPTIONS : CLUSTER_OPTIONS;

  // Pre-lay-out clusters dominated by side-effect leaf places. Only in
  // 'layered' mode — 'rectpacking' already packs every cluster's nodes.
  const prebuilt = new Map<string, PrebuiltCluster>();
  if (config.clusterLayout === 'layered' && config.leafPacking.enabled) {
    for (const [clusterId, cluster] of graph.clusters) {
      const { flow, leaves } = classifyLeaves(graph, cluster, config.leafPacking.arcs);
      if (leaves.length >= config.leafPacking.minLeaves && flow.length > 0) {
        prebuilt.set(clusterId, await layoutDominatedCluster(elk, graph, flow, leaves));
      }
    }
  }

  const elkChildren: ElkNode[] = [];
  for (const [clusterId, cluster] of graph.clusters) {
    const pre = prebuilt.get(clusterId);
    if (pre) {
      // Childless fixed-size box — ELK's root packer places it; the member
      // node positions are spliced back in during the walk.
      elkChildren.push({ id: clusterId, width: pre.width, height: pre.height });
      continue;
    }
    elkChildren.push({
      id: clusterId,
      layoutOptions: clusterOptions,
      children: cluster.nodes
        .map(id => graph.nodes.get(id))
        .filter((n): n is ParsedNode => n !== undefined)
        .map(n => ({ id: n.id, ...nodeDims(n) })),
      edges: byCluster.get(clusterId) ?? [],
    });
  }
  // Synthetic orchestrator cluster holds the remaining orphans. When there
  // are no real clusters the orchestrator IS the whole diagram (flat view),
  // so it gets a generous full layered layout instead of the compact block
  // packing tuned for sitting beside real subnets.
  const orchestratorOptions =
    graph.clusters.size === 0
      ? FLAT_OPTIONS
      : config.clusterLayout === 'rectpacking'
        ? RECTPACK_CLUSTER_OPTIONS
        : ORCHESTRATOR_OPTIONS;
  elkChildren.push({
    id: ORCHESTRATOR_CLUSTER_ID,
    layoutOptions: orchestratorOptions,
    children: graph.orphans
      .map(id => graph.nodes.get(id))
      .filter((n): n is ParsedNode => n !== undefined)
      .map(n => ({ id: n.id, ...nodeDims(n) })),
    edges: byCluster.get(ORCHESTRATOR_CLUSTER_ID) ?? [],
  });

  const rootGraph: ElkNode = {
    id: 'root',
    layoutOptions: ROOT_OPTIONS,
    children: elkChildren,
    // Cross-cluster edges only ever fed `edgePaths` (an unused nop2
    // affordance); `rectpacking` ignores them for placement. Drop them when
    // any cluster is a childless prebuilt box — the edges reference member
    // nodes ELK can no longer resolve in the hierarchy.
    edges: prebuilt.size > 0 ? [] : cross,
  };
  const layout: ElkNode = await elk.layout(rootGraph);

  const nodePositions = new Map<string, NodePosition>();
  const clusterBoxes = new Map<string, ClusterBox>();
  const edgePaths = new Map<string, EdgePath>();

  const walk = (node: ElkNode, parentX: number, parentY: number): void => {
    const ax = parentX + (node.x ?? 0);
    const ay = parentY + (node.y ?? 0);
    const pre = node.id !== 'root' ? prebuilt.get(node.id) : undefined;
    const isCluster =
      node.id !== 'root' && ((node.children?.length ?? 0) > 0 || pre !== undefined);
    if (isCluster) {
      clusterBoxes.set(node.id, {
        x: ax, y: ay,
        width: node.width ?? 0,
        height: node.height ?? 0,
      });
      // Prebuilt cluster: splice in the pre-computed member positions,
      // offset by the cluster's ELK-assigned absolute origin.
      if (pre) {
        for (const [memberId, r] of pre.rel) {
          nodePositions.set(memberId, {
            x: ax + r.x, y: ay + r.y, width: r.width, height: r.height,
          });
        }
      }
    }
    if (node.id !== 'root' && !isCluster) {
      nodePositions.set(node.id, {
        x: ax, y: ay,
        width: node.width ?? 0,
        height: node.height ?? 0,
      });
    }
    // Edges inside this node — their section coords are in the parent's
    // coordinate frame, so the offset to absolutize is (parentX, parentY)
    // for root edges, or (ax, ay) for cluster-internal edges.
    const edgeOffsetX = node.id === 'root' ? parentX : ax;
    const edgeOffsetY = node.id === 'root' ? parentY : ay;
    for (const edge of node.edges ?? []) {
      const key = edge.id ? edgeIdToKey.get(edge.id) : undefined;
      const section = edge.sections?.[0];
      if (!key || !section) continue;
      edgePaths.set(key, {
        start: {
          x: edgeOffsetX + section.startPoint.x,
          y: edgeOffsetY + section.startPoint.y,
        },
        end: {
          x: edgeOffsetX + section.endPoint.x,
          y: edgeOffsetY + section.endPoint.y,
        },
        bends: (section.bendPoints ?? []).map(p => ({
          x: edgeOffsetX + p.x,
          y: edgeOffsetY + p.y,
        })),
      });
    }
    for (const child of node.children ?? []) walk(child, ax, ay);
  };
  walk(layout, 0, 0);

  return {
    nodePositions,
    clusterBoxes,
    edgePaths,
    totalWidth: layout.width ?? 0,
    totalHeight: layout.height ?? 0,
  };
}

/**
 * Escape an attribute value for inclusion in a DOT string literal.
 *
 * Quotes are doubled (per the DOT escape convention `\"`).
 */
function quote(value: string): string {
  return `"${value.replace(/\\/g, '\\\\').replace(/"/g, '\\"')}"`;
}

/**
 * Render a node's attribute list — preserving the parsed attrs (including
 * libpetri's `width`/`height`, which are the *visual* shape dimensions)
 * and adding the ELK-computed `pos` so Graphviz `nop` can pin it.
 *
 * The `pos="x,y!"` form (with trailing `!`) is the neato pin-mode marker.
 * Do NOT emit ELK's layout-reserved width/height to Graphviz — those are
 * the bounding boxes needed for ELK packing (which account for xlabel
 * spillover), not the visible shape sizes. libpetri's standard styles use
 * `width=0.35` for places (25pt circles); overriding with ELK's
 * ~3 inch label-padded box made Graphviz render 114pt-radius circles.
 */
function nodeAttrLine(node: ParsedNode, pos: NodePosition): string {
  const attrs: string[] = [];
  // Center the pinned position on the node's bbox (ELK gives the top-left).
  const cx = pos.x + pos.width / 2;
  const cy = pos.y + pos.height / 2;
  attrs.push(`pos=${quote(`${cx.toFixed(2)},${cy.toFixed(2)}!`)}`);
  for (const [k, v] of Object.entries(node.attrs)) {
    if (k === 'pos') continue;
    attrs.push(`${k}=${quote(v)}`);
  }
  return `${node.id} [${attrs.join(', ')}];`;
}

function edgeAttrLine(src: string, dst: string, rawAttrs: string): string {
  // Splice libpetri's original attrs verbatim so style/penwidth/label/color
  // match `DotExporter` 1:1. We do NOT emit `pos=` for edges — under engine
  // `nop` Graphviz routes edges itself around the pinned node positions,
  // which gives proper boundary clipping (arrowheads land at the visual
  // node edge) and avoids needing a custom polyline-to-spline converter.
  // The only "custom" arrowhead is `arrowhead="odot"` for inhibitor edges,
  // which libpetri's exporter already writes into rawAttrs.
  const body = rawAttrs.trim();
  return `${src} -> ${dst}` + (body ? ` [${body}];` : ';');
}

/**
 * Emit a Graphviz DOT string with positions pinned. Render the result with
 * `@viz-js/viz` using:
 *
 * ```ts
 * viz.renderSVGElement(dot, {
 *   engine: 'nop',
 *   yInvert: true,
 * });
 * ```
 *
 * `engine: 'nop'` (a.k.a. `nop1`) honours the pinned `pos=` on every node
 * and routes edges around them. We use this rather than `nop2` because
 * `nop2` would force us to provide a spline for every edge ourselves (no
 * routing) — and Graphviz's own routing produces correctly-clipped
 * arrowheads at the visual node boundary, which our ELK polylines did not
 * (ELK uses the layout-reserved bbox, our visual circle is much smaller).
 *
 * `yInvert: true` matches ELK's Y-down convention to Graphviz's Y-up.
 */
export function writeBack(graph: GraphModel, layout: LayoutResult): string {
  const lines: string[] = [];
  lines.push('digraph LibpetriPinned {');
  lines.push('    rankdir=TB;');
  lines.push('    overlap="false";');
  lines.push('    compound="true";');
  lines.push('    fontname="Helvetica,Arial,sans-serif";');
  lines.push('    outputorder="edgesfirst";');
  lines.push('    node [fontname="Helvetica,Arial,sans-serif", fontsize=10];');
  lines.push('    edge [fontname="Helvetica,Arial,sans-serif", fontsize=9];');

  // Clusters with their pinned bounding boxes
  for (const [clusterId, cluster] of graph.clusters) {
    const box = layout.clusterBoxes.get(clusterId);
    lines.push(`    subgraph ${clusterId} {`);
    lines.push(`        label=${quote(cluster.shortName)};`);
    lines.push(`        style="rounded,dashed";`);
    lines.push(`        bgcolor="#FAFAFA";`);
    lines.push(`        penwidth=1.5;`);
    if (box) {
      const x1 = box.x.toFixed(2);
      const y1 = box.y.toFixed(2);
      const x2 = (box.x + box.width).toFixed(2);
      const y2 = (box.y + box.height).toFixed(2);
      lines.push(`        bb=${quote(`${x1},${y1},${x2},${y2}`)};`);
    }
    for (const nodeId of cluster.nodes) {
      const node = graph.nodes.get(nodeId);
      const pos = layout.nodePositions.get(nodeId);
      if (!node || !pos) continue;
      lines.push('        ' + nodeAttrLine(node, pos));
    }
    lines.push('    }');
  }

  // Orphans (root-level nodes) — laid out inside the synthetic
  // orchestrator cluster but emitted at root so they sit alongside the
  // real subnets without their own labelled box.
  for (const orphanId of graph.orphans) {
    const node = graph.nodes.get(orphanId);
    const pos = layout.nodePositions.get(orphanId);
    if (!node || !pos) continue;
    lines.push('    ' + nodeAttrLine(node, pos));
  }

  // Edges — emit just the source -> dest pair plus libpetri's original
  // styling attrs. Graphviz `nop` routes the line itself and clips arrow
  // heads to the visual node boundary.
  for (const edge of graph.edges) {
    lines.push('    ' + edgeAttrLine(edge.src, edge.dst, edge.rawAttrs));
  }

  lines.push('}');
  return lines.join('\n');
}
