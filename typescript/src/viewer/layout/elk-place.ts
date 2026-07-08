/**
 * ELK placement + DOT pin-mode rewrite.
 *
 * Stage 2 of the C0 pipeline. Takes the {@link GraphModel} produced by
 * {@link parseLibpetriDot} → {@link foldOrphans} → {@link replicateShared},
 * runs ELKjs to compute absolute `(x, y)` per node, bounding boxes per
 * cluster, and orthogonal `(x, y)` routes per edge, then emits a fresh DOT
 * string with node positions pinned via `pos="x,y!"`, cluster boxes via
 * `bb="…"`, and each edge's route as a `pos="e,…"` spline. Downstream callers
 * render the result through `@viz-js/viz` with `engine: 'nop2'` — Graphviz
 * draws the pinned node positions AND edge routes verbatim, doing no layout or
 * routing of its own (see {@link writeBack} / {@link edgePosSpline} for why we
 * route edges ourselves rather than let Graphviz's ortho router run).
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
  /** Keyed on `${src}->${dst}` — ELK-computed edge routes for Graphviz `nop2`. */
  readonly edgePaths: ReadonlyMap<string, EdgePath>;
  readonly totalWidth: number;
  readonly totalHeight: number;
}

// Shared edge-routing options for the layered layouts. Spacing gives parallel
// edges their own channels (ELK's ~10pt default lets dense fan-in/out at
// junctions and shared places collapse into one thick line) and keeps edges
// off the nodes/labels they pass. `mergeEdges` bundles arcs that share an
// endpoint into a common orthogonal trunk that branches at each end — so e.g.
// a transition's many reset arcs read as one labelled bus with a tidy branch
// up to each place, instead of a stack of nested right-angle brackets.
// Trade-off (accepted, EXP-004): arcs sharing an endpoint run collinearly along
// the shared trunk, so over that stretch their strokes over-paint — only the
// endpoints (arrowheads/labels) stay per-type distinct. Kept intentionally for
// legibility on dense fan-in/out; any added ELK layout cost is paid once per
// unique net and amortized by the pinned-DOT cache in render.ts.
const LAYERED_EDGE_OPTS: Record<string, string> = {
  'elk.spacing.edgeEdge': '18',
  'elk.spacing.edgeNode': '18',
  'elk.layered.spacing.edgeEdgeBetweenLayers': '16',
  'elk.layered.spacing.edgeNodeBetweenLayers': '16',
  'elk.layered.mergeEdges': 'true',
};

const CLUSTER_OPTIONS: Record<string, string> = {
  'elk.padding': `[top=${FONT_CLUSTER + 16},left=16,bottom=16,right=16]`,
  'elk.algorithm': 'layered',
  'elk.direction': 'DOWN',
  'elk.spacing.nodeNode': String(CLUSTER_SPACING),
  'elk.layered.spacing.nodeNodeBetweenLayers': String(CLUSTER_SPACING + 6),
  'elk.edgeRouting': 'ORTHOGONAL',
  ...LAYERED_EDGE_OPTS,
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
  ...LAYERED_EDGE_OPTS,
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
  ...LAYERED_EDGE_OPTS,
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
    // Cross-cluster edges feed `edgePaths` (the routes nop2 draws), but
    // `rectpacking` never routes them, so they fall back to the L-corner in
    // `edgePosSpline`. Drop them when any cluster is a childless prebuilt box —
    // the edges reference member nodes ELK can no longer resolve in the hierarchy.
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

// ======================== Orthogonal edge routing ========================
//
// We render the pinned graph with Graphviz engine `nop2`, which draws edges
// from the `pos=` spline we supply verbatim (no routing). We supply ELK's own
// orthogonal route for each edge. This deliberately avoids Graphviz's `ortho`
// spline router, which is unusable here: its maze/trapezoid allocator (see
// `mkMaze`, `trapezoid.c`) requests a large block that the @viz-js/viz wasm
// heap denies past ~220 node obstacles, and Graphviz does not check the failed
// allocation, so the next write traps the wasm ("memory access out of
// bounds"). Native Graphviz has the heap headroom and never trips it, but the
// wasm build does — so on the big Marvin nets `splines=ortho` hard-crashes.
// Drawing ELK's routes ourselves sidesteps that router entirely and cannot
// crash, on a net of any size.

/** Length of the drawn arrowhead, in points (Graphviz default ≈ 10). */
const ARROW_LEN = 10;

/**
 * Inches → drawn *half*-extent in points (72 dpi ÷ 2). Libpetri's `width`/
 * `height` attrs are inches; a node's drawn radius / box half-side is
 * `inches * HALF_PT_PER_IN`.
 */
const HALF_PT_PER_IN = 36;

interface Pt {
  readonly x: number;
  readonly y: number;
}

/** Visual node center — Graphviz draws the shape centered on the pinned pos. */
function drawnCenter(pos: NodePosition): Pt {
  return { x: pos.x + pos.width / 2, y: pos.y + pos.height / 2 };
}

interface Extent {
  readonly shape: 'circle' | 'diamond' | 'box';
  readonly rx: number;
  readonly ry: number;
}

/**
 * Half-extents of a node's *drawn* shape (not ELK's layout-reserved box).
 * The drawn shape comes from libpetri's own `width`/`height` attrs
 * (inches → points): circles/diamonds are fixed-size, while a transition box
 * grows to its label, so its half-width is estimated from the label length.
 */
function visualExtent(node: ParsedNode): Extent {
  const wIn = parseFloat(node.attrs.width ?? '');
  const hIn = parseFloat(node.attrs.height ?? '');
  const shape = node.attrs.shape ?? '';
  // Fallbacks are the libpetri StyleConstants defaults in drawn half-points:
  // place/end 0.35in, junction 0.3in, transition box 0.8×0.4in.
  if (shape === 'circle' || shape === 'doublecircle') {
    const r =
      (Number.isFinite(wIn) ? wIn * HALF_PT_PER_IN : 0.35 * HALF_PT_PER_IN) +
      (shape === 'doublecircle' ? 4 : 0); // +4pt for the outer end-place ring
    return { shape: 'circle', rx: r, ry: r };
  }
  if (shape === 'diamond') {
    // Junctions are squares-on-point; approachEndpoint clips to the diamond's
    // bounding box, so an arrowhead entering near a tip can float a few points
    // off the slanted face — cosmetic on 0.3in junctions.
    return {
      shape: 'diamond',
      rx: Number.isFinite(wIn) ? wIn * HALF_PT_PER_IN : 0.3 * HALF_PT_PER_IN,
      ry: Number.isFinite(hIn) ? hIn * HALF_PT_PER_IN : 0.3 * HALF_PT_PER_IN,
    };
  }
  // Box (transition): height is reliable; width grows to the label, so estimate
  // from the label length (~6pt/char + 16pt pad) and floor by the attr width.
  const label = (node.attrs.label ?? '').replace(/\\n/g, ' ');
  const estHalfW = (label.length * 6 + 16) / 2;
  return {
    shape: 'box',
    rx: Math.max(Number.isFinite(wIn) ? wIn * HALF_PT_PER_IN : 0.8 * HALF_PT_PER_IN, estHalfW),
    ry: Number.isFinite(hIn) ? hIn * HALF_PT_PER_IN : 0.4 * HALF_PT_PER_IN,
  };
}

interface Approach {
  /** Point ON the visual node boundary where the edge meets the shape. */
  readonly entry: Pt;
  /** Optional pre-entry corner that keeps the connector a right angle. */
  readonly jog?: Pt;
}

/**
 * Where an edge should meet a node's *visual* boundary, given ELK's route
 * point on the node's layout box (`boxEnd`, larger than the drawn shape) and
 * the adjacent route point (`neighbor`). Keeps the approach axis-aligned.
 *
 * When the approach would land within the shape's span it clips straight onto
 * the boundary (preserving ELK's fan-out across a wide box). When it would
 * MISS the shape — e.g. fan-in to a place whose label-padded box is far wider
 * than its little circle, so ELK enters at an x beyond the circle radius — it
 * funnels to the near-side centre of the shape and returns a `jog` so the
 * connector turns at a right angle instead of leaving the arrowhead floating
 * beside the node.
 */
function approachEndpoint(center: Pt, ext: Extent, boxEnd: Pt, neighbor: Pt): Approach {
  const vertical = Math.abs(neighbor.x - boxEnd.x) <= Math.abs(neighbor.y - boxEnd.y);
  if (vertical) {
    const sgn = neighbor.y < center.y ? -1 : 1; // meet the top (−) or bottom (+)
    const off = Math.abs(boxEnd.x - center.x);
    const reach = ext.shape === 'circle' ? ext.rx - 1 : ext.rx;
    if (off < reach) {
      const dy = ext.shape === 'circle' ? Math.sqrt(ext.rx * ext.rx - off * off) : ext.ry;
      return { entry: { x: boxEnd.x, y: center.y + sgn * dy } };
    }
    return { entry: { x: center.x, y: center.y + sgn * ext.ry }, jog: { x: center.x, y: neighbor.y } };
  }
  const sgn = neighbor.x < center.x ? -1 : 1; // meet the left (−) or right (+)
  const off = Math.abs(boxEnd.y - center.y);
  const reach = ext.shape === 'circle' ? ext.rx - 1 : ext.ry;
  if (off < reach) {
    const dx = ext.shape === 'circle' ? Math.sqrt(ext.rx * ext.rx - off * off) : ext.rx;
    return { entry: { x: center.x + sgn * dx, y: boxEnd.y } };
  }
  return { entry: { x: center.x + sgn * ext.rx, y: center.y }, jog: { x: neighbor.x, y: center.y } };
}

/** Format a point as Graphviz `x,y` with 2-decimal precision. */
const fmtPt = (p: Pt): string => `${p.x.toFixed(2)},${p.y.toFixed(2)}`;
const lerp = (a: Pt, b: Pt, t: number): Pt => ({ x: a.x + (b.x - a.x) * t, y: a.y + (b.y - a.y) * t });

/**
 * Build a Graphviz edge `pos` spline that draws ELK's orthogonal route as
 * straight segments, clipped to the visual node boundaries so arrowheads land
 * on the shape edge. Format: `e,<tip> <start> <c1> <c2> <anchor> …` where the
 * control-point triples are collinear (so each cubic renders as a line).
 *
 * Cross-cluster and leaf-packed edges have no ELK route (rectpacking and
 * prebuilt boxes don't route them), so they fall back to a straight L-corner
 * between node centers — which may cross intervening nodes. That is the
 * accepted price of right-angle edges at any net size.
 *
 * Returns null when either endpoint has no laid-out position.
 */
function edgePosSpline(
  graph: GraphModel,
  layout: LayoutResult,
  src: string,
  dst: string,
): string | null {
  const srcPos = layout.nodePositions.get(src);
  const dstPos = layout.nodePositions.get(dst);
  const srcNode = graph.nodes.get(src);
  const dstNode = graph.nodes.get(dst);
  if (!srcPos || !dstPos || !srcNode || !dstNode) return null;

  const sc = drawnCenter(srcPos);
  const tc = drawnCenter(dstPos);
  const route = layout.edgePaths.get(`${src}->${dst}`);
  // Full orthogonal polyline. ELK's own route when available (its right-angle
  // bends AND its box-border anchor points); otherwise an L-corner between the
  // drawn centers (vertical-then-horizontal) so the edge still turns square.
  let raw: Pt[];
  if (route) {
    raw = [route.start, ...route.bends, route.end];
  } else if (sc.x === tc.x || sc.y === tc.y) {
    raw = [sc, tc];
  } else {
    raw = [sc, { x: sc.x, y: tc.y }, tc];
  }
  if (raw.length < 2) return null;

  const extS = visualExtent(srcNode);
  const extT = visualExtent(dstNode);
  // Land both ends on the visual shape boundary (with a right-angle jog when
  // ELK's approach would otherwise miss a small shape — see approachEndpoint).
  const startA = approachEndpoint(sc, extS, raw[0]!, raw[1]!);
  const endA = approachEndpoint(tc, extT, raw[raw.length - 1]!, raw[raw.length - 2]!);

  // Drawn polyline: source boundary → (jog) → ELK bends → (jog) → target
  // boundary, dropping any zero-length steps so segments stay clean.
  const poly: Pt[] = [];
  const push = (p: Pt): void => {
    const last = poly[poly.length - 1];
    if (!last || last.x !== p.x || last.y !== p.y) poly.push(p);
  };
  push(startA.entry);
  if (startA.jog) push(startA.jog);
  for (const p of raw.slice(1, -1)) push(p);
  if (endA.jog) push(endA.jog);
  push(endA.entry);
  if (poly.length < 2) return null;

  // Safety net: force every segment axis-aligned. A few ELK routes come back
  // as a single diagonal 2-point segment; insert a corner where needed,
  // oriented so the segment entering the target keeps its approach axis.
  const ortho: Pt[] = [poly[0]!];
  for (let i = 1; i < poly.length; i++) {
    const a = ortho[ortho.length - 1]!;
    const b = poly[i]!;
    if (Math.abs(b.x - a.x) > 1 && Math.abs(b.y - a.y) > 1) {
      ortho.push(i === poly.length - 1 ? { x: b.x, y: a.y } : { x: a.x, y: b.y });
    }
    ortho.push(b);
  }

  const tip = ortho[ortho.length - 1]!;
  const prev = ortho[ortho.length - 2]!;
  // Pull the drawn line back from the tip by one arrowhead length, along the
  // (axis-aligned) approach, so Graphviz draws the arrow in that gap.
  const ax = prev.x - tip.x;
  const ay = prev.y - tip.y;
  const al = Math.hypot(ax, ay) || 1;
  // Clamp the pull-back to the final segment so the arrow base never overshoots
  // past `prev` and doubles the drawn line back on itself. Short final stubs
  // (< ARROW_LEN) are realistic here — a mergeEdges branch stub or the corner an
  // approachEndpoint jog lands next to the last ELK bend can both be tiny.
  const pull = Math.min(ARROW_LEN, al);
  const arrowBase: Pt = { x: tip.x + (ax / al) * pull, y: tip.y + (ay / al) * pull };

  const anchors: Pt[] = [...ortho.slice(0, -1), arrowBase];
  let spline = fmtPt(anchors[0]!);
  for (let i = 1; i < anchors.length; i++) {
    const a = anchors[i - 1]!;
    const b = anchors[i]!;
    spline += ` ${fmtPt(lerp(a, b, 1 / 3))} ${fmtPt(lerp(a, b, 2 / 3))} ${fmtPt(b)}`;
  }
  return `e,${fmtPt(tip)} ${spline}`;
}

/**
 * Render a node's attribute list — preserving the parsed attrs (including
 * libpetri's `width`/`height`, which are the *visual* shape dimensions)
 * and adding the ELK-computed `pos` so Graphviz `nop2` can pin it.
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
  const c = drawnCenter(pos);
  attrs.push(`pos=${quote(`${c.x.toFixed(2)},${c.y.toFixed(2)}!`)}`);
  for (const [k, v] of Object.entries(node.attrs)) {
    if (k === 'pos') continue;
    attrs.push(`${k}=${quote(v)}`);
  }
  return `${node.id} [${attrs.join(', ')}];`;
}

function edgeAttrLine(
  graph: GraphModel,
  layout: LayoutResult,
  src: string,
  dst: string,
  rawAttrs: string,
): string {
  // Splice libpetri's original attrs verbatim so style/penwidth/label/color/
  // arrowhead match `DotExporter` 1:1, then add ELK's orthogonal route as a
  // `pos=` spline for Graphviz `nop2` to draw. See `edgePosSpline` for why we
  // route ourselves rather than use Graphviz's (wasm-crashing) ortho router.
  const pos = edgePosSpline(graph, layout, src, dst);
  const parts = [rawAttrs.trim(), pos ? `pos="${pos}"` : ''].filter(Boolean);
  const body = parts.join(', ');
  return `${src} -> ${dst}` + (body ? ` [${body}];` : ';');
}

/**
 * Emit a Graphviz DOT string with node positions AND edge routes pinned.
 * Render the result with `@viz-js/viz` using:
 *
 * ```ts
 * viz.renderSVGElement(dot, {
 *   engine: 'nop2',
 *   yInvert: true,
 * });
 * ```
 *
 * `engine: 'nop2'` honours the pinned `pos=` on every node AND the `pos=`
 * spline on every edge, drawing both verbatim with no layout or routing. We
 * supply ELK's own orthogonal edge routes (clipped to the visual node
 * boundary for correct arrowheads — see {@link edgePosSpline}). This replaces
 * the former `nop`/`nop1` mode, where Graphviz routed edges itself: that gave
 * curved (not right-angle) edges, and switching it to `splines=ortho` crashed
 * the wasm on large nets (Graphviz's ortho maze allocator overruns the wasm
 * heap). Routing ourselves gives right angles on a net of any size, no crash.
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

  // Edges — libpetri's original styling attrs plus ELK's orthogonal route as
  // a `pos=` spline, drawn verbatim by Graphviz `nop2`.
  for (const edge of graph.edges) {
    lines.push('    ' + edgeAttrLine(graph, layout, edge.src, edge.dst, edge.rawAttrs));
  }

  lines.push('}');
  return lines.join('\n');
}
