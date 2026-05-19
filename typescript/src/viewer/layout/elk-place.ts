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
 * The two functions are pure: `elkLayout` takes only the graph; `writeBack`
 * takes (graph, layout). Neither touches the original DOT text — the model
 * after replication has nodes the original DOT doesn't, so patching the
 * original would be incorrect.
 *
 * @module viewer/layout/elk-place
 */

import ELK from 'elkjs/lib/elk.bundled.js';
import type {
  ElkExtendedEdge,
  ElkNode,
} from 'elkjs/lib/elk-api.js';
import type { GraphModel, ParsedNode } from './preprocess.js';

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
 */
export async function elkLayout(graph: GraphModel): Promise<LayoutResult> {
  const { byCluster, cross, edgeIdToKey } = partitionEdges(graph);

  const elkChildren: ElkNode[] = [];
  for (const [clusterId, cluster] of graph.clusters) {
    elkChildren.push({
      id: clusterId,
      layoutOptions: CLUSTER_OPTIONS,
      children: cluster.nodes
        .map(id => graph.nodes.get(id))
        .filter((n): n is ParsedNode => n !== undefined)
        .map(n => ({ id: n.id, ...nodeDims(n) })),
      edges: byCluster.get(clusterId) ?? [],
    });
  }
  // Synthetic orchestrator cluster holds the remaining orphans
  elkChildren.push({
    id: ORCHESTRATOR_CLUSTER_ID,
    layoutOptions: ORCHESTRATOR_OPTIONS,
    children: graph.orphans
      .map(id => graph.nodes.get(id))
      .filter((n): n is ParsedNode => n !== undefined)
      .map(n => ({ id: n.id, ...nodeDims(n) })),
    edges: byCluster.get(ORCHESTRATOR_CLUSTER_ID) ?? [],
  });

  const elk = new ELK();
  const rootGraph: ElkNode = {
    id: 'root',
    layoutOptions: ROOT_OPTIONS,
    children: elkChildren,
    edges: cross,
  };
  const layout: ElkNode = await elk.layout(rootGraph);

  const nodePositions = new Map<string, NodePosition>();
  const clusterBoxes = new Map<string, ClusterBox>();
  const edgePaths = new Map<string, EdgePath>();

  const walk = (node: ElkNode, parentX: number, parentY: number): void => {
    const ax = parentX + (node.x ?? 0);
    const ay = parentY + (node.y ?? 0);
    const isCluster = node.id !== 'root' && (node.children?.length ?? 0) > 0;
    if (isCluster) {
      clusterBoxes.set(node.id, {
        x: ax, y: ay,
        width: node.width ?? 0,
        height: node.height ?? 0,
      });
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
