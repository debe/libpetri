/**
 * Maps a PetriNet definition to a format-agnostic Graph.
 *
 * Petri net semantics live here. The mapper applies the visualization rules
 * specified in spec/09-export.md (EXP-012, EXP-013, EXP-014):
 *
 * - XOR / AND output groups with ≥2 children become synthetic junction nodes
 *   (diamond for XOR, square for AND).
 * - Output + reset arcs to the same place collapse into a single edge styled
 *   as the reset-output category and labelled "reset+out".
 * - Junction IDs use the form j_<transition>__<kind>_<idx>, where idx is a
 *   depth-first pre-order counter starting at 0.
 *
 * @module export/petri-net-mapper
 */

import type { PetriNet } from '../core/petri-net.js';
import type { Transition } from '../core/transition.js';
import type { Out } from '../core/out.js';
import { earliest, latest, hasDeadline } from '../core/timing.js';
import type { Graph, GraphNode, GraphEdge, RankDir } from './graph.js';
import { nodeStyle, edgeStyle, FONT, GRAPH } from './styles.js';
import type { NodeCategory } from './styles.js';

// ======================== Configuration ========================

export interface DotConfig {
  readonly direction: RankDir;
  readonly showTypes: boolean;
  readonly showIntervals: boolean;
  readonly showPriority: boolean;
  readonly environmentPlaces?: ReadonlySet<string>;
}

export const DEFAULT_DOT_CONFIG: DotConfig = {
  direction: 'TB',
  showTypes: true,
  showIntervals: true,
  showPriority: true,
};

// ======================== Public API ========================

/** Sanitizes a name for use as a graph node ID. */
export function sanitize(name: string): string {
  return name.replace(/[^a-zA-Z0-9_]/g, '_');
}

/** Maps a PetriNet to a format-agnostic Graph. */
export function mapToGraph(net: PetriNet, config: DotConfig = DEFAULT_DOT_CONFIG): Graph {
  const places = analyzePlaces(net);
  const envNames = config.environmentPlaces ?? new Set<string>();

  const nodes: GraphNode[] = [];
  const edges: GraphEdge[] = [];

  // Place nodes
  for (const [name, info] of places) {
    const category = placeCategory(info, envNames.has(name));
    const style = nodeStyle(category);
    nodes.push({
      id: 'p_' + sanitize(name),
      label: '',
      shape: style.shape,
      fill: style.fill,
      stroke: style.stroke,
      penwidth: style.penwidth,
      semanticId: name,
      style: style.style,
      width: style.width,
      attrs: { xlabel: name, fixedsize: 'true' },
    });
  }

  // Transition nodes
  for (const t of net.transitions) {
    const style = nodeStyle('transition');
    nodes.push({
      id: 't_' + sanitize(t.name),
      label: transitionLabel(t, config),
      shape: style.shape,
      fill: style.fill,
      stroke: style.stroke,
      penwidth: style.penwidth,
      semanticId: t.name,
      height: style.height,
      width: style.width,
    });
  }

  // Edges (and junction nodes)
  for (const t of net.transitions) {
    const tid = 't_' + sanitize(t.name);
    const tSanitized = sanitize(t.name);
    const resetPlaces = new Set(t.resets.map(r => r.place.name));
    const combined = new Set<string>();

    // Input arcs from inputSpecs
    for (const spec of t.inputSpecs) {
      const pid = 'p_' + sanitize(spec.place.name);
      const inputStyle = edgeStyle('input');
      let label: string | undefined;
      switch (spec.type) {
        case 'exactly':
          label = `×${spec.count}`;
          break;
        case 'all':
          label = '*';
          break;
        case 'at-least':
          label = `≥${spec.minimum}`;
          break;
      }
      edges.push({
        from: pid,
        to: tid,
        label,
        color: inputStyle.color,
        style: inputStyle.style,
        arrowhead: inputStyle.arrowhead,
        arcType: 'input',
      });
    }

    // Output arcs from outputSpec — emits junction nodes + edges, marks combined places.
    if (t.outputSpec !== null) {
      const ctx: EmitCtx = {
        tSanitized,
        resetPlaces,
        combined,
        nodes,
        edges,
        counter: 0,
      };
      emitOutput(t.outputSpec, tid, null, ctx);
    }

    // Inhibitor arcs
    for (const inh of t.inhibitors) {
      const pid = 'p_' + sanitize(inh.place.name);
      const inhStyle = edgeStyle('inhibitor');
      edges.push({
        from: pid,
        to: tid,
        color: inhStyle.color,
        style: inhStyle.style,
        arrowhead: inhStyle.arrowhead,
        arcType: 'inhibitor',
      });
    }

    // Read arcs
    for (const r of t.reads) {
      const pid = 'p_' + sanitize(r.place.name);
      const readStyle = edgeStyle('read');
      edges.push({
        from: pid,
        to: tid,
        label: 'read',
        color: readStyle.color,
        style: readStyle.style,
        arrowhead: readStyle.arrowhead,
        arcType: 'read',
      });
    }

    // Standalone reset arcs (only those not already combined with an output)
    for (const rst of t.resets) {
      if (!combined.has(rst.place.name)) {
        const pid = 'p_' + sanitize(rst.place.name);
        const resetStyle = edgeStyle('reset');
        edges.push({
          from: tid,
          to: pid,
          label: 'reset',
          color: resetStyle.color,
          style: resetStyle.style,
          arrowhead: resetStyle.arrowhead,
          penwidth: resetStyle.penwidth,
          arcType: 'reset',
        });
      }
    }
  }

  return {
    id: sanitize(net.name),
    rankdir: config.direction,
    nodes,
    edges,
    subgraphs: [],
    graphAttrs: {
      nodesep: String(GRAPH.nodesep),
      ranksep: String(GRAPH.ranksep),
      forcelabels: String(GRAPH.forcelabels),
      overlap: String(GRAPH.overlap),
      fontname: FONT.family,
      outputorder: GRAPH.outputorder,
    },
    nodeDefaults: {
      fontname: FONT.family,
      fontsize: String(FONT.nodeSize),
    },
    edgeDefaults: {
      fontname: FONT.family,
      fontsize: String(FONT.edgeSize),
    },
  };
}

// ======================== Place Analysis ========================

interface PlaceInfo {
  hasIncoming: boolean;
  hasOutgoing: boolean;
}

function analyzePlaces(net: PetriNet): Map<string, PlaceInfo> {
  const map = new Map<string, PlaceInfo>();

  function ensure(name: string): PlaceInfo {
    let info = map.get(name);
    if (!info) {
      info = { hasIncoming: false, hasOutgoing: false };
      map.set(name, info);
    }
    return info;
  }

  for (const t of net.transitions) {
    for (const spec of t.inputSpecs) {
      ensure(spec.place.name).hasOutgoing = true;
    }
    if (t.outputSpec !== null) {
      for (const p of t.outputPlaces()) {
        ensure(p.name).hasIncoming = true;
      }
    }
    for (const inh of t.inhibitors) {
      ensure(inh.place.name);
    }
    for (const r of t.reads) {
      ensure(r.place.name).hasOutgoing = true;
    }
    for (const rst of t.resets) {
      ensure(rst.place.name);
    }
  }

  return map;
}

function placeCategory(info: PlaceInfo, isEnvironment: boolean): NodeCategory {
  if (isEnvironment) return 'environment';
  if (!info.hasIncoming) return 'start';
  if (!info.hasOutgoing) return 'end';
  return 'place';
}

// ======================== Helpers ========================

function transitionLabel(t: Transition, config: DotConfig): string {
  const parts = [t.name];

  if (config.showIntervals) {
    const e = earliest(t.timing);
    const l = latest(t.timing);
    const max = hasDeadline(t.timing) ? String(l) : '∞';
    parts.push(`[${e}, ${max}]ms`);
  }

  if (config.showPriority && t.priority !== 0) {
    parts.push(`prio=${t.priority}`);
  }

  return parts.join(' ');
}

/**
 * Mutable per-transition state threaded through the recursive Out-tree walk.
 *
 * `counter` starts at 0 and increments once per emitted junction (depth-first
 * pre-order). `combined` accumulates place names where a reset+output combination
 * short-circuited the standalone reset edge.
 */
interface EmitCtx {
  readonly tSanitized: string;
  readonly resetPlaces: ReadonlySet<string>;
  readonly combined: Set<string>;
  readonly nodes: GraphNode[];
  readonly edges: GraphEdge[];
  counter: number;
}

/**
 * Emits output edges for an Out tree, inserting junction nodes for XOR/AND
 * groups with ≥2 children. Combined reset+output edges replace plain output
 * edges when a leaf place is also in `ctx.resetPlaces`.
 *
 * @param out          current Out subtree
 * @param parentId     id of the parent node (transition or junction)
 * @param branchLabel  label to apply to the edge entering this Out (timeout/XOR-branch label)
 * @param ctx          per-transition junction context (counter, reset set, accumulators)
 */
function emitOutput(out: Out, parentId: string, branchLabel: string | null, ctx: EmitCtx): void {
  switch (out.type) {
    case 'one': {
      const pid = 'p_' + sanitize(out.place.name);
      pushLeafEdge(parentId, pid, out.place.name, branchLabel, ctx, false);
      return;
    }

    case 'exactly': {
      const pid = 'p_' + sanitize(out.place.name);
      const label = (branchLabel ? branchLabel + ' ' : '') + `×${out.count}`;
      pushLeafEdge(parentId, pid, out.place.name, label, ctx, false);
      return;
    }

    case 'forward-input': {
      const pid = 'p_' + sanitize(out.to.name);
      const fwdLabel = (branchLabel ? branchLabel + ' ' : '') + '⟵' + out.from.name;
      // ForwardInput is dashed; reset+out combination overrides if applicable.
      pushLeafEdge(parentId, pid, out.to.name, fwdLabel, ctx, true);
      return;
    }

    case 'and':
    case 'xor': {
      // Single-child groups collapse: pass through.
      if (out.children.length < 2) {
        if (out.children.length === 1) {
          emitOutput(out.children[0]!, parentId, branchLabel, ctx);
        }
        return;
      }

      // Insert junction node — diamond gateway with heavy ✕ / ✚ glyph as discriminator.
      const kind = out.type;
      const idx = ctx.counter++;
      const junctionId = `j_${ctx.tSanitized}__${kind}_${idx}`;
      const category: NodeCategory = kind === 'xor' ? 'xor-junction' : 'and-junction';
      const jStyle = nodeStyle(category);
      ctx.nodes.push({
        id: junctionId,
        label: kind === 'xor' ? '✕' : '✚',
        shape: jStyle.shape,
        fill: jStyle.fill,
        stroke: jStyle.stroke,
        penwidth: jStyle.penwidth,
        semanticId: junctionId,
        height: jStyle.height,
        width: jStyle.width,
        attrs: { fixedsize: 'true', fontsize: '14' },
      });

      // Edge parent → junction (carries any inherited branch/timeout label).
      const outStyle = edgeStyle('output');
      ctx.edges.push({
        from: parentId,
        to: junctionId,
        label: branchLabel ?? undefined,
        color: outStyle.color,
        style: outStyle.style,
        arrowhead: outStyle.arrowhead,
        arcType: 'output',
      });

      // Recurse children: XOR junction propagates per-branch labels; AND junction does not.
      for (const child of out.children) {
        const childLabel = kind === 'xor' ? inferBranchLabel(child) : null;
        emitOutput(child, junctionId, childLabel, ctx);
      }
      return;
    }

    case 'timeout': {
      // Override any inherited branchLabel: the timeout label fully describes
      // this branch (the XOR pre-inference resolves to the same string).
      const timeoutLabel = `⏱${out.afterMs}ms`;
      emitOutput(out.child, parentId, timeoutLabel, ctx);
      return;
    }
  }
}

function pushLeafEdge(
  fromId: string,
  toId: string,
  placeName: string,
  branchLabel: string | null,
  ctx: EmitCtx,
  isForwardInput: boolean,
): void {
  if (ctx.resetPlaces.has(placeName)) {
    ctx.combined.add(placeName);
    const ro = edgeStyle('reset-output');
    ctx.edges.push({
      from: fromId,
      to: toId,
      label: 'reset+out',
      color: ro.color,
      style: ro.style,
      arrowhead: ro.arrowhead,
      penwidth: ro.penwidth,
      arcType: 'reset-output',
    });
    return;
  }

  const out = edgeStyle('output');
  ctx.edges.push({
    from: fromId,
    to: toId,
    label: branchLabel ?? undefined,
    color: out.color,
    style: isForwardInput ? 'dashed' : out.style,
    arrowhead: out.arrowhead,
    arcType: 'output',
  });
}

function inferBranchLabel(out: Out): string | null {
  switch (out.type) {
    case 'one': return out.place.name;
    case 'exactly': return `${out.place.name}\u00d7${out.count}`;
    case 'timeout': return `\u23f1${out.afterMs}ms`;
    case 'forward-input': return out.to.name;
    case 'and':
    case 'xor':
      return null;
  }
}
