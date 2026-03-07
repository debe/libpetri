/**
 * Maps a PetriNet definition to a format-agnostic Graph.
 *
 * This is where all the Petri net semantics live. The mapper understands
 * places, transitions, arcs, timing, and priority. It produces a Graph
 * that can be rendered to DOT (or any other format) without Petri net knowledge.
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

  // Edges
  for (const t of net.transitions) {
    const tid = 't_' + sanitize(t.name);

    // Input arcs from inputSpecs
    for (const spec of t.inputSpecs) {
      const pid = 'p_' + sanitize(spec.place.name);
      const inputStyle = edgeStyle('input');
      let label: string | undefined;
      switch (spec.type) {
        case 'exactly':
          label = `\u00d7${spec.count}`;
          break;
        case 'all':
          label = '*';
          break;
        case 'at-least':
          label = `\u2265${spec.minimum}`;
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

    // Output arcs from outputSpec
    if (t.outputSpec !== null) {
      edges.push(...outputEdges(tid, t.outputSpec, null));
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

    // Reset arcs (only those without matching output)
    const outputPlaceNames = t.outputSpec !== null
      ? new Set([...t.outputPlaces()].map(p => p.name))
      : new Set<string>();
    for (const rst of t.resets) {
      if (!outputPlaceNames.has(rst.place.name)) {
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
    const max = hasDeadline(t.timing) ? String(l) : '\u221e';
    parts.push(`[${e}, ${max}]ms`);
  }

  if (config.showPriority && t.priority !== 0) {
    parts.push(`prio=${t.priority}`);
  }

  return parts.join(' ');
}

function outputEdges(transitionId: string, out: Out, branchLabel: string | null): GraphEdge[] {
  const outStyle = edgeStyle('output');

  switch (out.type) {
    case 'place': {
      const pid = 'p_' + sanitize(out.place.name);
      return [{
        from: transitionId,
        to: pid,
        label: branchLabel ?? undefined,
        color: outStyle.color,
        style: outStyle.style,
        arrowhead: outStyle.arrowhead,
        arcType: 'output',
      }];
    }

    case 'forward-input': {
      const pid = 'p_' + sanitize(out.to.name);
      const label = (branchLabel ? branchLabel + ' ' : '') + '\u27f5' + out.from.name;
      return [{
        from: transitionId,
        to: pid,
        label,
        color: outStyle.color,
        style: 'dashed' as const,
        arrowhead: outStyle.arrowhead,
        arcType: 'output',
      }];
    }

    case 'and':
      return out.children.flatMap(c => outputEdges(transitionId, c, branchLabel));

    case 'xor': {
      const edges: GraphEdge[] = [];
      for (const child of out.children) {
        const label = inferBranchLabel(child);
        edges.push(...outputEdges(transitionId, child, label));
      }
      return edges;
    }

    case 'timeout':
      return outputEdges(transitionId, out.child, `\u23f1${out.afterMs}ms`);
  }
}

function inferBranchLabel(out: Out): string | null {
  switch (out.type) {
    case 'place': return out.place.name;
    case 'timeout': return `\u23f1${out.afterMs}ms`;
    case 'forward-input': return out.to.name;
    case 'and':
    case 'xor':
      return null;
  }
}
