import type { PetriNet } from '../core/petri-net.js';
import type { Transition } from '../core/transition.js';
import type { Out } from '../core/out.js';
import { earliest, latest, hasDeadline } from '../core/timing.js';

// ======================== Configuration ========================

export type Direction = 'TB' | 'BT' | 'LR' | 'RL';

export interface MermaidConfig {
  readonly direction: Direction;
  readonly showTypes: boolean;
  readonly showIntervals: boolean;
  readonly showPriority: boolean;
}

export const DEFAULT_CONFIG: MermaidConfig = {
  direction: 'TB',
  showTypes: true,
  showIntervals: true,
  showPriority: true,
};

export function minimalConfig(): MermaidConfig {
  return { direction: 'TB', showTypes: false, showIntervals: false, showPriority: false };
}

export function leftToRightConfig(): MermaidConfig {
  return { direction: 'LR', showTypes: true, showIntervals: true, showPriority: true };
}

// ======================== Sanitization ========================

/** Sanitizes a name for use as a Mermaid node ID. */
export function sanitize(name: string): string {
  return name.replace(/[^a-zA-Z0-9_]/g, '_');
}

function transitionId(t: Transition): string {
  return 't_' + sanitize(t.name);
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
  }

  return map;
}

// ======================== Export ========================

/**
 * Exports a PetriNet to Mermaid flowchart syntax.
 */
export function mermaidExport(net: PetriNet, config: MermaidConfig = DEFAULT_CONFIG): string {
  const places = analyzePlaces(net);
  const lines: string[] = [];

  // YAML front-matter for ELK layout
  lines.push('---');
  lines.push('config:');
  lines.push('  layout: elk');
  lines.push('---');
  lines.push(`flowchart ${config.direction}`);
  lines.push('');

  // Place nodes (stadium shape)
  for (const [name] of places) {
    // Type annotations for places not yet implemented
    const label = name;
    lines.push(`    ${sanitize(name)}(["${label}"])`);
  }
  lines.push('');

  // Transition nodes (rectangle)
  for (const t of net.transitions) {
    lines.push(`    ${transitionId(t)}["${transitionLabel(t, config)}"]`);
  }
  lines.push('');

  // Edges
  for (const t of net.transitions) {
    const tid = transitionId(t);

    // Input arcs from inputSpecs
    for (const spec of t.inputSpecs) {
      const pid = sanitize(spec.place.name);
      switch (spec.type) {
        case 'one':
          lines.push(`    ${pid} --> ${tid}`);
          break;
        case 'exactly':
          lines.push(`    ${pid} -->|×${spec.count}| ${tid}`);
          break;
        case 'all':
          lines.push(`    ${pid} -->|*| ${tid}`);
          break;
        case 'at-least':
          lines.push(`    ${pid} -->|≥${spec.minimum}| ${tid}`);
          break;
      }
    }

    // Output arcs from outputSpec
    if (t.outputSpec !== null) {
      for (const edge of outputEdges(tid, t.outputSpec, null)) {
        lines.push(`    ${edge}`);
      }
    }

    // Inhibitor arcs
    for (const inh of t.inhibitors) {
      lines.push(`    ${sanitize(inh.place.name)} --o ${tid}`);
    }

    // Read arcs
    for (const r of t.reads) {
      lines.push(`    ${sanitize(r.place.name)} -.->|read| ${tid}`);
    }

    // Reset arcs (only those without matching output)
    const outputPlaceNames = t.outputSpec !== null
      ? new Set([...t.outputPlaces()].map(p => p.name))
      : new Set<string>();
    for (const rst of t.resets) {
      if (!outputPlaceNames.has(rst.place.name)) {
        lines.push(`    ${tid} ==>|reset| ${sanitize(rst.place.name)}`);
      }
    }
  }
  lines.push('');

  // Styles
  const startIds: string[] = [];
  const endIds: string[] = [];
  const transIds: string[] = [];
  const xorTransIds: string[] = [];

  for (const [name, info] of places) {
    if (!info.hasIncoming) startIds.push(sanitize(name));
    if (!info.hasOutgoing) endIds.push(sanitize(name));
  }
  for (const t of net.transitions) {
    transIds.push(transitionId(t));
    if (t.outputSpec?.type === 'xor') {
      xorTransIds.push(transitionId(t));
    }
  }

  const hasStyles = startIds.length > 0 || endIds.length > 0 || transIds.length > 0;
  if (hasStyles) {
    lines.push('    %% Styles');
    if (startIds.length > 0) {
      lines.push('    classDef startPlace fill:#d4edda,stroke:#28a745,stroke-width:2px');
      lines.push(`    class ${startIds.join(',')} startPlace`);
    }
    if (endIds.length > 0) {
      lines.push('    classDef endPlace fill:#cce5ff,stroke:#004085,stroke-width:2px');
      lines.push(`    class ${endIds.join(',')} endPlace`);
    }
    if (transIds.length > 0) {
      lines.push('    classDef transition fill:#fff3cd,stroke:#856404,stroke-width:1px');
      lines.push(`    class ${transIds.join(',')} transition`);
    }
    if (xorTransIds.length > 0) {
      lines.push('    classDef xorTransition fill:#ffe6cc,stroke:#d79b00,stroke-width:2px');
      lines.push(`    class ${xorTransIds.join(',')} xorTransition`);
    }
  }

  return lines.join('\n');
}

// ======================== Helpers ========================

function transitionLabel(t: Transition, config: MermaidConfig): string {
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

function outputEdges(transitionId: string, out: Out, branchLabel: string | null): string[] {
  switch (out.type) {
    case 'place': {
      const pid = sanitize(out.place.name);
      return branchLabel !== null
        ? [`${transitionId} -->|${branchLabel}| ${pid}`]
        : [`${transitionId} --> ${pid}`];
    }

    case 'forward-input': {
      const pid = sanitize(out.to.name);
      const label = (branchLabel ? branchLabel + ' ' : '') + '⟵' + out.from.name;
      return [`${transitionId} -.->|${label}| ${pid}`];
    }

    case 'and':
      return out.children.flatMap(c => outputEdges(transitionId, c, branchLabel));

    case 'xor': {
      const edges: string[] = [];
      for (const child of out.children) {
        const label = inferBranchLabel(child);
        edges.push(...outputEdges(transitionId, child, label));
      }
      return edges;
    }

    case 'timeout':
      return outputEdges(transitionId, out.child, `⏱${out.afterMs}ms`);
  }
}

function inferBranchLabel(out: Out): string | null {
  switch (out.type) {
    case 'place': return out.place.name;
    case 'timeout': return `⏱${out.afterMs}ms`;
    case 'forward-input': return out.to.name;
    case 'and':
    case 'xor':
      return null;
  }
}
