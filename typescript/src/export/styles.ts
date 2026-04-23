// GENERATED from spec/petri-net-styles.json — do not edit manually.
// Regenerate with: scripts/generate-styles.sh

/**
 * Style loader for Petri net visualization.
 *
 * Reads the shared style definition from `spec/petri-net-styles.json` and
 * exposes typed accessors for node and edge visual properties.
 *
 * @module export/styles
 */

import type { NodeShape, EdgeLineStyle, ArrowHead } from './graph.js';

// ======================== Style Types ========================

export interface NodeVisual {
  readonly shape: NodeShape;
  readonly fill: string;
  readonly stroke: string;
  readonly penwidth: number;
  readonly style?: string;
  readonly height?: number;
  readonly width?: number;
}

export interface EdgeVisual {
  readonly color: string;
  readonly style: EdgeLineStyle;
  readonly arrowhead: ArrowHead;
  readonly penwidth?: number;
}

export interface FontStyle {
  readonly family: string;
  readonly nodeSize: number;
  readonly edgeSize: number;
}

export interface GraphStyle {
  readonly nodesep: number;
  readonly ranksep: number;
  readonly forcelabels: boolean;
  readonly overlap: boolean;
  readonly outputorder: string;
}

// ======================== Inline Style Data ========================

// Inlined from spec/petri-net-styles.json to avoid runtime JSON import issues.
// Keep in sync with the spec file.

const NODE_STYLES: Record<NodeCategory, NodeVisual> = {
  place:        { shape: 'circle',  fill: '#FFFFFF', stroke: '#333333', penwidth: 1.5, width: 0.35 },
  start:        { shape: 'circle',  fill: '#d4edda', stroke: '#28a745', penwidth: 2.0, width: 0.35 },
  end:          { shape: 'doublecircle',  fill: '#cce5ff', stroke: '#004085', penwidth: 2.0, width: 0.35 },
  environment:  { shape: 'circle',  fill: '#f8d7da', stroke: '#721c24', penwidth: 2.0, style: 'dashed', width: 0.35 },
  transition:   { shape: 'box',  fill: '#fff3cd', stroke: '#856404', penwidth: 1.0, height: 0.4, width: 0.8 },
};

const EDGE_STYLES: Record<EdgeCategory, EdgeVisual> = {
  input:     { color: '#333333', style: 'solid',  arrowhead: 'normal' },
  output:    { color: '#333333', style: 'solid',  arrowhead: 'normal' },
  inhibitor: { color: '#dc3545', style: 'solid',  arrowhead: 'odot' },
  read:      { color: '#6c757d', style: 'dashed',  arrowhead: 'normal' },
  reset:     { color: '#fd7e14', style: 'bold',  arrowhead: 'normal',  penwidth: 2.0 },
};

export const FONT: FontStyle = { family: 'Helvetica,Arial,sans-serif', nodeSize: 12, edgeSize: 10 };

export const GRAPH: GraphStyle = { nodesep: 0.5, ranksep: 0.75, forcelabels: true, overlap: false, outputorder: 'edgesfirst' };

// ======================== Public API ========================

export type NodeCategory = 'place' | 'start' | 'end' | 'environment' | 'transition';
export type EdgeCategory = 'input' | 'output' | 'inhibitor' | 'read' | 'reset';

/** Returns the visual style for the given node category. */
export function nodeStyle(category: NodeCategory): NodeVisual {
  return NODE_STYLES[category];
}

/** Returns the visual style for the given edge/arc type. */
export function edgeStyle(arcType: EdgeCategory): EdgeVisual {
  return EDGE_STYLES[arcType];
}
