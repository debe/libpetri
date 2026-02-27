/**
 * Diagram export for Petri nets.
 *
 * Provides DOT (Graphviz) export with proper Petri net visual conventions, and
 * a layered architecture with reusable typed graph primitives. Mermaid export
 * is retained for backward compatibility.
 *
 * @module export
 */

// DOT export (primary)
export type { Graph, GraphNode, GraphEdge, Subgraph, RankDir, NodeShape, EdgeLineStyle, ArrowHead } from './graph.js';
export type { NodeVisual, EdgeVisual, NodeCategory, EdgeCategory } from './styles.js';
export { nodeStyle, edgeStyle, FONT, GRAPH } from './styles.js';
export type { DotConfig } from './petri-net-mapper.js';
export { mapToGraph, sanitize, DEFAULT_DOT_CONFIG } from './petri-net-mapper.js';
export { renderDot } from './dot-renderer.js';
export { dotExport } from './dot-exporter.js';

// Mermaid export (deprecated — use dotExport instead)
export type { MermaidConfig, Direction } from './mermaid-exporter.js';
export {
  mermaidExport,
  sanitize as mermaidSanitize,
  DEFAULT_CONFIG, minimalConfig, leftToRightConfig,
} from './mermaid-exporter.js';
