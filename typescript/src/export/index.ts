/**
 * Diagram export for Petri nets.
 *
 * Provides DOT (Graphviz) export with proper Petri net visual conventions, and
 * a layered architecture with reusable typed graph primitives.
 *
 * @module export
 */

export type { Graph, GraphNode, GraphEdge, Subgraph, RankDir, NodeShape, EdgeLineStyle, ArrowHead } from './graph.js';
export type { NodeVisual, EdgeVisual, NodeCategory, EdgeCategory } from './styles.js';
export { nodeStyle, edgeStyle, FONT, GRAPH } from './styles.js';
export type { DotConfig } from './petri-net-mapper.js';
export { mapToGraph, sanitize, DEFAULT_DOT_CONFIG } from './petri-net-mapper.js';
export { renderDot } from './dot-renderer.js';
export { dotExport } from './dot-exporter.js';
