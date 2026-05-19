/**
 * Format-agnostic typed graph model.
 *
 * Consumed by both the DOT renderer and the animation layer. Nodes carry a
 * `semanticId` that maps back to `Place.name` / `Transition.name` — the stable
 * bridge for animation targeting.
 *
 * ID convention: places get `p_` prefix, transitions get `t_` prefix.
 *
 * @module export/graph
 */

// ======================== Enums / Unions ========================

export type RankDir = 'TB' | 'BT' | 'LR' | 'RL';

export type NodeShape = 'circle' | 'doublecircle' | 'box' | 'diamond' | 'ellipse' | 'record';

export type EdgeLineStyle = 'solid' | 'dashed' | 'bold' | 'invis';

export type ArrowHead = 'normal' | 'odot' | 'none' | 'diamond' | 'dot';

// ======================== Nodes ========================

export interface GraphNode {
  readonly id: string;
  readonly label: string;
  readonly shape: NodeShape;
  readonly fill: string;
  readonly stroke: string;
  readonly penwidth: number;
  /** Maps back to Place.name or Transition.name for animation targeting. */
  readonly semanticId: string;
  readonly style?: string;
  readonly height?: number;
  readonly width?: number;
  readonly attrs?: Readonly<Record<string, string>>;
}

// ======================== Edges ========================

export interface GraphEdge {
  readonly from: string;
  readonly to: string;
  readonly label?: string;
  readonly color: string;
  readonly style: EdgeLineStyle;
  readonly arrowhead: ArrowHead;
  readonly penwidth?: number;
  /** The arc type that produced this edge (for semantic queries). */
  readonly arcType: 'input' | 'output' | 'inhibitor' | 'read' | 'reset' | 'reset-output' | 'ghost';
  readonly attrs?: Readonly<Record<string, string>>;
}

// ======================== Subgraph ========================

/**
 * A subgraph (cluster) in the graph.
 *
 * Subgraphs may nest arbitrarily via {@link subgraphs} to model nested subnet
 * instance prefixes per {@code spec/11-modular-composition.md} **MOD-040** and
 * {@code spec/09-export.md} **EXP-016**. Edges whose endpoints both live
 * inside the same cluster are placed inside that cluster via {@link edges} so
 * Graphviz routes them correctly. Cross-cluster (or fully top-level) edges
 * live on the parent {@link Graph#edges} list.
 */
export interface Subgraph {
  readonly id: string;
  readonly label?: string;
  readonly nodes: readonly GraphNode[];
  /** Edges whose source and target both live inside this subgraph. */
  readonly edges?: readonly GraphEdge[];
  /** Nested child subgraphs (deeper instance prefixes). */
  readonly subgraphs?: readonly Subgraph[];
  readonly attrs?: Readonly<Record<string, string>>;
}

// ======================== Graph ========================

export interface Graph {
  readonly id: string;
  readonly rankdir: RankDir;
  readonly nodes: readonly GraphNode[];
  readonly edges: readonly GraphEdge[];
  readonly subgraphs: readonly Subgraph[];
  readonly graphAttrs: Readonly<Record<string, string>>;
  readonly nodeDefaults: Readonly<Record<string, string>>;
  readonly edgeDefaults: Readonly<Record<string, string>>;
}
