/**
 * Diagram export for Petri nets.
 *
 * Generates Mermaid flowchart syntax from a PetriNet definition, with configurable
 * direction, styling, and place/transition rendering.
 *
 * @module export
 */
export type { MermaidConfig, Direction } from './mermaid-exporter.js';
export {
  mermaidExport, sanitize,
  DEFAULT_CONFIG, minimalConfig, leftToRightConfig,
} from './mermaid-exporter.js';
