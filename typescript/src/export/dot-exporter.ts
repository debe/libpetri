/**
 * Convenience function for exporting a PetriNet to DOT format.
 *
 * @module export/dot-exporter
 */

import type { PetriNet } from '../core/petri-net.js';
import type { DotConfig } from './petri-net-mapper.js';
import { mapToGraph } from './petri-net-mapper.js';
import { renderDot } from './dot-renderer.js';

/**
 * Exports a PetriNet to DOT (Graphviz) format.
 *
 * @param net the Petri net to export
 * @param config optional export configuration
 * @returns DOT string suitable for rendering with Graphviz
 */
export function dotExport(net: PetriNet, config?: DotConfig): string {
  return renderDot(mapToGraph(net, config));
}
