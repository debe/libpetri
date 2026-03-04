/**
 * TypeDoc plugin for compile-time Petri net visualization.
 *
 * Generates interactive DOT/SVG diagrams from PetriNet definitions
 * and embeds them directly in TypeDoc output with pan/zoom/fullscreen support.
 *
 * ## Usage
 *
 * Add to `typedoc.json`:
 * ```json
 * { "plugin": ["libpetri/doclet"] }
 * ```
 *
 * Then annotate exports with `@petrinet`:
 * ```typescript
 * /**
 *  * Order processing workflow.
 *  *
 *  * @petrinet ./definition#STRUCTURE
 *  *{@literal /}
 * ```
 *
 * ## Tag format
 *
 * ```
 * @petrinet ./path/to/module#exportName      — access a PetriNet constant
 * @petrinet ./path/to/module#functionName()  — call a function returning PetriNet
 * @petrinet #localExport                     — resolve from same file
 * ```
 *
 * Mirrors: `org.libpetri.doclet` (Java)
 *
 * @module doclet
 */

export { load } from './petri-net-plugin.js';
export { renderSvg, escapeHtml } from './diagram-renderer.js';
export { dotToSvg } from './svg-renderer.js';
export { resolveNet, type ResolvedNet } from './net-resolver.js';
