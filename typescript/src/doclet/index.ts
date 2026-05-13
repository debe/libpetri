/**
 * TypeDoc plugin for compile-time Petri net visualization.
 *
 * Generates interactive DOT/SVG diagrams from `PetriNet`, `SubnetDef`, and
 * `Instance` definitions and embeds them directly in TypeDoc output with
 * pan/zoom/fullscreen + cluster collapse/expand support.
 *
 * ## Usage
 *
 * Add to `typedoc.json`:
 * ```json
 * { "plugin": ["libpetri/doclet"] }
 * ```
 *
 * Then annotate exports with `@petrinet` (full body) or `@subnet`
 * (interface-only):
 * ```typescript
 * /**
 *  * Order processing workflow.
 *  *
 *  * @petrinet ./definition#STRUCTURE
 *  *{@literal /}
 *
 * /**
 *  * Wraps a {@subnet ./definition#BOUNDED_BUFFER} for back-pressure.
 *  *{@literal /}
 * ```
 *
 * ## Tag format
 *
 * ```
 * @petrinet ./path/to/module#exportName      — access a static export
 * @petrinet ./path/to/module#functionName()  — call a function returning one
 * @petrinet #localExport                     — resolve from same file
 *
 * @subnet ./path/to/module#SUBNET_DEF        — interface-only inline diagram
 * ```
 *
 * Mirrors: `org.libpetri.doclet` (Java)
 *
 * @module doclet
 */

export { load } from './petri-net-plugin.js';
export { renderSvg, renderSubnetSvg, escapeHtml } from './diagram-renderer.js';
export { dotToSvg } from './svg-renderer.js';
export { resolveNet, type ResolvedNet } from './net-resolver.js';
export { forSubnetDef, forInstance } from './subnet-header.js';
export { fullBody as subnetFullBody, interfaceOnly as subnetInterfaceOnly } from './subnet-dot-export.js';
