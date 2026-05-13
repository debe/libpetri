/**
 * HTML-fragment generator for the small "subnet header" badge bar that the
 * {@link import('./diagram-renderer.js')} layers above subnet diagrams.
 *
 * For a {@link import('../core/subnet-def.js').SubnetDef} the header lists
 * the subnet name, the parameter type (best-effort — TypeScript erases
 * generics at runtime so the slot is shown as a placeholder), and one badge
 * per port and channel — colour-coded by direction
 * (`interface-port-input` / `-output` / `-inout` CSS classes, plus
 * `interface-channel` for sync channels).
 *
 * For an {@link import('../core/instance.js').Instance} the header lists the
 * instance prefix, the originating definition's name, and the {@link
 * import('../core/instance.js').Instance#params} summary.
 *
 * Mirrors: `org.libpetri.doclet.SubnetHeader`
 *
 * @module doclet/subnet-header
 */

import type { Instance } from '../core/instance.js';
import type { Interface, Port } from '../core/interface.js';
import type { SubnetDef } from '../core/subnet-def.js';
import { escapeHtml } from './diagram-renderer.js';

/**
 * Builds the header HTML for a {@link SubnetDef} field.
 *
 * @param def           the subnet definition
 * @param interfaceOnly when `true`, the header carries the "(interface only)"
 *                      badge so the reader knows the body is intentionally
 *                      omitted
 */
export function forSubnetDef(def: SubnetDef<unknown>, interfaceOnly: boolean): string {
  const sb: string[] = [];
  sb.push(`<div class="subnet-header">\n`);
  sb.push(`  <div class="subnet-header-row">\n`);
  sb.push(`    <span class="subnet-header-label">subnet</span>\n`);
  sb.push(`    <span class="subnet-header-name">${escapeHtml(def.name)}</span>\n`);
  // TypeScript erases generics at runtime, so the parameter-type slot is
  // populated with a placeholder ("?"). Java emits the simple class name —
  // the structural HTML is otherwise byte-equivalent.
  sb.push(`    <span class="subnet-header-param">&lt;?&gt;</span>\n`);
  if (interfaceOnly) {
    sb.push(`    <span class="subnet-header-badge subnet-header-badge-interface">interface only</span>\n`);
  }
  sb.push(`  </div>\n`);
  sb.push(renderPortChannelBadges(def.iface));
  sb.push(`</div>\n`);
  return sb.join('');
}

/**
 * Builds the header HTML for an {@link Instance} field.
 */
export function forInstance(instance: Instance<unknown>): string {
  const def = instance.def;
  const sb: string[] = [];
  sb.push(`<div class="subnet-header">\n`);
  sb.push(`  <div class="subnet-header-row">\n`);
  sb.push(`    <span class="subnet-header-label">instance</span>\n`);
  sb.push(`    <span class="subnet-header-name">${escapeHtml(instance.prefix)}</span>\n`);
  sb.push(`    <span class="subnet-header-of">of</span>\n`);
  sb.push(`    <span class="subnet-header-name">${escapeHtml(def.name)}</span>\n`);
  const params = instance.params;
  if (params !== null && params !== undefined) {
    sb.push(`    <span class="subnet-header-params">params=${escapeHtml(String(params))}</span>\n`);
  }
  sb.push(`  </div>\n`);
  sb.push(renderPortChannelBadges(def.iface));
  sb.push(`</div>\n`);
  return sb.join('');
}

/**
 * Renders the per-port and per-channel badge row. Each badge carries a CSS
 * class identifying its kind so the stylesheet can colour-code by direction.
 */
function renderPortChannelBadges(iface: Interface): string {
  if (iface.ports.size === 0 && iface.channels.size === 0) {
    return '';
  }
  const sb: string[] = [];
  sb.push(`  <div class="subnet-header-badges">\n`);
  for (const port of iface.ports.values()) {
    const kind = portKind(port);
    sb.push(`    <span class="interface-port-badge interface-port-badge-${kind}">`);
    sb.push(`<span class="badge-direction">${kind}</span>`);
    sb.push(`<span class="badge-name">${escapeHtml(port.name)}</span>`);
    // TypeScript erases generics so we can't print the runtime token type;
    // omit the type-name span rather than emit a bogus value.
    sb.push(`</span>\n`);
  }
  for (const channel of iface.channels.values()) {
    sb.push(`    <span class="interface-channel-badge">`);
    sb.push(`<span class="badge-direction">channel</span>`);
    sb.push(`<span class="badge-name">${escapeHtml(channel.name)}</span>`);
    sb.push(`</span>\n`);
  }
  sb.push(`  </div>\n`);
  return sb.join('');
}

function portKind(port: Port<unknown>): 'input' | 'output' | 'inout' {
  return port.direction;
}
