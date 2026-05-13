/**
 * DOT generators for the subnet-aware diagrams the {@link
 * import('./petri-net-plugin.js')} plugin draws.
 *
 * Two flavours:
 * - {@link fullBody} — the subnet's complete body, but with its interface-port
 *   places restyled with the `interface-port` category from
 *   `petri-net-styles.json` so they read as boundary elements at a glance. A
 *   small `subgraph cluster_iface_*` with label `"interface"` surrounds the
 *   port places and channel transitions to advertise the subnet boundary
 *   visually.
 * - {@link interfaceOnly} — a tiny diagram of just the port places, the
 *   channel transitions, and a single stub node indicating the body is
 *   omitted. Used by the `@subnet` block tag.
 *
 * This module stays in the doclet directory (rather than living in
 * `export/`) because it is a doclet-presentation concern — the production
 * export pipeline never adds the `interface` cluster.
 *
 * Mirrors: `org.libpetri.doclet.SubnetDotExport`
 *
 * @module doclet/subnet-dot-export
 */

import type { SubnetDef } from '../core/subnet-def.js';
import type { Interface, Port, Channel } from '../core/interface.js';
import { dotExport } from '../export/dot-exporter.js';
import { sanitize } from '../export/petri-net-mapper.js';
import { nodeStyle, FONT } from '../export/styles.js';

/**
 * Renders the full body of a {@link SubnetDef} with the interface ports
 * restyled. The output is a post-processed version of {@link dotExport}: the
 * port-place node attribute lines are rewritten so the post-processor swaps in
 * the {@code interface-port} category, channel-transition lines swap in
 * {@code sync-channel}, and an extra {@code subgraph cluster_iface_<name>}
 * block is appended that lists the port nodes by id — overriding their
 * cluster membership without re-emitting them (DOT semantics: a node
 * referenced inside a subgraph block by id alone is treated as a member of
 * that cluster).
 */
export function fullBody(def: SubnetDef<unknown>): string {
  let dot = dotExport(def.body);
  const portIds = portNodeIds(def.iface);
  const channelIds = channelNodeIds(def.iface);

  // Restyle: rewrite the matched node lines so the post-processor swaps in
  // the interface-port and sync-channel categories. The renderer emits each
  // node as one line ending with `];` so a per-id rewrite is sufficient and
  // deterministic.
  for (const portId of portIds) {
    dot = restyleNode(dot, portId, nodeStyle('interface-port'));
  }
  for (const chId of channelIds) {
    dot = restyleNode(dot, chId, nodeStyle('sync-channel'));
  }

  // Wrap the port and channel ids in a header cluster so the doclet's viewer
  // can render the boundary distinctly. Done by injecting an extra subgraph
  // block before the closing `}` of the digraph.
  if (portIds.size > 0 || channelIds.size > 0) {
    let iface = '';
    iface += `    subgraph cluster_iface_${sanitize(def.name)} {\n`;
    iface += `        label="interface";\n`;
    iface += `        style="rounded,dashed";\n`;
    iface += `        bgcolor="#F0F6FF";\n`;
    iface += `        penwidth=2;\n`;
    for (const id of portIds) {
      iface += `        ${id};\n`;
    }
    for (const id of channelIds) {
      iface += `        ${id};\n`;
    }
    iface += `    }\n`;

    const lastBrace = dot.lastIndexOf('}');
    if (lastBrace > 0) {
      dot = dot.substring(0, lastBrace) + iface + dot.substring(lastBrace);
    }
  }
  return dot;
}

/**
 * Renders an interface-only diagram: just the port places + channel
 * transitions + a single stub node labelled "(internals omitted)" so the
 * reader knows the body has not been drawn.
 */
export function interfaceOnly(def: SubnetDef<unknown>): string {
  const sb: string[] = [];
  sb.push(`digraph ${sanitize(def.name)} {\n`);
  sb.push(`    rankdir=LR;\n`);
  sb.push(`    nodesep=0.5;\n`);
  sb.push(`    ranksep=0.6;\n`);
  sb.push(`    fontname="${FONT.family}";\n`);
  sb.push(`    node [fontname="${FONT.family}", fontsize=12];\n`);
  sb.push(`    edge [fontname="${FONT.family}", fontsize=10];\n`);
  sb.push('\n');

  const stubId = 'stub_' + sanitize(def.name);

  // Group ports by direction: inputs on the left, outputs on the right,
  // inouts above. This keeps the interface diagram visually structured even
  // when the body internals are absent.
  const inputs: Port<unknown>[] = [];
  const outputs: Port<unknown>[] = [];
  const inouts: Port<unknown>[] = [];
  for (const port of def.iface.ports.values()) {
    switch (port.direction) {
      case 'input':  inputs.push(port);  break;
      case 'output': outputs.push(port); break;
      case 'inout':  inouts.push(port);  break;
    }
  }

  // Emit port nodes.
  for (const port of inputs) emitPortNode(sb, port, 'input');
  for (const port of outputs) emitPortNode(sb, port, 'output');
  for (const port of inouts) emitPortNode(sb, port, 'inout');

  // Emit channel nodes.
  const syncStyle = nodeStyle('sync-channel');
  for (const ch of def.iface.channels.values()) {
    sb.push(`    ${channelNodeId(ch)} [`);
    sb.push(`label="⇄ ${escapeLabel(ch.name)}", `);
    sb.push(`shape=${syncStyle.shape}, `);
    sb.push(`style="filled", `);
    sb.push(`fillcolor="${syncStyle.fill}", `);
    sb.push(`color="${syncStyle.stroke}", `);
    sb.push(`penwidth=${trimNumber(syncStyle.penwidth)}`);
    sb.push(`];\n`);
  }

  // Emit stub node.
  sb.push(`    ${stubId} [`);
  sb.push(`label="${escapeLabel(def.name)}\\n(internals omitted)", `);
  sb.push(`shape=box, style="filled,dashed,rounded", `);
  sb.push(`fillcolor="#FFFFFF", color="#666666", penwidth=1, `);
  sb.push(`fontsize=11`);
  sb.push(`];\n`);
  sb.push('\n');

  // Connect inputs -> stub -> outputs; inouts and channels link both ways.
  for (const port of inputs) {
    sb.push(`    ${portNodeId(port)} -> ${stubId} [color="#1d4ed8", arrowhead=normal];\n`);
  }
  for (const port of outputs) {
    sb.push(`    ${stubId} -> ${portNodeId(port)} [color="#1d4ed8", arrowhead=normal];\n`);
  }
  for (const port of inouts) {
    sb.push(`    ${portNodeId(port)} -> ${stubId} [color="#1d4ed8", arrowhead=normalnormal, dir=both];\n`);
  }
  for (const ch of def.iface.channels.values()) {
    sb.push(`    ${channelNodeId(ch)} -> ${stubId} [color="#6d28d9", arrowhead=normal, style=dashed];\n`);
  }

  sb.push(`}\n`);
  return sb.join('');
}

// ============================================================
//  Helpers
// ============================================================

function emitPortNode(sb: string[], port: Port<unknown>, direction: string): void {
  const style = nodeStyle('interface-port');
  // Token type isn't carried at runtime in TypeScript (generics erased), so
  // the xlabel is the direction marker only — Java additionally appends the
  // port's tokenType simple name. The structural content is otherwise
  // identical.
  sb.push(`    ${portNodeId(port)} [`);
  sb.push(`label="${escapeLabel(port.name)}", `);
  sb.push(`xlabel="${escapeLabel(direction)}", `);
  sb.push(`shape=${style.shape}, `);
  sb.push(`style="filled,${style.style ?? 'solid'}", `);
  sb.push(`fillcolor="${style.fill}", `);
  sb.push(`color="${style.stroke}", `);
  sb.push(`penwidth=${trimNumber(style.penwidth)}`);
  if (style.width !== undefined) {
    sb.push(`, width=${trimNumber(style.width)}, fixedsize=true`);
  }
  sb.push(`];\n`);
}

function portNodeId(port: Port<unknown>): string {
  return 'p_' + sanitize(port.place.name);
}

function channelNodeId(ch: Channel): string {
  return 't_' + sanitize(ch.transition.name);
}

function portNodeIds(iface: Interface): Set<string> {
  const ids = new Set<string>();
  for (const port of iface.ports.values()) ids.add(portNodeId(port));
  return ids;
}

function channelNodeIds(iface: Interface): Set<string> {
  const ids = new Set<string>();
  for (const ch of iface.channels.values()) ids.add(channelNodeId(ch));
  return ids;
}

/**
 * Rewrites the {@code fillcolor=}, {@code color=}, {@code style=}, and
 * {@code penwidth=} attributes of the line declaring the given node id so
 * the supplied style takes precedence. Operates as a plain text rewrite:
 * the {@link import('../export/dot-renderer.js').renderDot} output formats
 * each node line deterministically, so a per-attribute regex is reliable.
 */
function restyleNode(
  dot: string,
  nodeId: string,
  style: ReturnType<typeof nodeStyle>,
): string {
  // The node line begins with: <id> [
  // and ends with: ];
  // Find the line, then surgically swap fillcolor / color / style / penwidth.
  const marker = nodeId + ' [';
  let start = dot.indexOf('\n    ' + marker);
  if (start < 0) start = dot.indexOf('    ' + marker);
  if (start < 0) return dot;
  // Skip the leading newline if present so we operate on the line proper.
  if (dot.charAt(start) === '\n') start += 1;
  const lineEnd = dot.indexOf('];', start);
  if (lineEnd < 0) return dot;
  let line = dot.substring(start, lineEnd + 2);

  // Order matters: keep `fillcolor` before `color` so the substring search
  // for `color="` doesn't accidentally hit `fillcolor="`.
  line = replaceAttr(line, 'fillcolor', style.fill);
  line = replaceAttr(line, 'color', style.stroke);
  line = replaceAttr(line, 'penwidth', trimNumber(style.penwidth));
  if (style.style !== undefined) {
    // Compose with `filled` because the renderer already includes that.
    line = replaceAttr(line, 'style', `"filled,${style.style}"`);
  }

  return dot.substring(0, start) + line + dot.substring(lineEnd + 2);
}

/**
 * Replaces the value of a {@code key=value} pair within a single DOT
 * attribute list. Quotes the value when the existing form was quoted, leaves
 * the value unquoted when the existing form was unquoted (numeric).
 */
function replaceAttr(line: string, key: string, value: string): string {
  // Match key="..." (quoted) — the key must be preceded by a non-word char
  // (start, comma, or space) so `color=` doesn't match inside `fillcolor=`.
  const quotedPat = key + '="';
  const qStart = findAttrStart(line, quotedPat);
  if (qStart >= 0) {
    const valStart = qStart + quotedPat.length;
    const valEnd = line.indexOf('"', valStart);
    if (valEnd < 0) return line;
    let v = value;
    if (v.startsWith('"') && v.endsWith('"') && v.length >= 2) {
      v = v.substring(1, v.length - 1);
    }
    return line.substring(0, valStart) + v + line.substring(valEnd);
  }
  // Match key=NN (numeric, ends at ',' or ']').
  const unquoted = key + '=';
  const uStart = findAttrStart(line, unquoted);
  if (uStart < 0) return line;
  const valStart = uStart + unquoted.length;
  let valEnd = valStart;
  while (valEnd < line.length) {
    const c = line.charAt(valEnd);
    if (c === ',' || c === ']') break;
    valEnd++;
  }
  return line.substring(0, valStart) + value + line.substring(valEnd);
}

/**
 * Finds the start of a `key=` attribute pattern in `line`, ensuring the
 * match is not a suffix of another attribute name (e.g. `color=` must not
 * match inside `fillcolor=`). Returns -1 when no boundary-respecting match
 * exists.
 */
function findAttrStart(line: string, pattern: string): number {
  let from = 0;
  while (from < line.length) {
    const idx = line.indexOf(pattern, from);
    if (idx < 0) return -1;
    if (idx === 0) return idx;
    const prev = line.charAt(idx - 1);
    // Word-boundary check: previous char must not be alphanumeric/underscore.
    if (!/[A-Za-z0-9_]/.test(prev)) return idx;
    from = idx + 1;
  }
  return -1;
}

function trimNumber(d: number): string {
  if (Number.isInteger(d)) return String(d);
  return String(d);
}

function escapeLabel(s: string): string {
  return s.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
}
