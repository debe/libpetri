/**
 * Renders a Graph to DOT (Graphviz) string.
 *
 * Pure function with zero Petri net knowledge. Operates solely on the
 * format-agnostic Graph model.
 *
 * @module export/dot-renderer
 */

import type { Graph, GraphNode, GraphEdge, Subgraph } from './graph.js';

// ======================== Public API ========================

/** Renders a Graph to a DOT string suitable for Graphviz. */
export function renderDot(graph: Graph): string {
  const lines: string[] = [];

  lines.push(`digraph ${quoteId(graph.id)} {`);

  // Graph attributes
  lines.push(`    rankdir=${graph.rankdir};`);
  for (const [key, value] of Object.entries(graph.graphAttrs)) {
    lines.push(`    ${key}=${quoteAttr(value)};`);
  }

  // Node defaults
  if (Object.keys(graph.nodeDefaults).length > 0) {
    lines.push(`    node [${formatAttrs(graph.nodeDefaults)}];`);
  }

  // Edge defaults
  if (Object.keys(graph.edgeDefaults).length > 0) {
    lines.push(`    edge [${formatAttrs(graph.edgeDefaults)}];`);
  }

  lines.push('');

  // Subgraphs
  for (const sg of graph.subgraphs) {
    lines.push(...renderSubgraph(sg, '    '));
    lines.push('');
  }

  // Nodes
  for (const node of graph.nodes) {
    lines.push(`    ${renderNode(node)}`);
  }

  if (graph.nodes.length > 0) {
    lines.push('');
  }

  // Edges
  for (const edge of graph.edges) {
    lines.push(`    ${renderEdge(edge)}`);
  }

  lines.push('}');

  return lines.join('\n');
}

// ======================== Internal Rendering ========================

function renderNode(node: GraphNode): string {
  const attrs: Record<string, string> = {
    label: node.label,
    shape: node.shape,
    style: node.style ? `"filled,${node.style}"` : 'filled',
    fillcolor: node.fill,
    color: node.stroke,
    penwidth: String(node.penwidth),
  };

  if (node.height !== undefined) {
    attrs['height'] = String(node.height);
  }
  if (node.width !== undefined) {
    attrs['width'] = String(node.width);
  }

  // Merge extra attrs
  if (node.attrs) {
    for (const [key, value] of Object.entries(node.attrs)) {
      attrs[key] = value;
    }
  }

  return `${quoteId(node.id)} [${formatNodeAttrs(attrs)}];`;
}

function renderEdge(edge: GraphEdge): string {
  const attrs: Record<string, string> = {
    color: edge.color,
    style: edge.style,
    arrowhead: edge.arrowhead,
  };

  if (edge.label !== undefined) {
    attrs['label'] = edge.label;
  }
  if (edge.penwidth !== undefined) {
    attrs['penwidth'] = String(edge.penwidth);
  }

  // Merge extra attrs
  if (edge.attrs) {
    for (const [key, value] of Object.entries(edge.attrs)) {
      attrs[key] = value;
    }
  }

  return `${quoteId(edge.from)} -> ${quoteId(edge.to)} [${formatNodeAttrs(attrs)}];`;
}

function renderSubgraph(sg: Subgraph, indent: string): string[] {
  const lines: string[] = [];
  lines.push(`${indent}subgraph ${quoteId('cluster_' + sg.id)} {`);

  if (sg.label !== undefined) {
    lines.push(`${indent}    label=${quoteAttr(sg.label)};`);
  }

  if (sg.attrs) {
    for (const [key, value] of Object.entries(sg.attrs)) {
      lines.push(`${indent}    ${key}=${quoteAttr(value)};`);
    }
  }

  for (const node of sg.nodes) {
    lines.push(`${indent}    ${renderNode(node)}`);
  }

  lines.push(`${indent}}`);
  return lines;
}

// ======================== DOT Quoting ========================

/** Quotes a DOT identifier. Always quotes to be safe with special chars. */
function quoteId(id: string): string {
  // DOT keywords that must be quoted
  if (/^[a-zA-Z_][a-zA-Z0-9_]*$/.test(id) && !isDotKeyword(id)) {
    return id;
  }
  return `"${escapeDot(id)}"`;
}

/** Quotes a DOT attribute value. */
function quoteAttr(value: string): string {
  // Numbers don't need quoting
  if (/^-?\d+(\.\d+)?$/.test(value)) {
    return value;
  }
  return `"${escapeDot(value)}"`;
}

/** Escapes special characters for DOT strings. */
function escapeDot(s: string): string {
  return s.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
}

/**
 * Formats node/edge attributes where certain values (like style with commas)
 * need special handling.
 */
function formatNodeAttrs(attrs: Record<string, string>): string {
  return Object.entries(attrs)
    .map(([key, value]) => {
      // Style values that are already pre-quoted (contain the quote char)
      if (value.startsWith('"') && value.endsWith('"')) {
        return `${key}=${value}`;
      }
      return `${key}=${quoteAttr(value)}`;
    })
    .join(', ');
}

/** Formats simple key=value attributes. */
function formatAttrs(attrs: Readonly<Record<string, string>>): string {
  return Object.entries(attrs)
    .map(([key, value]) => `${key}=${quoteAttr(value)}`)
    .join(', ');
}

/** DOT language keywords that must be quoted when used as identifiers. */
function isDotKeyword(id: string): boolean {
  const lower = id.toLowerCase();
  return lower === 'graph' || lower === 'digraph' || lower === 'subgraph'
    || lower === 'node' || lower === 'edge' || lower === 'strict';
}
