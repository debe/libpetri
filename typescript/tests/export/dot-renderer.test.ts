import { describe, it, expect } from 'vitest';
import { renderDot } from '../../src/export/dot-renderer.js';
import type { Graph, GraphNode, GraphEdge } from '../../src/export/graph.js';

function emptyGraph(overrides?: Partial<Graph>): Graph {
  return {
    id: 'test',
    rankdir: 'TB',
    nodes: [],
    edges: [],
    subgraphs: [],
    graphAttrs: {},
    nodeDefaults: {},
    edgeDefaults: {},
    ...overrides,
  };
}

function placeNode(id: string, label: string, overrides?: Partial<GraphNode>): GraphNode {
  return {
    id,
    label,
    shape: 'circle',
    fill: '#FFFFFF',
    stroke: '#333333',
    penwidth: 1.5,
    semanticId: label,
    ...overrides,
  };
}

function edge(from: string, to: string, overrides?: Partial<GraphEdge>): GraphEdge {
  return {
    from,
    to,
    color: '#333333',
    style: 'solid',
    arrowhead: 'normal',
    arcType: 'input',
    ...overrides,
  };
}

describe('renderDot', () => {
  it('renders empty graph', () => {
    const result = renderDot(emptyGraph());

    expect(result).toContain('digraph test {');
    expect(result).toContain('rankdir=TB;');
    expect(result).toContain('}');
  });

  it('renders graph attributes', () => {
    const result = renderDot(emptyGraph({
      graphAttrs: { nodesep: '0.5', ranksep: '0.75' },
    }));

    expect(result).toContain('nodesep=0.5;');
    expect(result).toContain('ranksep=0.75;');
  });

  it('renders node defaults', () => {
    const result = renderDot(emptyGraph({
      nodeDefaults: { fontname: 'Helvetica', fontsize: '12' },
    }));

    expect(result).toContain('node [fontname="Helvetica", fontsize=12];');
  });

  it('renders edge defaults', () => {
    const result = renderDot(emptyGraph({
      edgeDefaults: { fontname: 'Arial', fontsize: '10' },
    }));

    expect(result).toContain('edge [fontname="Arial", fontsize=10];');
  });

  it('renders nodes with all attributes', () => {
    const result = renderDot(emptyGraph({
      nodes: [placeNode('p_Start', 'Start', { fill: '#d4edda', stroke: '#28a745', penwidth: 2.0 })],
    }));

    expect(result).toContain('p_Start [');
    expect(result).toContain('label="Start"');
    expect(result).toContain('shape="circle"');
    expect(result).toContain('fillcolor="#d4edda"');
    expect(result).toContain('color="#28a745"');
    expect(result).toContain('penwidth=2');
    expect(result).toContain('style="filled"');
  });

  it('renders nodes with dashed style', () => {
    const result = renderDot(emptyGraph({
      nodes: [placeNode('p_env', 'env', { style: 'dashed' })],
    }));

    expect(result).toContain('style="filled,dashed"');
  });

  it('renders nodes with height and width', () => {
    const result = renderDot(emptyGraph({
      nodes: [placeNode('t_fire', 'fire', { shape: 'box', height: 0.4, width: 0.8 })],
    }));

    expect(result).toContain('height=0.4');
    expect(result).toContain('width=0.8');
  });

  it('renders edges', () => {
    const result = renderDot(emptyGraph({
      nodes: [placeNode('p_A', 'A'), placeNode('p_B', 'B')],
      edges: [edge('p_A', 'p_B')],
    }));

    expect(result).toContain('p_A -> p_B [');
    expect(result).toContain('color="#333333"');
    expect(result).toContain('style="solid"');
    expect(result).toContain('arrowhead="normal"');
  });

  it('renders edges with labels', () => {
    const result = renderDot(emptyGraph({
      nodes: [placeNode('p_A', 'A'), placeNode('t_T', 'T')],
      edges: [edge('p_A', 't_T', { label: '\u00d73' })],
    }));

    expect(result).toContain('label="\u00d73"');
  });

  it('renders edges with penwidth', () => {
    const result = renderDot(emptyGraph({
      edges: [edge('t_T', 'p_A', { penwidth: 2.0 })],
    }));

    expect(result).toContain('penwidth=2');
  });

  it('renders inhibitor edge with odot arrowhead', () => {
    const result = renderDot(emptyGraph({
      edges: [edge('p_A', 't_T', {
        color: '#dc3545',
        arrowhead: 'odot',
        arcType: 'inhibitor',
      })],
    }));

    expect(result).toContain('arrowhead="odot"');
    expect(result).toContain('color="#dc3545"');
  });

  it('renders dashed edge style', () => {
    const result = renderDot(emptyGraph({
      edges: [edge('p_A', 't_T', { style: 'dashed', label: 'read' })],
    }));

    expect(result).toContain('style="dashed"');
    expect(result).toContain('label="read"');
  });

  it('renders subgraphs', () => {
    const result = renderDot(emptyGraph({
      subgraphs: [{
        id: 'sg1',
        label: 'Group 1',
        nodes: [placeNode('p_inner', 'inner')],
      }],
    }));

    expect(result).toContain('subgraph cluster_sg1 {');
    expect(result).toContain('label="Group 1";');
    expect(result).toContain('p_inner [');
  });

  it('quotes identifiers with special characters', () => {
    const result = renderDot(emptyGraph({
      id: 'my-graph',
    }));

    expect(result).toContain('digraph "my-graph" {');
  });

  it('quotes DOT keywords used as identifiers', () => {
    const result = renderDot(emptyGraph({
      nodes: [placeNode('node', 'node')],
    }));

    // 'node' is a DOT keyword, should be quoted
    expect(result).toContain('"node" [');
  });

  it('escapes double quotes in labels', () => {
    const result = renderDot(emptyGraph({
      nodes: [placeNode('p_test', 'label with "quotes"')],
    }));

    expect(result).toContain('label="label with \\"quotes\\""');
  });

  it('renders different rankdir', () => {
    const result = renderDot(emptyGraph({ rankdir: 'LR' }));
    expect(result).toContain('rankdir=LR;');
  });
});
