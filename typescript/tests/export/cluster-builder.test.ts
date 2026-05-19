/**
 * Tests for the ghost-edge synthesis in `partition()` (compound=true
 * cluster-to-cluster layout hints per spec EXP-017).
 *
 * Mirrors `java/.../ClusterBuilderTest.java` and the `#[cfg(test)] mod`
 * in `rust/libpetri-export/src/cluster_builder.rs`.
 */

import { describe, expect, it } from 'vitest';
import { partition } from '../../src/export/cluster-builder.js';
import type { GraphEdge, GraphNode } from '../../src/export/graph.js';

function node(id: string): GraphNode {
  return {
    id,
    label: id,
    shape: 'circle',
    fill: '#FFFFFF',
    stroke: '#333333',
    penwidth: 1.5,
    semanticId: id,
  };
}

function edge(from: string, to: string): GraphEdge {
  return {
    from,
    to,
    color: '#333333',
    style: 'solid',
    arrowhead: 'normal',
    arcType: 'input',
  };
}

describe('partition — ghost edges (EXP-017)', () => {
  it('emits one ghost edge for a single orphan bridging two clusters', () => {
    // Layout: p_left_a (cluster "left") -> t_orphan -> p_right_b (cluster "right")
    const nodes = [node('p_left_a'), node('t_orphan'), node('p_right_b')];
    const edges = [edge('p_left_a', 't_orphan'), edge('t_orphan', 'p_right_b')];
    const prefix = new Map<string, string>([
      ['p_left_a', 'left'],
      ['p_right_b', 'right'],
    ]);

    const result = partition(nodes, edges, prefix);

    // The two original cross-cluster edges plus exactly one ghost.
    expect(result.topLevelEdges).toHaveLength(3);
    const ghosts = result.topLevelEdges.filter(e => e.arcType === 'ghost');
    expect(ghosts).toHaveLength(1);
    expect(ghosts[0].style).toBe('invis');
    expect(ghosts[0].arrowhead).toBe('none');
    expect(ghosts[0].attrs?.ltail).toBe('cluster_left');
    expect(ghosts[0].attrs?.lhead).toBe('cluster_right');
    expect(ghosts[0].from).toBe('p_left_a');
    expect(ghosts[0].to).toBe('p_right_b');
  });

  it('dedups: 3 orphans bridging the same cluster pair produce 1 ghost edge', () => {
    const nodes = [
      node('p_left_a'),
      node('t_o1'), node('t_o2'), node('t_o3'),
      node('p_right_b'),
    ];
    const edges = [
      edge('p_left_a', 't_o1'), edge('t_o1', 'p_right_b'),
      edge('p_left_a', 't_o2'), edge('t_o2', 'p_right_b'),
      edge('p_left_a', 't_o3'), edge('t_o3', 'p_right_b'),
    ];
    const prefix = new Map<string, string>([
      ['p_left_a', 'left'],
      ['p_right_b', 'right'],
    ]);

    const result = partition(nodes, edges, prefix);

    const ghosts = result.topLevelEdges.filter(e => e.arcType === 'ghost');
    expect(ghosts).toHaveLength(1);
    expect(ghosts[0].attrs?.ltail).toBe('cluster_left');
    expect(ghosts[0].attrs?.lhead).toBe('cluster_right');
  });

  it('emits a ghost per ordered direction (X→Y and Y→X are distinct)', () => {
    const nodes = [
      node('p_left_a'), node('t_fwd'),
      node('p_right_b'), node('t_back'),
    ];
    const edges = [
      edge('p_left_a', 't_fwd'), edge('t_fwd', 'p_right_b'),
      edge('p_right_b', 't_back'), edge('t_back', 'p_left_a'),
    ];
    const prefix = new Map<string, string>([
      ['p_left_a', 'left'],
      ['p_right_b', 'right'],
    ]);

    const result = partition(nodes, edges, prefix);

    const ghosts = result.topLevelEdges.filter(e => e.arcType === 'ghost');
    expect(ghosts).toHaveLength(2);
    const pairs = ghosts.map(g => `${g.attrs?.ltail}->${g.attrs?.lhead}`).sort();
    expect(pairs).toEqual(['cluster_left->cluster_right', 'cluster_right->cluster_left']);
  });

  it('emits no ghost when orphan only touches a single cluster (X → orphan → X)', () => {
    const nodes = [node('p_a1'), node('t_orphan'), node('p_a2')];
    const edges = [edge('p_a1', 't_orphan'), edge('t_orphan', 'p_a2')];
    const prefix = new Map<string, string>([
      ['p_a1', 'same'],
      ['p_a2', 'same'],
    ]);

    const result = partition(nodes, edges, prefix);

    const ghosts = result.topLevelEdges.filter(e => e.arcType === 'ghost');
    expect(ghosts).toHaveLength(0);
  });

  it('emits no ghost when orphan only has one clustered neighbour', () => {
    // p_left_a (cluster) -> t_orphan -> p_top (top-level / orphan)
    const nodes = [node('p_left_a'), node('t_orphan'), node('p_top')];
    const edges = [edge('p_left_a', 't_orphan'), edge('t_orphan', 'p_top')];
    const prefix = new Map<string, string>([
      ['p_left_a', 'left'],
    ]);

    const result = partition(nodes, edges, prefix);

    const ghosts = result.topLevelEdges.filter(e => e.arcType === 'ghost');
    expect(ghosts).toHaveLength(0);
  });

  it('flat net (no prefixes) emits no ghost edges', () => {
    const nodes = [node('p_a'), node('t_x'), node('p_b')];
    const edges = [edge('p_a', 't_x'), edge('t_x', 'p_b')];

    const result = partition(nodes, edges, new Map());

    expect(result.topLevelEdges).toHaveLength(2);
    expect(result.topLevelEdges.every(e => e.arcType !== 'ghost')).toBe(true);
  });

  it('sanitizes cluster prefixes with / into _ for ltail/lhead', () => {
    const nodes = [node('p_outer_inner_a'), node('t_orphan'), node('p_far_b')];
    const edges = [edge('p_outer_inner_a', 't_orphan'), edge('t_orphan', 'p_far_b')];
    const prefix = new Map<string, string>([
      ['p_outer_inner_a', 'outer/inner'],
      ['p_far_b', 'far'],
    ]);

    const result = partition(nodes, edges, prefix);

    const ghosts = result.topLevelEdges.filter(e => e.arcType === 'ghost');
    expect(ghosts).toHaveLength(1);
    expect(ghosts[0].attrs?.ltail).toBe('cluster_outer_inner');
    expect(ghosts[0].attrs?.lhead).toBe('cluster_far');
  });

  it('handles multiple orphans bridging multiple cluster pairs', () => {
    // left -> o1 -> right
    // left -> o2 -> mid
    // mid  -> o3 -> right
    const nodes = [
      node('p_left_a'),
      node('p_mid_a'),
      node('p_right_a'),
      node('t_o1'), node('t_o2'), node('t_o3'),
    ];
    const edges = [
      edge('p_left_a', 't_o1'), edge('t_o1', 'p_right_a'),
      edge('p_left_a', 't_o2'), edge('t_o2', 'p_mid_a'),
      edge('p_mid_a', 't_o3'), edge('t_o3', 'p_right_a'),
    ];
    const prefix = new Map<string, string>([
      ['p_left_a', 'left'],
      ['p_mid_a', 'mid'],
      ['p_right_a', 'right'],
    ]);

    const result = partition(nodes, edges, prefix);

    const ghosts = result.topLevelEdges.filter(e => e.arcType === 'ghost');
    expect(ghosts).toHaveLength(3);
    const pairs = ghosts.map(g => `${g.attrs?.ltail}->${g.attrs?.lhead}`).sort();
    expect(pairs).toEqual([
      'cluster_left->cluster_mid',
      'cluster_left->cluster_right',
      'cluster_mid->cluster_right',
    ]);
  });
});
