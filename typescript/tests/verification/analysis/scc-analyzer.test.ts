import { describe, it, expect } from 'vitest';
import { computeSCCs, findTerminalSCCs } from '../../../src/verification/analysis/scc-analyzer.js';

describe('SCC Analyzer', () => {
  it('finds SCCs in a simple cycle', () => {
    // A -> B -> C -> A
    const nodes = ['A', 'B', 'C'];
    const edges: Record<string, string[]> = { A: ['B'], B: ['C'], C: ['A'] };
    const successors = (n: string) => edges[n] ?? [];

    const sccs = computeSCCs(nodes, successors);
    expect(sccs).toHaveLength(1);
    expect(sccs[0]!.size).toBe(3);
  });

  it('finds SCCs in a linear chain', () => {
    // A -> B -> C
    const nodes = ['A', 'B', 'C'];
    const edges: Record<string, string[]> = { A: ['B'], B: ['C'] };
    const successors = (n: string) => edges[n] ?? [];

    const sccs = computeSCCs(nodes, successors);
    expect(sccs).toHaveLength(3);
    // Each node is its own SCC
    for (const scc of sccs) {
      expect(scc.size).toBe(1);
    }
  });

  it('finds multiple SCCs', () => {
    // Two cycles: {A,B} and {C,D}, A -> C
    const nodes = ['A', 'B', 'C', 'D'];
    const edges: Record<string, string[]> = {
      A: ['B', 'C'], B: ['A'], C: ['D'], D: ['C'],
    };
    const successors = (n: string) => edges[n] ?? [];

    const sccs = computeSCCs(nodes, successors);
    expect(sccs).toHaveLength(2);
  });

  it('single node is its own SCC', () => {
    const sccs = computeSCCs(['X'], () => []);
    expect(sccs).toHaveLength(1);
    expect(sccs[0]!.has('X')).toBe(true);
  });

  it('findTerminalSCCs identifies bottom SCCs', () => {
    // A -> B -> C -> B (cycle), A is transient, {B,C} is terminal
    const nodes = ['A', 'B', 'C'];
    const edges: Record<string, string[]> = { A: ['B'], B: ['C'], C: ['B'] };
    const successors = (n: string) => edges[n] ?? [];

    const terminal = findTerminalSCCs(nodes, successors);
    expect(terminal).toHaveLength(1);
    expect(terminal[0]!.has('B')).toBe(true);
    expect(terminal[0]!.has('C')).toBe(true);
    expect(terminal[0]!.has('A')).toBe(false);
  });

  it('all SCCs terminal when no cross-edges', () => {
    // A -> A, B -> B (two self-loops, no inter-SCC edges)
    const nodes = ['A', 'B'];
    const edges: Record<string, string[]> = { A: ['A'], B: ['B'] };
    const successors = (n: string) => edges[n] ?? [];

    const terminal = findTerminalSCCs(nodes, successors);
    expect(terminal).toHaveLength(2);
  });

  it('handles empty graph', () => {
    const sccs = computeSCCs([] as string[], () => []);
    expect(sccs).toHaveLength(0);

    const terminal = findTerminalSCCs([] as string[], () => []);
    expect(terminal).toHaveLength(0);
  });
});
