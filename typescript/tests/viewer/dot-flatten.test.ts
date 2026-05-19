/**
 * Tests for the viewer's DOT flattener: strips `subgraph cluster_*`
 * wrappers and `ltail`/`lhead` cluster references while preserving
 * every node and edge in the input DOT.
 */
import { describe, it, expect } from 'vitest';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';
import { flattenClusters } from '../../src/viewer/dot-flatten.js';

const here = dirname(fileURLToPath(import.meta.url));
const VOICE_WORKFLOW_DOT = resolve(
  here,
  '..',
  'fixtures',
  'voice-workflow-baseline.dot',
);

describe('flattenClusters', () => {
  it('strips a single cluster wrapper and keeps its nodes + edges', () => {
    const input = [
      'digraph G {',
      '    subgraph cluster_a {',
      '        label="a";',
      '        style="rounded,dashed";',
      '        n1 [shape=circle];',
      '        n2 [shape=circle];',
      '        n1 -> n2;',
      '    }',
      '}',
    ].join('\n');
    const out = flattenClusters(input);
    expect(out).not.toMatch(/subgraph\s+cluster_/);
    expect(out).toContain('n1 [shape=circle];');
    expect(out).toContain('n2 [shape=circle];');
    expect(out).toContain('n1 -> n2;');
    // Cluster-level attributes dropped (would otherwise apply to the
    // outer digraph and silently restyle everything).
    expect(out).not.toMatch(/label="a"/);
    expect(out).not.toMatch(/style="rounded,dashed"/);
  });

  it('strips nested cluster wrappers, contents survive', () => {
    const input = [
      'digraph G {',
      '    subgraph cluster_outer {',
      '        label="outer";',
      '        subgraph cluster_inner {',
      '            label="inner";',
      '            n_inner [shape=box];',
      '        }',
      '        n_outer [shape=circle];',
      '    }',
      '}',
    ].join('\n');
    const out = flattenClusters(input);
    expect(out).not.toMatch(/subgraph\s+cluster_/);
    expect(out).toContain('n_inner [shape=box];');
    expect(out).toContain('n_outer [shape=circle];');
    expect(out).not.toMatch(/label="outer"/);
    expect(out).not.toMatch(/label="inner"/);
  });

  it('strips ltail and lhead cluster refs from edges', () => {
    const input = [
      'digraph G {',
      '    a -> b [color="#000", style="invis", ltail="cluster_x", lhead="cluster_y"];',
      '    c -> d [ltail="cluster_x"];',
      '    e -> f [lhead="cluster_y", color="red"];',
      '}',
    ].join('\n');
    const out = flattenClusters(input);
    expect(out).not.toMatch(/ltail=/);
    expect(out).not.toMatch(/lhead=/);
    // The edges themselves remain — only the cluster references were stripped.
    expect(out).toMatch(/a -> b \[/);
    expect(out).toMatch(/c -> d/);
    expect(out).toMatch(/e -> f/);
    // Non-cluster attributes preserved.
    expect(out).toContain('color="#000"');
    expect(out).toContain('color="red"');
    expect(out).toContain('style="invis"');
  });

  it('leaves non-cluster subgraph blocks alone (defensive)', () => {
    const input = [
      'digraph G {',
      '    subgraph plain_group {',
      '        n1 [shape=circle];',
      '    }',
      '}',
    ].join('\n');
    const out = flattenClusters(input);
    // The matcher is anchored on `cluster_` — plain subgraphs untouched.
    expect(out).toContain('subgraph plain_group');
  });

  it('is idempotent on already-flat DOT', () => {
    const flat = [
      'digraph G {',
      '    n1 [shape=circle];',
      '    n2 [shape=box];',
      '    n1 -> n2;',
      '}',
    ].join('\n');
    expect(flattenClusters(flat)).toBe(flat);
  });

  it('flattens the real voice-workflow fixture correctly', () => {
    const input = readFileSync(VOICE_WORKFLOW_DOT, 'utf-8');
    const out = flattenClusters(input);

    expect(out).not.toMatch(/subgraph\s+cluster_/);
    expect(out).not.toMatch(/\bltail\s*=/);
    expect(out).not.toMatch(/\blhead\s*=/);

    // Every place node and transition node from the input survives the
    // flatten — count-equal on the semantic-ID prefixes.
    const placeIds = (s: string): string[] =>
      Array.from(s.matchAll(/\bp_[A-Za-z0-9_]+\b/g), (m) => m[0]);
    const transitionIds = (s: string): string[] =>
      Array.from(s.matchAll(/\bt_[A-Za-z0-9_]+\b/g), (m) => m[0]);
    const inputPlaces = new Set(placeIds(input));
    const outputPlaces = new Set(placeIds(out));
    expect(outputPlaces.size).toBe(inputPlaces.size);
    for (const p of inputPlaces) expect(outputPlaces.has(p)).toBe(true);
    const inputTransitions = new Set(transitionIds(input));
    const outputTransitions = new Set(transitionIds(out));
    expect(outputTransitions.size).toBe(inputTransitions.size);
    for (const t of inputTransitions) expect(outputTransitions.has(t)).toBe(true);
  });
});
