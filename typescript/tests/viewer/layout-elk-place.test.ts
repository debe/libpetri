/**
 * Tests for the ELK placement + DOT pin-mode rewrite (Stage 2).
 *
 * Verifies that `elkLayout` produces a position for every renderable node
 * and a bounding box for every cluster, and that `writeBack` emits DOT
 * that round-trips through `@viz-js/viz` with `engine: 'nop2'` without
 * errors and at the expected ELK-native dimensions.
 *
 * @vitest-environment happy-dom
 */
import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';
import { instance as vizInstance } from '@viz-js/viz';
import {
  foldOrphans,
  parseLibpetriDot,
  replicateShared,
} from '../../src/viewer/layout/preprocess.js';
import {
  elkLayout,
  writeBack,
} from '../../src/viewer/layout/elk-place.js';

const here = dirname(fileURLToPath(import.meta.url));
const FIXTURE = resolve(here, '../fixtures/voice-workflow-baseline.dot');
const DOT = readFileSync(FIXTURE, 'utf8');

describe('elkLayout', () => {
  it('produces a position for every renderable node in every cluster', async () => {
    const graph = replicateShared(foldOrphans(parseLibpetriDot(DOT), 0.7), { max: Infinity });
    const layout = await elkLayout(graph);

    for (const [clusterId, cluster] of graph.clusters) {
      expect(layout.clusterBoxes.has(clusterId)).toBe(true);
      for (const nodeId of cluster.nodes) {
        if (!graph.nodes.has(nodeId)) continue;
        const pos = layout.nodePositions.get(nodeId);
        expect(pos, `missing position for ${nodeId} in ${clusterId}`).toBeDefined();
        expect(pos!.width).toBeGreaterThan(0);
        expect(pos!.height).toBeGreaterThan(0);
      }
    }
    for (const orphanId of graph.orphans) {
      expect(layout.nodePositions.has(orphanId)).toBe(true);
    }
  });

  it('produces a non-trivial bounding box for Marvin (rough match to v3)', async () => {
    const graph = replicateShared(foldOrphans(parseLibpetriDot(DOT), 0.7), { max: Infinity });
    const layout = await elkLayout(graph);

    // v3 C0-GOOD reference: 4387×3915 ± a lot of layout-engine variance.
    // Assert order-of-magnitude rather than near-exact.
    expect(layout.totalWidth).toBeGreaterThan(2000);
    expect(layout.totalHeight).toBeGreaterThan(2000);
    expect(layout.totalWidth).toBeLessThan(8000);
    expect(layout.totalHeight).toBeLessThan(8000);
  });

  it('cluster bboxes contain their member nodes', async () => {
    const graph = replicateShared(foldOrphans(parseLibpetriDot(DOT), 0.7), { max: Infinity });
    const layout = await elkLayout(graph);

    for (const [clusterId, cluster] of graph.clusters) {
      const box = layout.clusterBoxes.get(clusterId)!;
      for (const nodeId of cluster.nodes) {
        const pos = layout.nodePositions.get(nodeId);
        if (!pos) continue;
        const cx = pos.x + pos.width / 2;
        const cy = pos.y + pos.height / 2;
        expect(cx, `${nodeId} cx out of ${clusterId} box`).toBeGreaterThanOrEqual(box.x);
        expect(cx).toBeLessThanOrEqual(box.x + box.width);
        expect(cy, `${nodeId} cy out of ${clusterId} box`).toBeGreaterThanOrEqual(box.y);
        expect(cy).toBeLessThanOrEqual(box.y + box.height);
      }
    }
  });
});

describe('writeBack', () => {
  it('emits a DOT with pos="x,y!" per node, bb= per cluster, and orthogonal edge routes', async () => {
    const graph = replicateShared(foldOrphans(parseLibpetriDot(DOT), 0.7), { max: Infinity });
    const layout = await elkLayout(graph);
    const dot = writeBack(graph, layout);

    expect(dot).toContain('subgraph cluster_productSearch');
    // bb= attribute for the cluster
    expect(dot).toMatch(/bb="[\d.]+,[\d.]+,[\d.]+,[\d.]+"/);
    // pos="x,y!" pin marker for a known node
    expect(dot).toMatch(/pos="[\d.]+,[\d.]+!"/);
    // Arc-type attributes round-tripped — odot only on inhibitor edges
    expect(dot).toMatch(/arrowhead="normal"/);
    // Edges carry an ELK-routed `pos="e,…"` spline for Graphviz nop2 to draw
    // (we route ourselves instead of using Graphviz's wasm-crashing ortho).
    expect(dot).toMatch(/pos="e,[\d.]+,[\d.]+ /);
  });

  it('preserves node visual attrs through the round-trip', async () => {
    const graph = replicateShared(foldOrphans(parseLibpetriDot(DOT), 0.7), { max: Infinity });
    const layout = await elkLayout(graph);
    const dot = writeBack(graph, layout);

    // Sample place keeps its xlabel + shape
    expect(dot).toContain('xlabel="productSearch/CombinationsReady"');
    expect(dot).toContain('shape="circle"');
    // Sample transition keeps its label + box shape
    expect(dot).toContain('shape="box"');
  });

  it('round-trips through Graphviz nop without rescaling dimensions', async () => {
    const graph = replicateShared(foldOrphans(parseLibpetriDot(DOT), 0.7), { max: Infinity });
    const layout = await elkLayout(graph);
    const dot = writeBack(graph, layout);

    const viz = await vizInstance();
    const svg = viz.renderSVGElement(dot, {
      // Production renders with nop2 (render.ts); test with the same engine so
      // the pinned node AND edge positions are exercised, not Graphviz routing.
      engine: 'nop2',
      yInvert: true,
    });
    expect(svg.tagName).toBe('svg');
    // The Graphviz output should contain all our clusters as <g class="cluster">
    const clusters = svg.querySelectorAll('g.cluster');
    expect(clusters.length).toBeGreaterThan(0);
    // Output SVG dimensions should be close to the ELK layout's totalWidth
    // (within ~10%) — `nop2` honours the pinned positions verbatim, no
    // ~6× rescaling like `nop`/`nop1` mode.
    const wAttr = svg.getAttribute('width') ?? '';
    const widthPt = parseFloat(wAttr.replace(/pt$/, ''));
    expect(widthPt).toBeGreaterThan(layout.totalWidth * 0.9);
    expect(widthPt).toBeLessThan(layout.totalWidth * 1.2);
  }, 30_000);

  it('preserves libpetri edge attrs verbatim (penwidth, label, color)', async () => {
    const graph = replicateShared(foldOrphans(parseLibpetriDot(DOT), 0.7), { max: Infinity });
    const layout = await elkLayout(graph);
    const dot = writeBack(graph, layout);

    // Reset edges keep their libpetri `penwidth=2.0` + `label="reset"`.
    // Inhibitor edges keep their `arrowhead="odot"`. Otherwise the rendered
    // diagram diverges visually from a fresh DotExporter emit and users see
    // mismatched line widths/labels in the C0 view vs everywhere else.
    // libpetri emits `penwidth=2` (no decimal) on reset/start nodes — must
    // round-trip exactly so stroke-width matches across renderers.
    expect(dot).toMatch(/penwidth=2(?:\.0+)?[\s,\]]/);
    expect(dot).toMatch(/label="reset"/);
    expect(dot).toMatch(/style="bold"/);
    expect(dot).toMatch(/arrowhead="odot"/);
  });

  it('renders visible nodes inside each cluster (not empty boxes)', async () => {
    // Regression: if writeBack pushes ELK's layout-reserved width/height
    // (which include xlabel padding, ~3 inches) to Graphviz, every circle
    // is drawn at ~110pt radius — completely covering its own cluster
    // contents and producing an "empty boxes" visual. Visual shape size
    // must come from libpetri's original `width="0.35"` attrs (12.6pt).
    const graph = replicateShared(foldOrphans(parseLibpetriDot(DOT), 0.7), { max: Infinity });
    const layout = await elkLayout(graph);
    const dot = writeBack(graph, layout);

    const viz = await vizInstance();
    const svg = viz.renderSVGElement(dot, { engine: 'nop2', yInvert: true });

    // Every place ellipse should be a small libpetri circle (rx ≈ 12.6pt
    // for places, 16.6pt for end-doublecircles, never > ~30pt).
    const ellipses = Array.from(svg.querySelectorAll('g.node ellipse'));
    expect(ellipses.length).toBeGreaterThan(0);
    for (const el of ellipses) {
      const rx = parseFloat(el.getAttribute('rx') ?? '0');
      expect(
        rx,
        `node ellipse rx=${rx} is implausibly large — likely the ELK ` +
          `layout-box leaked into Graphviz, painting a giant circle on ` +
          `top of the cluster contents`,
      ).toBeLessThan(30);
      expect(rx).toBeGreaterThan(2);
    }

    // At least one node from each major libpetri cluster should be present
    // by title (sanity that nodes survived parse → preprocess → write →
    // render). Cluster_intent had 10 internal nodes in baseline.
    const intentNodeTitles = Array.from(svg.querySelectorAll('g.node > title'))
      .map(t => t.textContent ?? '')
      .filter(s => s.includes('intent_') || s === 'p_IntentDetectionCustomerInput');
    expect(intentNodeTitles.length).toBeGreaterThan(3);
  }, 30_000);
});

describe('elkLayout — clusterLayout + leafPacking config', () => {
  /**
   * A DOT with two clusters: `cluster_hub` — one transition fanning N reset
   * arcs to N degree-1 leaf places (the FORK_INPUT-style pathology) — and
   * `cluster_flow` — an ordinary place→transition flow with no side-effect
   * leaves.
   */
  function syntheticDot(resetLeaves: number): string {
    const l: string[] = ['digraph G {', '  rankdir=TB;'];
    l.push('  subgraph cluster_hub {');
    l.push('    label="hub";');
    l.push('    t_hub [label="hub/ForkInput", shape="box"];');
    for (let i = 0; i < resetLeaves; i++) {
      // Realistic place-name width — reset-target places have long names.
      l.push(`    p_leaf${i} [label="ResetTargetPlace_${i}", shape="circle"];`);
    }
    l.push('  }');
    l.push('  subgraph cluster_flow {');
    l.push('    label="flow";');
    l.push('    t_a [label="flow/A", shape="box"];');
    l.push('    p_mid [label="mid", shape="circle"];');
    l.push('    t_b [label="flow/B", shape="box"];');
    l.push('  }');
    for (let i = 0; i < resetLeaves; i++) {
      l.push(`  t_hub -> p_leaf${i} [label="reset", color="#fd7e14"];`);
    }
    l.push('  t_a -> p_mid;');
    l.push('  p_mid -> t_b;');
    l.push('}');
    return l.join('\n');
  }

  const build = (dot: string) =>
    replicateShared(foldOrphans(parseLibpetriDot(dot), 0.7), { max: Infinity });

  const aspect = (b: { width: number; height: number }) => b.width / b.height;

  it('default config packs a reset-leaf-dominated cluster (no wide row)', async () => {
    const graph = build(syntheticDot(14));
    const off = await elkLayout(graph, { leafPacking: false });
    const on = await elkLayout(graph); // default — leafPacking enabled

    const hubOff = off.clusterBoxes.get('cluster_hub')!;
    const hubOn = on.clusterBoxes.get('cluster_hub')!;

    // Without packing the 14 leaves form one wide ELK layer; with packing
    // they become a compact grid block — markedly narrower and less
    // width-biased.
    expect(aspect(hubOn)).toBeLessThan(aspect(hubOff));
    expect(aspect(hubOn)).toBeLessThan(2);
    expect(hubOn.width).toBeLessThan(hubOff.width * 0.7);

    // Every leaf still has a position, inside the hub box.
    for (let i = 0; i < 14; i++) {
      const pos = on.nodePositions.get(`p_leaf${i}`);
      expect(pos, `p_leaf${i} missing position`).toBeDefined();
      const cx = pos!.x + pos!.width / 2;
      const cy = pos!.y + pos!.height / 2;
      expect(cx).toBeGreaterThanOrEqual(hubOn.x);
      expect(cx).toBeLessThanOrEqual(hubOn.x + hubOn.width);
      expect(cy).toBeGreaterThanOrEqual(hubOn.y);
      expect(cy).toBeLessThanOrEqual(hubOn.y + hubOn.height);
    }
  });

  it('leaves a non-dominated cluster untouched by leaf packing', async () => {
    const graph = build(syntheticDot(14));
    const off = await elkLayout(graph, { leafPacking: false });
    const on = await elkLayout(graph);

    // cluster_flow has zero side-effect leaves — identical box either way.
    const flowOff = off.clusterBoxes.get('cluster_flow')!;
    const flowOn = on.clusterBoxes.get('cluster_flow')!;
    expect(flowOn.width).toBeCloseTo(flowOff.width, 5);
    expect(flowOn.height).toBeCloseTo(flowOff.height, 5);
  });

  it('honours the minLeaves threshold', async () => {
    const graph = build(syntheticDot(14));
    const off = await elkLayout(graph, { leafPacking: false });
    // 14 leaves < minLeaves 20 → not dominated → identical to disabled.
    const tuned = await elkLayout(graph, { leafPacking: { minLeaves: 20 } });
    const hubOff = off.clusterBoxes.get('cluster_hub')!;
    const hubTuned = tuned.clusterBoxes.get('cluster_hub')!;
    expect(hubTuned.width).toBeCloseTo(hubOff.width, 5);
    expect(hubTuned.height).toBeCloseTo(hubOff.height, 5);
  });

  it('clusterLayout: rectpacking lays every node out without error', async () => {
    const graph = build(syntheticDot(14));
    const layout = await elkLayout(graph, { clusterLayout: 'rectpacking' });
    for (const [, cluster] of graph.clusters) {
      for (const nodeId of cluster.nodes) {
        if (graph.nodes.has(nodeId)) {
          expect(layout.nodePositions.has(nodeId)).toBe(true);
        }
      }
    }
    expect(layout.totalWidth).toBeGreaterThan(0);
  });

  it('still draws every reset edge after packing (writeBack)', async () => {
    const graph = build(syntheticDot(14));
    const layout = await elkLayout(graph);
    const dot = writeBack(graph, layout);
    const resetEdges = dot.match(/->[^;]*label="reset"/g) ?? [];
    expect(resetEdges.length).toBe(14);
  });
});
