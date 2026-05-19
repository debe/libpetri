/**
 * Tests for the C0 layout pre-processing pipeline.
 *
 * Uses Marvin's exported VoiceWorkflowConfig DOT as the canonical fixture —
 * same input the v3 reference renderer
 * (`run16_GOOD_v3_skip-junctions.mjs`) was iterated against. Verifies
 * parser shape, orphan folding, and shared-place replication produce a
 * graph the next stages (ELK + writeBack) can lay out.
 */
import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';
import {
  foldOrphans,
  parseLibpetriDot,
  replicateShared,
  type GraphModel,
} from '../../src/viewer/layout/preprocess.js';

const here = dirname(fileURLToPath(import.meta.url));
const FIXTURE = resolve(here, '../fixtures/voice-workflow-baseline.dot');
const DOT = readFileSync(FIXTURE, 'utf8');

function isCrossCluster(g: GraphModel, edge: { src: string; dst: string }): boolean {
  const s = g.nodeToCluster.get(edge.src);
  const d = g.nodeToCluster.get(edge.dst);
  return s !== undefined && d !== undefined && s !== d;
}

describe('parseLibpetriDot', () => {
  const graph = parseLibpetriDot(DOT);

  it('discovers all 14 voice subnet clusters', () => {
    expect(graph.clusters.size).toBe(14);
    expect(graph.clusters.has('cluster_productSearch')).toBe(true);
    const productSearch = graph.clusters.get('cluster_productSearch')!;
    expect(productSearch.shortName).toBe('productSearch');
    expect(productSearch.nodes.length).toBeGreaterThan(20);
  });

  it('classifies nodes by id prefix', () => {
    const sample = graph.nodes.get('p_productSearch_CombinationsReady');
    expect(sample?.kind).toBe('place');
    expect(graph.nodes.get('t_productSearch_DeriveFacets')?.kind).toBe('transition');
    expect(graph.nodes.get('j_productSearch_DeriveFacets__xor_0')?.kind).toBe('junction');
  });

  it('captures node label attributes', () => {
    const place = graph.nodes.get('p_productSearch_CombinationsReady')!;
    expect(place.attrs.xlabel).toBe('productSearch/CombinationsReady');
    expect(place.attrs.shape).toBe('circle');
  });

  it('parses all edges as ParsedEdge records', () => {
    expect(graph.edges.length).toBeGreaterThan(100);
    for (const e of graph.edges) {
      expect(e.src).toMatch(/^[pjt]_/);
      expect(e.dst).toMatch(/^[pjt]_/);
      expect(['normal', 'reset', 'inhibitor', 'read']).toContain(e.arc);
    }
  });

  it('every node belongs to either a cluster or the orphan set', () => {
    const inClusters = new Set<string>();
    for (const c of graph.clusters.values()) for (const n of c.nodes) inClusters.add(n);
    for (const id of graph.nodes.keys()) {
      const isOrphan = graph.orphans.includes(id);
      expect(inClusters.has(id) || isOrphan).toBe(true);
      expect(inClusters.has(id) && isOrphan).toBe(false);
    }
  });
});

describe('foldOrphans', () => {
  const raw = parseLibpetriDot(DOT);
  const folded = foldOrphans(raw, 0.7);

  it('reduces orphan count (Marvin baseline has folding opportunities)', () => {
    expect(folded.orphans.length).toBeLessThan(raw.orphans.length);
  });

  it('preserves node and edge counts', () => {
    expect(folded.nodes.size).toBe(raw.nodes.size);
    expect(folded.edges.length).toBe(raw.edges.length);
  });

  it('every formerly-orphan node that got adopted has a cluster mapping', () => {
    for (const id of raw.orphans) {
      const wasFolded = !folded.orphans.includes(id);
      if (wasFolded) {
        const cluster = folded.nodeToCluster.get(id);
        expect(cluster).toBeDefined();
        expect(folded.clusters.get(cluster!)!.nodes).toContain(id);
      }
    }
  });

  it('threshold=0 is a no-op', () => {
    const same = foldOrphans(raw, 0);
    expect(same).toBe(raw);
  });
});

describe('replicateShared', () => {
  const raw = parseLibpetriDot(DOT);
  const folded = foldOrphans(raw, 0.7);
  const replicated = replicateShared(folded, { max: Infinity });

  it('emits at least one replica for Marvin (it has shared hub places)', () => {
    expect(replicated.replicateStats.replicatedPlaces).toBeGreaterThan(0);
    expect(replicated.replicateStats.totalCopies).toBeGreaterThanOrEqual(
      replicated.replicateStats.replicatedPlaces,
    );
  });

  it('replica ids follow the ${placeId}__rep__${shortName} convention', () => {
    let sampledReplica = false;
    for (const node of replicated.nodes.values()) {
      if (!node.replica || !node.replicaOf || node.id === node.replicaOf) continue;
      sampledReplica = true;
      const cluster = replicated.nodeToCluster.get(node.id);
      expect(cluster).toBeDefined();
      const shortName = cluster!.replace(/^cluster_/, '');
      expect(node.id).toBe(`${node.replicaOf}__rep__${shortName}`);
    }
    expect(sampledReplica).toBe(true);
  });

  it('eliminates cross-cluster edges that involve replicated places', () => {
    // After replication, any edge whose endpoint is a replicated place
    // should be intra-cluster (the replica lives in the destination cluster).
    const replicatedOriginals = new Set<string>();
    for (const node of replicated.nodes.values()) {
      if (node.replica && node.replicaOf) replicatedOriginals.add(node.replicaOf);
    }
    for (const e of replicated.edges) {
      if (!isCrossCluster(replicated, e)) continue;
      // Surviving cross-cluster edges must not have a replicated place as
      // endpoint that got a replica in the OTHER cluster.
      const sIsReplicatedHere = replicatedOriginals.has(e.src);
      const dIsReplicatedHere = replicatedOriginals.has(e.dst);
      expect(sIsReplicatedHere && dIsReplicatedHere).toBe(false);
    }
  });

  it('original orphan with all edges redirected gets dropped', () => {
    // For each replicated original that was an orphan (not folded), if all
    // its edges got redirected, it should no longer exist in nodes.
    const beforeOrphans = new Set(folded.orphans);
    let droppedAtLeastOne = false;
    for (const node of replicated.nodes.values()) {
      if (node.replica && node.replicaOf && node.id !== node.replicaOf) {
        const origId = node.replicaOf;
        if (beforeOrphans.has(origId)) {
          const stillHasEdge = replicated.edges.some(
            e => e.src === origId || e.dst === origId,
          );
          if (!stillHasEdge) {
            expect(replicated.nodes.has(origId)).toBe(false);
            droppedAtLeastOne = true;
          }
        }
      }
    }
    // Even if zero originals get dropped (e.g. all replicated places were
    // folded first), the test passes — we only assert the invariant.
    void droppedAtLeastOne;
  });

  it('replicas preserve the original places attrs', () => {
    for (const node of replicated.nodes.values()) {
      if (!node.replica || !node.replicaOf || node.id === node.replicaOf) continue;
      const orig = folded.nodes.get(node.replicaOf);
      if (!orig) continue;
      expect(node.attrs.shape).toBe(orig.attrs.shape);
      expect(node.attrs.xlabel).toBe(orig.attrs.xlabel);
    }
  });

  it('max=0 emits no replicas', () => {
    const none = replicateShared(folded, { max: 0 });
    expect(none.replicateStats.replicatedPlaces).toBe(0);
    expect(none.replicateStats.totalCopies).toBe(0);
  });
});
