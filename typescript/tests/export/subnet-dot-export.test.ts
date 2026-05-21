/**
 * DOT-cluster export tests per `spec/09-export.md` **EXP-016** and
 * `spec/11-modular-composition.md` **MOD-040**.
 *
 * These tests exercise the cluster grouping the {@link dotExport} pipeline
 * applies to nets produced via modular composition. They do not assert on
 * the cluster's visual styling beyond what the spec mandates (presence of
 * `subgraph cluster_<sanitizedPrefix>` blocks, correct membership, nested
 * structure).
 *
 * Mirrors `java/src/test/java/org/libpetri/export/SubnetDotExportTest.java`.
 */

import { describe, expect, it } from 'vitest';
import { dotExport } from '../../src/export/dot-exporter.js';
import { DEFAULT_DOT_CONFIG } from '../../src/export/petri-net-mapper.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, type Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { Interface } from '../../src/core/interface.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { producer, consumer } from '../fixtures/subnet-fixtures.js';

/** Index of the next occurrence of `needle` after `from`; fails the test if absent. */
function find(haystack: string, needle: string, from: number): number {
  const idx = haystack.indexOf(needle, from);
  if (idx < 0) {
    throw new Error(`expected to find '${needle}' starting at ${from} in:\n${haystack}`);
  }
  return idx;
}

describe('dotExport — subnet clusters (EXP-016 / MOD-040)', () => {
  // ============================================================
  //  EXP-016 AC#4: flat net produces no cluster blocks
  // ============================================================

  it('dotExport_flatNet_noClusters', () => {
    const pending = place<string>('Pending');
    const processed = place<string>('Processed');
    const process = Transition.builder('Process')
      .inputs(one(pending))
      .outputs(outPlace(processed))
      .build();
    const net = PetriNet.builder('FlatNet').transition(process).build();

    const dot = dotExport(net);

    expect(dot.includes('subgraph cluster_'))
      .toBe(false);
  });

  // ============================================================
  //  EXP-016 AC#1, AC#2: single instance produces one cluster
  // ============================================================

  it('dotExport_singleInstance_oneCluster', () => {
    const producerInst = producer().instantiate('producer1');
    const sink = place<string>('hostSink');

    const host = PetriNet.builder('Host')
      .place(sink)
      .compose(producerInst, { output: sink as Place<unknown> })
      .build();

    const dot = dotExport(host);

    // EXP-016 AC#1: cluster block present.
    expect(dot).toContain('subgraph cluster_producer1 {');

    // EXP-016 AC#2: cluster contains the renamed nodes (p_producer1_*
    // and t_producer1_*).
    const clusterStart = find(dot, 'subgraph cluster_producer1 {', 0);
    const clusterEnd = find(dot, '}', clusterStart);
    const clusterBody = dot.substring(clusterStart, clusterEnd);
    expect(clusterBody).toContain('p_producer1_nextItem');
    expect(clusterBody).toContain('t_producer1_produce');

    // The merged host place stays at the top level (its name has no '/').
    // It must appear OUTSIDE the cluster.
    const hostSinkIdx = dot.indexOf('p_hostSink');
    expect(hostSinkIdx).toBeGreaterThanOrEqual(0);
    expect(hostSinkIdx > clusterEnd || hostSinkIdx < clusterStart).toBe(true);
  });

  // ============================================================
  //  EXP-016 AC#1, AC#2: two top-level instances produce two clusters
  // ============================================================

  it('dotExport_twoInstances_twoSiblingClusters', () => {
    const producerDef = producer();
    const p1 = producerDef.instantiate('b1');
    const p2 = producerDef.instantiate('b2');
    const sink = place<string>('sink');

    const host = PetriNet.builder('TwoProducers')
      .place(sink)
      .compose(p1, { output: sink as Place<unknown> })
      .compose(p2, { output: sink as Place<unknown> })
      .build();

    const dot = dotExport(host);

    expect(dot).toContain('subgraph cluster_b1 {');
    expect(dot).toContain('subgraph cluster_b2 {');

    // Each cluster contains exactly its instance's renamed nodes.
    const b1Start = find(dot, 'subgraph cluster_b1 {', 0);
    const b1End = find(dot, '}', b1Start);
    const b1Body = dot.substring(b1Start, b1End);
    expect(b1Body).toContain('p_b1_nextItem');
    expect(b1Body).toContain('t_b1_produce');
    expect(b1Body.includes('p_b2_')).toBe(false);

    const b2Start = find(dot, 'subgraph cluster_b2 {', 0);
    const b2End = find(dot, '}', b2Start);
    const b2Body = dot.substring(b2Start, b2End);
    expect(b2Body).toContain('p_b2_nextItem');
    expect(b2Body).toContain('t_b2_produce');
    expect(b2Body.includes('p_b1_')).toBe(false);
  });

  // ============================================================
  //  EXP-016 AC#3 + MOD-013: nested instances produce nested clusters
  // ============================================================

  it('dotExport_nestedInstance_nestedClusters', () => {
    // Build a producer subnet, compose into an outer subnet (T), then
    // instantiate T with a top-level prefix. The flattened names should
    // contain "outer/inner/<...>" entries (per [MOD-013] prefix
    // concatenation), and the DOT export should produce nested clusters
    // cluster_outer { cluster_outer_inner }.
    const producerDef = producer();

    const outerOut = place<string>('out');
    const producerInner = producerDef.instantiate('inner');
    const outerSubnetBody = PetriNet.builder('OuterBody')
      .place(outerOut)
      .compose(producerInner, { output: outerOut as Place<unknown> })
      .build();
    const outerIface = Interface.builder()
      .outputPort('out', outerOut)
      .build();
    const outerDef = SubnetDef.fromNet(outerSubnetBody, outerIface);

    const hostSink = place<string>('hostSink');
    const outer = outerDef.instantiate('outer');
    const host = PetriNet.builder('Host')
      .place(hostSink)
      .compose(outer, { out: hostSink as Place<unknown> })
      .build();

    const dot = dotExport(host);

    // Outer cluster must be present.
    expect(dot).toContain('subgraph cluster_outer {');
    // Nested cluster id: sanitize("outer/inner") -> "outer_inner".
    expect(dot).toContain('subgraph cluster_outer_inner {');

    // Structural nesting: cluster_outer_inner block must appear inside the
    // cluster_outer block (the inner closing brace must be before
    // cluster_outer's closing brace).
    const outerStart = find(dot, 'subgraph cluster_outer {', 0);
    const innerStart = find(dot, 'subgraph cluster_outer_inner {', outerStart);
    const innerEnd = find(dot, '}', innerStart);
    const outerEnd = find(dot, '}', innerEnd + 1);
    expect(innerEnd).toBeLessThan(outerEnd);

    // Members: p_outer_inner_nextItem is the deepest leaf, must be in inner.
    const innerBody = dot.substring(innerStart, innerEnd);
    expect(innerBody).toContain('p_outer_inner_nextItem');
  });

  // ============================================================
  //  EXP-016 AC#5: cluster IDs match the sanitization regex
  // ============================================================

  it('dotExport_clusterIdsAreSanitized', () => {
    const producerDef = producer();
    const producerInner = producerDef.instantiate('inner');
    const outerOut = place<string>('out');
    const outerBody = PetriNet.builder('OuterBody')
      .place(outerOut)
      .compose(producerInner, { output: outerOut as Place<unknown> })
      .build();
    const outerIface = Interface.builder()
      .outputPort('out', outerOut)
      .build();
    const outerDef = SubnetDef.fromNet(outerBody, outerIface);
    const hostSink = place<string>('hostSink');
    const outer = outerDef.instantiate('outer');
    const host = PetriNet.builder('Host')
      .place(hostSink)
      .compose(outer, { out: hostSink as Place<unknown> })
      .build();

    const dot = dotExport(host);

    // No raw "cluster_outer/inner" leaked through (would be a sanitization bug).
    expect(dot.includes('cluster_outer/inner')).toBe(false);
  });

  // ============================================================
  //  EXP-016 (cross-cluster edges): edges between two prefixes live at top-level
  // ============================================================

  it('dotExport_edgeCrossesCluster_atTopLevel', () => {
    // Compose two instances wired through a top-level host place. Edges
    // between cluster contents and that host place are top-level so
    // Graphviz routes them between cluster boxes rather than inside one.
    const producerInst = producer().instantiate('prod');
    const consumerInst = consumer().instantiate('cons');
    const wire = place<string>('wire');

    const host = PetriNet.builder('PC')
      .place(wire)
      .compose(producerInst, { output: wire as Place<unknown> })
      .compose(consumerInst, { input: wire as Place<unknown> })
      .build();

    const dot = dotExport(host);

    // Locate cluster bodies.
    const prodStart = find(dot, 'subgraph cluster_prod {', 0);
    const prodEnd = find(dot, '}', prodStart);
    const prodBody = dot.substring(prodStart, prodEnd);

    const consStart = find(dot, 'subgraph cluster_cons {', 0);
    const consEnd = find(dot, '}', consStart);
    const consBody = dot.substring(consStart, consEnd);

    // The cross-cluster edges (t_prod_produce -> p_wire and p_wire ->
    // t_cons_consume) must NOT appear inside either cluster body.
    expect(prodBody.includes('p_wire')).toBe(false);
    expect(consBody.includes('p_wire')).toBe(false);

    // The edge t_prod_produce -> p_wire must appear OUTSIDE both clusters.
    const crossEdgeIdx = dot.indexOf('t_prod_produce -> p_wire');
    expect(crossEdgeIdx).toBeGreaterThanOrEqual(0);
    const inProdCluster = crossEdgeIdx > prodStart && crossEdgeIdx < prodEnd;
    const inConsCluster = crossEdgeIdx > consStart && crossEdgeIdx < consEnd;
    expect(inProdCluster).toBe(false);
    expect(inConsCluster).toBe(false);
  });

  // ============================================================
  //  MOD-026 / MOD-040: direct composition clusters by subnet name
  // ============================================================

  /** A producer whose output place is named `pipe` (wires by name). */
  function pipeProducer(): SubnetDef<void> {
    const seed = place<string>('seed');
    const pipe = place<string>('pipe');
    return SubnetDef.builder('PipeProducer')
      .place(seed)
      .place(pipe)
      .transition(Transition.builder('emit').inputs(one(seed)).outputs(outPlace(pipe)).build())
      .build();
  }

  /** A consumer whose input place is named `pipe` (wires by name). */
  function pipeConsumer(): SubnetDef<void> {
    const pipe = place<string>('pipe');
    const sink = place<string>('sink');
    return SubnetDef.builder('PipeConsumer')
      .place(pipe)
      .place(sink)
      .transition(Transition.builder('eat').inputs(one(pipe)).outputs(outPlace(sink)).build())
      .build();
  }

  it('dotExport_directComposed_clustersBySubnetName', () => {
    // MOD-026: a directly-composed net has no '/' prefixes, but the recorded
    // subnet-membership metadata lets the exporter cluster each subnet's
    // private nodes under cluster_<subnetName>.
    const net = PetriNet.builder('Pipeline')
      .compose(pipeProducer())
      .compose(pipeConsumer())
      .build();

    const dot = dotExport(net);

    expect(dot).toContain('subgraph cluster_PipeProducer {');
    expect(dot).toContain('subgraph cluster_PipeConsumer {');

    const prodStart = find(dot, 'subgraph cluster_PipeProducer {', 0);
    const prodEnd = find(dot, '}', prodStart);
    const prodBody = dot.substring(prodStart, prodEnd);
    expect(prodBody).toContain('p_seed');
    expect(prodBody).toContain('t_emit');

    const consStart = find(dot, 'subgraph cluster_PipeConsumer {', 0);
    const consEnd = find(dot, '}', consStart);
    const consBody = dot.substring(consStart, consEnd);
    expect(consBody).toContain('p_sink');
    expect(consBody).toContain('t_eat');

    // The shared 'pipe' place has no single owner — it must render at the top
    // level, outside both clusters.
    expect(prodBody.includes('p_pipe')).toBe(false);
    expect(consBody.includes('p_pipe')).toBe(false);
  });

  it('dotExport_directComposed_clusterSourcePrefix_ignoresMetadata', () => {
    // ClusterSource 'prefix' clusters only by '/' name segments; a
    // direct-composed net has none, so no clusters are emitted.
    const net = PetriNet.builder('Pipeline')
      .compose(pipeProducer())
      .compose(pipeConsumer())
      .build();

    const dot = dotExport(net, { ...DEFAULT_DOT_CONFIG, clusterSource: 'prefix' });

    expect(dot.includes('subgraph cluster_')).toBe(false);
  });

  it('dotExport_clusterSourceNone_suppressesAllClusters', () => {
    // ClusterSource 'none' suppresses clustering even for a prefix-
    // instantiated net that would otherwise cluster.
    const producerInst = producer().instantiate('producer1');
    const sink = place<string>('hostSink');
    const host = PetriNet.builder('Host')
      .place(sink)
      .compose(producerInst, { output: sink as Place<unknown> })
      .build();

    const dot = dotExport(host, { ...DEFAULT_DOT_CONFIG, clusterSource: 'none' });

    expect(dot.includes('subgraph cluster_')).toBe(false);
  });

  // ============================================================
  //  MOD-040 / EXP-016 AC#7: mixed direct + instance composition
  // ============================================================

  it('dotExport_mixedDirectAndInstance_bothClusterKinds', () => {
    // MOD-040 AC#7: a net that both directly composes a subnet and instance-
    // composes another carries metadata for the direct nodes and '/' prefixes
    // for the instance nodes. Under the default 'auto' source the exporter
    // clusters direct nodes by subnet name and instance nodes by prefix —
    // both cluster kinds coexist.
    const producerInst = producer().instantiate('inst1');
    const hostSink = place<string>('hostSink');

    const net = PetriNet.builder('Mixed')
      .place(hostSink)
      .compose(pipeProducer())
      .compose(producerInst, { output: hostSink as Place<unknown> })
      .build();

    const dot = dotExport(net);

    // Direct-composed subnet → metadata cluster keyed by subnet name.
    expect(dot).toContain('subgraph cluster_PipeProducer {');
    // Instance-composed subnet → prefix cluster keyed by instance prefix.
    expect(dot).toContain('subgraph cluster_inst1 {');

    const metaStart = find(dot, 'subgraph cluster_PipeProducer {', 0);
    const metaEnd = find(dot, '}', metaStart);
    const metaBody = dot.substring(metaStart, metaEnd);
    expect(metaBody).toContain('p_seed');
    expect(metaBody).toContain('t_emit');
    expect(metaBody.includes('inst1')).toBe(false);

    const instStart = find(dot, 'subgraph cluster_inst1 {', 0);
    const instEnd = find(dot, '}', instStart);
    const instBody = dot.substring(instStart, instEnd);
    expect(instBody).toContain('p_inst1_nextItem');
    expect(instBody).toContain('t_inst1_produce');
  });

  // ============================================================
  //  MOD-040 / EXP-016: ClusterSource 'metadata' is strict (no fallback)
  // ============================================================

  it('dotExport_clusterSourceMetadata_ignoresPrefixOnlyNet', () => {
    // ClusterSource 'metadata' clusters strictly from subnet-membership
    // metadata. An instance-composed net carries no metadata — only '/'
    // prefixes — so 'metadata' emits no clusters at all. This is what
    // distinguishes 'metadata' from 'auto', which would cluster by prefix.
    const producerInst = producer().instantiate('producer1');
    const sink = place<string>('hostSink');
    const host = PetriNet.builder('Host')
      .place(sink)
      .compose(producerInst, { output: sink as Place<unknown> })
      .build();

    const dot = dotExport(host, { ...DEFAULT_DOT_CONFIG, clusterSource: 'metadata' });

    expect(dot.includes('subgraph cluster_')).toBe(false);
  });
});
