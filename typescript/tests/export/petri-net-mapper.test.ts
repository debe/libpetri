import { describe, it, expect } from 'vitest';
import { mapToGraph, sanitize, DEFAULT_DOT_CONFIG } from '../../src/export/petri-net-mapper.js';
import { dotExport } from '../../src/export/dot-exporter.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one, exactly, all, atLeast } from '../../src/core/in.js';
import { outOne, outExactly, andPlaces, xorPlaces, and, xor, timeout, forwardInput } from '../../src/core/out.js';
import { delayed, window } from '../../src/core/timing.js';

describe('sanitize', () => {
  it('keeps alphanumeric and underscores', () => {
    expect(sanitize('hello_world')).toBe('hello_world');
  });

  it('replaces special characters', () => {
    expect(sanitize('my-place.name')).toBe('my_place_name');
  });

  it('replaces spaces', () => {
    expect(sanitize('Place Name')).toBe('Place_Name');
  });
});

describe('mapToGraph', () => {
  const p1 = place('Start');
  const p2 = place('End');

  it('creates graph with correct id and rankdir', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .build();
    const net = PetriNet.builder('TestNet').transition(t).build();
    const graph = mapToGraph(net);

    expect(graph.id).toBe('TestNet');
    expect(graph.rankdir).toBe('TB');
  });

  it('creates place nodes with p_ prefix', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const startNode = graph.nodes.find(n => n.id === 'p_Start');
    expect(startNode).toBeDefined();
    expect(startNode!.label).toBe('');
    expect(startNode!.shape).toBe('circle');
    expect(startNode!.semanticId).toBe('Start');
    expect(startNode!.attrs?.xlabel).toBe('Start');
    expect(startNode!.attrs?.fixedsize).toBe('true');
    expect(startNode!.width).toBe(0.35);
  });

  it('creates transition nodes with t_ prefix', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const transNode = graph.nodes.find(n => n.id === 't_Process');
    expect(transNode).toBeDefined();
    expect(transNode!.label).toContain('Process');
    expect(transNode!.shape).toBe('box');
    expect(transNode!.semanticId).toBe('Process');
  });

  it('styles start places (no incoming arcs)', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const startNode = graph.nodes.find(n => n.id === 'p_Start');
    expect(startNode!.fill).toBe('#d4edda');
    expect(startNode!.stroke).toBe('#28a745');
  });

  it('styles end places (no outgoing arcs)', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const endNode = graph.nodes.find(n => n.id === 'p_End');
    expect(endNode!.fill).toBe('#cce5ff');
    expect(endNode!.stroke).toBe('#004085');
  });

  it('styles environment places with dashed border', () => {
    const envPlace = place('Events');
    const t = Transition.builder('Process')
      .inputs(one(envPlace))
      .outputs(outOne(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net, {
      ...DEFAULT_DOT_CONFIG,
      environmentPlaces: new Set(['Events']),
    });

    const envNode = graph.nodes.find(n => n.id === 'p_Events');
    expect(envNode!.fill).toBe('#f8d7da');
    expect(envNode!.stroke).toBe('#721c24');
    expect(envNode!.style).toBe('dashed');
  });

  // Input arcs
  it('generates input edges for one()', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const inputEdge = graph.edges.find(e => e.from === 'p_Start' && e.to === 't_Process');
    expect(inputEdge).toBeDefined();
    expect(inputEdge!.arcType).toBe('input');
    expect(inputEdge!.label).toBeUndefined();
  });

  it('generates input edges with cardinality label for exactly()', () => {
    const t = Transition.builder('Batch')
      .inputs(exactly(3, p1))
      .outputs(outOne(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const inputEdge = graph.edges.find(e => e.from === 'p_Start' && e.to === 't_Batch');
    expect(inputEdge!.label).toBe('\u00d73');
  });

  it('generates input edges with * label for all()', () => {
    const t = Transition.builder('Drain')
      .inputs(all(p1))
      .outputs(outOne(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const inputEdge = graph.edges.find(e => e.from === 'p_Start');
    expect(inputEdge!.label).toBe('*');
  });

  it('generates input edges with >= label for atLeast()', () => {
    const t = Transition.builder('Accumulate')
      .inputs(atLeast(5, p1))
      .outputs(outOne(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const inputEdge = graph.edges.find(e => e.from === 'p_Start');
    expect(inputEdge!.label).toBe('\u22655');
  });

  // Output arcs
  it('generates output edges', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const outputEdge = graph.edges.find(e => e.from === 't_Process' && e.to === 'p_End');
    expect(outputEdge).toBeDefined();
    expect(outputEdge!.arcType).toBe('output');
  });

  it('generates AND junction with edges to all children', () => {
    const p3 = place('Middle');
    const t = Transition.builder('Fork')
      .inputs(one(p1))
      .outputs(andPlaces(p2, p3))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    // One AND junction node — diamond gateway: heavy '✚' label, white fill
    const junction = graph.nodes.find(n => n.id.startsWith('j_Fork__and_'));
    expect(junction).toBeDefined();
    expect(junction!.shape).toBe('diamond');
    expect(junction!.label).toBe('✚');
    expect(junction!.fill).toBe('#FFFFFF');
    expect(junction!.stroke).toBe('#333333');
    expect(junction!.attrs?.fontsize).toBe('14');
    expect(junction!.width).toBe(0.3);

    // T → junction (one edge), junction → each child (two edges, no labels)
    const tToJ = graph.edges.filter(e => e.from === 't_Fork' && e.to === junction!.id);
    expect(tToJ).toHaveLength(1);
    const jToChildren = graph.edges.filter(e => e.from === junction!.id && e.arcType === 'output');
    expect(jToChildren).toHaveLength(2);
    for (const e of jToChildren) {
      expect(e.label).toBeUndefined();
    }
  });

  it('generates XOR junction with per-branch labels on junction→child edges', () => {
    const success = place('Success');
    const error = place('Error');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(xorPlaces(success, error))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const junction = graph.nodes.find(n => n.id.startsWith('j_Process__xor_'));
    expect(junction).toBeDefined();
    expect(junction!.shape).toBe('diamond');
    expect(junction!.label).toBe('✕');
    expect(junction!.fill).toBe('#FFFFFF');
    expect(junction!.attrs?.fontsize).toBe('14');

    // T → junction has no branch label
    const tToJ = graph.edges.find(e => e.from === 't_Process' && e.to === junction!.id);
    expect(tToJ!.label).toBeUndefined();

    // junction → child carries the place name as the branch label
    const successEdge = graph.edges.find(e => e.to === 'p_Success');
    const errorEdge = graph.edges.find(e => e.to === 'p_Error');
    expect(successEdge!.from).toBe(junction!.id);
    expect(errorEdge!.from).toBe(junction!.id);
    expect(successEdge!.label).toBe('Success');
    expect(errorEdge!.label).toBe('Error');
  });

  it('collapses single-child XOR/AND: no junction emitted', () => {
    const p_only = place('Only');
    // Note: xor() requires ≥2 children; constructor refuses single-child XOR.
    // AND with one child is allowed by the core API.
    const tAnd = Transition.builder('SingleAnd')
      .inputs(one(p1))
      .outputs(andPlaces(p_only))
      .build();
    const net = PetriNet.builder('Test').transition(tAnd).build();
    const graph = mapToGraph(net);

    const junctions = graph.nodes.filter(n => n.id.startsWith('j_'));
    expect(junctions).toHaveLength(0);

    // Single direct edge transition → place
    const directEdge = graph.edges.find(e => e.from === 't_SingleAnd' && e.to === 'p_Only');
    expect(directEdge).toBeDefined();
    expect(directEdge!.arcType).toBe('output');
  });

  it('combines reset+output into a single styled edge', () => {
    const cache = place('Cache');
    const t = Transition.builder('Refresh')
      .inputs(one(p1))
      .outputs(outOne(cache))
      .reset(cache)
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    // Exactly one edge to p_Cache, and it's the combined reset-output style
    const edgesToCache = graph.edges.filter(e => e.to === 'p_Cache');
    expect(edgesToCache).toHaveLength(1);
    const combined = edgesToCache[0]!;
    expect(combined.arcType).toBe('reset-output');
    expect(combined.label).toBe('reset+out');
    expect(combined.color).toBe('#fd7e14');
    expect(combined.style).toBe('bold');
    expect(combined.penwidth).toBe(2.0);

    // No standalone reset edge for this place
    const standaloneReset = graph.edges.find(e => e.arcType === 'reset' && e.to === 'p_Cache');
    expect(standaloneReset).toBeUndefined();
  });

  it('keeps standalone reset+output combination distinct from non-combined reset', () => {
    // Transition with reset(P) + output(P) AND a standalone reset to a different place.
    const cache = place('Cache');
    const tmp = place('Tmp');
    const t = Transition.builder('Mixed')
      .inputs(one(p1))
      .outputs(outOne(cache))
      .reset(cache)
      .reset(tmp)
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const cacheEdges = graph.edges.filter(e => e.to === 'p_Cache');
    expect(cacheEdges).toHaveLength(1);
    expect(cacheEdges[0]!.arcType).toBe('reset-output');

    const tmpEdges = graph.edges.filter(e => e.to === 'p_Tmp');
    expect(tmpEdges).toHaveLength(1);
    expect(tmpEdges[0]!.arcType).toBe('reset');
    expect(tmpEdges[0]!.label).toBe('reset');
  });

  it('combines reset+output through XOR junction (junction→child gets reset style)', () => {
    const ok = place('Ok');
    const cache = place('Cache');
    const t = Transition.builder('Try')
      .inputs(one(p1))
      .outputs(xorPlaces(ok, cache))
      .reset(cache)
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const junction = graph.nodes.find(n => n.id.startsWith('j_Try__xor_'));
    expect(junction).toBeDefined();

    // junction → Cache is the combined reset+out edge
    const toCache = graph.edges.find(e => e.to === 'p_Cache');
    expect(toCache!.from).toBe(junction!.id);
    expect(toCache!.arcType).toBe('reset-output');
    expect(toCache!.label).toBe('reset+out');

    // junction → Ok is plain output
    const toOk = graph.edges.find(e => e.to === 'p_Ok');
    expect(toOk!.arcType).toBe('output');
    expect(toOk!.label).toBe('Ok');
  });

  it('uses deterministic junction IDs in depth-first order', () => {
    const a = place('A');
    const b = place('B');
    const c = place('C');
    const d = place('D');
    // AND( XOR(A, B), XOR(C, D) ) → root AND junction + two nested XOR junctions
    const t = Transition.builder('Nested')
      .inputs(one(p1))
      .outputs(and(
        xor(outOne(a), outOne(b)),
        xor(outOne(c), outOne(d)),
      ))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const junctions = graph.nodes
      .filter(n => n.id.startsWith('j_Nested__'))
      .map(n => n.id);
    // AND_0 emitted first, then XOR_1, then XOR_2
    expect(junctions).toEqual([
      'j_Nested__and_0',
      'j_Nested__xor_1',
      'j_Nested__xor_2',
    ]);
  });

  // EXP-014 AC#2: repeated exports of the same net produce byte-identical DOT.
  it('produces byte-identical DOT for repeated exports', () => {
    const a = place('A');
    const b = place('B');
    const c = place('C');
    const d = place('D');
    const cache = place('Cache');

    // Nested junctions + reset+output covers the full range of EXP-012/013/014 paths.
    const nested = Transition.builder('Nested')
      .inputs(one(p1))
      .outputs(and(
        xor(outOne(a), outOne(b)),
        xor(outOne(c), outOne(d)),
      ))
      .build();
    const refresh = Transition.builder('RefreshCache')
      .inputs(one(a))
      .outputs(outOne(cache))
      .reset(cache)
      .build();
    const net = PetriNet.builder('Stable').transition(nested).transition(refresh).build();

    const first = dotExport(net);
    const second = dotExport(net);
    expect(second).toBe(first);
  });

  it('generates timeout output edges', () => {
    const timeoutP = place('Timeout');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(timeout(5000, outOne(timeoutP)))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const timeoutEdge = graph.edges.find(e => e.to === 'p_Timeout');
    expect(timeoutEdge!.label).toContain('5000ms');
  });

  it('generates forward-input output edges', () => {
    const retryPlace = place('Retry');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(timeout(5000, forwardInput(p1, retryPlace)))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const fwdEdge = graph.edges.find(e => e.to === 'p_Retry');
    expect(fwdEdge).toBeDefined();
    expect(fwdEdge!.label).toContain('Start');
    expect(fwdEdge!.style).toBe('dashed');
  });

  // Control arcs
  it('generates inhibitor edges with odot arrowhead', () => {
    const pause = place('Pause');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .inhibitor(pause)
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const inhEdge = graph.edges.find(e => e.arcType === 'inhibitor');
    expect(inhEdge).toBeDefined();
    expect(inhEdge!.from).toBe('p_Pause');
    expect(inhEdge!.to).toBe('t_Process');
    expect(inhEdge!.arrowhead).toBe('odot');
    expect(inhEdge!.color).toBe('#dc3545');
  });

  it('generates read edges with dashed style', () => {
    const config = place('Config');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .read(config)
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const readEdge = graph.edges.find(e => e.arcType === 'read');
    expect(readEdge).toBeDefined();
    expect(readEdge!.style).toBe('dashed');
    expect(readEdge!.label).toBe('read');
    expect(readEdge!.color).toBe('#6c757d');
  });

  it('generates reset edges with bold style', () => {
    const cache = place('Cache');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .reset(cache)
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const resetEdge = graph.edges.find(e => e.arcType === 'reset');
    expect(resetEdge).toBeDefined();
    expect(resetEdge!.from).toBe('t_Process');
    expect(resetEdge!.to).toBe('p_Cache');
    expect(resetEdge!.style).toBe('bold');
    expect(resetEdge!.label).toBe('reset');
    expect(resetEdge!.color).toBe('#fd7e14');
    expect(resetEdge!.penwidth).toBe(2.0);
  });

  // XOR transition styling — uses standard box shape like all transitions
  it('styles XOR transitions with box shape', () => {
    const success = place('Success');
    const error = place('Error');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(xorPlaces(success, error))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const transNode = graph.nodes.find(n => n.id === 't_Process');
    expect(transNode!.shape).toBe('box');
    expect(transNode!.fill).toBe('#fff3cd');
  });

  // Transition labels
  it('includes timing interval in transition label', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .timing(delayed(500))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const transNode = graph.nodes.find(n => n.id === 't_Process');
    expect(transNode!.label).toContain('[500, \u221e]ms');
  });

  it('includes timing window in transition label', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .timing(window(100, 2000))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const transNode = graph.nodes.find(n => n.id === 't_Process');
    expect(transNode!.label).toContain('[100, 2000]ms');
  });

  it('includes priority in transition label', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .priority(10)
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const transNode = graph.nodes.find(n => n.id === 't_Process');
    expect(transNode!.label).toContain('prio=10');
  });

  it('omits timing and priority when config says so', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .timing(delayed(500))
      .priority(10)
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net, {
      direction: 'TB',
      showTypes: false,
      showIntervals: false,
      showPriority: false,
    });

    const transNode = graph.nodes.find(n => n.id === 't_Process');
    expect(transNode!.label).toBe('Process');
  });

  // Config
  it('respects direction config', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net, { ...DEFAULT_DOT_CONFIG, direction: 'LR' });

    expect(graph.rankdir).toBe('LR');
  });

  it('sets graph font and spacing attributes', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outOne(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    expect(graph.graphAttrs['nodesep']).toBe('0.5');
    expect(graph.graphAttrs['ranksep']).toBe('0.75');
    expect(graph.graphAttrs['outputorder']).toBe('edgesfirst');
    expect(graph.nodeDefaults['fontname']).toBeDefined();
  });
});
