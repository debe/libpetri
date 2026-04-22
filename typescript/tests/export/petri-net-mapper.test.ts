import { describe, it, expect } from 'vitest';
import { mapToGraph, sanitize, DEFAULT_DOT_CONFIG } from '../../src/export/petri-net-mapper.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one, exactly, all, atLeast } from '../../src/core/in.js';
import { outPlace, andPlaces, xorPlaces, timeout, forwardInput } from '../../src/core/out.js';
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
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('TestNet').transition(t).build();
    const graph = mapToGraph(net);

    expect(graph.id).toBe('TestNet');
    expect(graph.rankdir).toBe('TB');
  });

  it('creates place nodes with p_ prefix', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outPlace(p2))
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
      .outputs(outPlace(p2))
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
      .outputs(outPlace(p2))
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
      .outputs(outPlace(p2))
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
      .outputs(outPlace(p2))
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
      .outputs(outPlace(p2))
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
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const inputEdge = graph.edges.find(e => e.from === 'p_Start' && e.to === 't_Batch');
    expect(inputEdge!.label).toBe('\u00d73');
  });

  it('generates input edges with * label for all()', () => {
    const t = Transition.builder('Drain')
      .inputs(all(p1))
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const inputEdge = graph.edges.find(e => e.from === 'p_Start');
    expect(inputEdge!.label).toBe('*');
  });

  it('generates input edges with >= label for atLeast()', () => {
    const t = Transition.builder('Accumulate')
      .inputs(atLeast(5, p1))
      .outputs(outPlace(p2))
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
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const outputEdge = graph.edges.find(e => e.from === 't_Process' && e.to === 'p_End');
    expect(outputEdge).toBeDefined();
    expect(outputEdge!.arcType).toBe('output');
  });

  it('generates AND output edges (all children)', () => {
    const p3 = place('Middle');
    const t = Transition.builder('Fork')
      .inputs(one(p1))
      .outputs(andPlaces(p2, p3))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const outEdges = graph.edges.filter(e => e.from === 't_Fork' && e.arcType === 'output');
    expect(outEdges).toHaveLength(2);
  });

  it('generates XOR output edges with branch labels', () => {
    const success = place('Success');
    const error = place('Error');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(xorPlaces(success, error))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    const successEdge = graph.edges.find(e => e.to === 'p_Success');
    const errorEdge = graph.edges.find(e => e.to === 'p_Error');
    expect(successEdge!.label).toBe('Success');
    expect(errorEdge!.label).toBe('Error');
  });

  it('generates timeout output edges', () => {
    const timeoutP = place('Timeout');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(timeout(5000, outPlace(timeoutP)))
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
      .outputs(outPlace(p2))
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
      .outputs(outPlace(p2))
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
      .outputs(outPlace(p2))
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
      .outputs(outPlace(p2))
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
      .outputs(outPlace(p2))
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
      .outputs(outPlace(p2))
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
      .outputs(outPlace(p2))
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
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net, { ...DEFAULT_DOT_CONFIG, direction: 'LR' });

    expect(graph.rankdir).toBe('LR');
  });

  it('sets graph font and spacing attributes', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const graph = mapToGraph(net);

    expect(graph.graphAttrs['nodesep']).toBe('0.5');
    expect(graph.graphAttrs['ranksep']).toBe('0.75');
    expect(graph.graphAttrs['outputorder']).toBe('edgesfirst');
    expect(graph.graphAttrs['splines']).toBe('curved');
    expect(graph.nodeDefaults['fontname']).toBeDefined();
  });
});
