import { describe, it, expect } from 'vitest';
import { mermaidExport, sanitize, minimalConfig, leftToRightConfig } from '../../src/export/mermaid-exporter.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one, exactly } from '../../src/core/in.js';
import { outPlace, andPlaces, xorPlaces, timeout } from '../../src/core/out.js';
import { delayed } from '../../src/core/timing.js';

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

describe('mermaidExport', () => {
  const p1 = place('Start');
  const p2 = place('End');

  it('generates flowchart header', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const result = mermaidExport(net);

    expect(result).toContain('flowchart TB');
    expect(result).toContain('layout: elk');
  });

  it('generates place nodes', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const result = mermaidExport(net);

    expect(result).toContain('Start(["Start"])');
    expect(result).toContain('End(["End"])');
  });

  it('generates transition node with timing', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .timing(delayed(500))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const result = mermaidExport(net);

    expect(result).toContain('t_Process["Process [500, ∞]ms"]');
  });

  it('generates solid input/output edges', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const result = mermaidExport(net);

    expect(result).toContain('Start --> t_Process');
    expect(result).toContain('t_Process --> End');
  });

  it('generates weighted input arcs', () => {
    const t = Transition.builder('Batch')
      .inputs(exactly(3, p1))
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const result = mermaidExport(net);

    expect(result).toContain('Start -->|×3| t_Batch');
  });

  it('generates inhibitor arcs', () => {
    const pause = place('Pause');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .inhibitor(pause)
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const result = mermaidExport(net);

    expect(result).toContain('Pause --o t_Process');
  });

  it('generates read arcs', () => {
    const config = place('Config');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .read(config)
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const result = mermaidExport(net);

    expect(result).toContain('Config -.->|read| t_Process');
  });

  it('generates reset arcs', () => {
    const cache = place('Cache');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .reset(cache)
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const result = mermaidExport(net);

    expect(result).toContain('t_Process ==>|reset| Cache');
  });

  it('generates XOR branch labels', () => {
    const success = place('Success');
    const error = place('Error');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(xorPlaces(success, error))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const result = mermaidExport(net);

    expect(result).toContain('|Success|');
    expect(result).toContain('|Error|');
  });

  it('generates timeout labels', () => {
    const success = place('Success');
    const timeoutP = place('Timeout');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(timeout(5000, outPlace(timeoutP)))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const result = mermaidExport(net);

    expect(result).toContain('⏱5000ms');
  });

  it('generates styles for start/end places', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const result = mermaidExport(net);

    expect(result).toContain('classDef startPlace');
    expect(result).toContain('classDef endPlace');
    expect(result).toContain('class Start startPlace');
    expect(result).toContain('class End endPlace');
  });

  it('generates XOR transition styling', () => {
    const success = place('Success');
    const error = place('Error');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(xorPlaces(success, error))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const result = mermaidExport(net);

    expect(result).toContain('classDef xorTransition');
    expect(result).toContain('class t_Process xorTransition');
  });

  it('minimal config hides details', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .timing(delayed(500))
      .priority(10)
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const result = mermaidExport(net, minimalConfig());

    expect(result).toContain('t_Process["Process"]');
    expect(result).not.toContain('[500');
    expect(result).not.toContain('prio');
  });

  it('left-to-right direction', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const result = mermaidExport(net, leftToRightConfig());

    expect(result).toContain('flowchart LR');
  });

  it('shows priority when non-zero', () => {
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .priority(10)
      .build();
    const net = PetriNet.builder('Test').transition(t).build();
    const result = mermaidExport(net);

    expect(result).toContain('prio=10');
  });
});
