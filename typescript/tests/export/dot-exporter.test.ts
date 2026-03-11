import { describe, it, expect } from 'vitest';
import { dotExport } from '../../src/export/dot-exporter.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one, exactly } from '../../src/core/in.js';
import { outPlace, andPlaces, xorPlaces, timeout } from '../../src/core/out.js';
import { delayed } from '../../src/core/timing.js';

describe('dotExport', () => {
  it('produces valid DOT for a simple net', () => {
    const p1 = place('Start');
    const p2 = place('End');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('SimpleNet').transition(t).build();

    const dot = dotExport(net);

    expect(dot).toContain('digraph SimpleNet {');
    expect(dot).toContain('rankdir=TB;');
    expect(dot).toContain('p_Start [');
    expect(dot).toContain('p_End [');
    expect(dot).toContain('t_Process [');
    expect(dot).toContain('p_Start -> t_Process');
    expect(dot).toContain('t_Process -> p_End');
    expect(dot).toContain('}');
  });

  it('contains circle shapes for places and box for transitions', () => {
    const p1 = place('In');
    const p2 = place('Out');
    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();

    const dot = dotExport(net);

    // Places are circles with xlabel and fixedsize
    expect(dot).toMatch(/p_In \[.*shape="circle"/);
    expect(dot).toMatch(/p_In \[.*label=""/);
    expect(dot).toMatch(/p_In \[.*xlabel="In"/);
    expect(dot).toMatch(/p_In \[.*fixedsize="true"/);
    expect(dot).toMatch(/p_Out \[.*shape="doublecircle"/);
    // Transitions are boxes
    expect(dot).toMatch(/t_T \[.*shape="box"/);
  });

  it('handles a net with all 5 arc types', () => {
    const input = place('Input');
    const output = place('Output');
    const blocker = place('Blocker');
    const config = place('Config');
    const cache = place('Cache');

    const t = Transition.builder('Process')
      .inputs(one(input))
      .outputs(outPlace(output))
      .inhibitor(blocker)
      .read(config)
      .reset(cache)
      .build();
    const net = PetriNet.builder('AllArcs').transition(t).build();

    const dot = dotExport(net);

    // Input arc
    expect(dot).toContain('p_Input -> t_Process');
    // Output arc
    expect(dot).toContain('t_Process -> p_Output');
    // Inhibitor arc (odot arrowhead)
    expect(dot).toMatch(/p_Blocker -> t_Process.*arrowhead="odot"/);
    // Read arc (dashed)
    expect(dot).toMatch(/p_Config -> t_Process.*style="dashed"/);
    // Reset arc (bold)
    expect(dot).toMatch(/t_Process -> p_Cache.*style="bold"/);
  });

  it('handles XOR outputs with branch labels', () => {
    const start = place('Start');
    const success = place('Success');
    const error = place('Error');
    const t = Transition.builder('Process')
      .inputs(one(start))
      .outputs(xorPlaces(success, error))
      .build();
    const net = PetriNet.builder('XorNet').transition(t).build();

    const dot = dotExport(net);

    expect(dot).toContain('label="Success"');
    expect(dot).toContain('label="Error"');
    // XOR transitions use standard box shape
    expect(dot).toMatch(/t_Process \[.*shape="box"/);
  });

  it('handles weighted input arcs', () => {
    const start = place('Start');
    const end = place('End');
    const t = Transition.builder('Batch')
      .inputs(exactly(3, start))
      .outputs(outPlace(end))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();

    const dot = dotExport(net);

    expect(dot).toContain('\u00d73');
  });

  it('includes timing in transition labels', () => {
    const p1 = place('Start');
    const p2 = place('End');
    const t = Transition.builder('Process')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .timing(delayed(500))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();

    const dot = dotExport(net);

    expect(dot).toContain('[500');
  });

  it('handles timeout outputs', () => {
    const start = place('Start');
    const timeoutP = place('Timeout');
    const t = Transition.builder('Process')
      .inputs(one(start))
      .outputs(timeout(5000, outPlace(timeoutP)))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();

    const dot = dotExport(net);

    expect(dot).toContain('5000ms');
  });

  it('respects config direction', () => {
    const p1 = place('Start');
    const p2 = place('End');
    const t = Transition.builder('T')
      .inputs(one(p1))
      .outputs(outPlace(p2))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();

    const dot = dotExport(net, { direction: 'LR', showTypes: true, showIntervals: true, showPriority: true });

    expect(dot).toContain('rankdir=LR;');
  });

  it('renders environment places with dashed style', () => {
    const envPlace = place('Events');
    const output = place('Out');
    const t = Transition.builder('T')
      .inputs(one(envPlace))
      .outputs(outPlace(output))
      .build();
    const net = PetriNet.builder('Test').transition(t).build();

    const dot = dotExport(net, {
      direction: 'TB',
      showTypes: true,
      showIntervals: true,
      showPriority: true,
      environmentPlaces: new Set(['Events']),
    });

    expect(dot).toMatch(/p_Events \[.*style="filled,dashed"/);
    expect(dot).toMatch(/p_Events \[.*fillcolor="#f8d7da"/);
  });

  it('handles multi-transition net', () => {
    const pending = place('Pending');
    const validated = place('Validated');
    const processed = place('Processed');

    const validate = Transition.builder('Validate')
      .inputs(one(pending))
      .outputs(outPlace(validated))
      .build();
    const process = Transition.builder('Process')
      .inputs(one(validated))
      .outputs(outPlace(processed))
      .build();

    const net = PetriNet.builder('Pipeline')
      .transitions(validate, process)
      .build();

    const dot = dotExport(net);

    expect(dot).toContain('p_Pending');
    expect(dot).toContain('p_Validated');
    expect(dot).toContain('p_Processed');
    expect(dot).toContain('t_Validate');
    expect(dot).toContain('t_Process');
  });
});
