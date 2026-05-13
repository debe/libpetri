import { describe, it, expect } from 'vitest';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { Interface } from '../../src/core/interface.js';
import type { Subnet } from '../../src/core/subnet.js';
import { closedSubnet, openSubnet } from '../../src/core/subnet.js';

interface Item {
  readonly tag: string;
}

describe('SubnetDef', () => {
  // ============================================================
  //  MOD-001: definition + accessors
  // ============================================================

  it('builder produces SubnetDef with name, body, iface', () => {
    const input = place<Item>('incoming');
    const output = place<Item>('outgoing');

    const t = Transition.builder('forward')
      .inputs(one(input))
      .outputs(outPlace(output))
      .build();

    const def = SubnetDef.builder('Forwarder')
      .transition(t)
      .inputPort('in', input)
      .outputPort('out', output)
      .build();

    expect(def.name).toBe('Forwarder');
    expect(def.body).toBeDefined();
    expect(def.iface).toBeDefined();
    expect(def.body.places.has(input)).toBe(true);
    expect(def.body.places.has(output)).toBe(true);
    expect(def.body.transitions.size).toBe(1);
  });

  // ============================================================
  //  MOD-003: ports declared via builder end up on the Interface
  // ============================================================

  it('input/output/inout ports appear on Interface', () => {
    const inP = place<Item>('in_p');
    const outP = place<Item>('out_p');
    const ioP = place<Item>('io_p');

    // Single transition references all three places so they're auto-collected
    // into the body via PetriNetBuilder.transition.
    const wire = Transition.builder('wire')
      .inputs(one(inP))
      .read(ioP)
      .outputs(outPlace(outP))
      .build();

    const def = SubnetDef.builder('Triple')
      .transition(wire)
      .inputPort('in', inP)
      .outputPort('out', outP)
      .inoutPort('io', ioP)
      .build();

    const iface = def.iface;
    expect(iface.ports.size).toBe(3);

    expect(iface.port('in')?.direction).toBe('input');
    expect(iface.port('out')?.direction).toBe('output');
    expect(iface.port('io')?.direction).toBe('inout');

    expect(iface.port('in')?.place).toBe(inP);
    expect(iface.port('out')?.place).toBe(outP);
    expect(iface.port('io')?.place).toBe(ioP);
  });

  // ============================================================
  //  MOD-005: channels declared via builder end up on the Interface
  // ============================================================

  it('channel declared appears on Interface', () => {
    const p = place<Item>('p');
    const attempt = Transition.builder('attempt').read(p).build();

    const def = SubnetDef.builder('RetryPolicy')
      .transition(attempt)
      .channel('attempt', attempt)
      .build();

    const ch = def.iface.channel('attempt');
    expect(ch).toBeDefined();
    expect(ch?.transition).toBe(attempt);
  });

  // ============================================================
  //  MOD-006: validation rejections
  // ============================================================

  it('build rejects port place not in body', () => {
    const bodyPlace = place<Item>('inBody');
    const stranger = place<Item>('stranger');

    const t = Transition.builder('op').read(bodyPlace).build();

    expect(() =>
      SubnetDef.builder('Bad')
        .transition(t)
        .inputPort('ghost', stranger)
        .build(),
    ).toThrow(/ghost|stranger/);
  });

  it('build rejects channel transition not in body', () => {
    const p = place<Item>('p');
    const inBody = Transition.builder('real').read(p).build();
    const outOfBody = Transition.builder('ghost').read(p).build();

    expect(() =>
      SubnetDef.builder('Bad')
        .transition(inBody)
        .channel('ghost', outOfBody)
        .build(),
    ).toThrow(/ghost/);
  });

  it('build rejects duplicate port name within port namespace', () => {
    const p1 = place<Item>('p1');
    const p2 = place<Item>('p2');

    expect(() =>
      SubnetDef.builder('Bad')
        .inputPort('dup', p1)
        .outputPort('dup', p2)
        .build(),
    ).toThrow(/dup/);
  });

  it('build rejects duplicate channel name within channel namespace', () => {
    const p = place<Item>('p');
    const t1 = Transition.builder('t1').read(p).build();
    const t2 = Transition.builder('t2').read(p).build();

    expect(() =>
      SubnetDef.builder('Bad')
        .transitions(t1, t2)
        .channel('ch', t1)
        .channel('ch', t2)
        .build(),
    ).toThrow(/ch/);
  });

  // ============================================================
  //  MOD-014: fromNet retrofit factory
  // ============================================================

  it('fromNet produces SubnetDef whose body equals input net', () => {
    const a = place<Item>('a');
    const b = place<Item>('b');
    const t = Transition.builder('t')
      .inputs(one(a))
      .outputs(outPlace(b))
      .build();

    const net = PetriNet.builder('Original').transition(t).build();

    const iface = Interface.builder()
      .inputPort('in', a)
      .build();

    const def = SubnetDef.fromNet(net, iface);

    expect(def.body).toBe(net);
    expect(def.iface).toBe(iface);
    expect(def.name).toBe('Original');
  });

  it('fromNet validates port place membership (MOD-014)', () => {
    const a = place<Item>('a');
    const stranger = place<Item>('stranger');
    const t = Transition.builder('t').read(a).build();
    const net = PetriNet.builder('N').transition(t).build();

    const iface = Interface.builder()
      .inputPort('ghost', stranger)
      .build();

    expect(() => SubnetDef.fromNet(net, iface)).toThrow(/ghost|stranger/);
  });

  it('fromNet validates channel transition membership (MOD-014)', () => {
    const a = place<Item>('a');
    const inNet = Transition.builder('inNet').read(a).build();
    const outOfNet = Transition.builder('outOfNet').read(a).build();
    const net = PetriNet.builder('N').transition(inNet).build();

    const iface = Interface.builder()
      .channel('orphan', outOfNet)
      .build();

    expect(() => SubnetDef.fromNet(net, iface)).toThrow(/orphan/);
  });

  // ============================================================
  //  MOD-051: verify(harness) is implemented in task #15
  //  (See tests/verification/subnet-verify.test.ts for full coverage.)
  // ============================================================

  it('verify is callable (real implementation; full coverage in subnet-verify.test.ts)', async () => {
    const p = place<Item>('p');
    const t = Transition.builder('t').read(p).build();
    const def = SubnetDef.builder('S').transition(t).build();

    // No ports, no properties — the harness builds the synthetic net and
    // returns an empty per-property map. Should not throw "not implemented".
    const result = await def.verify({
      params: undefined as never,
      portInputGenerators: {},
      properties: [],
    });
    expect(result.syntheticNet).toBeDefined();
    expect(result.perProperty.size).toBe(0);
    expect(result.allProven()).toBe(true);
    expect(result.anyViolated()).toBe(false);
  });

  // ============================================================
  //  Subnet discriminated-union exhaustiveness (MOD-002)
  // ============================================================

  it('Subnet pattern matching on kind is exhaustive', () => {
    const p = place<Item>('p');
    const t = Transition.builder('t').read(p).build();
    const def = SubnetDef.builder('S').transition(t).build();

    const open: Subnet = openSubnet(def);
    const closed: Subnet = closedSubnet(PetriNet.builder('X').build());

    function classify(s: Subnet): string {
      switch (s.kind) {
        case 'closed': return `closed:${s.net.name}`;
        case 'open': return `open:${s.def.name}`;
        default: {
          // Exhaustiveness check — `s` must be `never` here.
          const _exhaustive: never = s;
          return _exhaustive;
        }
      }
    }

    expect(classify(open)).toBe('open:S');
    expect(classify(closed)).toBe('closed:X');
  });
});
