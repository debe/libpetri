import { describe, it, expect } from 'vitest';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { Interface, InterfaceBuilder } from '../../src/core/interface.js';

interface Item { readonly tag: string }

/**
 * Focused unit tests for {@link SubnetDef.fromNet} per **MOD-014**.
 *
 * The general retrofit-validation cases live next to the SubnetDef contract
 * in `subnet-def.test.ts`; this file covers the additional MOD-014 / MOD-006
 * surface explicitly called out by the per-language plan: name uniqueness on
 * a hand-built `Interface`, channel-transition membership, and structural
 * round-trips on a degenerate net.
 *
 * Mirrors the Java {@code SubnetDefFromNetTest} coverage matrix.
 */
describe('SubnetDef.fromNet (MOD-014 retrofit utility)', () => {
  // ============================================================
  //  fromNet_validNet_succeeds
  // ============================================================

  it('valid net + iface yields a well-formed SubnetDef<void>', () => {
    const a = place<Item>('a');
    const b = place<Item>('b');
    const t = Transition.builder('t').inputs(one(a)).outputs(outPlace(b)).build();
    const net = PetriNet.builder('Original').transition(t).build();

    const iface = Interface.builder()
      .inputPort('in', a)
      .outputPort('out', b)
      .channel('ch', t)
      .build();

    const def = SubnetDef.fromNet(net, iface);

    expect(def.body).toBe(net);
    expect(def.iface).toBe(iface);
    expect(def.name).toBe('Original');
    expect(def.iface.ports.size).toBe(2);
    expect(def.iface.channels.size).toBe(1);
    expect(def.iface.port('in')?.place).toBe(a);
    expect(def.iface.channel('ch')?.transition).toBe(t);
  });

  // ============================================================
  //  fromNet_portPlaceMissing_throws
  // ============================================================

  it('port place missing from net is rejected (MOD-014)', () => {
    const a = place<Item>('a');
    const stranger = place<Item>('stranger');
    const t = Transition.builder('t').read(a).build();
    const net = PetriNet.builder('N').transition(t).build();

    const iface = Interface.builder()
      .inputPort('ghost', stranger)
      .build();

    expect(() => SubnetDef.fromNet(net, iface)).toThrow(/ghost|stranger/);
  });

  // ============================================================
  //  fromNet_channelTransitionMissing_throws
  // ============================================================

  it('channel transition missing from net is rejected (MOD-014)', () => {
    const a = place<Item>('a');
    const inNet = Transition.builder('inNet').read(a).build();
    const outOfNet = Transition.builder('outOfNet').read(a).build();
    const net = PetriNet.builder('N').transition(inNet).build();

    const iface = Interface.builder()
      .channel('orphan', outOfNet)
      .build();

    expect(() => SubnetDef.fromNet(net, iface)).toThrow(/orphan|outOfNet/);
  });

  // ============================================================
  //  fromNet_duplicatePortNames_throws
  //
  //  Interface.builder rejects duplicate port names eagerly so this case is
  //  guarded by the builder; we assert the guard catches the bypass attempt.
  // ============================================================

  it('duplicate port names are rejected by Interface.builder (MOD-006)', () => {
    const a = place<Item>('a');
    const b = place<Item>('b');
    const t = Transition.builder('t').read(a).read(b).build();
    PetriNet.builder('N').transition(t).build();

    expect(() => Interface.builder()
      .inputPort('dup', a)
      .outputPort('dup', b)
      .build(),
    ).toThrow(/dup/);
  });

  // ============================================================
  //  fromNet defensive port-name uniqueness on a hand-built Interface
  //
  //  Bypassing InterfaceBuilder by constructing the maps directly (the only
  //  way duplicate names could leak past the builder) — verify fromNet
  //  catches the duplicate. We construct the iface via the builder, then
  //  swap in a fabricated map that contains a duplicate name. This exercises
  //  the fromNet defensive check (line 188-198 of subnet-def.ts).
  // ============================================================

  it('fromNet defensively re-checks port-name uniqueness even with hand-built Interface', () => {
    const a = place<Item>('a');
    const b = place<Item>('b');
    const t = Transition.builder('t').read(a).read(b).build();
    const net = PetriNet.builder('N').transition(t).build();

    // Build a map with two entries that happen to share the same `name`
    // field. ReadonlyMap is keyed by string, so we use a Map keyed by the
    // ports' synthetic keys but both ports carry name='dup'.
    const fakePorts = new Map<string, { name: string; direction: 'input' | 'output' | 'inout'; place: typeof a }>([
      ['p1', { name: 'dup', direction: 'input', place: a }],
      ['p2', { name: 'dup', direction: 'output', place: b }],
    ]);

    // Bypass InterfaceBuilder by constructing the Interface via the symbol-
    // gated constructor path used internally — this tests the defensive
    // re-check rather than the InterfaceBuilder's own duplicate guard.
    // Since the symbol is internal, we exercise this scenario indirectly:
    // the builder route already enforces uniqueness, but for completeness
    // the assertion here is that an Interface with two distinct keys whose
    // ports share a name still trips fromNet's defensive check.
    //
    // Construct via a custom subclass that exposes the bypass — the public
    // surface gives no other route. The whole point of fromNet's defensive
    // check is to catch a hand-built Interface (for callers that subclass /
    // monkey-patch). Here we simulate that via Object.create:
    const sneakyIface = Object.create(Interface.prototype) as Interface;
    Object.defineProperty(sneakyIface, 'ports', {
      value: fakePorts,
      enumerable: true,
    });
    Object.defineProperty(sneakyIface, 'channels', {
      value: new Map(),
      enumerable: true,
    });

    expect(() => SubnetDef.fromNet(net, sneakyIface)).toThrow(/duplicate port name 'dup'/);
  });

  // ============================================================
  //  fromNet_duplicateChannelNames_throws (defensive, hand-built)
  // ============================================================

  it('fromNet defensively re-checks channel-name uniqueness even with hand-built Interface', () => {
    const a = place<Item>('a');
    const t1 = Transition.builder('t1').read(a).build();
    const t2 = Transition.builder('t2').read(a).build();
    const net = PetriNet.builder('N').transitions(t1, t2).build();

    const fakeChannels = new Map<string, { name: string; transition: typeof t1 }>([
      ['c1', { name: 'dup', transition: t1 }],
      ['c2', { name: 'dup', transition: t2 }],
    ]);

    const sneakyIface = Object.create(Interface.prototype) as Interface;
    Object.defineProperty(sneakyIface, 'ports', {
      value: new Map(),
      enumerable: true,
    });
    Object.defineProperty(sneakyIface, 'channels', {
      value: fakeChannels,
      enumerable: true,
    });

    expect(() => SubnetDef.fromNet(net, sneakyIface)).toThrow(/duplicate channel name 'dup'/);
  });

  // ============================================================
  //  fromNet_emptyNetEmptyIface_succeeds
  //
  //  Edge case: a structurally empty net with no places, no transitions, and
  //  an empty interface should round-trip without error. The result is a
  //  trivially valid SubnetDef<void>.
  // ============================================================

  it('empty net + empty interface round-trips', () => {
    const net = PetriNet.builder('Empty').build();
    const iface = Interface.builder().build();

    const def = SubnetDef.fromNet(net, iface);

    expect(def.body).toBe(net);
    expect(def.iface).toBe(iface);
    expect(def.body.places.size).toBe(0);
    expect(def.body.transitions.size).toBe(0);
    expect(def.iface.ports.size).toBe(0);
    expect(def.iface.channels.size).toBe(0);
  });

  // ============================================================
  //  fromNet_resultIsSubnetDef_void
  //
  //  MOD-014 AC #3: the resulting subnet definition is unparameterised
  //  (parameter type is the implementation's unit/void type). In TypeScript
  //  this is the `void` parameter; we assert structurally via the builder
  //  return-type and by attempting an instantiate without params.
  // ============================================================

  it('result is SubnetDef<void> — instantiable without params', () => {
    const a = place<Item>('a');
    const t = Transition.builder('t').read(a).build();
    const net = PetriNet.builder('N').transition(t).build();
    const iface = new InterfaceBuilder()
      .inputPort('in', a)
      .build();

    const def = SubnetDef.fromNet(net, iface);

    // Compile-time: TypeScript narrows fromNet's return type to
    // SubnetDef<void>; runtime check that instantiate works without params.
    const inst = def.instantiate('sut');
    expect(inst).toBeDefined();
    expect(inst.params).toBeUndefined();
    expect(inst.prefix).toBe('sut');
    // Renamed body should preserve the structural shape.
    expect(inst.renamedBody.places.size).toBe(net.places.size);
    expect(inst.renamedBody.transitions.size).toBe(net.transitions.size);
  });
});
