import { describe, expect, it } from 'vitest';
import { PetriNet } from '../../src/core/petri-net.js';
import { place } from '../../src/core/place.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { Transition } from '../../src/core/transition.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { producer, retryPolicy } from '../fixtures/subnet-fixtures.js';

/**
 * Tests for `PetriNetBuilder.compose(instance)` — identity-default
 * auto-composition per **MOD-024**.
 *
 * Rule: every declared port whose underlying Place is equal (by name,
 * matching TS's Place equality semantics) to a host-builder place
 * auto-binds to it. If the subnet declares no interface ports at all,
 * body places are matched against host places directly by name.
 *
 * Mirrors `java/src/test/java/org/libpetri/core/AutoComposeTest.java`.
 */
describe('PetriNetBuilder.compose(instance) — MOD-024 auto-compose', () => {
  it('autoCompose_explicitInterface_matchesByPlaceEquality', () => {
    const prod = producer().instantiate('p1');
    const hostOutput = place<string>('output');

    const host = PetriNet.builder('Host')
      .place(hostOutput)
      .compose(prod)
      .build();

    // Host place survives; renamed interface place "p1/output" does not.
    expect([...host.places].some((p) => p.name === 'output')).toBe(true);
    expect([...host.places].some((p) => p.name === 'p1/output')).toBe(false);

    // Internal renamed place flows through.
    expect([...host.places].some((p) => p.name === 'p1/nextItem')).toBe(true);

    // produce's output arc points at a place named 'output'.
    const produce = [...host.transitions].find((t) => t.name === 'p1/produce')!;
    expect([...produce.outputPlaces()].some((p) => p.name === 'output')).toBe(true);
  });

  it('autoCompose_structurallyEqualToExplicitBindPort', () => {
    const hostOutput = place<string>('output');

    const autoHost = PetriNet.builder('Host')
      .place(hostOutput)
      .compose(producer().instantiate('p1'))
      .build();

    const explicitHost = PetriNet.builder('Host')
      .place(hostOutput)
      .compose(producer().instantiate('p1'), (b) => b.bindPort<string>('output', hostOutput))
      .build();

    // Place name set equal.
    const autoNames = [...autoHost.places].map((p) => p.name).sort();
    const explicitNames = [...explicitHost.places].map((p) => p.name).sort();
    expect(autoNames).toEqual(explicitNames);

    // Transition names equal in insertion order.
    const autoTrans = [...autoHost.transitions].map((t) => t.name);
    const explicitTrans = [...explicitHost.transitions].map((t) => t.name);
    expect(autoTrans).toEqual(explicitTrans);

    // For each transition, structural topology matches (arc-place names).
    const autoByName = new Map([...autoHost.transitions].map((t) => [t.name, t]));
    const explicitByName = new Map([...explicitHost.transitions].map((t) => [t.name, t]));
    for (const name of autoTrans) {
      const a = autoByName.get(name)!;
      const e = explicitByName.get(name)!;
      const aIn = a.inputSpecs.map((s) => s.place.name);
      const eIn = e.inputSpecs.map((s) => s.place.name);
      expect(aIn).toEqual(eIn);
      const aOut = [...a.outputPlaces()].map((p) => p.name).sort();
      const eOut = [...e.outputPlaces()].map((p) => p.name).sort();
      expect(aOut).toEqual(eOut);
    }
  });

  it('autoCompose_hostHasNoPreDeclaredPlace_arrivesViaArcs', () => {
    // The host doesn't pre-declare any place; producer's "output" port
    // carries Place('output') on its interface. Auto-compose trusts the
    // SubnetDef's declaration and merges into that place, which arrives
    // implicitly via the rewritten produce.output arc.
    const prod = producer().instantiate('p1');

    const host = PetriNet.builder('Host').compose(prod).build();

    expect([...host.places].some((p) => p.name === 'output')).toBe(true);
    expect([...host.places].some((p) => p.name === 'p1/output')).toBe(false);
  });

  it('autoCompose_noInterfaceDeclared_infersFromBodyPlaces', () => {
    const shared = place<string>('shared');
    const internal = place<string>('internal');

    const move = Transition.builder('move')
      .inputs(one(internal))
      .outputs(outPlace(shared))
      .build();

    const bareSubnet = SubnetDef.builder('Bare')
      .place(internal)
      .place(shared)
      .transition(move)
      .build(); // NO inputPort/outputPort declarations
    const inst = bareSubnet.instantiate('b1');

    const host = PetriNet.builder('Host')
      .place(shared)
      .compose(inst)
      .build();

    expect([...host.places].some((p) => p.name === 'shared')).toBe(true);
    expect([...host.places].some((p) => p.name === 'b1/shared')).toBe(false);
    expect([...host.places].some((p) => p.name === 'b1/internal')).toBe(true);

    // move's output points at a place named 'shared' (the host-side one).
    const renamedMove = [...host.transitions].find((t) => t.name === 'b1/move')!;
    expect([...renamedMove.outputPlaces()].some((p) => p.name === 'shared')).toBe(true);
  });

  it('autoCompose_subnetWithChannel_throwsNamingChannelsAndSuggestingOverload', () => {
    // AC-4: error must name the offending channel ("attempt") and direct
    // the caller to the explicit-binding overload.
    const retry = retryPolicy().instantiate('r1');
    const hostBuilder = PetriNet.builder('Host');

    expect(() => hostBuilder.compose(retry)).toThrow(/channel/);
    expect(() => hostBuilder.compose(retry)).toThrow(/attempt/);
    expect(() => hostBuilder.compose(retry)).toThrow(/bindChannel|bind\.bindChannel/i);
  });

  it('autoCompose_multipleSubnets_endToEnd', () => {
    const pipe = place<string>('pipe');

    const producerDef = SubnetDef.builder('ProdLocal')
      .place(place<string>('seed'))
      .place(pipe)
      .transition(
        Transition.builder('emit')
          .inputs(one(place<string>('seed')))
          .outputs(outPlace(pipe))
          .build(),
      )
      .outputPort('out', pipe)
      .build();

    const consumerDef = SubnetDef.builder('ConsLocal')
      .place(pipe)
      .place(place<string>('sink'))
      .transition(
        Transition.builder('eat')
          .inputs(one(pipe))
          .outputs(outPlace(place<string>('sink')))
          .build(),
      )
      .inputPort('in', pipe)
      .build();

    const host = PetriNet.builder('Host')
      .place(pipe)
      .compose(producerDef.instantiate('p'))
      .compose(consumerDef.instantiate('c'))
      .build();

    expect([...host.places].some((p) => p.name === 'pipe')).toBe(true);

    const emit = [...host.transitions].find((t) => t.name === 'p/emit')!;
    const eat = [...host.transitions].find((t) => t.name === 'c/eat')!;
    expect([...emit.outputPlaces()].some((p) => p.name === 'pipe')).toBe(true);
    expect(eat.inputSpecs.some((a) => a.place.name === 'pipe')).toBe(true);
  });

  it('autoCompose_inoutPort_alsoMatchesByEquality', () => {
    const counter = place<number>('counter');

    const subnet = SubnetDef.builder('Counter')
      .place(counter)
      .transition(
        Transition.builder('tick')
          .inputs(one(counter))
          .outputs(outPlace(counter))
          .build(),
      )
      .inoutPort('counter', counter)
      .build();

    const host = PetriNet.builder('Host')
      .place(counter)
      .compose(subnet.instantiate('c1'))
      .build();

    expect([...host.places].some((p) => p.name === 'counter')).toBe(true);
    expect([...host.places].some((p) => p.name === 'c1/counter')).toBe(false);
  });

  it('autoCompose_emptyBody_isHarmless', () => {
    const empty = SubnetDef.builder('Empty').build();
    const host = PetriNet.builder('Host').compose(empty.instantiate('e1')).build();
    expect(host.places.size).toBe(0);
    expect(host.transitions.size).toBe(0);
  });

  it('autoCompose_twoInstances_perInstanceStateIsolation', () => {
    // MOD-012: two auto-composed instances of the same SubnetDef must
    // keep their internal places under disjoint prefixed names.
    const shared = place<string>('output');

    const host = PetriNet.builder('Host')
      .place(shared)
      .compose(producer().instantiate('p1'))
      .compose(producer().instantiate('p2'))
      .build();

    const names = [...host.places].map((p) => p.name);
    expect(names).toContain('p1/nextItem');
    expect(names).toContain('p2/nextItem');
    expect(names).not.toContain('nextItem');

    const transNames = [...host.transitions].map((t) => t.name);
    expect(transNames).toContain('p1/produce');
    expect(transNames).toContain('p2/produce');
  });
});
