import { describe, expect, it } from 'vitest';
import { PetriNet } from '../../src/core/petri-net.js';
import { place } from '../../src/core/place.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { Transition } from '../../src/core/transition.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { FusionSet } from '../../src/core/fusion-set.js';
import { passthrough } from '../../src/core/transition-action.js';
import { producer } from '../fixtures/subnet-fixtures.js';

/**
 * Tests for subnet-membership metadata recorded by
 * `PetriNetBuilder.compose(def)` — per **MOD-026**.
 *
 * Direct composition records a `node-name → subnet-name` mapping on the built
 * net: a node contributed by exactly one subnet maps to that subnet; a place
 * contributed by two or more subnets is a shared rendezvous place and is
 * omitted. The mapping is what cluster-aware DOT export uses to reconstruct
 * `subgraph cluster_*` blocks without prefix names.
 *
 * Mirrors `java/src/test/java/org/libpetri/core/ComposeDirectMembershipTest.java`.
 */
describe('compose(def) subnet-membership metadata — MOD-026', () => {
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

  const sortedEntries = (m: ReadonlyMap<string, string>): [string, string][] =>
    [...m.entries()].sort((a, b) => a[0].localeCompare(b[0]));

  it('directCompose_recordsMembershipPerSubnet', () => {
    const net = PetriNet.builder('Host')
      .compose(pipeProducer())
      .compose(pipeConsumer())
      .build();

    const membership = net.subnetMembership;
    expect(membership.get('seed')).toBe('PipeProducer');
    expect(membership.get('emit')).toBe('PipeProducer');
    expect(membership.get('sink')).toBe('PipeConsumer');
    expect(membership.get('eat')).toBe('PipeConsumer');
  });

  it('directCompose_sharedPlace_hasNoMembershipEntry', () => {
    // 'pipe' is contributed by both subnets — a shared rendezvous place with
    // no single owner, so it carries no membership entry (it renders
    // top-level, outside any cluster).
    const net = PetriNet.builder('Host')
      .compose(pipeProducer())
      .compose(pipeConsumer())
      .build();

    expect(net.subnetMembership.has('pipe')).toBe(false);
  });

  it('directCompose_membershipIsOrderIndependent', () => {
    const ab = PetriNet.builder('Host')
      .compose(pipeProducer())
      .compose(pipeConsumer())
      .build();
    const ba = PetriNet.builder('Host')
      .compose(pipeConsumer())
      .compose(pipeProducer())
      .build();

    expect(sortedEntries(ab.subnetMembership)).toEqual(sortedEntries(ba.subnetMembership));
  });

  it('flatNet_hasEmptyMembership', () => {
    const a = place<string>('a');
    const b = place<string>('b');
    const net = PetriNet.builder('Flat')
      .transition(Transition.builder('move').inputs(one(a)).outputs(outPlace(b)).build())
      .build();

    expect(net.subnetMembership.size).toBe(0);
  });

  it('instanceCompose_hasEmptyMembership', () => {
    // compose(instance) is the prefix-rename path — it records no membership;
    // the exporter clusters those nodes by name prefix.
    const net = PetriNet.builder('Host')
      .compose(producer().instantiate('p1'))
      .build();

    expect(net.subnetMembership.size).toBe(0);
  });

  it('directCompose_thenFuse_dropsNonCanonicalEntry', () => {
    // Fusion removes the non-canonical place 'b'; its membership entry must be
    // dropped so the map names only places that still exist.
    const a = place<string>('a');
    const b = place<string>('b');
    const subnet = SubnetDef.builder('AB')
      .transition(Transition.builder('move').inputs(one(a)).outputs(outPlace(b)).build())
      .build();

    const net = PetriNet.builder('Host')
      .compose(subnet)
      .fuse(FusionSet.of('ab', a, b))
      .build();

    expect(net.subnetMembership.get('a')).toBe('AB');
    expect(net.subnetMembership.has('b')).toBe(false);
    expect(net.subnetMembership.get('move')).toBe('AB');
  });

  it('bindActions_preservesMembership', () => {
    const net = PetriNet.builder('Host')
      .compose(pipeProducer())
      .compose(pipeConsumer())
      .build();

    const bound = net.bindActions(new Map([['emit', passthrough()]]));

    expect(sortedEntries(bound.subnetMembership)).toEqual(sortedEntries(net.subnetMembership));
  });

  it('directCompose_subnetNameWithSlash_isSanitised', () => {
    // A subnet name containing '/' must be sanitised so it never triggers
    // spurious nested-cluster splitting in the exporter.
    const x = place<string>('x');
    const y = place<string>('y');
    const subnet = SubnetDef.builder('group/sub')
      .transition(Transition.builder('step').inputs(one(x)).outputs(outPlace(y)).build())
      .build();

    const net = PetriNet.builder('Host').compose(subnet).build();

    expect(net.subnetMembership.get('step')).toBe('group_sub');
  });
});
