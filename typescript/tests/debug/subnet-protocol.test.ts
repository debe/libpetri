/**
 * Wire-level tests for the debug protocol's subnet-instance support per
 * `spec/11-modular-composition.md` **MOD-041**.
 *
 * Covers:
 * - {@link buildSubnetInstances} populated for composed nets, empty for flat
 *   nets.
 * - {@link PlaceInfo.instancePrefix} and {@link TransitionInfo.instancePrefix}
 *   populated from the name's prefix portion (omitted for flat names).
 * - {@link NetEvent} variants exposed via {@link eventInstancePrefix} as a
 *   derived helper.
 * - {@link toEventInfo} surfacing `instancePrefix` in the wire-facing
 *   {@link NetEventInfo} `details` map (omitted for flat events).
 *
 * Mirrors `java/src/test/java/org/libpetri/debug/DebugProtocolSubnetTest.java`.
 */

import { describe, expect, it } from 'vitest';
import {
  DebugSessionRegistry,
  buildNetStructure,
  buildSubnetInstances,
} from '../../src/debug/debug-session-registry.js';
import { toEventInfo } from '../../src/debug/net-event-converter.js';
import {
  eventInstancePrefix,
  instancePrefixOfName,
  type NetEvent,
} from '../../src/event/net-event.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, type Place } from '../../src/core/place.js';
import { tokenOf } from '../../src/core/token.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { Interface } from '../../src/core/interface.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { producer, consumer } from '../fixtures/subnet-fixtures.js';

const NOW_MS = Date.parse('2026-05-09T12:00:00Z');

/** Builds a two-instance composed pipeline: producer1 -> wire -> consumer1. */
function composedTwoInstanceNet(): PetriNet {
  const producerInst = producer().instantiate('producer1');
  const consumerInst = consumer().instantiate('consumer1');
  const wire = place<string>('wire');
  return PetriNet.builder('Pipeline')
    .place(wire)
    .compose(producerInst, { output: wire as Place<unknown> })
    .compose(consumerInst, { input: wire as Place<unknown> })
    .build();
}

/** Builds a flat (non-composed) net with no '/' in any name. */
function flatNet(): PetriNet {
  const input = place<string>('Input');
  const output = place<string>('Output');
  const t = Transition.builder('Process')
    .inputs(one(input))
    .outputs(outPlace(output))
    .build();
  return PetriNet.builder('FlatNet').transition(t).build();
}

describe('Debug protocol — subnet instances (MOD-041)', () => {
  // ============================================================
  //  MOD-041 AC#5: flat net produces empty subnetInstances list
  // ============================================================

  it('subscribed_flatNet_emptySubnetInstances', () => {
    const registry = new DebugSessionRegistry();
    const session = registry.register('s1', flatNet());

    const subnetInstances = buildSubnetInstances(session);

    expect(subnetInstances).toEqual([]);
  });

  // ============================================================
  //  MOD-041 AC#1, AC#2: composed net produces populated descriptors
  // ============================================================

  it('subscribed_composedNet_populatedSubnetInstances', () => {
    const registry = new DebugSessionRegistry();
    const session = registry.register('s1', composedTwoInstanceNet());

    const subnetInstances = buildSubnetInstances(session);

    expect(subnetInstances).toHaveLength(2);

    const byPrefix = new Map(subnetInstances.map(d => [d.prefix, d]));
    expect(byPrefix.has('producer1')).toBe(true);
    expect(byPrefix.has('consumer1')).toBe(true);

    // producer1 must enumerate its single transition.
    const producerDescriptor = byPrefix.get('producer1')!;
    expect([...producerDescriptor.transitionNames].sort()).toEqual(['producer1/produce']);
    // The internal nextItem place is part of the producer instance; the
    // merged port place ("wire") is a host place and must NOT appear
    // under producer1's exposedPlaceNames.
    expect(producerDescriptor.exposedPlaceNames).toContain('producer1/nextItem');
    expect(producerDescriptor.exposedPlaceNames).not.toContain('wire');

    // consumer1 must enumerate its single transition.
    const consumerDescriptor = byPrefix.get('consumer1')!;
    expect([...consumerDescriptor.transitionNames].sort()).toEqual(['consumer1/consume']);
    expect(consumerDescriptor.exposedPlaceNames).toContain('consumer1/consumed');

    // Top-level instances have no parentPrefix (omitted from the wire).
    expect(producerDescriptor.parentPrefix).toBeUndefined();
    expect(consumerDescriptor.parentPrefix).toBeUndefined();
  });

  // ============================================================
  //  MOD-041 AC#4: nested instance has parentPrefix set
  // ============================================================

  it('subscribed_nestedInstance_parentPrefixSet', () => {
    // Build a producer subnet, compose into an outer subnet (T), then
    // instantiate T with a top-level prefix. The nested instance prefix
    // is "outer/inner" and its parentPrefix MUST be "outer".
    const producerInner = producer().instantiate('inner');
    const outerOut = place<string>('out');
    const outerBody = PetriNet.builder('OuterBody')
      .place(outerOut)
      .compose(producerInner, { output: outerOut as Place<unknown> })
      .build();
    const outerIface = Interface.builder()
      .outputPort('out', outerOut)
      .build();
    const outerDef = SubnetDef.fromNet(outerBody, outerIface);
    const outer = outerDef.instantiate('outer');
    const hostSink = place<string>('hostSink');
    const net = PetriNet.builder('Host')
      .place(hostSink)
      .compose(outer, { out: hostSink as Place<unknown> })
      .build();

    const registry = new DebugSessionRegistry();
    const session = registry.register('nested', net);

    const subnetInstances = buildSubnetInstances(session);

    const nested = subnetInstances.find(d => d.prefix === 'outer/inner');
    expect(nested).toBeDefined();
    expect(nested!.parentPrefix).toBe('outer');
  });

  // ============================================================
  //  MOD-041 AC#3: PlaceInfo / TransitionInfo carry instancePrefix
  // ============================================================

  it('placeInfo_instancePrefix_populated', () => {
    const registry = new DebugSessionRegistry();
    const session = registry.register('s1', composedTwoInstanceNet());

    const structure = buildNetStructure(session);

    const p = structure.places.find(pi => pi.name === 'producer1/nextItem');
    expect(p).toBeDefined();
    expect(p!.instancePrefix).toBe('producer1');
  });

  it('placeInfo_flatPlace_undefinedInstancePrefix', () => {
    const registry = new DebugSessionRegistry();
    const session = registry.register('s1', composedTwoInstanceNet());

    const structure = buildNetStructure(session);

    // The host wire place has no '/' so instancePrefix must be omitted.
    const p = structure.places.find(pi => pi.name === 'wire');
    expect(p).toBeDefined();
    expect(p!.instancePrefix).toBeUndefined();
    // Wire shape: omitted from JSON entirely (not present as null).
    expect('instancePrefix' in p!).toBe(false);
  });

  it('transitionInfo_instancePrefix_populated', () => {
    const registry = new DebugSessionRegistry();
    const session = registry.register('s1', composedTwoInstanceNet());

    const structure = buildNetStructure(session);

    const t = structure.transitions.find(ti => ti.name === 'producer1/produce');
    expect(t).toBeDefined();
    expect(t!.instancePrefix).toBe('producer1');
  });

  it('transitionInfo_flatTransition_undefinedInstancePrefix', () => {
    const registry = new DebugSessionRegistry();
    const session = registry.register('s1', flatNet());

    const structure = buildNetStructure(session);

    const t = structure.transitions.find(ti => ti.name === 'Process');
    expect(t).toBeDefined();
    expect(t!.instancePrefix).toBeUndefined();
    expect('instancePrefix' in t!).toBe(false);
  });

  // ============================================================
  //  MOD-041: NetEvent.instancePrefix() derived helper
  // ============================================================

  it('netEvent_transitionStarted_instancePrefix', () => {
    const prefixed: NetEvent = {
      type: 'transition-started',
      timestamp: NOW_MS,
      transitionName: 'buf1/enqueue',
      consumedTokens: [],
    };
    expect(eventInstancePrefix(prefixed)).toBe('buf1');

    const flat: NetEvent = {
      type: 'transition-started',
      timestamp: NOW_MS,
      transitionName: 'Process',
      consumedTokens: [],
    };
    expect(eventInstancePrefix(flat)).toBeUndefined();
  });

  it('netEvent_tokenAdded_instancePrefix', () => {
    const prefixed: NetEvent = {
      type: 'token-added',
      timestamp: NOW_MS,
      placeName: 'buf1/items',
      token: tokenOf('hi'),
    };
    expect(eventInstancePrefix(prefixed)).toBe('buf1');

    const nested: NetEvent = {
      type: 'token-added',
      timestamp: NOW_MS,
      placeName: 'outer/inner/items',
      token: tokenOf('hi'),
    };
    expect(eventInstancePrefix(nested)).toBe('outer/inner');

    const flat: NetEvent = {
      type: 'token-added',
      timestamp: NOW_MS,
      placeName: 'Output',
      token: tokenOf('hi'),
    };
    expect(eventInstancePrefix(flat)).toBeUndefined();
  });

  // Direct contract test on the name helper (consumed by other modules too).
  it('instancePrefixOfName_lastSegmentSplit', () => {
    expect(instancePrefixOfName('a/b')).toBe('a');
    expect(instancePrefixOfName('outer/inner/leaf')).toBe('outer/inner');
    expect(instancePrefixOfName('flat')).toBeUndefined();
    expect(instancePrefixOfName(null)).toBeUndefined();
    expect(instancePrefixOfName(undefined)).toBeUndefined();
    // Leading-slash edge case: lastIndexOf > 0 contract — '/' alone or
    // '/foo' returns undefined because the prefix would be empty string.
    expect(instancePrefixOfName('/foo')).toBeUndefined();
  });

  // ============================================================
  //  MOD-041: net-event-converter surfaces instancePrefix on the wire
  // ============================================================

  it('netEventConverter_emitsInstancePrefixForPrefixedEvents', () => {
    const prefixedTransition: NetEvent = {
      type: 'transition-enabled',
      timestamp: NOW_MS,
      transitionName: 'buf1/enqueue',
    };
    const info = toEventInfo(prefixedTransition);
    expect(info.details['instancePrefix']).toBe('buf1');

    const prefixedToken: NetEvent = {
      type: 'token-added',
      timestamp: NOW_MS,
      placeName: 'buf1/items',
      token: tokenOf('v'),
    };
    const tokenInfo = toEventInfo(prefixedToken);
    expect(tokenInfo.details['instancePrefix']).toBe('buf1');
  });

  it('netEventConverter_omitsInstancePrefixForFlatEvents', () => {
    const flat: NetEvent = {
      type: 'transition-enabled',
      timestamp: NOW_MS,
      transitionName: 'Process',
    };
    const info = toEventInfo(flat);
    expect('instancePrefix' in info.details).toBe(false);
  });
});
