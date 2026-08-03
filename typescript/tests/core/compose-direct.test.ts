import { describe, expect, it } from 'vitest';
import { PetriNet } from '../../src/core/petri-net.js';
import { place } from '../../src/core/place.js';
import { SubnetDef } from '../../src/core/subnet-def.js';
import { Transition } from '../../src/core/transition.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { FusionSet } from '../../src/core/fusion-set.js';
import { TimePetriNetAnalyzer, type LivenessResult } from '../../src/verification/analysis/time-petri-net-analyzer.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { producer, consumer, retryPolicy, leakyBucket } from '../fixtures/subnet-fixtures.js';
import { bindProducers } from '../fixtures/producing-actions.js';

/**
 * Tests for `PetriNetBuilder.compose(def)` — direct composition per
 * **MOD-025**.
 *
 * Rule: a `SubnetDef` composed directly is integrated *without*
 * instantiation/prefix-renaming. Body places and transitions keep their
 * original names; places merge into the host by name. Direct composition is
 * order-independent.
 *
 * Mirrors `java/src/test/java/org/libpetri/core/ComposeDirectTest.java`
 * (scenario 9 — place token-type conflict — is Java-only: TS Place equality
 * is name-only at runtime, see MOD-025).
 */
describe('PetriNetBuilder.compose(def) — MOD-025 direct composition', () => {
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

  const names = (xs: Iterable<{ name: string }>): string[] => [...xs].map((x) => x.name).sort();

  it('composeDirect_mergesBodyPlacesByName', () => {
    const hostOutput = place<string>('output');
    const host = PetriNet.builder('Host').place(hostOutput).compose(producer()).build();

    expect([...host.places].filter((p) => p.name === 'output')).toHaveLength(1);
    expect([...host.places].some((p) => p.name === 'nextItem')).toBe(true);

    const produce = [...host.transitions].find((t) => t.name === 'produce')!;
    expect([...produce.outputPlaces()].some((p) => p.name === 'output')).toBe(true);
  });

  it('composeDirect_hostHasNoPreDeclaredPlace_arrivesUnPrefixed', () => {
    const host = PetriNet.builder('Host').compose(producer()).build();
    expect([...host.places].some((p) => p.name === 'output')).toBe(true);
    expect([...host.places].some((p) => p.name === 'nextItem')).toBe(true);
  });

  it('composeDirect_introducesNoPrefixSeparator', () => {
    const host = PetriNet.builder('Host').compose(producer()).compose(consumer()).build();
    expect([...host.places].some((p) => p.name.includes('/'))).toBe(false);
    expect([...host.transitions].some((t) => t.name.includes('/'))).toBe(false);
  });

  it('composeDirect_isOrderIndependent', () => {
    const prodThenCons = PetriNet.builder('Host').compose(pipeProducer()).compose(pipeConsumer()).build();
    const consThenProd = PetriNet.builder('Host').compose(pipeConsumer()).compose(pipeProducer()).build();

    expect(names(prodThenCons.places)).toEqual(names(consThenProd.places));
    expect(names(prodThenCons.transitions)).toEqual(names(consThenProd.transitions));

    for (const tName of ['emit', 'eat']) {
      const a = [...prodThenCons.transitions].find((t) => t.name === tName)!;
      const b = [...consThenProd.transitions].find((t) => t.name === tName)!;
      expect(names([...a.inputSpecs].map((s) => s.place))).toEqual(names([...b.inputSpecs].map((s) => s.place)));
      expect(names(a.outputPlaces())).toEqual(names(b.outputPlaces()));
    }
  });

  it('composeDirect_structurallyEqualToHandWrittenFlatNet', () => {
    const composed = PetriNet.builder('Net').compose(pipeProducer()).compose(pipeConsumer()).build();

    const seed = place<string>('seed');
    const pipe = place<string>('pipe');
    const sink = place<string>('sink');
    const handWritten = PetriNet.builder('Net')
      .transition(Transition.builder('emit').inputs(one(seed)).outputs(outPlace(pipe)).build())
      .transition(Transition.builder('eat').inputs(one(pipe)).outputs(outPlace(sink)).build())
      .build();

    expect(names(composed.places)).toEqual(names(handWritten.places));
    expect(names(composed.transitions)).toEqual(names(handWritten.transitions));
  });

  it('composeDirect_mixedWithInstanceCompose_coexist', () => {
    const host = PetriNet.builder('Host')
      .compose(producer())
      .compose(consumer().instantiate('c1'))
      .build();

    const tNames = [...host.transitions].map((t) => t.name);
    expect(tNames).toContain('produce');     // direct — un-prefixed
    expect(tNames).toContain('c1/consume');  // instance — prefixed
  });

  it('composeDirect_transitionNameCollision_throws', () => {
    const builder = PetriNet.builder('Host').compose(producer());
    let err: Error | undefined;
    try {
      builder.compose(producer());
    } catch (e) {
      err = e as Error;
    }
    expect(err).toBeDefined();
    expect(err!.message).toContain('produce');
    expect(err!.message).toContain('instantiate');
  });

  it('composeDirect_subnetWithChannel_throwsNamingChannel', () => {
    let err: Error | undefined;
    try {
      PetriNet.builder('Host').compose(retryPolicy());
    } catch (e) {
      err = e as Error;
    }
    expect(err).toBeDefined();
    expect(err!.message).toContain('channel');
    expect(err!.message).toContain('attempt');
    expect(err!.message).toContain('instantiate');
  });

  it('composeDirect_emptySubnet_isNoOp', () => {
    const empty = SubnetDef.builder('Empty').build();
    const host = PetriNet.builder('Host').compose(empty).build();
    expect(host.places.size).toBe(0);
    expect(host.transitions.size).toBe(0);
  });

  it('composeDirect_arclessStandalonePlace_flowsThrough', () => {
    const standalone = place<string>('standalone');
    const subnet = SubnetDef.builder('Standalone').place(standalone).build();
    const host = PetriNet.builder('Host').compose(subnet).build();
    expect([...host.places].some((p) => p.name === 'standalone')).toBe(true);
  });

  it('composeDirect_inhibitorArcPlace_mergesByName', () => {
    const hostSlots = place<string>('slots');
    const host = PetriNet.builder('Host').place(hostSlots).compose(leakyBucket(2)).build();

    const reject = [...host.transitions].find((t) => t.name === 'reject')!;
    expect([...reject.inhibitors].some((arc) => arc.place.name === 'slots')).toBe(true);
    expect([...host.places].filter((p) => p.name === 'slots')).toHaveLength(1);
  });

  it('composeDirect_thenFuse_fusionRunsAtBuild', () => {
    const a = place<string>('a');
    const b = place<string>('b');
    const subnet = SubnetDef.builder('AB')
      .transition(Transition.builder('move').inputs(one(a)).outputs(outPlace(b)).build())
      .build();

    const net = PetriNet.builder('Host')
      .compose(subnet)
      .fuse(FusionSet.of('ab', a, b))
      .build();

    expect([...net.places].some((p) => p.name === 'a')).toBe(true);
    expect([...net.places].some((p) => p.name === 'b')).toBe(false);
  });

  it('composeDirect_producerToConsumer_isBoundedAndReachable', () => {
    // SCG-1: a direct-composed producer→pipe←consumer chain is bounded and
    // the sink is reachable — proves the name-merge wired the two subnets.
    const net = PetriNet.builder('DirectComposed').compose(pipeProducer()).compose(pipeConsumer()).build();
    const result = analyzePipeChain(net);

    expect(result.isComplete).toBe(true);
    expect(result.isGoalLive).toBe(true);
  });

  it('composeDirect_orderIndependentUnderStateClassAnalysis', () => {
    // SCG-2: formal backing for order-independence — both compose orders
    // produce nets with identical reachability and state-class structure.
    const prodThenCons = PetriNet.builder('A').compose(pipeProducer()).compose(pipeConsumer()).build();
    const consThenProd = PetriNet.builder('B').compose(pipeConsumer()).compose(pipeProducer()).build();

    const a = analyzePipeChain(prodThenCons);
    const b = analyzePipeChain(consThenProd);

    expect(a.isGoalLive).toBe(b.isGoalLive);
    expect(a.isComplete).toBe(b.isComplete);
    expect(a.stateClassGraph.size()).toBe(b.stateClassGraph.size());
  });

  function analyzePipeChain(net: PetriNet): LivenessResult {
    const seed = [...net.places].find((p) => p.name === 'seed')!;
    const sink = [...net.places].find((p) => p.name === 'sink')!;
    return TimePetriNetAnalyzer.forNet(bindProducers(net))
      .initialMarking(MarkingState.builder().tokens(seed, 1).build())
      .goalPlaces(sink)
      .maxClasses(100)
      .build()
      .analyze();
  }
});
