import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import {
  deadlockFree, mutualExclusion, placeBound, unreachable,
} from '../../src/verification/smt-property.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';

// All tests in this file require Z3 WASM which is slow to initialize.
// Tests are set to a generous timeout.
const Z3_TIMEOUT = 60_000;

describe('SmtVerifier (Z3 integration)', () => {
  it('circular net is deadlock-free', async () => {
    const pA = place('A');
    const pB = place('B');
    const t1 = Transition.builder('AtoB')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const t2 = Transition.builder('BtoA')
      .inputs(one(pB))
      .outputs(outPlace(pA))
      .build();
    const net = PetriNet.builder('CircularNet').transitions(t1, t2).build();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(pA, 1))
      .property(deadlockFree())
      .timeout(30_000)
      .verify();

    expect(result).toBeDefined();
    expect(result.report).toBeDefined();
    // Circular net should be proven deadlock-free (structurally or by IC3)
    expect(result.verdict.type).toBe('proven');
  }, Z3_TIMEOUT);

  it('mutual exclusion in single-token circular net', async () => {
    const pA = place('A');
    const pB = place('B');
    const t1 = Transition.builder('AtoB')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const t2 = Transition.builder('BtoA')
      .inputs(one(pB))
      .outputs(outPlace(pA))
      .build();
    const net = PetriNet.builder('MutualExclusion').transitions(t1, t2).build();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(pA, 1))
      .property(mutualExclusion(pA, pB))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
    // IC3 should synthesize an inductive invariant
    if (result.verdict.type === 'proven') {
      expect(result.verdict.method).toBeDefined();
    }
  }, Z3_TIMEOUT);

  it('deadlock net finds violation', async () => {
    const pA = place('A');
    const pB = place('B');
    const pC = place('C');

    // T1: A -> B, T2: B + C -> A
    // With A=1, C=0: T1 fires -> B=1, then T2 needs B+C but C=0 -> DEADLOCK
    const t1 = Transition.builder('T1')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const t2 = Transition.builder('T2')
      .inputs(one(pB), one(pC))
      .outputs(outPlace(pA))
      .build();
    const net = PetriNet.builder('DeadlockNet').transitions(t1, t2).build();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(pA, 1))
      .property(deadlockFree())
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('violated');
  }, Z3_TIMEOUT);

  it('place bound proven for bounded net', async () => {
    const pA = place('A');
    const pB = place('B');
    const t1 = Transition.builder('AtoB')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const t2 = Transition.builder('BtoA')
      .inputs(one(pB))
      .outputs(outPlace(pA))
      .build();
    const net = PetriNet.builder('Bounded').transitions(t1, t2).build();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(pA, 1))
      .property(placeBound(pB, 1))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
  }, Z3_TIMEOUT);

  it('unreachable property proven for conserving net', async () => {
    const pA = place('A');
    const pB = place('B');
    const pC = place('C');

    const t1 = Transition.builder('AtoB')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const t2 = Transition.builder('BtoA')
      .inputs(one(pB))
      .outputs(outPlace(pA))
      .build();
    const t3 = Transition.builder('AtoC')
      .inputs(one(pA))
      .outputs(outPlace(pC))
      .build();

    // Net: A -> B -> A, A -> C (conservation: A+B+C=1)
    // A and C simultaneously having tokens requires A>=1 AND C>=1 => sum >= 2, contradiction
    const net = PetriNet.builder('Unreachable').transitions(t1, t2, t3).build();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(pA, 1))
      .property(unreachable(new Set([pA, pC])))
      .timeout(30_000)
      .verify();

    // Should not be violated (A and C simultaneously marked is unreachable)
    expect(result.verdict.type).not.toBe('violated');
  }, Z3_TIMEOUT);

  it('deadlock net counterexample trace is populated', async () => {
    const pA = place('A');
    const pB = place('B');
    const pC = place('C');

    const t1 = Transition.builder('T1')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const t2 = Transition.builder('T2')
      .inputs(one(pB), one(pC))
      .outputs(outPlace(pA))
      .build();
    const net = PetriNet.builder('DeadlockNet').transitions(t1, t2).build();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(pA, 1))
      .property(deadlockFree())
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('violated');
    // Counterexample trace should contain at least one state
    expect(result.counterexampleTrace.length).toBeGreaterThan(0);
  }, Z3_TIMEOUT);

  it('result includes report and statistics', async () => {
    const pA = place('A');
    const pB = place('B');
    const t1 = Transition.builder('AtoB')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const t2 = Transition.builder('BtoA')
      .inputs(one(pB))
      .outputs(outPlace(pA))
      .build();
    const net = PetriNet.builder('N').transitions(t1, t2).build();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(pA, 1))
      .property(deadlockFree())
      .timeout(30_000)
      .verify();

    expect(result.report).toContain('IC3/PDR SAFETY VERIFICATION');
    expect(result.report).toContain('Phase 1');
    expect(result.statistics.places).toBe(2);
    expect(result.statistics.transitions).toBe(2);
    expect(result.elapsedMs).toBeGreaterThan(0);
  }, Z3_TIMEOUT);

  it('structural pre-check proves simple deadlock-free net early', async () => {
    // Circular net should be proven by structural analysis (Commoner's theorem)
    const pA = place('A');
    const pB = place('B');
    const t1 = Transition.builder('AtoB')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const t2 = Transition.builder('BtoA')
      .inputs(one(pB))
      .outputs(outPlace(pA))
      .build();
    const net = PetriNet.builder('N').transitions(t1, t2).build();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(pA, 1))
      .property(deadlockFree())
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
    if (result.verdict.type === 'proven') {
      expect(result.verdict.method).toBe('structural');
    }
  }, Z3_TIMEOUT);

  it('initialMarking accepts MarkingState directly', async () => {
    const pA = place('A');
    const pB = place('B');
    const t1 = Transition.builder('AtoB')
      .inputs(one(pA))
      .outputs(outPlace(pB))
      .build();
    const t2 = Transition.builder('BtoA')
      .inputs(one(pB))
      .outputs(outPlace(pA))
      .build();
    const net = PetriNet.builder('N').transitions(t1, t2).build();
    const marking = MarkingState.builder().tokens(pA, 1).build();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(marking)
      .property(deadlockFree())
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
  }, Z3_TIMEOUT);
});
