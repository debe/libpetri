import { it, expect } from 'vitest';
import { describeZ3 } from '../fixtures/z3.js';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { deadlockFree, placeBound, mutualExclusion } from '../../src/verification/smt-property.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { bindProducers } from '../fixtures/producing-actions.js';

// End-to-end abstract counterexample replay (C3) against the real z3 executable.
const Z3_TIMEOUT = 60_000;

describeZ3('counterexample replay (Z3 integration)', () => {
  // T1: A -> B, T2: B + C -> A with M0 = {A:1}: T1 fires, then T2 starves on C.
  const deadlockNet = () => {
    const pA = place('A');
    const pB = place('B');
    const pC = place('C');
    const t1 = Transition.builder('T1').inputs(one(pA)).outputs(outPlace(pB)).build();
    const t2 = Transition.builder('T2').inputs(one(pB), one(pC)).outputs(outPlace(pA)).build();
    const net = PetriNet.builder('DeadlockNet').transitions(t1, t2).build();
    return { pA, pB, pC, net };
  };

  it('confirms a genuine deadlock counterexample and re-emits the trace in firing order', async () => {
    const { pA, pB, net } = deadlockNet();
    const result = await SmtVerifier.forNet(bindProducers(net))
      .initialMarking(m => m.tokens(pA, 1))
      .property(deadlockFree())
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('violated');
    expect(result.counterexampleConfirmed).toBe(true);
    expect(result.report).toContain('Counterexample replay: CONFIRMED');
    expect(result.report).toContain('replay order');

    // Replay order: M0 = {A:1} first, the deadlocked {B:1} last — regardless of
    // the derivation tree's traversal order.
    expect(result.counterexampleTrace.length).toBeGreaterThanOrEqual(2);
    expect(result.counterexampleTrace[0]!.tokens(pA)).toBe(1);
    expect(result.counterexampleTrace[0]!.tokens(pB)).toBe(0);
    const last = result.counterexampleTrace[result.counterexampleTrace.length - 1]!;
    expect(last.tokens(pB)).toBe(1);
    expect(last.tokens(pA)).toBe(0);
    // One step per consecutive state pair, in firing order.
    expect(result.counterexampleTransitions).toHaveLength(result.counterexampleTrace.length - 1);
    expect(result.counterexampleTransitions[0]).toBe('T1');
  }, Z3_TIMEOUT);

  it('confirms a mutual-exclusion violation with a replayed interleaving', async () => {
    // Two independent enter transitions — both criticals reachable together.
    const idle1 = place('idle1');
    const idle2 = place('idle2');
    const crit1 = place('crit1');
    const crit2 = place('crit2');
    const enter1 = Transition.builder('enter1').inputs(one(idle1)).outputs(outPlace(crit1)).build();
    const exit1 = Transition.builder('exit1').inputs(one(crit1)).outputs(outPlace(idle1)).build();
    const enter2 = Transition.builder('enter2').inputs(one(idle2)).outputs(outPlace(crit2)).build();
    const exit2 = Transition.builder('exit2').inputs(one(crit2)).outputs(outPlace(idle2)).build();
    const net = PetriNet.builder('MutexUnlocked').transitions(enter1, exit1, enter2, exit2).build();

    const result = await SmtVerifier.forNet(bindProducers(net))
      .initialMarking(m => m.tokens(idle1, 1).tokens(idle2, 1))
      .property(mutualExclusion(crit1, crit2))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('violated');
    expect(result.counterexampleConfirmed).toBe(true);
    const last = result.counterexampleTrace[result.counterexampleTrace.length - 1]!;
    expect(last.tokens(crit1)).toBeGreaterThanOrEqual(1);
    expect(last.tokens(crit2)).toBeGreaterThanOrEqual(1);
  }, Z3_TIMEOUT);

  it('counterexampleReplay(false) opts out: verdict unchanged, no proof requested, confirmed = null', async () => {
    // Without the replay the HORN script asks for no refutation proof (as in Rust
    // and Java), so there are no decoded states either: the verdict rests on the
    // solver's answer alone.
    const { pA, net } = deadlockNet();
    const result = await SmtVerifier.forNet(bindProducers(net))
      .initialMarking(m => m.tokens(pA, 1))
      .property(deadlockFree())
      .counterexampleReplay(false)
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('violated');
    expect(result.counterexampleConfirmed).toBeNull();
    expect(result.report).not.toContain('Counterexample replay');
    expect(result.counterexampleTrace).toHaveLength(0);
  }, Z3_TIMEOUT);

  it('a proven verdict reports counterexampleConfirmed = null', async () => {
    const pA = place('A');
    const pB = place('B');
    const t1 = Transition.builder('AtoB').inputs(one(pA)).outputs(outPlace(pB)).build();
    const t2 = Transition.builder('BtoA').inputs(one(pB)).outputs(outPlace(pA)).build();
    const net = PetriNet.builder('Cycle').transitions(t1, t2).build();

    const result = await SmtVerifier.forNet(bindProducers(net))
      .initialMarking(m => m.tokens(pA, 1))
      .property(placeBound(pB, 1))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
    expect(result.counterexampleConfirmed).toBeNull();
  }, Z3_TIMEOUT);

  it('replays a multi-token bound violation across several firings', async () => {
    // p0(3) -> t -> p1; placeBound(p1, 2) needs three firings to violate.
    const p0 = place('p0');
    const p1 = place('p1');
    const t = Transition.builder('t').inputs(one(p0)).outputs(outPlace(p1)).build();
    const net = PetriNet.builder('ConservedPair').transitions(t).build();

    const result = await SmtVerifier.forNet(bindProducers(net))
      .initialMarking(m => m.tokens(p0, 3))
      .property(placeBound(p1, 2))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('violated');
    expect(result.counterexampleConfirmed).toBe(true);
    const last = result.counterexampleTrace[result.counterexampleTrace.length - 1]!;
    expect(last.tokens(p1)).toBe(3);
    expect(result.counterexampleTransitions).toEqual(['t', 't', 't']);
  }, Z3_TIMEOUT);
});
