import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { deadlockFree, placeBound, terminatesAtSink, unreachable } from '../../src/verification/smt-property.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import type { Place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { immediate, window, type Timing } from '../../src/core/timing.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { OpenNetContract, verifyOpenNet } from '../../src/verification/open-net/index.js';
import { isReapable, lateTransitions, relaxLate, reapableTransitions } from '../../src/verification/reaping.js';
import { verifyViaNameScg } from '../../src/verification/nu-scg-verifier.js';
import { matchKey, matchSpec } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { andPlaces } from '../../src/core/out.js';
import { deadline, delayed, exact } from '../../src/core/timing.js';
import { bindProducers } from '../fixtures/producing-actions.js';
import { ignore } from '../../src/verification/analysis/environment-analysis-mode.js';
import { describeZ3 } from '../fixtures/z3.js';
import { allMints } from '../fixtures/all-mints.js';

/**
 * Deadline reaping in the verifier's quiescence ([VER-002], [VER-004], [TIME-013]).
 *
 * A `deadline` / `window` transition a late executor reaps keeps its input tokens and is not
 * re-enabled until one of its input places changes, so the executor can rest at a marking the
 * untimed net still enables. Lean: `Libpetri/Novel/ReapingVsUntimed.lean`,
 * `reaping_refutes_ver004_ac3`, whose witness is `witness()` below. Mirrors
 * `rust/libpetri-verification/tests/reaping.rs`.
 */

const p0 = place('p0');
const p1 = place('p1');

function arc(name: string, from: Place<any>, to: Place<any>, timing: Timing = immediate()): Transition {
  return Transition.builder(name).inputs(one(from)).outputs(outPlace(to)).timing(timing).build();
}

/** `p0 —t→ p1`, `t = window(3, 5)`: the Lean witness. */
function witness(): PetriNet {
  return bindProducers(PetriNet.builder('reaping-witness').transitions(arc('t', p0, p1, window(3, 5))).build());
}

function verifier(net: PetriNet): SmtVerifier {
  return SmtVerifier.forNet(net).mintTransitions(...allMints(net))
    .initialMarking(m => m.tokens(p0, 1))
    .sinkPlaces(p1)
    .timeout(30_000);
}

describe('reapability', () => {
  it('deadline and window are reapable and nothing else is', () => {
    expect(isReapable(deadline(5))).toBe(true);
    expect(isReapable(window(3, 5))).toBe(true);
    expect(isReapable(exact(5))).toBe(false);
    expect(isReapable(delayed(5))).toBe(false);
    expect(isReapable(immediate())).toBe(false);
  });

  it('relaxing drops every latest bound and keeps the earliest', () => {
    const net = PetriNet.builder('reap')
      .transitions(
        arc('d', p0, p1, deadline(5)), arc('w', p0, p1, window(3, 5)), arc('w0', p0, p1, window(0, 5)),
        arc('x', p0, p1, exact(4)), arc('x0', p0, p1, exact(0)), arc('y', p0, p1, delayed(2)),
        arc('i', p0, p1, immediate()),
      )
      .build();
    expect([...reapableTransitions(net)].sort()).toEqual(['d', 'w', 'w0']);
    const late = lateTransitions(net);
    expect([...late].sort()).toEqual(['d', 'w', 'w0', 'x', 'x0']);
    const relaxed = relaxLate(net, late);
    const timing = (name: string) => [...relaxed.transitions].find(t => t.name === name)!.timing;
    expect(timing('d')).toEqual(immediate());
    expect(timing('w')).toEqual(delayed(3));
    expect(timing('w0')).toEqual(immediate());
    expect(timing('x')).toEqual(delayed(4));
    expect(timing('x0')).toEqual(immediate());
    expect(timing('y')).toEqual(delayed(2));
    expect(timing('i')).toEqual(immediate());
    expect(relaxLate(net, new Set())).toBe(net);
  });

  it('a net without latest bounds is not relaxed', () => {
    const net = PetriNet.builder('plain').transitions(arc('y', p0, p1, delayed(2)), arc('i', p0, p1)).build();
    expect(lateTransitions(net).size).toBe(0);
    expect(relaxLate(net, new Set(['y', 'i']))).toBe(net);
  });

  it('the quiescence clause skips the reapable transition', () => {
    const horn = (noReaping: boolean) =>
      verifier(witness()).property(deadlockFree()).assumeNoReaping(noReaping).encodeScripts().horn;
    expect(horn(true)).toContain('(< m0 1)');
    expect(horn(false)).not.toContain('(< m0 1)');
  });

  it('marking property scripts do not change', () => {
    const horn = (noReaping: boolean) =>
      verifier(witness()).property(placeBound(p1, 1)).assumeNoReaping(noReaping).encodeScripts().horn;
    expect(horn(false)).toBe(horn(true));
  });
});

describeZ3('deadline reaping (TIME-013)', () => {
  it('the witness rests at its initial marking: DeadlockFree violated by the empty trace', async () => {
    const r = await verifier(witness()).property(deadlockFree()).verify();
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.counterexampleTransitions).toEqual([]);
    expect(r.counterexampleTrace[0]?.tokens(p0)).toBe(1);
    expect(r.report).toContain('Reaping (TIME-013): t can be reaped');
  });

  it('assumeNoReaping restores the strict verdict and names the assumption', async () => {
    const r = await verifier(witness()).property(deadlockFree()).assumeNoReaping(true).verify();
    expect(r.verdict.type, r.report).toBe('proven');
    expect(r.report).toContain('ASSUMPTION: no transition is reaped (the assume-no-reaping option)');
  });

  it('the fixpoint query alone finds the reaped rest', async () => {
    const r = await verifier(witness()).property(deadlockFree())
      .stateEquationPhase(false).firingBound(false).verify();
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.route).toBe('smt');
    expect(r.counterexampleTransitions).toEqual([]);
    expect(r.counterexampleTrace[0]?.tokens(p0)).toBe(1);
  });

  it('terminatesAtSink sees the reaped rest too', async () => {
    const r = await verifier(witness()).property(terminatesAtSink()).verify();
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.counterexampleTransitions).toEqual([]);
    const strict = await verifier(witness()).property(terminatesAtSink()).assumeNoReaping(true).verify();
    expect(strict.verdict.type, strict.report).toBe('proven');
  });

  it('a reapable transition shadowed by an immediate one changes nothing', async () => {
    const net = bindProducers(PetriNet.builder('shadowed')
      .transitions(arc('t', p0, p1, window(3, 5)), arc('u', p0, p1)).build());
    const r = await verifier(net).property(deadlockFree()).verify();
    expect(r.verdict.type, r.report).toBe('proven');
  });

  it('a reapable self-loop is not proven structurally', async () => {
    const a = place('a');
    const net = bindProducers(PetriNet.builder('self-loop').transitions(arc('t', a, a, window(3, 5))).build());
    const run = (noReaping: boolean) => SmtVerifier.forNet(net).mintTransitions(...allMints(net))
      .enumerationMaxClasses(0)
      .initialMarking(m => m.tokens(a, 1))
      .property(deadlockFree())
      .assumeNoReaping(noReaping)
      .timeout(30_000)
      .verify();
    const reaping = await run(false);
    expect(reaping.route, reaping.report).not.toBe('structural');
    expect(reaping.verdict.type, reaping.report).toBe('violated');
    expect(reaping.counterexampleTransitions).toEqual([]);
    expect((await run(true)).verdict.type).toBe('proven');
  });

  it('the timed check confirms the reaped rest', async () => {
    const r = await verifier(witness()).property(deadlockFree()).timedCounterexampleCheck(true).verify();
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.counterexampleTiming).toBe('timed-confirmed');
  });

  it('open net: both routes read a reaped relay as resting', async () => {
    const q = place('q');
    const out = place('out');
    const net = bindProducers(PetriNet.builder('reaped-relay').transitions(arc('relay', q, out, window(3, 5))).build());
    const contract = OpenNetContract.builder().arrive(1, q).expect('out', 1, out).build();
    const graph = await verifyOpenNet(net, contract);
    expect(graph.verdict.type, graph.report).toBe('violated');
    expect(graph.route).toBe('enumeration');
    expect(graph.report).toContain('Reaping (TIME-013): relay can be reaped');
    const strict = await verifyOpenNet(net, contract, { assumeNoReaping: true });
    expect(strict.verdict.type, strict.report).toBe('proven');
    expect(strict.report).toContain('ASSUMPTION: no transition is reaped');
    const smt = await verifyOpenNet(net, contract, { maxClasses: 0 });
    expect(smt.verdict.type, smt.report).toBe('violated');
    expect(smt.route).toBe('smt');
    const smtStrict = await verifyOpenNet(net, contract, { maxClasses: 0, assumeNoReaping: true });
    expect(smtStrict.verdict.type, smtStrict.report).toBe('proven');
  });
});

describe('Route B reads a reaped join as resting', () => {
  it('the same-mint join at window(50, 200)', () => {
    const source = place('source');
    const a = place<string>('branchA');
    const b = place<string>('branchB');
    const merged = place<string>('merged');
    const key = (v: string) => nameId(v);
    const fork = Transition.builder('fork').inputs(one(source)).outputs(andPlaces(a, b)).build();
    const join = Transition.builder('join').timing(window(50, 200))
      .inputs(one(a), one(b))
      .match(matchSpec(matchKey(a, key), matchKey(b, key)))
      .outputs(outPlace(merged))
      .build();
    const net = bindProducers(PetriNet.builder('reaped_join').transitions(fork, join).build());
    const initial = MarkingState.builder().tokens(source, 1).build();
    const run = (reapable: ReadonlySet<string>) => verifyViaNameScg(
      net, initial, deadlockFree(), new Set([merged]), new Set(), ignore(), 1_000, 'base',
      new Set(), allMints(net), 'conflict', [], null, reapable, reapable)!;
    const strict = run(new Set());
    expect(strict.verdict.type).toBe('proven');
    const reaping = run(new Set(['join']));
    expect(reaping.verdict.type).toBe('violated');
    expect(reaping.transitions).toEqual(['fork']);
    expect(reaping.note).toContain('latest bound of join was lifted');
  });
});

// ==================== lateness on Route B (TIME-006, TIME-013) ====================

const pRace = place('p');
const aRace = place('a');
const bRace = place('b');
const sourceRace = place('source');

/**
 * `t1: p → a` at `early`, `t2: p → b` at `delayed(10)`, beside a same-mint ν-join so the query
 * runs on Route B. On time `t1` always wins the race for `p`; a late executor reaps a deadline /
 * window `t1`, or fires an exact one after `t2`, and marks `b`. Lean:
 * `TimedScg/Retrodict.reaping_escapes_timed_graph`, `TimedScg/Late.late_run_sound`.
 */
function lateRace(early: Timing): PetriNet {
  const ba = place<string>('branchA');
  const bb = place<string>('branchB');
  const merged = place<string>('merged');
  const key = (v: string) => nameId(v);
  const fork = Transition.builder('fork').inputs(one(sourceRace)).outputs(andPlaces(ba, bb)).build();
  const join = Transition.builder('join')
    .inputs(one(ba), one(bb))
    .match(matchSpec(matchKey(ba, key), matchKey(bb, key)))
    .outputs(outPlace(merged))
    .build();
  return bindProducers(PetriNet.builder('late-race')
    .transitions(arc('t1', pRace, aRace, early), arc('t2', pRace, bRace, delayed(10)), fork, join)
    .build());
}

function verifyLateRace(early: Timing, noReaping: boolean) {
  return SmtVerifier.forNet(lateRace(early)).mintTransitions(...allMints(lateRace(early)))
    .initialMarking(m => m.tokens(pRace, 1).tokens(sourceRace, 1))
    .property(unreachable(new Set([bRace])))
    .assumeNoReaping(noReaping)
    .timeout(30_000)
    .verify();
}

describe('Route B reads a late executor', () => {
  it('marking properties see a reaped race', async () => {
    for (const early of [deadline(5), window(3, 5)]) {
      const late = await verifyLateRace(early, false);
      expect(late.route, late.report).toBe('nu-scg');
      expect(late.verdict.type, late.report).toBe('violated');
      expect(late.counterexampleTransitions.at(-1), late.report).toBe('t2');
      const onTime = await verifyLateRace(early, true);
      expect(onTime.route, onTime.report).toBe('nu-scg');
      expect(onTime.verdict.type, onTime.report).toBe('proven');
      expect(onTime.report).toContain('ASSUMPTION: no transition is reaped');
      expect(onTime.report).toContain('on-time executor');
    }
  });

  it('lifts the latest bound of exact', async () => {
    const late = await verifyLateRace(exact(5), false);
    expect(late.route, late.report).toBe('nu-scg');
    expect(late.verdict.type, late.report).toBe('violated');
    expect(late.report).toContain('latest bound of t1 was lifted');
    const onTime = await verifyLateRace(exact(5), true);
    expect(onTime.verdict.type, onTime.report).toBe('proven');
    expect(onTime.report).toContain('on-time executor');
  });

  it('leaves a net without latest bounds alone', async () => {
    const late = await verifyLateRace(delayed(5), false);
    const onTime = await verifyLateRace(delayed(5), true);
    expect(late.route, late.report).toBe('nu-scg');
    expect(late.verdict.type, late.report).toBe('violated');
    expect(late.report).not.toContain('lifted');
    expect(late.report).not.toContain('TIME-013');
    const strip = (r: string) => r.split('\n').filter(l => !l.includes('Elapsed')).join('\n');
    expect(strip(late.report)).toBe(strip(onTime.report));
  });
});

describeZ3('reap-awareness on every quiescence route', () => {
  it('the firing bound reads the reaped rest', async () => {
    const r = await verifier(witness()).property(deadlockFree()).stateEquationPhase(false).verify();
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.report).toContain('Firing bound (VER-019)');
    expect(r.counterexampleTransitions).toEqual([]);
    const strict = await verifier(witness()).property(deadlockFree()).stateEquationPhase(false)
      .assumeNoReaping(true).verify();
    expect(strict.verdict.type, strict.report).toBe('proven');
  });

  it('the state-equation phase reads the reaped rest', async () => {
    const r = await verifier(witness()).property(deadlockFree()).firingBound(false).verify();
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.report).toContain('State-equation phase (VER-018)');
    const strict = await verifier(witness()).property(deadlockFree()).firingBound(false)
      .assumeNoReaping(true).verify();
    expect(strict.verdict.type, strict.report).toBe('proven');
  });

  it('Route A reads a reaped join as resting', async () => {
    const source = place('source');
    const budget = place('budget');
    const ba = place<string>('branchA');
    const bb = place<string>('branchB');
    const merged = place<string>('merged');
    const key = (v: string) => nameId(v);
    const fork = Transition.builder('fork').inputs(one(source), one(budget)).outputs(andPlaces(ba, bb)).build();
    const join = Transition.builder('join').timing(window(50, 200))
      .inputs(one(ba), one(bb))
      .match(matchSpec(matchKey(ba, key), matchKey(bb, key)))
      .outputs(outPlace(merged))
      .build();
    const net = bindProducers(PetriNet.builder('reaped-join-route-a').transitions(fork, join).build());
    const run = (noReaping: boolean) => SmtVerifier.forNet(net).mintTransitions(...allMints(net))
      .enumerationMaxClasses(0)
      .initialMarking(m => m.tokens(source, 1).tokens(budget, 1))
      .property(deadlockFree())
      .sinkPlaces(merged)
      .budgetPlaces(budget)
      .nuMaxClasses(1)
      .assumeNoReaping(noReaping)
      .timeout(30_000)
      .verify();
    const reaping = await run(false);
    expect(reaping.report).toContain('ν-encoding: name-coloured');
    expect(reaping.verdict.type, reaping.report).toBe('violated');
    const strict = await run(true);
    expect(strict.verdict.type, strict.report).not.toBe('violated');
  }, 120_000);

  it('the timed check never turns a violation and names its assumptions', async () => {
    const net = bindProducers(PetriNet.builder('race')
      .transitions(arc('t1', pRace, aRace, window(3, 5)), arc('t2', pRace, bRace, delayed(10)))
      .build());
    const r = await SmtVerifier.forNet(net).mintTransitions(...allMints(net))
      .initialMarking(m => m.tokens(pRace, 1))
      .property(unreachable(new Set([bRace])))
      .timedCounterexampleCheck(true)
      .timeout(30_000)
      .verify();
    expect(r.verdict.type, r.report).toBe('violated');
    expect(r.counterexampleTiming, r.report).toBe('spurious-under-timing');
    expect(r.report).toContain('assumes an on-time executor');
    expect(r.report).toContain('atomic');
  });
});
