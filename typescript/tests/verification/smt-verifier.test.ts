import { describe, it, expect } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import {
  deadlockFree, mutualExclusion, placeBound, unreachable,
  branchPlaceBound, joinedOrDeadLettered,
} from '../../src/verification/smt-property.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place, environmentPlace } from '../../src/core/place.js';
import { one, exactly } from '../../src/core/in.js';
import { outPlace, xorPlaces, andPlaces } from '../../src/core/out.js';
import { matchSpec, matchKey } from '../../src/core/match-spec.js';
import { nameId } from '../../src/core/name.js';
import { alwaysAvailable, bounded, ignore } from '../../src/verification/analysis/environment-analysis-mode.js';

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

  it('xor branch to sink deadlocks with environment place', async () => {
    // Idle=1 (processing resource), Trigger=env (external events)
    // Dispatch: Idle + Trigger -> XOR(Active, Rejected)
    // Complete: Active -> Idle (loop back)
    // Rejected is a sink — no transition consumes from it.
    // XOR expansion means the solver considers the Rejected branch:
    //   Dispatch fires -> Rejected=1, Idle=0 -> no transition enabled -> DEADLOCK
    const idle = place('Idle');
    const trigger = environmentPlace('Trigger');
    const active = place('Active');
    const rejected = place('Rejected');

    const dispatch = Transition.builder('Dispatch')
      .inputs(one(idle), one(trigger.place))
      .outputs(xorPlaces(active, rejected))
      .build();
    const complete = Transition.builder('Complete')
      .inputs(one(active))
      .outputs(outPlace(idle))
      .build();

    const net = PetriNet.builder('XorSinkNet').transitions(dispatch, complete).build();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(idle, 1))
      .environmentPlaces(trigger)
      .environmentMode(alwaysAvailable())
      .property(deadlockFree())
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('violated');
    expect(result.counterexampleTrace.length).toBeGreaterThan(0);
    // Strengthened: the violation must be the real Rejected-sink path (Dispatch fired
    // via env injection), NOT the frozen initial state. Pre-fix this passed for the
    // wrong reason (Trigger=0 forever -> initial {Idle:1} was itself a deadlock).
    const reachedRejected = result.counterexampleTrace.some(m => m.tokens(rejected) > 0);
    expect(reachedRejected).toBe(true);
  }, Z3_TIMEOUT);

  // ---------------------------------------------------------------------------
  // VER-006: Environment Analysis Mode — env injection broadens reachability.
  // Regression for the soundness bug where SmtVerifier vacuously "proved" safety
  // bounds on nets with environment places (env columns could only be consumed,
  // never produced, so the reachable set froze at the initial marking).
  // Net: env IN -> T -> OUT. Under AlwaysAvailable, IN can be injected without
  // bound, so OUT grows without bound and placeBound(OUT, k) is violated for all k.
  // ---------------------------------------------------------------------------
  describe('VER-006 environment injection soundness', () => {
    const envSourceNet = () => {
      const inEnv = environmentPlace('IN');
      const out = place('OUT');
      const t = Transition.builder('T')
        .inputs(one(inEnv.place))
        .outputs(outPlace(out))
        .build();
      const net = PetriNet.builder('env-source').transitions(t).build();
      return { inEnv, out, net };
    };

    for (const k of [0, 1, 5]) {
      it(`alwaysAvailable injects: placeBound(OUT, ${k}) is violated`, async () => {
        const { inEnv, out, net } = envSourceNet();
        const result = await SmtVerifier.forNet(net)
          .environmentPlaces(inEnv)
          .environmentMode(alwaysAvailable())
          .property(placeBound(out, k))
          .timeout(30_000)
          .verify();
        expect(result.verdict.type).toBe('violated');
      }, Z3_TIMEOUT);
    }

    it('bounded(k) gates env input by per-firing multiplicity (VER-006 AC#3)', async () => {
      // T2 needs EXACTLY 2 tokens from env IN per firing. bounded(k) limits how
      // many env tokens a single firing may draw (consistent with the state class
      // graph): bounded(1) starves T2 (proven OUT stays 0), alwaysAvailable feeds
      // it without limit (violated). This also exercises the env-aware P-invariant:
      // the closed-net law IN + 2*OUT = 0 must be discarded so OUT is not pinned.
      const buildNet = () => {
        const inEnv = environmentPlace('IN');
        const out = place('OUT');
        const t = Transition.builder('T2')
          .inputs(exactly(2, inEnv.place))
          .outputs(outPlace(out))
          .build();
        const net = PetriNet.builder('env-mult').transitions(t).build();
        return { inEnv, out, net };
      };

      const b = buildNet();
      const bounded1 = await SmtVerifier.forNet(b.net)
        .environmentPlaces(b.inEnv)
        .environmentMode(bounded(1))
        .property(placeBound(b.out, 0))
        .timeout(30_000)
        .verify();
      expect(bounded1.verdict.type).toBe('proven');

      const a = buildNet();
      const always = await SmtVerifier.forNet(a.net)
        .environmentPlaces(a.inEnv)
        .environmentMode(alwaysAvailable())
        .property(placeBound(a.out, 0))
        .timeout(30_000)
        .verify();
      expect(always.verdict.type).toBe('violated');
    }, Z3_TIMEOUT);

    it('ignore mode with env places does not silently prove (downgrades to unknown)', async () => {
      const { inEnv, out, net } = envSourceNet();
      const result = await SmtVerifier.forNet(net)
        .environmentPlaces(inEnv)
        .environmentMode(ignore())
        .property(placeBound(out, 1))
        .timeout(30_000)
        .verify();
      // Ignore mode does not model injection; a "proven" here would be vacuous.
      expect(result.verdict.type).toBe('unknown');
    }, Z3_TIMEOUT);

    it('control: closed net placeBound stays sound (defect is env-specific)', async () => {
      const a = place('A');
      const b = place('B');
      const t1 = Transition.builder('AtoB').inputs(one(a)).outputs(outPlace(b)).build();
      const t2 = Transition.builder('BtoA').inputs(one(b)).outputs(outPlace(a)).build();
      const net = PetriNet.builder('closed-cycle').transitions(t1, t2).build();

      const safe = await SmtVerifier.forNet(net)
        .initialMarking(m => m.tokens(a, 1))
        .property(placeBound(b, 1))
        .timeout(30_000)
        .verify();
      expect(safe.verdict.type).toBe('proven');

      const unsafe = await SmtVerifier.forNet(net)
        .initialMarking(m => m.tokens(a, 1))
        .property(placeBound(b, 0))
        .timeout(30_000)
        .verify();
      expect(unsafe.verdict.type).toBe('violated');
    }, Z3_TIMEOUT);
  });

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

// === NU-040 / NU-050: ν-net verification (sound carve-out, Stage 6a) ===
// The untimed encoder over-approximates ν-join name equality. That is sound for
// reachability-safety bounds (a `proven` holds for the real net) — so the
// bounded-budget decidability lever is checkable today — but not for quiescence
// properties, and not for unbounded fresh names.
describe('SmtVerifier ν-net carve-out (NU-040/NU-050)', () => {
  // Structural scatter-gather: `fork` consumes a `budget` token and stamps a
  // `pending` token plus both branches; `join` correlates the branches by name,
  // consumes `pending`, and returns the `budget` token. The conservation laws
  // budget+pending=k and branchA=branchB=pending hold regardless of names, so
  // the over-approximation can prove the bounds.
  function nuScatterGatherNet() {
    const source = place('source');
    const budget = place('budget');
    const pending = place('pending');
    const a = place<string>('branchA');
    const b = place<string>('branchB');
    const merged = place<string>('merged');

    const fork = Transition.builder('fork')
      .inputs(one(source), one(budget))
      .outputs(andPlaces(a, b, pending))
      .build();

    const join = Transition.builder('join')
      .inputs(one(a), one(b), one(pending))
      .match(matchSpec(
        matchKey(a, (s: string) => nameId(s)),
        matchKey(b, (s: string) => nameId(s)),
      ))
      .outputs(andPlaces(merged, budget))
      .build();

    const net = PetriNet.builder('nuScatterGatherVerify').transitions(fork, join).build();
    return { net, source, budget, pending };
  }

  it('proves BranchPlaceBound(budget, k) with a declared budget', async () => {
    // NU-040 #1: the live correlation pool is bounded by conservation.
    const { net, source, budget } = nuScatterGatherNet();
    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => { m.tokens(source, 3); m.tokens(budget, 2); })
      .property(branchPlaceBound(budget, 2))
      .budgetPlaces(budget)
      .timeout(30_000)
      .verify();
    expect(result.verdict.type).toBe('proven');
  }, Z3_TIMEOUT);

  it('proves BranchPlaceBound(pending, k) exactly via name-colouring', async () => {
    // NU-040 #2 (bound half): at most k live groups. The scatter-gather is in the
    // name-coloured fragment, so the bound is decided exactly (NU-050 #1), not via
    // the name-blind over-approximation.
    const { net, source, budget, pending } = nuScatterGatherNet();
    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => { m.tokens(source, 3); m.tokens(budget, 2); })
      .property(branchPlaceBound(pending, 2))
      .budgetPlaces(budget)
      .timeout(30_000)
      .verify();
    expect(result.verdict.type).toBe('proven');
    expect(result.report).toContain('name-coloured');
  }, Z3_TIMEOUT);

  it('returns unknown for an undeclared-budget ν-net (NU-050 #2)', async () => {
    // Treated as unbounded — unknown rather than a precision-limited verdict,
    // even for a bound the over-approximation could prove.
    const { net, source, budget } = nuScatterGatherNet();
    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => { m.tokens(source, 3); m.tokens(budget, 2); })
      .property(branchPlaceBound(budget, 2))
      .timeout(30_000)
      .verify();
    expect(result.verdict.type).toBe('unknown');
    const reason = (result.verdict as { type: 'unknown'; reason: string }).reason;
    expect(reason).toContain('budget');
    expect(reason).toContain('unbounded');
  }, Z3_TIMEOUT);

  it('returns unknown for JoinedOrDeadLettered on a ν-net (quiescence deferred)', async () => {
    const { net, source, budget, pending } = nuScatterGatherNet();
    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => { m.tokens(source, 3); m.tokens(budget, 2); })
      .property(joinedOrDeadLettered(pending))
      .budgetPlaces(budget)
      .timeout(30_000)
      .verify();
    expect(result.verdict.type).toBe('unknown');
  }, Z3_TIMEOUT);

  it('returns unknown for DeadlockFree on a ν-net (quiescence deferred)', async () => {
    const { net, source, budget } = nuScatterGatherNet();
    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => { m.tokens(source, 3); m.tokens(budget, 2); })
      .property(deadlockFree())
      .budgetPlaces(budget)
      .timeout(30_000)
      .verify();
    expect(result.verdict.type).toBe('unknown');
  }, Z3_TIMEOUT);

  it('proves JoinedOrDeadLettered on a non-ν net where pending always drains', async () => {
    const start = place('start');
    const pending = place('pending');
    const done = place('done');
    const produce = Transition.builder('gen').inputs(one(start)).outputs(outPlace(pending)).build();
    const fin = Transition.builder('fin').inputs(one(pending)).outputs(outPlace(done)).build();
    const net = PetriNet.builder('pendingDrains').transitions(produce, fin).build();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(start, 1))
      .property(joinedOrDeadLettered(pending))
      .timeout(30_000)
      .verify();
    expect(result.verdict.type).toBe('proven');
  }, Z3_TIMEOUT);

  it('finds JoinedOrDeadLettered violated on a non-ν net with a stranded pending', async () => {
    const start = place('start');
    const pending = place('pending');
    const leak = Transition.builder('leak').inputs(one(start)).outputs(outPlace(pending)).build();
    const net = PetriNet.builder('pendingStrands').transitions(leak).build();

    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => m.tokens(start, 1))
      .property(joinedOrDeadLettered(pending))
      .timeout(30_000)
      .verify();
    expect(result.verdict.type).toBe('violated');
  }, Z3_TIMEOUT);

  // === NU-050 #1: name-coloured exact ν-verification (Stage 6b, Route A) ===
  // The flat encoder over-approximates ν-join name equality (name-blind). The
  // bounded name-coloured encoding (k = budget) decides it exactly: a join fires
  // only on same-coloured tokens, so a counterexample requiring two distinct names
  // to be equal is eliminated.

  // Two INDEPENDENT mints feed one join: `forkA` mints a name into branchA,
  // `forkB` a DIFFERENT name into branchB. Their names can never be equal, so the
  // join can never correlate them and `merged` is unreachable. The name-blind
  // over-approximation would (wrongly) fire the join — the spurious "two distinct
  // names are equal" counterexample NU-050 #1 kills.
  function nuDistinctMintsNet() {
    const sourceA = place('sourceA');
    const sourceB = place('sourceB');
    const budget = place('budget');
    const a = place<string>('branchA');
    const b = place<string>('branchB');
    const merged = place<string>('merged');

    const forkA = Transition.builder('forkA')
      .inputs(one(sourceA), one(budget))
      .outputs(outPlace(a))
      .build();
    const forkB = Transition.builder('forkB')
      .inputs(one(sourceB), one(budget))
      .outputs(outPlace(b))
      .build();
    const join = Transition.builder('join')
      .inputs(one(a), one(b))
      .match(matchSpec(
        matchKey(a, (s: string) => nameId(s)),
        matchKey(b, (s: string) => nameId(s)),
      ))
      .outputs(outPlace(merged))
      .build();

    const net = PetriNet.builder('nuDistinctMints').transitions(forkA, forkB, join).build();
    return { net, sourceA, sourceB, budget, merged };
  }

  it('proves Unreachable(merged) for distinct mints via name-colouring (NU-050 #1)', async () => {
    // Distinct globally-fresh colours can never match -> merged unreachable -> proven.
    // The name-blind over-approximation would report this violated (spurious).
    const { net, sourceA, sourceB, budget, merged } = nuDistinctMintsNet();
    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => { m.tokens(sourceA, 1); m.tokens(sourceB, 1); m.tokens(budget, 2); })
      .property(unreachable(new Set([merged])))
      .budgetPlaces(budget)
      .timeout(30_000)
      .verify();
    expect(result.verdict.type).toBe('proven');
    expect(result.report).toContain('name-coloured');
  }, Z3_TIMEOUT);

  it('finds Unreachable(merged) violated for same-mint siblings (non-vacuity)', async () => {
    // Companion: the SAME-mint scatter-gather stamps both branches with one name,
    // so the join CAN fire and `merged` IS reachable. The colouring tracks real
    // reachability — Unreachable(merged) is violated.
    const { net, source, budget } = nuScatterGatherNet();
    const merged = place<string>('merged');
    const result = await SmtVerifier.forNet(net)
      .initialMarking(m => { m.tokens(source, 3); m.tokens(budget, 2); })
      .property(unreachable(new Set([merged])))
      .budgetPlaces(budget)
      .timeout(30_000)
      .verify();
    expect(result.verdict.type).toBe('violated');
  }, Z3_TIMEOUT);
});
