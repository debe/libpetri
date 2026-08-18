import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { checkCertificate } from '../../src/verification/z3/certificate-checker.js';
import { createSpacerRunner, type SpacerContext } from '../../src/verification/z3/spacer-runner.js';
import { flatten } from '../../src/verification/encoding/net-flattener.js';
import type { FlatNet } from '../../src/verification/encoding/flat-net.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { IncidenceMatrix } from '../../src/verification/encoding/incidence-matrix.js';
import { computePInvariants, validateInvariantsExact } from '../../src/verification/invariant/p-invariant-computer.js';
import { pInvariant, type PInvariant } from '../../src/verification/invariant/p-invariant.js';
import { placeBound } from '../../src/verification/smt-property.js';
import { alwaysAvailable } from '../../src/verification/analysis/environment-analysis-mode.js';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one, exactly } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { bindProducers } from '../fixtures/producing-actions.js';

// All tests in this file require Z3 WASM which is slow to initialize.
// Tests are set to a generous timeout.
const Z3_TIMEOUT = 60_000;

const pA = place('A');
const pB = place('B');

/** Circular net A ⇄ B (single token conserved). */
function circularNet(): PetriNet {
  const t1 = Transition.builder('AtoB').inputs(one(pA)).outputs(outPlace(pB)).build();
  const t2 = Transition.builder('BtoA').inputs(one(pB)).outputs(outPlace(pA)).build();
  return PetriNet.builder('CircularNet').transitions(t1, t2).build();
}

/**
 * Weighted net: A → B and 2B → A. No P-invariant exists (the incidence columns
 * are independent), and the hand-built certificate 2A + B ≤ 4 is inductive
 * ONLY in the correct place orientation — swapping the de Bruijn mapping turns
 * it into A + 2B ≤ 4, which transition AtoB violates (e.g. (2,1) → (1,2)).
 */
function weightedNet(): PetriNet {
  const t1 = Transition.builder('AtoB').inputs(one(pA)).outputs(outPlace(pB)).build();
  const t2 = Transition.builder('BBtoA').inputs(exactly(2, pB)).outputs(outPlace(pA)).build();
  return PetriNet.builder('WeightedNet').transitions(t1, t2).build();
}

describe('checkCertificate (unit)', () => {
  let runner: SpacerContext;
  let ctx: any;

  beforeAll(async () => {
    runner = await createSpacerRunner(30_000);
    ctx = runner.ctx;
  }, Z3_TIMEOUT);

  afterAll(() => {
    runner.dispose();
  });

  /** Bound-variable per place index: qvars[j] is argument j of Reachable. */
  function qvars(flatNet: FlatNet): { vars: any[]; vA: any; vB: any } {
    const vars = [ctx.Int.const('qv0'), ctx.Int.const('qv1')];
    return {
      vars,
      vA: vars[flatNet.placeIndex.get('A')!],
      vB: vars[flatNet.placeIndex.get('B')!],
    };
  }

  /** `forall vars. Reachable(vars) = phi` — the shape Spacer produces. */
  function forallAnswer(vars: any[], phi: any): any {
    const reachable = ctx.Function.declare('Reachable', ctx.Int.sort(), ctx.Int.sort(), ctx.Bool.sort());
    return ctx.ForAll(vars, reachable.call(...vars).eq(phi));
  }

  it('hand-built correct invariant passes all three VCs (forall + eq shape)', async () => {
    const flatNet = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const { vars, vA, vB } = qvars(flatNet);
    // A + B = 1 is inductive, holds initially, and excludes B > 1.
    const answer = forallAnswer(vars, vA.add(vB).eq(1));

    const outcome = await checkCertificate(
      ctx, answer, flatNet, m0, placeBound(pB, 1), [], new Set(), 30_000,
    );
    expect(outcome.type).toBe('passed');
  }, Z3_TIMEOUT);

  it('maps de Bruijn indices by Reachable argument position, not declaration order', async () => {
    const flatNet = flatten(weightedNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 2).build();
    const { vars, vA, vB } = qvars(flatNet);
    // 2A + B <= 4 is inductive; the de Bruijn swap A + 2B <= 4 is NOT
    // (AtoB fires (2,1) -> (1,2)), so a mis-ordered substitution fails VC2.
    const answer = forallAnswer(vars, vA.mul(2).add(vB).le(4));

    const outcome = await checkCertificate(
      ctx, answer, flatNet, m0, placeBound(pB, 4), [], new Set(), 30_000,
    );
    expect(outcome.type).toBe('passed');
  }, Z3_TIMEOUT);

  it('handles a ground (unquantified) Reachable definition', async () => {
    const flatNet = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const { vars, vA, vB } = qvars(flatNet);
    const reachable = ctx.Function.declare('Reachable', ctx.Int.sort(), ctx.Int.sort(), ctx.Bool.sort());
    // Same definition, but with free constants instead of a forall.
    const answer = reachable.call(...vars).eq(vA.add(vB).eq(1));

    const outcome = await checkCertificate(
      ctx, answer, flatNet, m0, placeBound(pB, 1), [], new Set(), 30_000,
    );
    expect(outcome.type).toBe('passed');
  }, Z3_TIMEOUT);

  /** Hand-built P-invariant over named places (weights indexed by place index). */
  function handInvariant(flatNet: FlatNet, entries: Record<string, number>, constant: number): PInvariant {
    const weights = new Array<number>(flatNet.places.length).fill(0);
    const support = new Set<number>();
    for (const [name, w] of Object.entries(entries)) {
      const idx = flatNet.placeIndex.get(name)!;
      weights[idx] = w;
      support.add(idx);
    }
    return pInvariant(weights, constant, support);
  }

  it('strengthening-dependent certificate passes with the validated P-invariants', async () => {
    const flatNet = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const { vars, vB } = qvars(flatNet);
    // The shape Spacer synthesizes against strengthened CHC bodies on the
    // conservation cycle: ¬(B ≥ 2) — inductive only RELATIVE to A + B = 1
    // (e.g. (2,1) → (1,2) violates it bare).
    const answer = forallAnswer(vars, ctx.Not(vB.ge(2)));

    // Bare candidate (no invariants): consecution must fail...
    const bare = await checkCertificate(
      ctx, answer, flatNet, m0, placeBound(pB, 1), [], new Set(), 30_000,
    );
    expect(bare.type).toBe('failed');
    if (bare.type === 'failed') {
      expect(bare.reason).toBe('consecution not inductive');
    }

    // ...but the candidate strengthened with the verifier's validated
    // P-invariants (A + B = 1) is a genuine certificate.
    const matrix = IncidenceMatrix.from(flatNet);
    const { valid: invariants } = validateInvariantsExact(
      matrix, computePInvariants(matrix, flatNet, m0), flatNet, m0,
    );
    expect(invariants.length).toBeGreaterThan(0);
    const outcome = await checkCertificate(
      ctx, answer, flatNet, m0, placeBound(pB, 1), invariants, new Set(), 30_000,
    );
    expect(outcome.type).toBe('passed');
  }, Z3_TIMEOUT);

  it('poisoned P-invariant (wrong constant) fails VC1 of the candidate', async () => {
    const flatNet = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const { vars, vB } = qvars(flatNet);
    const answer = forallAnswer(vars, ctx.Not(vB.ge(2)));
    // A + B = 2 contradicts the initial marking A + B = 1.
    const poisoned = handInvariant(flatNet, { A: 1, B: 1 }, 2);

    const outcome = await checkCertificate(
      ctx, answer, flatNet, m0, placeBound(pB, 1), [poisoned], new Set(), 30_000,
    );
    expect(outcome.type).toBe('failed');
    if (outcome.type === 'failed') {
      expect(outcome.reason).toMatch(/init not covered/);
    }
  }, Z3_TIMEOUT);

  it('poisoned P-invariant (wrong weights) fails VC2 of the candidate', async () => {
    const flatNet = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const { vars } = qvars(flatNet);
    const answer = forallAnswer(vars, ctx.Bool.val(true));
    // 2A + B = 2 holds initially but AtoB fires (1,0) → (0,1): 1 ≠ 2.
    const poisoned = handInvariant(flatNet, { A: 2, B: 1 }, 2);

    const outcome = await checkCertificate(
      ctx, answer, flatNet, m0, placeBound(pB, 1), [poisoned], new Set(), 30_000,
    );
    expect(outcome.type).toBe('failed');
    if (outcome.type === 'failed') {
      expect(outcome.reason).toBe('consecution not inductive');
    }
  }, Z3_TIMEOUT);

  it('corrupted invariant `true` fails VC3 (safety)', async () => {
    const flatNet = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const { vars } = qvars(flatNet);
    // `true` trivially satisfies init and consecution but admits B > 1.
    const answer = forallAnswer(vars, ctx.Bool.val(true));

    const outcome = await checkCertificate(
      ctx, answer, flatNet, m0, placeBound(pB, 1), [], new Set(), 30_000,
    );
    expect(outcome.type).toBe('failed');
    if (outcome.type === 'failed') {
      expect(outcome.reason).toMatch(/safety not implied/);
      expect(outcome.invariant).toBe('true');
    }
  }, Z3_TIMEOUT);

  it('consecution-violating invariant fails VC2', async () => {
    const flatNet = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const { vars, vB } = qvars(flatNet);
    // B = 0 holds initially but AtoB fires (1,0) -> (0,1).
    const answer = forallAnswer(vars, vB.eq(0));

    const outcome = await checkCertificate(
      ctx, answer, flatNet, m0, placeBound(pB, 1), [], new Set(), 30_000,
    );
    expect(outcome.type).toBe('failed');
    if (outcome.type === 'failed') {
      expect(outcome.reason).toBe('consecution not inductive');
    }
  }, Z3_TIMEOUT);

  it('init-excluding invariant fails VC1', async () => {
    const flatNet = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const { vars, vA } = qvars(flatNet);
    // A = 0 contradicts the initial marking A = 1.
    const answer = forallAnswer(vars, vA.eq(0));

    const outcome = await checkCertificate(
      ctx, answer, flatNet, m0, placeBound(pB, 1), [], new Set(), 30_000,
    );
    expect(outcome.type).toBe('failed');
    if (outcome.type === 'failed') {
      expect(outcome.reason).toMatch(/init not covered/);
    }
  }, Z3_TIMEOUT);

  it('missing answer (null) fails as invariant missing', async () => {
    const flatNet = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();

    const outcome = await checkCertificate(
      ctx, null, flatNet, m0, placeBound(pB, 1), [], new Set(), 30_000,
    );
    expect(outcome.type).toBe('failed');
    if (outcome.type === 'failed') {
      expect(outcome.reason).toMatch(/invariant missing/);
    }
  }, Z3_TIMEOUT);

  it('answer without a Reachable definition fails as unparseable', async () => {
    const flatNet = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();

    const outcome = await checkCertificate(
      ctx, ctx.Bool.val(true), flatNet, m0, placeBound(pB, 1), [], new Set(), 30_000,
    );
    expect(outcome.type).toBe('failed');
    if (outcome.type === 'failed') {
      expect(outcome.reason).toMatch(/unparseable/);
    }
  }, Z3_TIMEOUT);
});

describe('SmtVerifier certificate check wiring', () => {
  it('IC3-proven verdict carries the certificate PASSED line (default on)', async () => {
    const result = await SmtVerifier.forNet(bindProducers(circularNet()))
      .initialMarking(m => m.tokens(pA, 1))
      .property(placeBound(pB, 1))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
    expect(result.report).toContain('  Certificate check: PASSED (init, consecution, safety)');
  }, Z3_TIMEOUT);

  it('certificateCheck(false) skips the check', async () => {
    const result = await SmtVerifier.forNet(bindProducers(circularNet()))
      .initialMarking(m => m.tokens(pA, 1))
      .property(placeBound(pB, 1))
      .certificateCheck(false)
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
    expect(result.report).not.toContain('Certificate check');
  }, Z3_TIMEOUT);
});
