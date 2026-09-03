import { describe, it, expect } from 'vitest';
import { checkCertificate, parseVcResults, reasonUnknown, witness } from '../../src/verification/z3/certificate-checker.js';
import { resolveZ3, type Z3Solver } from '../../src/verification/z3/z3-process.js';
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
import { place, environmentPlace } from '../../src/core/place.js';
import { one, exactly } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { bindProducers } from '../fixtures/producing-actions.js';
import { describeZ3 } from '../fixtures/z3.js';

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
 * Weighted net: A → B and 2B → A. No P-invariant exists (the incidence columns are
 * independent), and the hand-written certificate 2A + B ≤ 4 is inductive ONLY in the
 * correct place orientation — swapping the parameters turns it into A + 2B ≤ 4, which
 * transition AtoB violates (e.g. (2,1) → (1,2)).
 */
function weightedNet(): PetriNet {
  const t1 = Transition.builder('AtoB').inputs(one(pA)).outputs(outPlace(pB)).build();
  const t2 = Transition.builder('BBtoA').inputs(exactly(2, pB)).outputs(outPlace(pA)).build();
  return PetriNet.builder('WeightedNet').transitions(t1, t2).build();
}

/** The parameter list `((x!0 Int) (x!1 Int) …)` for `P` places. */
function params(P: number): string {
  const parts: string[] = [];
  for (let i = 0; i < P; i++) parts.push(`(x!${i} Int)`);
  return `(${parts.join(' ')})`;
}

/** `(define-fun Reachable <params> Bool <body>)`, parameter j standing for place j. */
function certificate(flat: FlatNet, body: string): string {
  return `(define-fun Reachable ${params(flat.places.length)} Bool\n    ${body})`;
}

function v(flat: FlatNet, name: string): string {
  return `x!${flat.placeIndex.get(name)!}`;
}

describeZ3('checkCertificate (unit)', () => {
  const solver: Z3Solver = resolveZ3();

  function check(cert: string | null, flat: FlatNet, m0: MarkingState, bound: number, invariants: readonly PInvariant[] = []) {
    return checkCertificate(cert, flat, m0, placeBound(pB, bound), invariants, new Set(), solver, 30_000);
  }

  it('hand-written correct invariant passes all three VCs', async () => {
    const flat = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    // A + B = 1 is inductive, holds initially, and excludes B > 1.
    const outcome = await check(certificate(flat, `(= (+ ${v(flat, 'A')} ${v(flat, 'B')}) 1)`), flat, m0, 1);
    expect(outcome.type).toBe('passed');
  }, Z3_TIMEOUT);

  it('parameters are positional: a body over renamed parameters is the same certificate', async () => {
    const flat = flatten(weightedNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 2).build();
    // 2A + B <= 4 is inductive; the swap A + 2B <= 4 is NOT (AtoB fires (2,1) -> (1,2)).
    const ia = flat.placeIndex.get('A')!;
    const names = ['', ''];
    names[ia] = 'b';
    names[1 - ia] = 'a';
    const cert = `(define-fun Reachable ((${names[0]} Int) (${names[1]} Int)) Bool\n    (<= (+ (* 2 ${names[ia]}) ${names[1 - ia]}) 4))`;
    const outcome = await check(cert, flat, m0, 4);
    expect(outcome.type).toBe('passed');
  }, Z3_TIMEOUT);

  it('a |quoted| Reachable head is accepted', async () => {
    const flat = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const cert = `(define-fun |Reachable| ${params(2)} Bool\n    (= (+ ${v(flat, 'A')} ${v(flat, 'B')}) 1))`;
    expect((await check(cert, flat, m0, 1)).type).toBe('passed');
  }, Z3_TIMEOUT);

  it('auxiliary definitions of the model block stay resolvable', async () => {
    const flat = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const cert = '(define-fun Error () Bool\n    false)\n(define-fun one () Int\n    1)\n'
      + certificate(flat, `(= (+ ${v(flat, 'A')} ${v(flat, 'B')}) one)`);
    expect((await check(cert, flat, m0, 1)).type).toBe('passed');
  }, Z3_TIMEOUT);

  /** Hand-built P-invariant over named places (weights indexed by place index). */
  function handInvariant(flat: FlatNet, entries: Record<string, number>, constant: number): PInvariant {
    const weights = new Array<number>(flat.places.length).fill(0);
    const support = new Set<number>();
    for (const [name, w] of Object.entries(entries)) {
      const idx = flat.placeIndex.get(name)!;
      weights[idx] = w;
      support.add(idx);
    }
    return pInvariant(weights, constant, support);
  }

  it('strengthening-dependent certificate passes with the validated P-invariants', async () => {
    const flat = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    // The shape Spacer synthesizes against strengthened CHC bodies on the
    // conservation cycle: ¬(B ≥ 2) — inductive only RELATIVE to A + B = 1.
    const cert = certificate(flat, `(not (>= ${v(flat, 'B')} 2))`);

    const bare = await check(cert, flat, m0, 1);
    expect(bare.type).toBe('failed');
    if (bare.type === 'failed') {
      expect(bare.vc).toBe('consecution (VC2)');
      expect(bare.detail).toMatch(/^solver returned SATISFIABLE/);
    }

    const matrix = IncidenceMatrix.from(flat);
    const { valid: invariants } = validateInvariantsExact(matrix, computePInvariants(matrix, flat, m0), flat, m0);
    expect(invariants.length).toBeGreaterThan(0);
    expect((await check(cert, flat, m0, 1, invariants)).type).toBe('passed');
  }, Z3_TIMEOUT);

  it('poisoned P-invariant (wrong constant) fails VC1 of the candidate', async () => {
    const flat = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const poisoned = handInvariant(flat, { A: 1, B: 1 }, 2);
    const outcome = await check(certificate(flat, `(not (>= ${v(flat, 'B')} 2))`), flat, m0, 1, [poisoned]);
    expect(outcome.type).toBe('failed');
    if (outcome.type === 'failed') expect(outcome.vc).toBe('initiation (VC1)');
  }, Z3_TIMEOUT);

  it('poisoned P-invariant (wrong weights) fails VC2 of the candidate', async () => {
    const flat = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    // 2A + B = 2 holds initially but AtoB fires (1,0) → (0,1): 1 ≠ 2.
    const poisoned = handInvariant(flat, { A: 2, B: 1 }, 2);
    const outcome = await check(certificate(flat, 'true'), flat, m0, 1, [poisoned]);
    expect(outcome.type).toBe('failed');
    if (outcome.type === 'failed') expect(outcome.vc).toBe('consecution (VC2)');
  }, Z3_TIMEOUT);

  it('corrupted invariant `true` fails VC3 (safety)', async () => {
    const flat = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const cert = certificate(flat, 'true');
    const outcome = await check(cert, flat, m0, 1);
    expect(outcome.type).toBe('failed');
    if (outcome.type === 'failed') {
      expect(outcome.vc).toBe('safety (VC3)');
      // The detail names the marking that escapes the invariant.
      expect(outcome.detail).toMatch(/^solver returned SATISFIABLE \(witness: /);
      expect(outcome.invariant).toBe(cert);
    }
  }, Z3_TIMEOUT);

  it('consecution-violating invariant fails VC2', async () => {
    const flat = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const outcome = await check(certificate(flat, `(= ${v(flat, 'B')} 0)`), flat, m0, 1);
    expect(outcome.type).toBe('failed');
    if (outcome.type === 'failed') expect(outcome.vc).toBe('consecution (VC2)');
  }, Z3_TIMEOUT);

  it('init-excluding invariant fails VC1', async () => {
    const flat = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const outcome = await check(certificate(flat, `(= ${v(flat, 'A')} 0)`), flat, m0, 1);
    expect(outcome.type).toBe('failed');
    if (outcome.type === 'failed') expect(outcome.vc).toBe('initiation (VC1)');
  }, Z3_TIMEOUT);

  it('env injection is part of the checked step relation', async () => {
    // env E -> Drain -> S with alwaysAvailable injection. I = (E <= 0 AND S >= 0)
    // holds initially and is preserved by every TRANSITION step — only the
    // injection step E' = E+1 breaks it.
    const e = environmentPlace('E');
    const s = place('S');
    const t = Transition.builder('Drain').inputs(one(e.place)).outputs(outPlace(s)).build();
    const flat = flatten(PetriNet.builder('EnvNet').transitions(t).build(), new Set([e]), alwaysAvailable());
    const cert = certificate(flat, `(and (<= ${v(flat, 'E')} 0) (>= ${v(flat, 'S')} 0))`);
    const outcome = await checkCertificate(cert, flat, MarkingState.empty(), placeBound(s, 5), [], new Set(), solver, 30_000);
    expect(outcome.type).toBe('failed');
    if (outcome.type === 'failed') expect(outcome.vc).toBe('consecution (VC2)');
  }, Z3_TIMEOUT);

  it('missing certificate (null) is unavailable, not a failed VC', async () => {
    const flat = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const outcome = await check(null, flat, m0, 1);
    expect(outcome.type).toBe('unavailable');
    if (outcome.type === 'unavailable') expect(outcome.reason).toMatch(/no inductive invariant/);
  }, Z3_TIMEOUT);

  it('a block without a Reachable definition is unavailable', async () => {
    const flat = flatten(circularNet(), new Set(), alwaysAvailable());
    const m0 = MarkingState.builder().tokens(pA, 1).build();
    const outcome = await check('(define-fun Error () Bool false)', flat, m0, 1);
    expect(outcome.type).toBe('unavailable');
    if (outcome.type === 'unavailable') expect(outcome.reason).toBe('certificate does not define Reachable');
  }, Z3_TIMEOUT);
});

describe('certificate reply parsing (no solver)', () => {
  it('parseVcResults wants exactly three answers and no error line', () => {
    expect(parseVcResults('unsat\nunsat\nunsat\n')).toEqual(['unsat', 'unsat', 'unsat']);
    expect(() => parseVcResults('unsat\nunsat\n')).toThrow(/expected 3 VC answers/);
    expect(() => parseVcResults('(error "line 3: x")\nunsat\nunsat\nunsat')).toThrow(/z3 error/);
    expect(() => parseVcResults('timeout')).toThrow(/hard timeout/);
  });

  it('witness reads the model values in place order', () => {
    const flat = flatten(circularNet(), new Set(), alwaysAvailable());
    const model = 'sat\n(\n  (define-fun m1 () Int\n    (- 1))\n  (define-fun m0 () Int\n    2)\n)';
    expect(witness(model, flat)).toBe(`${flat.places[0]!.name}=2, ${flat.places[1]!.name}=-1`);
    expect(witness('unknown', flat)).toBeNull();
  });

  it('reasonUnknown reads the info reply', () => {
    expect(reasonUnknown('unknown\n(:reason-unknown "timeout")')).toBe('timeout');
    expect(reasonUnknown('unknown')).toBeNull();
  });
});

describeZ3('SmtVerifier certificate check wiring', () => {
  it('IC3-proven verdict carries the certificate PASSED line (default on)', async () => {
    const result = await SmtVerifier.forNet(bindProducers(circularNet()))
      .initialMarking(m => m.tokens(pA, 1))
      .property(placeBound(pB, 1))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
    expect(result.report).toContain('  Certificate check: PASSED (init, consecution, safety)');
  }, Z3_TIMEOUT);

  it('certificateCheck(false) skips the check and says so', async () => {
    const result = await SmtVerifier.forNet(bindProducers(circularNet()))
      .initialMarking(m => m.tokens(pA, 1))
      .property(placeBound(pB, 1))
      .certificateCheck(false)
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('proven');
    expect(result.report).toContain('  Certificate check: not applicable (disabled)');
    expect(result.report).not.toContain('Certificate check: PASSED');
  }, Z3_TIMEOUT);
});
