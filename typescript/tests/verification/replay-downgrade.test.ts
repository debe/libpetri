import { it, expect, vi } from 'vitest';
import { SmtVerifier } from '../../src/verification/smt-verifier.js';
import { MarkingState } from '../../src/verification/marking-state.js';
import { placeBound } from '../../src/verification/smt-property.js';
import { PetriNet } from '../../src/core/petri-net.js';
import { Transition } from '../../src/core/transition.js';
import { place } from '../../src/core/place.js';
import { one } from '../../src/core/in.js';
import { outPlace } from '../../src/core/out.js';
import { bindProducers } from '../fixtures/producing-actions.js';
import { describeZ3 } from '../fixtures/z3.js';

const Z3_TIMEOUT = 60_000;

// Two seams reproduce the failure mode replay exists to catch: Spacer claims a
// violation the encoded system cannot reach.
//   1. the runner reports VIOLATED for a query that actually came back proven;
//   2. the decoder yields the initial marking as the only decoded state.
// The net's whole abstract state space is then explored without hitting either
// budget and no marking violates — a genuine `no-chain`, the ONLY outcome that
// may withdraw the verdict.
vi.mock('../../src/verification/z3/spacer-runner.js', async (importOriginal) => {
  const mod = await importOriginal<typeof import('../../src/verification/z3/spacer-runner.js')>();
  return {
    ...mod,
    runZ3Spacer: async (solver: any, timeoutMs: number, smt2: string, phase: string) => {
      const result = await mod.runZ3Spacer(solver, timeoutMs, smt2, phase);
      if (result.type !== 'proven') return result;
      return { type: 'violated' as const, answer: 'unsat' };
    },
  };
});

vi.mock('../../src/verification/z3/counterexample-decoder.js', async (importOriginal) => {
  const mod = await importOriginal<typeof import('../../src/verification/z3/counterexample-decoder.js')>();
  return {
    ...mod,
    decode: (_answer: string, _flatNet: any) => ({
      states: new Set([MarkingState.builder().tokens(place('A'), 1).build()]),
      note: null,
    }),
  };
});

/** A -> B and nothing else; M0 = {A: 1}. */
function twoStepNet() {
  const pA = place('A');
  const pB = place('B');
  const t = Transition.builder('T').inputs(one(pA)).outputs(outPlace(pB)).build();
  return { pA, pB, net: PetriNet.builder('TwoStep').transitions(t).build() };
}

describeZ3('SmtVerifier replay downgrade (unchainable counterexample seam)', () => {
  it('a counterexample with no firing chain downgrades the violated verdict to unknown', async () => {
    const { pA, pB, net } = twoStepNet();

    // placeBound(B, 5) is unreachable in this net, so the search completes.
    const result = await SmtVerifier.forNet(bindProducers(net))
      .initialMarking(m => m.tokens(pA, 1))
      .property(placeBound(pB, 5))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('unknown');
    if (result.verdict.type === 'unknown') {
      expect(result.verdict.reason).toBe(
        'counterexample replay found no firing chain to the violation under the ' +
          'abstract semantics, so VIOLATED is withheld',
      );
    }
    // The replay APPLIED and refuted the trace: `false`, not the `null` that
    // means "replay did not apply" (see SmtVerificationResult).
    expect(result.counterexampleConfirmed).toBe(false);
    expect(result.counterexampleTrace).toHaveLength(0);
    // The report must carry the evidence: the decoded set and the raw Z3 answer.
    expect(result.report).toContain('Counterexample replay: FAILED');
    expect(result.report).toContain('Decoded states (order-free set, 1)');
    expect(result.report).toContain('{A:1}');
    expect(result.report).toContain('Raw Z3 answer:');
    // The downgrade reason says "VIOLATED is withheld"; no VIOLATED verdict is reported.
    expect(result.report).not.toMatch(/^VIOLATED: /m);
  }, Z3_TIMEOUT);

  it('a truncated search keeps the violated verdict, unconfirmed', async () => {
    // Bad state D is 4 steps from M0 and only M0 is decoded, so the segment
    // budget (3) cuts the search short. Truncation is not evidence of a
    // spurious counterexample — the verdict stands with confirmed = false.
    const names = ['A', 'B', 'C', 'D', 'E'] as const;
    const places = names.map(n => place(n));
    const transitions = [];
    for (let i = 0; i + 1 < places.length; i++) {
      transitions.push(
        Transition.builder(`T${i}`).inputs(one(places[i]!)).outputs(outPlace(places[i + 1]!)).build(),
      );
    }
    const net = PetriNet.builder('LongChain').transitions(...transitions).build();

    const result = await SmtVerifier.forNet(bindProducers(net))
      .initialMarking(m => m.tokens(places[0]!, 1))
      .property(placeBound(places[4]!, 0))
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('violated');
    expect(result.counterexampleConfirmed).toBe(false);
    expect(result.report).toContain('Counterexample replay: UNCONFIRMED');
    expect(result.report).toContain('abstract replay did not complete');
  }, Z3_TIMEOUT);

  it('counterexampleReplay(false) bypasses the downgrade (verdict stays violated)', async () => {
    const { pA, pB, net } = twoStepNet();

    const result = await SmtVerifier.forNet(bindProducers(net))
      .initialMarking(m => m.tokens(pA, 1))
      .property(placeBound(pB, 0))
      .counterexampleReplay(false)
      .timeout(30_000)
      .verify();

    expect(result.verdict.type).toBe('violated');
    expect(result.counterexampleConfirmed).toBeNull();
  }, Z3_TIMEOUT);
});
